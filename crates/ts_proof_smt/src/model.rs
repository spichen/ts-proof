//! S-expression parser for Z3 `(get-model)` output.
//!
//! Only `define-fun` constants with no arguments are read. Quantified or
//! functional interpretations are rejected so a partial model cannot be
//! presented as a complete counterexample.

use std::collections::BTreeMap;
use ts_proof_vir::{Value, VirType};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

pub fn values_from_model(
    output: &str,
    sorts: &BTreeMap<String, VirType>,
) -> Result<BTreeMap<String, Value>, String> {
    let sexps = parse_sexps(output)?;
    let mut model = BTreeMap::new();
    for sexp in sexps {
        collect(&sexp, sorts, &mut model)?;
    }
    Ok(model)
}

fn collect(
    sexp: &Sexp,
    sorts: &BTreeMap<String, VirType>,
    model: &mut BTreeMap<String, Value>,
) -> Result<(), String> {
    let Sexp::List(items) = sexp else {
        return Ok(());
    };
    if items.first().and_then(atom) == Some("define-fun") {
        // (define-fun smt_name () Sort value)
        if items.len() < 5 {
            return Err(format!("short define-fun: {sexp:?}"));
        }
        let smt_name = atom(&items[1]).ok_or("define-fun name")?.to_string();
        let args = match &items[2] {
            Sexp::List(args) if args.is_empty() => args,
            _ => {
                return Err(format!(
                    "refusing a function interpretation in the model for {smt_name}"
                ));
            }
        };
        let _ = args;
        let source_name = source_name_for(&smt_name, sorts);
        let sort = sorts.get(&source_name).copied();
        let value = read_value(&items[4], sort)?;
        model.insert(source_name, value);
        return Ok(());
    }
    for item in items {
        if matches!(item, Sexp::List(_)) {
            collect(item, sorts, model)?;
        }
    }
    Ok(())
}

fn source_name_for(smt_name: &str, sorts: &BTreeMap<String, VirType>) -> String {
    for name in sorts.keys() {
        if crate::smt_symbol(name) == smt_name {
            return name.clone();
        }
    }
    smt_name.to_string()
}

fn read_value(sexp: &Sexp, sort: Option<VirType>) -> Result<Value, String> {
    match sexp {
        Sexp::Atom(atom) => atom_value(atom, sort),
        Sexp::List(items) => match (items.first().and_then(atom), sort) {
            (Some("-"), Some(VirType::Int) | None) if items.len() == 2 => {
                let n = read_value(&items[1], Some(VirType::Int))?;
                match n {
                    Value::Int(n) => Ok(Value::Int(ts_proof_vir::canon(&format!("-{n}")))),
                    other => Err(format!("negation of non-int {other}")),
                }
            }
            (Some("ite"), _) => Err("refusing ite in a counterexample constant".into()),
            (Some("-"), _) => Err(format!("unexpected negation for sort {sort:?}")),
            _ => Err(format!("unsupported model value {sexp:?}")),
        },
    }
}

fn atom_value(atom: &str, sort: Option<VirType>) -> Result<Value, String> {
    if atom == "true" {
        return Ok(Value::Bool(true));
    }
    if atom == "false" {
        return Ok(Value::Bool(false));
    }
    if let Some(text) = atom.strip_prefix('"') {
        let text = text.strip_suffix('"').unwrap_or(text);
        return Ok(Value::Str(text.replace("\"\"", "\"")));
    }
    if atom.bytes().all(|b| b.is_ascii_digit()) || (atom.starts_with('-') && atom.len() > 1) {
        return Ok(Value::Int(ts_proof_vir::canon(atom)));
    }
    Err(format!("cannot read model atom `{atom}` as {sort:?}"))
}

fn atom(sexp: &Sexp) -> Option<&str> {
    match sexp {
        Sexp::Atom(text) => Some(text.as_str()),
        Sexp::List(_) => None,
    }
}

fn parse_sexps(input: &str) -> Result<Vec<Sexp>, String> {
    let mut parser = Parser {
        chars: input.chars().collect(),
        i: 0,
    };
    let mut out = Vec::new();
    parser.skip();
    while parser.i < parser.chars.len() {
        // Z3 prints `sat` / `unsat` before the model. Skip bare words that are
        // not lists; the solver outcome is decided by the caller.
        if parser.chars[parser.i] != '(' {
            while parser.i < parser.chars.len() && !parser.chars[parser.i].is_whitespace() && parser.chars[parser.i] != '('
            {
                parser.i += 1;
            }
            parser.skip();
            continue;
        }
        out.push(parser.parse_one()?);
        parser.skip();
    }
    Ok(out)
}

struct Parser {
    chars: Vec<char>,
    i: usize,
}

impl Parser {
    fn skip(&mut self) {
        while self.i < self.chars.len() && self.chars[self.i].is_whitespace() {
            self.i += 1;
        }
        if self.starts_with(";") {
            while self.i < self.chars.len() && self.chars[self.i] != '\n' {
                self.i += 1;
            }
            self.skip();
        }
    }

    fn starts_with(&self, s: &str) -> bool {
        let rest: String = self.chars[self.i..].iter().collect();
        rest.starts_with(s)
    }

    fn parse_one(&mut self) -> Result<Sexp, String> {
        self.skip();
        if self.i >= self.chars.len() {
            return Err("unexpected end of model".into());
        }
        if self.chars[self.i] == '(' {
            self.i += 1;
            let mut items = Vec::new();
            loop {
                self.skip();
                if self.i >= self.chars.len() {
                    return Err("unclosed list in model".into());
                }
                if self.chars[self.i] == ')' {
                    self.i += 1;
                    break;
                }
                items.push(self.parse_one()?);
            }
            Ok(Sexp::List(items))
        } else if self.chars[self.i] == '"' {
            let mut text = String::from("\"");
            self.i += 1;
            while self.i < self.chars.len() {
                let c = self.chars[self.i];
                self.i += 1;
                text.push(c);
                if c == '"' {
                    // SMT-LIB escapes a quote by doubling it.
                    if self.i < self.chars.len() && self.chars[self.i] == '"' {
                        text.push('"');
                        self.i += 1;
                        continue;
                    }
                    break;
                }
            }
            Ok(Sexp::Atom(text))
        } else {
            let start = self.i;
            while self.i < self.chars.len()
                && !self.chars[self.i].is_whitespace()
                && self.chars[self.i] != '('
                && self.chars[self.i] != ')'
            {
                self.i += 1;
            }
            let text: String = self.chars[start..self.i].iter().collect();
            if text.is_empty() {
                return Err("empty atom".into());
            }
            Ok(Sexp::Atom(text))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_int_bool_and_negative() {
        let model = r#"
sat
(
  (define-fun v_now () Int
    100)
  (define-fun v_ttl () Int
    (- 10))
  (define-fun v_authorized () Bool
    false)
)
"#;
        let mut sorts = BTreeMap::new();
        sorts.insert("now".into(), VirType::Int);
        sorts.insert("ttl".into(), VirType::Int);
        sorts.insert("authorized".into(), VirType::Bool);
        let values = values_from_model(model, &sorts).unwrap();
        assert_eq!(values.get("now"), Some(&Value::Int("100".into())));
        assert_eq!(values.get("ttl"), Some(&Value::Int("-10".into())));
        assert_eq!(values.get("authorized"), Some(&Value::Bool(false)));
    }
}
