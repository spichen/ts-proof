//! SMT-LIB serialization and a process-based Z3 backend.
//!
//! A formula is proved only when Z3 returns `unsat` for its negation.
//! `sat`, `unknown`, timeout, and solver errors are not proofs.

mod model;
mod solver;

use std::collections::BTreeMap;
use std::fmt::Write as _;
use ts_proof_core::{Diagnostic, ErrorCode, Span};
use ts_proof_vir::{BinOp, Expr, UnaryOp, Value, VirType};

pub use model::values_from_model;
pub use solver::{find_z3, z3_version, SolverOutcome, Z3};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Query {
    pub smt: String,
    pub sorts: BTreeMap<String, VirType>,
}

#[derive(Clone, Debug)]
pub struct EncodedObligation {
    pub name: String,
    pub span: Span,
    pub validity: Expr,
    pub query: Query,
    /// Expressions evaluated against a satisfying model so the report can show
    /// `result`, not only the input constants Z3 assigned.
    pub display: Vec<(String, Expr)>,
    pub expected: String,
}

pub fn encode_validity(formula: &Expr, known: &BTreeMap<String, VirType>) -> Result<Query, Diagnostic> {
    let mut sorts = known.clone();
    infer(formula, &mut sorts, None)?;
    let mut free = BTreeMap::new();
    formula.free_vars(&mut free);
    for name in free.keys() {
        if !sorts.contains_key(name) {
            return Err(Diagnostic::new(
                ErrorCode::Verify006,
                format!("sort of `{name}` is not determined; refusing to guess an SMT sort"),
            ));
        }
    }
    let mut smt = String::new();
    writeln!(smt, "(set-option :produce-models true)").unwrap();
    writeln!(smt, "(set-logic ALL)").unwrap();
    for (name, sort) in &sorts {
        if free.contains_key(name) {
            writeln!(
                smt,
                "(declare-const {} {})",
                smt_symbol(name),
                sort_name(*sort)
            )
            .unwrap();
        }
    }
    // Prove `formula` by checking that its negation is unsatisfiable.
    writeln!(smt, "(assert {})", encode(&Expr::not(formula.clone()))).unwrap();
    writeln!(smt, "(check-sat)").unwrap();
    writeln!(smt, "(get-model)").unwrap();
    Ok(Query { smt, sorts })
}

fn sort_name(ty: VirType) -> &'static str {
    match ty {
        VirType::Bool => "Bool",
        VirType::Int => "Int",
        VirType::String => "String",
        VirType::Unit => "Bool",
    }
}

/// SMT-LIB symbols cannot contain `.` or start with a digit. Map ghost names
/// reversibly so counterexamples can be shown with their source names.
pub fn smt_symbol(name: &str) -> String {
    let mut out = String::from("v_");
    for c in name.chars() {
        match c {
            '.' => out.push_str("_d_"),
            '-' => out.push_str("_m_"),
            c if c.is_ascii_alphanumeric() || c == '_' => out.push(c),
            other => {
                out.push_str("_u");
                out.push_str(&format!("{:x}", other as u32));
                out.push('_');
            }
        }
    }
    out
}

pub fn encode(expr: &Expr) -> String {
    match expr {
        Expr::Bool(true) => "true".into(),
        Expr::Bool(false) => "false".into(),
        Expr::Int(n) => encode_int(n),
        Expr::Str(s) => format!("\"{}\"", escape_smt_string(s)),
        Expr::Var(name) => smt_symbol(name),
        Expr::Unary(UnaryOp::Not, e) => format!("(not {})", encode(e)),
        Expr::Unary(UnaryOp::Neg, e) => format!("(- {})", encode(e)),
        Expr::Binary(op, l, r) => format!("({} {} {})", bin(*op), encode(l), encode(r)),
        Expr::Ite {
            cond,
            then_expr,
            else_expr,
        } => format!(
            "(ite {} {} {})",
            encode(cond),
            encode(then_expr),
            encode(else_expr)
        ),
    }
}

fn bin(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Eq => "=",
        BinOp::Ne => "distinct",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Implies => "=>",
    }
}

fn encode_int(n: &str) -> String {
    if let Some(rest) = n.strip_prefix('-') {
        format!("(- {rest})")
    } else {
        n.to_string()
    }
}

fn escape_smt_string(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '"' => out.push_str("\"\""),
            '\\' => out.push_str("\\"),
            c => out.push(c),
        }
    }
    out
}

/// A sort that may still be an unbound variable. Unbound variables are never
/// defaulted to Bool: that would make `x === 0` ill-sorted or unsound.
enum MaybeSort {
    Known(VirType),
    Unknown,
}

/// Infer sorts. `expected` is the sort required by the parent context.
fn infer(
    expr: &Expr,
    sorts: &mut BTreeMap<String, VirType>,
    expected: Option<VirType>,
) -> Result<MaybeSort, Diagnostic> {
    let got = match expr {
        Expr::Bool(_) => MaybeSort::Known(VirType::Bool),
        Expr::Int(_) => MaybeSort::Known(VirType::Int),
        Expr::Str(_) => MaybeSort::Known(VirType::String),
        Expr::Var(name) => {
            if let Some(expected) = expected {
                bind(sorts, name, expected)?;
                MaybeSort::Known(expected)
            } else if let Some(ty) = sorts.get(name).copied() {
                MaybeSort::Known(ty)
            } else {
                MaybeSort::Unknown
            }
        }
        Expr::Unary(UnaryOp::Not, e) => {
            infer(e, sorts, Some(VirType::Bool))?;
            MaybeSort::Known(VirType::Bool)
        }
        Expr::Unary(UnaryOp::Neg, e) => {
            infer(e, sorts, Some(VirType::Int))?;
            MaybeSort::Known(VirType::Int)
        }
        Expr::Binary(op, l, r) => match op {
            BinOp::And | BinOp::Or | BinOp::Implies => {
                infer(l, sorts, Some(VirType::Bool))?;
                infer(r, sorts, Some(VirType::Bool))?;
                MaybeSort::Known(VirType::Bool)
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                infer(l, sorts, Some(VirType::Int))?;
                infer(r, sorts, Some(VirType::Int))?;
                MaybeSort::Known(VirType::Int)
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                infer(l, sorts, Some(VirType::Int))?;
                infer(r, sorts, Some(VirType::Int))?;
                MaybeSort::Known(VirType::Bool)
            }
            BinOp::Eq | BinOp::Ne => {
                unify_eq(l, r, sorts)?;
                MaybeSort::Known(VirType::Bool)
            }
        },
        Expr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            infer(cond, sorts, Some(VirType::Bool))?;
            let t = infer(then_expr, sorts, expected)?;
            let branch = match t {
                MaybeSort::Known(ty) => Some(ty),
                MaybeSort::Unknown => expected,
            };
            let e = infer(else_expr, sorts, branch)?;
            match (t, e, expected) {
                (MaybeSort::Known(a), MaybeSort::Known(b), _) if a == b => MaybeSort::Known(a),
                (MaybeSort::Known(a), MaybeSort::Unknown, _) => {
                    bind_vars(else_expr, a, sorts)?;
                    MaybeSort::Known(a)
                }
                (MaybeSort::Unknown, MaybeSort::Known(b), _) => {
                    bind_vars(then_expr, b, sorts)?;
                    MaybeSort::Known(b)
                }
                (MaybeSort::Unknown, MaybeSort::Unknown, Some(ty)) => {
                    bind_vars(then_expr, ty, sorts)?;
                    bind_vars(else_expr, ty, sorts)?;
                    MaybeSort::Known(ty)
                }
                (MaybeSort::Known(a), MaybeSort::Known(b), _) => {
                    return Err(Diagnostic::new(
                        ErrorCode::Verify006,
                        format!("conditional branches have sorts {a:?} and {b:?}"),
                    ));
                }
                _ => {
                    return Err(Diagnostic::new(
                        ErrorCode::Verify006,
                        "conditional branches have unknown sorts",
                    ));
                }
            }
        }
    };
    if let (Some(expected), MaybeSort::Known(got)) = (expected, &got) {
        if *got != expected {
            return Err(Diagnostic::new(
                ErrorCode::Verify006,
                format!("sort mismatch: expected {expected:?}, got {got:?} in {expr}"),
            ));
        }
    }
    Ok(got)
}

fn unify_eq(
    l: &Expr,
    r: &Expr,
    sorts: &mut BTreeMap<String, VirType>,
) -> Result<(), Diagnostic> {
    let ls = infer(l, sorts, None)?;
    let rs = infer(r, sorts, None)?;
    match (ls, rs) {
        (MaybeSort::Known(a), MaybeSort::Known(b)) if a == b => Ok(()),
        (MaybeSort::Known(a), MaybeSort::Known(b)) => Err(Diagnostic::new(
            ErrorCode::Verify006,
            format!("cannot compare {a:?} with {b:?}"),
        )),
        (MaybeSort::Known(a), MaybeSort::Unknown) => bind_vars(r, a, sorts),
        (MaybeSort::Unknown, MaybeSort::Known(b)) => bind_vars(l, b, sorts),
        (MaybeSort::Unknown, MaybeSort::Unknown) => Err(Diagnostic::new(
            ErrorCode::Verify006,
            "equality does not determine a sort; annotate the operands",
        )),
    }
}

fn bind_vars(
    expr: &Expr,
    ty: VirType,
    sorts: &mut BTreeMap<String, VirType>,
) -> Result<(), Diagnostic> {
    if let Expr::Var(name) = expr {
        bind(sorts, name, ty)?;
    }
    Ok(())
}

fn bind(
    sorts: &mut BTreeMap<String, VirType>,
    name: &str,
    ty: VirType,
) -> Result<(), Diagnostic> {
    if let Some(prev) = sorts.get(name) {
        if *prev != ty {
            return Err(Diagnostic::new(
                ErrorCode::Verify006,
                format!("`{name}` is used as both {prev:?} and {ty:?}"),
            ));
        }
    } else {
        sorts.insert(name.to_string(), ty);
    }
    Ok(())
}

/// Evaluate `expr` under a concrete model. Missing variables yield `None`.
pub fn eval_model(expr: &Expr, model: &BTreeMap<String, Value>) -> Option<Value> {
    ts_proof_vir::eval(expr, model)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn negation_of_expiry_is_the_query_shape() {
        // ttl > 0 => now + ttl > now
        let now = Expr::var("now");
        let ttl = Expr::var("ttl");
        let formula = Expr::implies(
            Expr::binary(BinOp::Gt, ttl.clone(), Expr::int("0")),
            Expr::binary(
                BinOp::Gt,
                Expr::binary(BinOp::Add, now.clone(), ttl),
                now,
            ),
        );
        let mut known = BTreeMap::new();
        known.insert("now".into(), VirType::Int);
        known.insert("ttl".into(), VirType::Int);
        let q = encode_validity(&formula, &known).unwrap();
        assert!(q.smt.contains("(check-sat)"));
        assert!(q.smt.contains("(declare-const v_now Int)"));
        assert!(q.smt.contains("(assert"));
    }
}
