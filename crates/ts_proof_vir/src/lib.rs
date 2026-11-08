//! Typed verification IR.
//!
//! Control, state, and effects are explicit. SMT-LIB is generated from this IR,
//! never from raw TypeScript syntax.

use std::collections::BTreeMap;
use std::fmt;
use ts_proof_core::Span;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirType {
    Bool,
    Int,
    String,
    Unit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Implies,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Not,
    Neg,
}

/// Mathematical expression. Integer literals are canonical decimal strings so
/// values are not limited by machine word size.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    Bool(bool),
    Int(String),
    Str(String),
    Var(String),
    Unary(UnaryOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Ite {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
}

impl Expr {
    pub fn var(name: impl Into<String>) -> Self {
        Self::Var(name.into())
    }

    pub fn int(raw: impl AsRef<str>) -> Self {
        Self::Int(canon(raw.as_ref()))
    }

    pub fn bool(v: bool) -> Self {
        Self::Bool(v)
    }

    pub fn not(e: Expr) -> Self {
        match e {
            Self::Bool(b) => Self::Bool(!b),
            Self::Unary(UnaryOp::Not, inner) => *inner,
            other => Self::Unary(UnaryOp::Not, Box::new(other)),
        }
    }

    pub fn neg(e: Expr) -> Self {
        match e {
            Self::Int(n) => Self::Int(canon(&format!("-{n}"))),
            Self::Unary(UnaryOp::Neg, inner) => *inner,
            other => Self::Unary(UnaryOp::Neg, Box::new(other)),
        }
    }

    pub fn binary(op: BinOp, l: Expr, r: Expr) -> Self {
        use BinOp::*;
        match (op, &l, &r) {
            (And, Self::Bool(true), _) => return r,
            (And, _, Self::Bool(true)) => return l,
            (And, Self::Bool(false), _) | (And, _, Self::Bool(false)) => return Self::Bool(false),
            (Or, Self::Bool(false), _) => return r,
            (Or, _, Self::Bool(false)) => return l,
            (Or, Self::Bool(true), _) | (Or, _, Self::Bool(true)) => return Self::Bool(true),
            (Implies, Self::Bool(true), _) => return r,
            (Implies, Self::Bool(false), _) | (Implies, _, Self::Bool(true)) => {
                return Self::Bool(true);
            }
            (Add, Self::Int(a), Self::Int(b)) => {
                if let Some(z) = checked_int(a, b, i128::checked_add) {
                    return Self::Int(z);
                }
            }
            (Add, _, Self::Int(z)) if z == "0" => return l,
            (Add, Self::Int(z), _) if z == "0" => return r,
            (Sub, Self::Int(a), Self::Int(b)) => {
                if let Some(z) = checked_int(a, b, i128::checked_sub) {
                    return Self::Int(z);
                }
            }
            (Sub, _, Self::Int(z)) if z == "0" => return l,
            (Mul, Self::Int(a), Self::Int(b)) => {
                if let Some(z) = checked_int(a, b, i128::checked_mul) {
                    return Self::Int(z);
                }
            }
            (Mul, _, Self::Int(z)) if z == "1" => return l,
            (Mul, Self::Int(z), _) if z == "1" => return r,
            (Mul, _, Self::Int(z)) | (Mul, Self::Int(z), _) if z == "0" => {
                return Self::Int("0".into());
            }
            (Eq, Self::Int(a), Self::Int(b)) => return Self::Bool(a == b),
            (Eq, Self::Bool(a), Self::Bool(b)) => return Self::Bool(a == b),
            (Eq, Self::Str(a), Self::Str(b)) => return Self::Bool(a == b),
            (Ne, Self::Int(a), Self::Int(b)) => return Self::Bool(a != b),
            (Ne, Self::Bool(a), Self::Bool(b)) => return Self::Bool(a != b),
            (Lt | Le | Gt | Ge, Self::Int(a), Self::Int(b)) => {
                if let Some(value) = cmp_ints(a, b, op) {
                    return Self::Bool(value);
                }
            }
            _ => {}
        }
        Self::Binary(op, Box::new(l), Box::new(r))
    }

    pub fn and(l: Expr, r: Expr) -> Self {
        Self::binary(BinOp::And, l, r)
    }

    pub fn or(l: Expr, r: Expr) -> Self {
        Self::binary(BinOp::Or, l, r)
    }

    pub fn implies(l: Expr, r: Expr) -> Self {
        Self::binary(BinOp::Implies, l, r)
    }

    pub fn eq(l: Expr, r: Expr) -> Self {
        Self::binary(BinOp::Eq, l, r)
    }

    pub fn ite(cond: Expr, then_expr: Expr, else_expr: Expr) -> Self {
        match cond {
            Self::Bool(true) => then_expr,
            Self::Bool(false) => else_expr,
            cond if then_expr == else_expr => then_expr,
            cond => Self::Ite {
                cond: Box::new(cond),
                then_expr: Box::new(then_expr),
                else_expr: Box::new(else_expr),
            },
        }
    }

    pub fn subst(&self, env: &BTreeMap<String, Expr>) -> Expr {
        match self {
            Self::Var(name) => env.get(name).cloned().unwrap_or_else(|| self.clone()),
            Self::Unary(op, e) => match op {
                UnaryOp::Not => Self::not(e.subst(env)),
                UnaryOp::Neg => Self::neg(e.subst(env)),
            },
            Self::Binary(op, l, r) => Self::binary(*op, l.subst(env), r.subst(env)),
            Self::Ite {
                cond,
                then_expr,
                else_expr,
            } => Self::ite(cond.subst(env), then_expr.subst(env), else_expr.subst(env)),
            other => other.clone(),
        }
    }

    pub fn free_vars(&self, out: &mut BTreeMap<String, ()>) {
        match self {
            Self::Var(name) => {
                out.insert(name.clone(), ());
            }
            Self::Unary(_, e) => e.free_vars(out),
            Self::Binary(_, l, r) => {
                l.free_vars(out);
                r.free_vars(out);
            }
            Self::Ite {
                cond,
                then_expr,
                else_expr,
            } => {
                cond.free_vars(out);
                then_expr.free_vars(out);
                else_expr.free_vars(out);
            }
            _ => {}
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{b}"),
            Self::Int(n) => write!(f, "{n}"),
            Self::Str(s) => write!(f, "\"{s}\""),
            Self::Var(v) => write!(f, "{v}"),
            Self::Unary(UnaryOp::Not, e) => write!(f, "!({e})"),
            Self::Unary(UnaryOp::Neg, e) => write!(f, "-({e})"),
            Self::Binary(op, l, r) => write!(f, "({l} {} {r})", bin_symbol(*op)),
            Self::Ite {
                cond,
                then_expr,
                else_expr,
            } => write!(f, "({cond} ? {then_expr} : {else_expr})"),
        }
    }
}

fn bin_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Eq => "===",
        BinOp::Ne => "!==",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::Implies => "=>",
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Assign {
        name: String,
        expr: Expr,
        span: Span,
    },
    If {
        cond: Expr,
        then_branch: Vec<Stmt>,
        else_branch: Vec<Stmt>,
        span: Span,
    },
    Return {
        expr: Option<Expr>,
        span: Span,
    },
    Throw {
        span: Span,
    },
    While {
        cond: Expr,
        invariant: Expr,
        modified: Vec<String>,
        body: Vec<Stmt>,
        span: Span,
    },
    /// Records an attempted effect and increments `counter` by one.
    /// Additional state updates are ordinary assignments around this statement.
    Effect {
        /// Stable effect id, for example `kms.sign` or `db.write.tokens`.
        effect: String,
        /// Ghost counter incremented on this attempt, for example `trace.kms.sign`.
        counter: String,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirParam {
    pub name: String,
    pub ty: VirType,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ghost {
    pub name: String,
    pub ty: VirType,
    pub init: Expr,
}

/// A verification target: a function or a composed endpoint.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirFunction {
    pub name: String,
    pub params: Vec<VirParam>,
    pub ghosts: Vec<Ghost>,
    /// Interpreted in the initial state. Parameter names denote arguments.
    pub requires: Expr,
    /// Parameter names denote the initial arguments. `result` and ghost names
    /// denote the final state. `old.<param>` is also the initial argument.
    pub ensures: Expr,
    pub body: Vec<Stmt>,
    pub span: Span,
    /// Names that should be printed in a counterexample, in order.
    pub display: Vec<String>,
    pub kind: FunctionKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FunctionKind {
    Function,
    Endpoint { method: String, path: String },
    Lemma { law: String },
}

/// Concrete value recovered from a solver model or an interpreter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Int(String),
    Str(String),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{b}"),
            Self::Int(n) => write!(f, "{n}"),
            Self::Str(s) => write!(f, "\"{s}\""),
        }
    }
}

pub fn canon(raw: &str) -> String {
    ts_proof_core::canon_int(raw).unwrap_or_else(|| raw.to_string())
}

fn cmp_ints(a: &str, b: &str, op: BinOp) -> Option<bool> {
    let x: i128 = a.parse().ok()?;
    let y: i128 = b.parse().ok()?;
    Some(match op {
        BinOp::Lt => x < y,
        BinOp::Le => x <= y,
        BinOp::Gt => x > y,
        BinOp::Ge => x >= y,
        _ => return None,
    })
}

fn checked_int(a: &str, b: &str, op: fn(i128, i128) -> Option<i128>) -> Option<String> {
    let x: i128 = a.parse().ok()?;
    let y: i128 = b.parse().ok()?;
    Some(op(x, y)?.to_string())
}

/// Evaluate a closed expression. Returns `None` if a variable is missing or a
/// literal produced by overflow folding is not a plain integer.
pub fn eval(expr: &Expr, env: &BTreeMap<String, Value>) -> Option<Value> {
    match expr {
        Expr::Bool(b) => Some(Value::Bool(*b)),
        Expr::Int(n) => {
            if n.starts_with('(') {
                return None;
            }
            Some(Value::Int(canon(n)))
        }
        Expr::Str(s) => Some(Value::Str(s.clone())),
        Expr::Var(n) => env.get(n).cloned(),
        Expr::Unary(UnaryOp::Not, e) => match eval(e, env)? {
            Value::Bool(b) => Some(Value::Bool(!b)),
            _ => None,
        },
        Expr::Unary(UnaryOp::Neg, e) => match eval(e, env)? {
            Value::Int(n) => Some(Value::Int(canon(&format!("-{n}")))),
            _ => None,
        },
        Expr::Binary(op, l, r) => {
            let lv = eval(l, env)?;
            let rv = eval(r, env)?;
            eval_bin(*op, lv, rv)
        }
        Expr::Ite {
            cond,
            then_expr,
            else_expr,
        } => match eval(cond, env)? {
            Value::Bool(true) => eval(then_expr, env),
            Value::Bool(false) => eval(else_expr, env),
            _ => None,
        },
    }
}

fn eval_bin(op: BinOp, l: Value, r: Value) -> Option<Value> {
    use BinOp::*;
    match (op, l, r) {
        (Add, Value::Int(a), Value::Int(b)) => Some(Value::Int(checked_binop(&a, &b, i128::checked_add)?)),
        (Sub, Value::Int(a), Value::Int(b)) => Some(Value::Int(checked_binop(&a, &b, i128::checked_sub)?)),
        (Mul, Value::Int(a), Value::Int(b)) => Some(Value::Int(checked_binop(&a, &b, i128::checked_mul)?)),
        (Eq, a, b) => Some(Value::Bool(values_eq(&a, &b))),
        (Ne, a, b) => Some(Value::Bool(!values_eq(&a, &b))),
        (Lt, Value::Int(a), Value::Int(b)) => Some(Value::Bool(cmp_int(&a, &b)? < 0)),
        (Le, Value::Int(a), Value::Int(b)) => Some(Value::Bool(cmp_int(&a, &b)? <= 0)),
        (Gt, Value::Int(a), Value::Int(b)) => Some(Value::Bool(cmp_int(&a, &b)? > 0)),
        (Ge, Value::Int(a), Value::Int(b)) => Some(Value::Bool(cmp_int(&a, &b)? >= 0)),
        (And, Value::Bool(a), Value::Bool(b)) => Some(Value::Bool(a && b)),
        (Or, Value::Bool(a), Value::Bool(b)) => Some(Value::Bool(a || b)),
        (Implies, Value::Bool(a), Value::Bool(b)) => Some(Value::Bool(!a || b)),
        _ => None,
    }
}

fn values_eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Int(x), Value::Int(y)) => canon(x) == canon(y),
        (Value::Str(x), Value::Str(y)) => x == y,
        _ => false,
    }
}

fn cmp_int(a: &str, b: &str) -> Option<i32> {
    let x: i128 = a.parse().ok()?;
    let y: i128 = b.parse().ok()?;
    Some(if x < y {
        -1
    } else if x > y {
        1
    } else {
        0
    })
}

fn checked_binop(a: &str, b: &str, op: fn(i128, i128) -> Option<i128>) -> Option<String> {
    let x: i128 = a.parse().ok()?;
    let y: i128 = b.parse().ok()?;
    Some(op(x, y)?.to_string())
}

/// Variables assigned anywhere in `stmts`, including effect counters.
pub fn modified_vars(stmts: &[Stmt]) -> Vec<String> {
    let mut out = Vec::new();
    fn walk(stmts: &[Stmt], out: &mut Vec<String>) {
        for s in stmts {
            match s {
                Stmt::Assign { name, .. } => push_unique(out, name),
                Stmt::Effect { counter, .. } => push_unique(out, counter),
                Stmt::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    walk(then_branch, out);
                    walk(else_branch, out);
                }
                Stmt::While { body, .. } => walk(body, out),
                Stmt::Return { .. } | Stmt::Throw { .. } => {}
            }
        }
    }
    walk(stmts, &mut out);
    out
}

fn push_unique(out: &mut Vec<String>, name: &str) {
    if !out.iter().any(|n| n == name) {
        out.push(name.to_string());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn implication_folds() {
        let e = Expr::implies(Expr::Bool(true), Expr::var("p"));
        assert_eq!(e, Expr::var("p"));
    }

    #[test]
    fn subst_replaces_only_bound_names() {
        let mut env = BTreeMap::new();
        env.insert("ttl".into(), Expr::int("1"));
        let e = Expr::binary(BinOp::Gt, Expr::var("ttl"), Expr::int("0")).subst(&env);
        assert_eq!(e, Expr::Bool(true));
    }
}
