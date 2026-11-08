use crate::Span;
use std::collections::BTreeMap;

/// Compiler-neutral program snapshot. Produced by the `tsrs` bridge, consumed by
/// lowering and adapters. Types here are ownership-stable and carry source spans.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    pub files: Vec<crate::SourceFile>,
    pub functions: Vec<Function>,
    pub consts: Vec<ConstDecl>,
    pub top_level: Vec<Stmt>,
    pub laws: Vec<Law>,
    pub endpoint_laws: Vec<EndpointLaw>,
    pub proofs: Vec<Proof>,
    /// Local binding name → external effect declaration.
    pub externals: BTreeMap<String, External>,
}

impl Program {
    pub fn empty() -> Self {
        Self {
            files: Vec::new(),
            functions: Vec::new(),
            consts: Vec::new(),
            top_level: Vec::new(),
            laws: Vec::new(),
            endpoint_laws: Vec::new(),
            proofs: Vec::new(),
            externals: BTreeMap::new(),
        }
    }

    pub fn function(&self, name: &str) -> Option<&Function> {
        self.functions.iter().find(|f| f.name == name)
    }

    pub fn source(&self, file: &str) -> Option<&str> {
        self.files
            .iter()
            .find(|f| f.path == file)
            .map(|f| f.source.as_str())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    pub name: String,
    pub params: Vec<Param>,
    pub ret: Option<TsType>,
    pub body: Vec<Stmt>,
    pub span: Span,
    pub is_async: bool,
    pub decorators: Vec<Decorator>,
    pub class_name: Option<String>,
    pub class_decorators: Vec<Decorator>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub ty: Option<TsType>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decorator {
    pub name: String,
    pub args: Vec<Expr>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TsType {
    Bool,
    Int,
    String,
    Void,
    Null,
    Promise(Box<TsType>),
    Named(String),
    /// `T | null`. Other unions are rejected by the parser.
    Nullable(Box<TsType>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstDecl {
    pub name: String,
    pub expr: Expr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum External {
    Function { effect: String, span: Span },
    Namespace {
        methods: BTreeMap<String, String>,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Law {
    pub name: String,
    pub target: String,
    pub requires: Option<SpecFn>,
    pub ensures: Option<SpecFn>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EndpointLaw {
    pub name: String,
    pub method: String,
    pub path: String,
    pub requires: Option<SpecFn>,
    pub ensures: SpecFn,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecFn {
    /// Names bound by the arrow. `result`, `request`, `trace`, `response`, `db`,
    /// and `http` are specification roots. Other names must be function parameters.
    pub params: Vec<String>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub name: String,
    pub law: String,
    pub lemmas: Vec<Lemma>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lemma {
    pub name: Option<String>,
    pub expr: Expr,
    pub span: Span,
    /// Names of lemmas this one cites. A cycle is VERIFY009.
    pub depends_on: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Let {
        name: String,
        init: Expr,
        span: Span,
    },
    Assign {
        name: String,
        expr: Expr,
        span: Span,
    },
    If {
        cond: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
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
        invariant: Option<Expr>,
        body: Vec<Stmt>,
        span: Span,
    },
    Expr {
        expr: Expr,
        span: Span,
    },
    Try {
        body: Vec<Stmt>,
        catch_param: String,
        catch_body: Vec<Stmt>,
        span: Span,
    },
    /// Inserted when a middleware calls its `next` parameter.
    /// `error` is true for `next(err)`.
    Next {
        error: bool,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Bool(bool),
    /// Canonical decimal integer. The `n` suffix of a bigint literal is stripped.
    /// Plain integer literals are mathematical integers, never IEEE-754 numbers.
    Int(String),
    Str(String),
    Null,
    Ident(String),
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
        span: Span,
    },
    Binary {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
        span: Span,
    },
    Ternary {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
        span: Span,
    },
    /// `a.b` when it is not itself the callee of a call. Call callees use [`Callee`].
    Member {
        object: Box<Expr>,
        field: String,
        span: Span,
    },
    Call {
        callee: Callee,
        args: Vec<Expr>,
        span: Span,
    },
    Array {
        items: Vec<Expr>,
        span: Span,
    },
    Object {
        fields: Vec<(String, Expr)>,
        span: Span,
    },
    /// Specification arrow. Verification-only. A block-bodied proof arrow is not
    /// stored here; `prove` is lowered into [`Proof`] directly.
    Arrow {
        params: Vec<String>,
        body: Box<Expr>,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Callee {
    Ident(String),
    Member { object: Box<Expr>, field: String },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
}

impl Expr {
    pub fn span_hint(&self) -> Option<&Span> {
        match self {
            Self::Unary { span, .. }
            | Self::Binary { span, .. }
            | Self::Ternary { span, .. }
            | Self::Member { span, .. }
            | Self::Call { span, .. }
            | Self::Array { span, .. }
            | Self::Object { span, .. }
            | Self::Arrow { span, .. } => Some(span),
            _ => None,
        }
    }
}

/// Canonicalize a decimal integer literal. Rejects empty input.
pub fn canon_int(raw: &str) -> Option<String> {
    let (neg, digits) = if let Some(rest) = raw.strip_prefix('-') {
        (true, rest)
    } else {
        (false, raw)
    };
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let trimmed = digits.trim_start_matches('0');
    let body = if trimmed.is_empty() { "0" } else { trimmed };
    if neg && body != "0" {
        Some(format!("-{body}"))
    } else {
        Some(body.to_string())
    }
}
