//! Lower LAW and PROOF expressions into VIR formulas.
//!
//! Arrows are symbolic. They are never called. `call(target, ...params)` means
//! the result of the law's target. Lemmas are not assumed here; the proof crate
//! checks them on their own.

use ts_proof_core::{BinOp as AstBin, Callee, Diagnostic, ErrorCode, Expr as Ast, Span, SpecFn, UnaryOp};
use ts_proof_vir::{BinOp, Expr};

#[derive(Clone, Debug)]
pub struct Formula {
    pub expr: Expr,
    pub params: Vec<String>,
    pub span: Span,
}

pub fn lower_spec(spec: &SpecFn, target: Option<&str>, target_params: &[String]) -> Result<Formula, Diagnostic> {
    let expr = lower_expr(&spec.body, &spec.params, target, target_params, &spec.span)?;
    Ok(Formula {
        expr,
        params: spec.params.clone(),
        span: spec.span.clone(),
    })
}

pub fn lower_expr(
    expr: &Ast,
    arrow_params: &[String],
    target: Option<&str>,
    target_params: &[String],
    span: &Span,
) -> Result<Expr, Diagnostic> {
    let at = expr.span_hint().unwrap_or(span);
    match expr {
        Ast::Bool(v) => Ok(Expr::bool(*v)),
        Ast::Int(n) => Ok(Expr::int(n)),
        Ast::Str(s) => Ok(Expr::Str(s.clone())),
        Ast::Null => Err(bad(at, "null is not a specification value")),
        Ast::Ident(name) => {
            if arrow_params.iter().any(|p| p == name) || target_params.iter().any(|p| p == name) || is_scalar_root(name)
            {
                Ok(Expr::var(name))
            } else if is_spec_root(name) {
                Err(bad(at, format!("`{name}` is a specification root; use `{name}.field`")))
            } else {
                Err(bad(at, format!("`{name}` is not a parameter or a specification root")))
            }
        }
        Ast::Unary { op: UnaryOp::Not, expr, .. } => Ok(Expr::not(lower_expr(expr, arrow_params, target, target_params, span)?)),
        Ast::Unary { op: UnaryOp::Neg, expr, .. } => Ok(Expr::neg(lower_expr(expr, arrow_params, target, target_params, span)?)),
        Ast::Binary { op, left, right, .. } => {
            let l = lower_expr(left, arrow_params, target, target_params, span)?;
            let r = lower_expr(right, arrow_params, target, target_params, span)?;
            Ok(Expr::binary(map_op(*op), l, r))
        }
        Ast::Ternary { cond, then_expr, else_expr, .. } => {
            let c = lower_expr(cond, arrow_params, target, target_params, span)?;
            let t = lower_expr(then_expr, arrow_params, target, target_params, span)?;
            let e = lower_expr(else_expr, arrow_params, target, target_params, span)?;
            Ok(Expr::ite(c, t, e))
        }
        Ast::Member { .. } => {
            let name = dotted(expr).ok_or_else(|| bad(at, "unsupported member expression in a formula"))?;
            if !known_path(&name, arrow_params, target_params) {
                return Err(bad(at, format!("`{name}` is not a supported specification path")));
            }
            Ok(Expr::var(name))
        }
        Ast::Call { callee, args, span: call_span } => {
            lower_call(callee, args, arrow_params, target, target_params, call_span)
        }
        Ast::Array { .. } | Ast::Object { .. } | Ast::Arrow { .. } => {
            Err(bad(at, "arrays, objects, and nested arrows are not formulas"))
        }
    }
}

fn lower_call(
    callee: &Callee,
    args: &[Ast],
    arrow_params: &[String],
    target: Option<&str>,
    target_params: &[String],
    span: &Span,
) -> Result<Expr, Diagnostic> {
    match callee {
        Callee::Ident(name) if name == "implies" && args.len() == 2 => {
            let l = lower_expr(&args[0], arrow_params, target, target_params, span)?;
            let r = lower_expr(&args[1], arrow_params, target, target_params, span)?;
            Ok(Expr::implies(l, r))
        }
        Callee::Ident(name) if name == "call" => lower_result_call(args, target, target_params, span),
        Callee::Member { object, field } if field == "count" && args.len() == 1 => {
            match object.as_ref() {
                Ast::Ident(name) if name == "trace" => {}
                _ => return Err(bad(span, "only trace.count(name) is a supported counter")),
            }
            let Ast::Str(effect) = &args[0] else {
                return Err(bad(span, "trace.count needs a string effect name"));
            };
            if effect.is_empty() || !effect.chars().all(|c| c.is_ascii_alphanumeric() || c == '.' || c == '_') {
                return Err(bad(span, "unsupported effect name in trace.count"));
            }
            Ok(Expr::var(format!("trace.{effect}")))
        }
        Callee::Member { object, field } => {
            let op = spec_method(field).ok_or_else(|| bad(span, format!("unsupported specification method `{field}`")))?;
            if args.len() != 1 {
                return Err(bad(span, format!("`{field}` takes one argument")));
            }
            let left = lower_expr(object, arrow_params, target, target_params, span)?;
            let right = lower_expr(&args[0], arrow_params, target, target_params, span)?;
            Ok(Expr::binary(op, left, right))
        }
        Callee::Ident(name) => Err(bad(span, format!("unsupported specification call `{name}`"))),
    }
}

fn lower_result_call(
    args: &[Ast],
    target: Option<&str>,
    target_params: &[String],
    span: &Span,
) -> Result<Expr, Diagnostic> {
    let Some(target) = target else {
        return Err(bad(span, "call() is only valid in a function law"));
    };
    let Some(Ast::Ident(name)) = args.first() else {
        return Err(bad(span, "call() needs the law target as its first argument"));
    };
    if name != target {
        return Err(bad(
            span,
            format!("call() must name this law's target `{target}`"),
        ));
    }
    if args.len() != target_params.len() + 1 {
        return Err(bad(span, "call() arguments must be the target parameters, in order"));
    }
    for (arg, param) in args.iter().skip(1).zip(target_params) {
        let Ast::Ident(got) = arg else {
            return Err(bad(span, "call() arguments must be the parameter names"));
        };
        if got != param {
            return Err(bad(
                span,
                format!("call() argument `{got}` does not match parameter `{param}`"),
            ));
        }
    }
    Ok(Expr::var("result"))
}

fn spec_method(name: &str) -> Option<BinOp> {
    Some(match name {
        "gte" => BinOp::Ge,
        "gt" => BinOp::Gt,
        "lte" => BinOp::Le,
        "lt" => BinOp::Lt,
        "eq" => BinOp::Eq,
        "neq" => BinOp::Ne,
        "and" => BinOp::And,
        "or" => BinOp::Or,
        "implies" => BinOp::Implies,
        "add" => BinOp::Add,
        "sub" => BinOp::Sub,
        "mul" => BinOp::Mul,
        _ => return None,
    })
}

fn map_op(op: AstBin) -> BinOp {
    match op {
        AstBin::Add => BinOp::Add,
        AstBin::Sub => BinOp::Sub,
        AstBin::Mul => BinOp::Mul,
        AstBin::Eq => BinOp::Eq,
        AstBin::Ne => BinOp::Ne,
        AstBin::Lt => BinOp::Lt,
        AstBin::Le => BinOp::Le,
        AstBin::Gt => BinOp::Gt,
        AstBin::Ge => BinOp::Ge,
        AstBin::And => BinOp::And,
        AstBin::Or => BinOp::Or,
    }
}

fn dotted(expr: &Ast) -> Option<String> {
    match expr {
        Ast::Ident(name) => Some(name.clone()),
        Ast::Member { object, field, .. } => Some(format!("{}.{}", dotted(object)?, field)),
        _ => None,
    }
}

fn is_spec_root(name: &str) -> bool {
    matches!(name, "request" | "trace" | "response" | "db" | "http" | "old")
}

fn bad(span: &Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(ErrorCode::Verify002, message.into()).at(span.clone())
}

fn is_scalar_root(name: &str) -> bool {
    matches!(name, "result" | "thrown")
}

fn known_path(name: &str, arrow_params: &[String], target_params: &[String]) -> bool {
    let root = name.split('.').next().unwrap_or(name);
    is_spec_root(root)
        || is_scalar_root(root)
        || arrow_params.iter().any(|p| p == root)
        || target_params.iter().any(|p| p == root)
}
