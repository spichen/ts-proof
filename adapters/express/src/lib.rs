//! Express adapter.
//!
//! A middleware continues the chain only when it calls `next()`. Returning
//! without `next()` stops the chain. `next(err)` enters the error handler.
//! `res.status` does not commit a response. `json`, `send`, and `end` do.
//! Dynamic route registration is rejected.

use std::collections::{BTreeMap, BTreeSet};
use ts_proof_adapters::{AdapterMetadata, ClassifyCtx, Layer, LayerKind, VerificationAdapter};
use ts_proof_core::{Callee, Diagnostic, ErrorCode, Expr, Program, Span, Stmt};
use ts_proof_effects::{assign, stamp, TrustItem};
use ts_proof_vir::Stmt as VirStmt;

pub struct ExpressAdapter;

impl ExpressAdapter {
    pub fn new() -> Self {
        Self
    }
}

impl Default for ExpressAdapter {
    fn default() -> Self {
        Self
    }
}

impl VerificationAdapter for ExpressAdapter {
    fn metadata(&self) -> AdapterMetadata {
        AdapterMetadata {
            name: "express".into(),
            version: "0.1.0".into(),
            framework: "express".into(),
            supported_versions: vec!["5.x".into()],
            trust: "external-model".into(),
            capabilities: vec![
                "route-discovery".into(),
                "middleware-composition".into(),
                "response".into(),
                "error-handler".into(),
                "router-mount".into(),
            ],
        }
    }

    fn discover(&self, program: &Program) -> Result<Vec<Layer>, Vec<Diagnostic>> {
        let mut regs: Vec<Reg> = Vec::new();
        let mut diags = Vec::new();
        for stmt in &program.top_level {
            let Stmt::Expr { expr, span } = stmt else {
                continue;
            };
            match classify_registration(program, expr, span) {
                Ok(Some(reg)) => regs.push(reg),
                Ok(None) => {}
                Err(diag) => diags.push(diag),
            }
        }
        if !diags.is_empty() {
            return Err(diags);
        }
        flatten(&regs, program).map_err(|d| vec![d])
    }

    fn lower_call(
        &self,
        call: &Expr,
        ctx: &mut ClassifyCtx<'_>,
    ) -> Result<Option<Vec<VirStmt>>, Vec<Diagnostic>> {
        let Some(response) = ctx.response_ident else {
            return Ok(None);
        };
        match response_op(call, response) {
            ResponseOp::NotResponse => Ok(None),
            ResponseOp::Status { code, span } => {
                let code = ctx.pure.pure(code).map_err(|d| vec![d])?;
                Ok(Some(vec![
                    assign("response.status", code, span.clone()),
                    assign("response.statusSet", ts_proof_vir::Expr::Bool(true), span),
                ]))
            }
            ResponseOp::Commit { status, bodies, span } => {
                for body in bodies {
                    ctx.pure.seal(body).map_err(|d| vec![d])?;
                }
                let mut stmts = Vec::new();
                if let Some(code) = status {
                    let code = ctx.pure.pure(code).map_err(|d| vec![d])?;
                    stmts.push(assign("response.status", code, span.clone()));
                    stmts.push(assign(
                        "response.statusSet",
                        ts_proof_vir::Expr::Bool(true),
                        span.clone(),
                    ));
                } else {
                    stmts.push(assign(
                        "response.status",
                        ts_proof_vir::Expr::ite(
                            ts_proof_vir::Expr::var("response.statusSet"),
                            ts_proof_vir::Expr::var("response.status"),
                            ts_proof_vir::Expr::int("200"),
                        ),
                        span.clone(),
                    ));
                    stmts.push(assign(
                        "response.statusSet",
                        ts_proof_vir::Expr::Bool(true),
                        span.clone(),
                    ));
                }
                stmts.push(assign(
                    "response.committed",
                    ts_proof_vir::Expr::Bool(true),
                    span.clone(),
                ));
                stmts.extend(stamp("response.clock", span));
                Ok(Some(stmts))
            }
        }
    }

    fn contracts(&self) -> Vec<TrustItem> {
        vec![TrustItem::model(
            "express",
            "Supported static routes and synchronous middleware. next() inlines the rest of the chain. A response is committed only by json, send, or end. Thrown exceptions abort the chain; only next(err) enters an error handler. One request is modeled at a time.",
        )]
    }
}

struct Reg {
    receiver: String,
    kind: RegKind,
    span: Span,
}

enum RegKind {
    Middleware {
        prefix: Option<String>,
        handlers: Vec<String>,
    },
    Route {
        method: String,
        path: String,
        handlers: Vec<String>,
    },
    Mount { prefix: String, router: String },
    Error { name: String },
}

fn classify_registration(program: &Program, expr: &Expr, span: &Span) -> Result<Option<Reg>, Diagnostic> {
    let Expr::Call { callee, args, .. } = expr else {
        return Ok(None);
    };
    let Callee::Member { object, field } = callee else {
        return Ok(None);
    };
    let Expr::Ident(receiver) = object.as_ref() else {
        return Err(bad(span, "router receiver must be an identifier"));
    };
    let method = field.to_ascii_lowercase();
    if !matches!(method.as_str(), "get" | "post" | "put" | "delete" | "patch" | "use") {
        return Ok(None);
    }
    if method == "use" {
        return Ok(Some(classify_use(program, receiver, args, span)?));
    }
    let (path, handlers) = split_route_args(program, args, span)?;
    Ok(Some(Reg {
        receiver: receiver.clone(),
        kind: RegKind::Route {
            method: method.to_ascii_uppercase(),
            path,
            handlers,
        },
        span: span.clone(),
    }))
}

fn classify_use(program: &Program, receiver: &str, args: &[Expr], span: &Span) -> Result<Reg, Diagnostic> {
    if args.is_empty() {
        return Err(bad(span, "app.use needs middleware or a router"));
    }
    let (prefix, idents) = if let Expr::Str(prefix) = &args[0] {
        (Some(prefix.clone()), idents(&args[1..], span)?)
    } else {
        (None, idents(args, span)?)
    };
    if idents.len() == 1 && program.function(&idents[0]).is_none() {
        let Some(prefix) = prefix else {
            return Err(bad(span, "a mounted router needs a static path prefix"));
        };
        return Ok(Reg {
            receiver: receiver.to_string(),
            kind: RegKind::Mount {
                prefix,
                router: idents[0].clone(),
            },
            span: span.clone(),
        });
    }
    if idents.len() == 1 {
        if let Some(func) = program.function(&idents[0]) {
            if func.params.len() >= 4 {
                return Ok(Reg {
                    receiver: receiver.to_string(),
                    kind: RegKind::Error {
                        name: idents[0].clone(),
                    },
                    span: span.clone(),
                });
            }
        }
    }
    for name in &idents {
        if program.function(name).is_none() {
            return Err(bad(span, format!("unknown middleware `{name}`")));
        }
    }
    Ok(Reg {
        receiver: receiver.to_string(),
        kind: RegKind::Middleware {
            prefix,
            handlers: idents,
        },
        span: span.clone(),
    })
}

fn split_route_args(program: &Program, args: &[Expr], span: &Span) -> Result<(String, Vec<String>), Diagnostic> {
    let Some(Expr::Str(path)) = args.first() else {
        return Err(bad(
            span,
            "dynamic route paths are unsupported; use a string literal",
        ));
    };
    if path.contains('*') {
        return Err(bad(span, "wildcard routes are unsupported"));
    }
    let handlers = idents(&args[1..], span)?;
    if handlers.is_empty() {
        return Err(bad(span, "route has no handler"));
    }
    for name in &handlers {
        if program.function(name).is_none() {
            return Err(bad(span, format!("unknown handler `{name}`")));
        }
    }
    Ok((path.clone(), handlers))
}

fn idents(args: &[Expr], span: &Span) -> Result<Vec<String>, Diagnostic> {
    let mut out = Vec::new();
    for arg in args {
        match arg {
            Expr::Ident(name) => out.push(name.clone()),
            _ => {
                return Err(bad(
                    span,
                    "only identifier middleware and handlers are supported",
                ))
            }
        }
    }
    Ok(out)
}

fn flatten(regs: &[Reg], program: &Program) -> Result<Vec<Layer>, Diagnostic> {
    let mut by_receiver: BTreeMap<&str, Vec<&Reg>> = BTreeMap::new();
    let mut mounted = BTreeSet::new();
    for reg in regs {
        by_receiver.entry(reg.receiver.as_str()).or_default().push(reg);
        if let RegKind::Mount { router, .. } = &reg.kind {
            mounted.insert(router.as_str());
        }
    }
    let mut layers = Vec::new();
    for receiver in by_receiver.keys() {
        if mounted.contains(receiver) {
            continue;
        }
        let mut visiting = BTreeSet::new();
        flatten_into(*receiver, "", regs, &by_receiver, &mut visiting, &mut layers, program)?;
    }
    reject_overlaps(&layers)?;
    Ok(layers)
}

fn flatten_into(
    receiver: &str,
    prefix: &str,
    regs: &[Reg],
    by_receiver: &BTreeMap<&str, Vec<&Reg>>,
    visiting: &mut BTreeSet<String>,
    out: &mut Vec<Layer>,
    program: &Program,
) -> Result<(), Diagnostic> {
    if !visiting.insert(receiver.to_string()) {
        return Err(Diagnostic::new(
            ErrorCode::Verify011,
            format!("cyclic router mount involving `{receiver}`"),
        ));
    }
    for reg in by_receiver.get(receiver).into_iter().flatten() {
        match &reg.kind {
            RegKind::Middleware { prefix: pre, handlers } => {
                let path = pre.as_deref().map(|p| join_path(prefix, p));
                out.push(Layer {
                    adapter: "express".into(),
                    span: reg.span.clone(),
                    kind: LayerKind::Middleware {
                        handlers: handlers.clone(),
                        prefix: path,
                    },
                });
            }
            RegKind::Route { method, path, handlers } => out.push(Layer {
                adapter: "express".into(),
                span: reg.span.clone(),
                kind: LayerKind::Route {
                    method: method.clone(),
                    path: join_path(prefix, path),
                    guards: Vec::new(),
                    handlers: handlers.clone(),
                },
            }),
            RegKind::Mount { prefix: pre, router } => {
                flatten_into(router, &join_path(prefix, pre), regs, by_receiver, visiting, out, program)?;
            }
            RegKind::Error { name } => out.push(Layer {
                adapter: "express".into(),
                span: reg.span.clone(),
                kind: LayerKind::ErrorHandler { name: name.clone() },
            }),
        }
    }
    visiting.remove(receiver);
    let _ = program;
    Ok(())
}

fn join_path(prefix: &str, path: &str) -> String {
    let prefix = prefix.trim_end_matches('/');
    if prefix.is_empty() {
        return path.to_string();
    }
    if path == "/" {
        return prefix.to_string();
    }
    format!("{prefix}{path}")
}

fn reject_overlaps(layers: &[Layer]) -> Result<(), Diagnostic> {
    let routes: Vec<_> = layers
        .iter()
        .filter_map(|layer| match &layer.kind {
            LayerKind::Route { method, path, .. } => Some((method.as_str(), path.as_str(), &layer.span)),
            _ => None,
        })
        .collect();
    for (i, (m1, p1, s1)) in routes.iter().enumerate() {
        for (m2, p2, _) in routes.iter().skip(i + 1) {
            if m1 == m2 && p1 != p2 && patterns_overlap(p1, p2) {
                return Err(Diagnostic::new(
                    ErrorCode::Verify011,
                    format!("overlapping routes {m1} {p1} and {m2} {p2} are unsupported"),
                )
                .at((*s1).clone()));
            }
        }
    }
    Ok(())
}

fn path_segments(path: &str) -> Vec<&str> {
    path.split('/').filter(|s| !s.is_empty()).collect()
}

fn patterns_overlap(a: &str, b: &str) -> bool {
    let a = path_segments(a);
    let b = path_segments(b);
    if a.len() != b.len() {
        return false;
    }
    a.iter()
        .zip(b.iter())
        .all(|(x, y)| x == y || x.starts_with(':') || y.starts_with(':'))
}

enum ResponseOp<'a> {
    NotResponse,
    Status { code: &'a Expr, span: Span },
    Commit {
        status: Option<&'a Expr>,
        bodies: &'a [Expr],
        span: Span,
    },
}

fn response_op<'a>(call: &'a Expr, response: &str) -> ResponseOp<'a> {
    let Expr::Call { callee, args, span } = call else {
        return ResponseOp::NotResponse;
    };
    let Callee::Member { object, field } = callee else {
        return ResponseOp::NotResponse;
    };
    if field == "status" && is_ident(object, response) && args.len() == 1 {
        return ResponseOp::Status {
            code: &args[0],
            span: span.clone(),
        };
    }
    if matches!(field.as_str(), "json" | "send" | "end") {
        if is_ident(object, response) {
            return ResponseOp::Commit {
                status: None,
                bodies: args,
                span: span.clone(),
            };
        }
        if let Expr::Call { callee, args: status_args, .. } = object.as_ref() {
            if let Callee::Member { object, field } = callee {
                if field == "status" && is_ident(object, response) && status_args.len() == 1 {
                    return ResponseOp::Commit {
                        status: Some(&status_args[0]),
                        bodies: args,
                        span: span.clone(),
                    };
                }
            }
        }
    }
    ResponseOp::NotResponse
}

fn is_ident(expr: &Expr, name: &str) -> bool {
    matches!(expr, Expr::Ident(id) if id == name)
}

fn bad(span: &Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(ErrorCode::Verify011, message.into()).at(span.clone())
}
