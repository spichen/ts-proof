//! NestJS adapter for static controller methods.
//!
//! A guard is a function returning boolean. `false` commits HTTP 403 and does
//! not run the handler. Dependency injection, pipes, interceptors, and exception
//! filters are rejected rather than approximated.

use ts_proof_adapters::{AdapterMetadata, ClassifyCtx, Layer, LayerKind, VerificationAdapter};
use ts_proof_core::{Diagnostic, ErrorCode, Expr, Program, Span};
use ts_proof_effects::TrustItem;
use ts_proof_vir::Stmt;

pub struct NestAdapter;

impl NestAdapter {
    pub fn new() -> Self {
        Self
    }
}

impl Default for NestAdapter {
    fn default() -> Self {
        Self
    }
}

impl VerificationAdapter for NestAdapter {
    fn metadata(&self) -> AdapterMetadata {
        AdapterMetadata {
            name: "nestjs".into(),
            version: "0.1.0".into(),
            framework: "nestjs".into(),
            supported_versions: vec!["10.x".into(), "11.x".into()],
            trust: "external-model".into(),
            capabilities: vec!["controllers".into(), "guards".into()],
        }
    }

    fn discover(&self, program: &Program) -> Result<Vec<Layer>, Vec<Diagnostic>> {
        let mut layers = Vec::new();
        let mut diags = Vec::new();
        for func in &program.functions {
            if func.class_name.is_none() {
                continue;
            }
            let Some(controller) = decorator(&func.class_decorators, "Controller") else {
                continue;
            };
            let Some(route) = route_decorator(&func.decorators) else {
                if func.decorators.iter().any(|d| {
                    matches!(d.name.as_str(), "Get" | "Post" | "Put" | "Delete" | "Patch")
                }) {
                    diags.push(bad(&func.span, "unreadable Nest route decorator"));
                }
                continue;
            };
            let prefix = string_arg(controller).unwrap_or_else(|| "/".into());
            let path = join_path(&prefix, &route.path);
            let mut guards = Vec::new();
            for dec in &func.decorators {
                if dec.name == "UseGuards" {
                    for arg in &dec.args {
                        match arg {
                            Expr::Ident(name) if program.function(name).is_some() => {
                                guards.push(name.clone());
                            }
                            _ => diags.push(bad(
                                &dec.span,
                                "UseGuards only accepts identifier functions in this subset",
                            )),
                        }
                    }
                }
            }
            if route.unsupported {
                diags.push(bad(&func.span, "dynamic Nest paths are unsupported"));
                continue;
            }
            layers.push(Layer {
                adapter: "nestjs".into(),
                span: func.span.clone(),
                kind: LayerKind::Route {
                    method: route.method,
                    path,
                    guards,
                    handlers: vec![func.name.clone()],
                },
            });
        }
        if diags.is_empty() { Ok(layers) } else { Err(diags) }
    }

    fn lower_call(
        &self,
        _call: &Expr,
        _ctx: &mut ClassifyCtx<'_>,
    ) -> Result<Option<Vec<Stmt>>, Vec<Diagnostic>> {
        Ok(None)
    }

    fn contracts(&self) -> Vec<TrustItem> {
        vec![TrustItem::model(
            "nestjs",
            "Controllers and boolean guards are modeled. Pipes, interceptors, exception filters, and dependency injection are unsupported. A guard returning false commits 403 and skips the handler.",
        )]
    }
}

struct RouteDec {
    method: String,
    path: String,
    unsupported: bool,
}

fn route_decorator(decs: &[ts_proof_core::Decorator]) -> Option<RouteDec> {
    for dec in decs {
        let method = match dec.name.as_str() {
            "Get" => "GET",
            "Post" => "POST",
            "Put" => "PUT",
            "Delete" => "DELETE",
            "Patch" => "PATCH",
            _ => continue,
        };
        let (path, unsupported) = match dec.args.first() {
            None => ("/".into(), false),
            Some(Expr::Str(path)) => (path.clone(), path.contains('*')),
            Some(_) => ("/".into(), true),
        };
        return Some(RouteDec {
            method: method.into(),
            path,
            unsupported,
        });
    }
    None
}

fn decorator<'a>(decs: &'a [ts_proof_core::Decorator], name: &str) -> Option<&'a ts_proof_core::Decorator> {
    decs.iter().find(|d| d.name == name)
}

fn string_arg(dec: &ts_proof_core::Decorator) -> Option<String> {
    match dec.args.first() {
        Some(Expr::Str(s)) => Some(s.clone()),
        None => Some("/".into()),
        _ => None,
    }
}

fn join_path(prefix: &str, path: &str) -> String {
    let prefix = prefix.trim_end_matches('/');
    if path.is_empty() || path == "/" {
        return if prefix.is_empty() {
            "/".into()
        } else {
            prefix.to_string()
        };
    }
    let path = if path.starts_with('/') {
        path.to_string()
    } else {
        format!("/{path}")
    };
    if prefix.is_empty() {
        path
    } else {
        format!("{prefix}{path}")
    }
}

fn bad(span: &Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(ErrorCode::Verify011, message.into()).at(span.clone())
}
