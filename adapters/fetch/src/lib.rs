//! Fetch adapter.
//!
//! `http.last_url` is the last completed destination, not a universal quantifier
//! over every call. The first four completed destinations are stored in
//! `http.url.0` through `http.url.3`. A fifth attempt fails closed because those
//! destinations would be untracked. Header and body expressions are pure-lowered
//! so an effect cannot hide inside the init object.

use ts_proof_adapters::{AdapterMetadata, ClassifyCtx, Layer, PureLower, VerificationAdapter};
use ts_proof_core::{Callee, Diagnostic, ErrorCode, Expr, Program, Span};
use ts_proof_effects::{assign, effect_stmt, TrustItem};
use ts_proof_vir::{BinOp, Expr as VExpr, Stmt};

pub struct FetchAdapter;

impl FetchAdapter {
    pub fn new() -> Self {
        Self
    }
}

impl Default for FetchAdapter {
    fn default() -> Self {
        Self
    }
}

const SLOTS: usize = 4;

impl VerificationAdapter for FetchAdapter {
    fn metadata(&self) -> AdapterMetadata {
        AdapterMetadata {
            name: "fetch".into(),
            version: "0.1.0".into(),
            framework: "fetch".into(),
            supported_versions: vec!["undici".into(), "node-18+".into()],
            trust: "external-model".into(),
            capabilities: vec!["destination".into(), "method".into(), "failure".into()],
        }
    }

    fn discover(&self, _program: &Program) -> Result<Vec<Layer>, Vec<Diagnostic>> {
        Ok(Vec::new())
    }

    fn lower_call(
        &self,
        call: &Expr,
        ctx: &mut ClassifyCtx<'_>,
    ) -> Result<Option<Vec<Stmt>>, Vec<Diagnostic>> {
        let Expr::Call { callee, args, span } = call else {
            return Ok(None);
        };
        let is_fetch = match callee {
            Callee::Ident(name) if name == "fetch" => true,
            Callee::Member { field, .. } if field == "fetch" => true,
            _ => false,
        };
        if !is_fetch {
            return Ok(None);
        }
        let Some(url) = args.first() else {
            return Err(vec![bad(span, "fetch requires a destination")]);
        };
        let url = ctx.pure.pure(url).map_err(|d| vec![d])?;
        let method = method_of(args.get(1), span, ctx.pure)?;
        let fail = ctx.pure.fresh_fail(span);
        let failure = ctx.pure.on_failure(span);
        let mut success = Vec::new();
        for slot in 0..SLOTS {
            let name = format!("http.url.{slot}");
            success.push(assign(
                &name,
                VExpr::ite(
                    VExpr::eq(VExpr::var("http.count"), VExpr::int(slot.to_string())),
                    url.clone(),
                    VExpr::var(&name),
                ),
                span.clone(),
            ));
        }
        success.push(assign("http.last_url", url, span.clone()));
        success.push(assign(
            "http.last_method",
            VExpr::Str(method),
            span.clone(),
        ));
        success.push(assign(
            "http.count",
            VExpr::binary(BinOp::Add, VExpr::var("http.count"), VExpr::int("1")),
            span.clone(),
        ));
        success.push(effect_stmt("http.fetch.ok", span.clone()));
        // A call past the tracked slots cannot be named in a destination law.
        let overflow = VExpr::binary(
            BinOp::Ge,
            VExpr::var("http.count"),
            VExpr::int(SLOTS.to_string()),
        );
        let stmts = vec![
            effect_stmt("http.fetch", span.clone()),
            Stmt::If {
                cond: VExpr::or(fail, overflow),
                then_branch: failure,
                else_branch: success,
                span: span.clone(),
            },
        ];
        // Count is incremented inside success, so the overflow test above sees the
        // pre-call count. The fifth attempt (count already 4) fails closed.
        Ok(Some(stmts))
    }

    fn contracts(&self) -> Vec<TrustItem> {
        vec![TrustItem::model(
            "fetch",
            "Outbound calls record an attempt, then either fail or complete. http.last_url is only the last completed destination. http.url.0 through http.url.3 record the first four completed calls. The remote server's decision is not proved.",
        )]
    }
}

fn method_of(
    init: Option<&Expr>,
    span: &Span,
    pure: &mut dyn PureLower,
) -> Result<String, Vec<Diagnostic>> {
    let Some(init) = init else {
        return Ok("GET".into());
    };
    let Expr::Object { fields, .. } = init else {
        return Err(vec![bad(span, "fetch init must be an object literal")]);
    };
    let mut method = "GET".to_string();
    let mut seen_method = false;
    for (name, value) in fields {
        match name.as_str() {
            "method" => {
                if seen_method {
                    return Err(vec![bad(span, "fetch method is repeated")]);
                }
                seen_method = true;
                let Expr::Str(text) = value else {
                    return Err(vec![bad(span, "fetch method must be a string literal")]);
                };
                method = text.clone();
            }
            "headers" => {
                let Expr::Object { fields, .. } = value else {
                    return Err(vec![bad(span, "fetch headers must be an object literal")]);
                };
                for (_, header) in fields {
                    pure.seal(header).map_err(|d| vec![d])?;
                }
            }
            "body" => {
                pure.seal(value).map_err(|d| vec![d])?;
            }
            _ => {
                return Err(vec![bad(
                    span,
                    format!("unsupported fetch option `{name}`"),
                )]);
            }
        }
    }
    Ok(method)
}

fn bad(span: &Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(ErrorCode::Verify011, message.into()).at(span.clone())
}
