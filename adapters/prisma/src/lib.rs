//! Prisma adapter. The client binding must be named `prisma`.
//! Each call is a trusted autocommit. `$transaction` is rejected.
//! Returned rows are not modeled; calls must be statements.

use ts_proof_adapters::{AdapterMetadata, ClassifyCtx, Layer, VerificationAdapter};
use ts_proof_core::{Callee, Diagnostic, ErrorCode, Expr, Program, Span};
use ts_proof_effects::{effect_stmt, successful_write, TrustItem};
use ts_proof_vir::Stmt;

pub struct PrismaAdapter;

impl PrismaAdapter {
    pub fn new() -> Self {
        Self
    }
}

impl Default for PrismaAdapter {
    fn default() -> Self {
        Self
    }
}

impl VerificationAdapter for PrismaAdapter {
    fn metadata(&self) -> AdapterMetadata {
        AdapterMetadata {
            name: "prisma".into(),
            version: "0.1.0".into(),
            framework: "prisma".into(),
            supported_versions: vec!["5.x".into(), "6.x".into()],
            trust: "external-model".into(),
            capabilities: vec!["create".into(), "update".into(), "delete".into(), "find".into()],
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
        let Some((model, op, args, span)) = prisma_call(call) else {
            return Ok(None);
        };
        if op == "$transaction" {
            return Err(vec![bad(span, "prisma.$transaction is unsupported")]);
        }
        let fail = ctx.pure.fresh_fail(span);
        let failure = ctx.pure.on_failure(span);
        let stmts = match op {
            "create" | "update" => {
                let columns = data_of(args.first(), span)?;
                let mut lowered = Vec::new();
                for (name, expr) in columns {
                    lowered.push((name, ctx.pure.pure(expr).map_err(|d| vec![d])?));
                }
                let record_row = op == "create";
                branch(
                    &format!("db.write.{model}"),
                    fail,
                    failure,
                    successful_write(model, &lowered, record_row, span.clone()),
                    span,
                )
            }
            "delete" => branch(
                &format!("db.delete.{model}"),
                fail,
                failure,
                vec![effect_stmt(&format!("db.delete.{model}.ok"), span.clone())],
                span,
            ),
            "findUnique" | "findFirst" | "findMany" => branch(
                &format!("db.read.{model}"),
                fail,
                failure,
                vec![effect_stmt(&format!("db.read.{model}.ok"), span.clone())],
                span,
            ),
            other => return Err(vec![bad(span, format!("unsupported prisma operation `{other}`"))]),
        };
        Ok(Some(stmts))
    }

    fn contracts(&self) -> Vec<TrustItem> {
        vec![TrustItem::model(
            "prisma",
            "The binding must be named prisma. Each supported call is one autocommit against the model name. Interactive transactions, nested writes, and returned rows are not modeled. `where` is ignored as a filter; it does not constrain which row changes.",
        )]
    }
}

fn prisma_call(call: &Expr) -> Option<(&str, &str, &[Expr], &Span)> {
    let Expr::Call { callee, args, span } = call else {
        return None;
    };
    let Callee::Member { object, field } = callee else {
        return None;
    };
    let Expr::Member { object, field: model, .. } = object.as_ref() else {
        return None;
    };
    let Expr::Ident(root) = object.as_ref() else {
        return None;
    };
    if root != "prisma" {
        return None;
    }
    Some((model.as_str(), field.as_str(), args.as_slice(), span))
}

fn data_of<'a>(arg: Option<&'a Expr>, span: &Span) -> Result<Vec<(String, &'a Expr)>, Vec<Diagnostic>> {
    let Some(Expr::Object { fields, .. }) = arg else {
        return Err(vec![bad(span, "prisma call expects an object literal")]);
    };
    let mut data = None;
    for (name, expr) in fields {
        match name.as_str() {
            "data" => data = Some(expr),
            "where" => {}
            other => return Err(vec![bad(span, format!("unsupported prisma option `{other}`"))]),
        }
    }
    let Some(Expr::Object { fields, .. }) = data else {
        return Err(vec![bad(span, "prisma create/update requires data: { ... }")]);
    };
    Ok(fields.iter().map(|(name, expr)| (name.clone(), expr)).collect())
}

fn branch(
    effect: &str,
    cond: ts_proof_vir::Expr,
    failure: Vec<Stmt>,
    success: Vec<Stmt>,
    span: &Span,
) -> Vec<Stmt> {
    vec![
        effect_stmt(effect, span.clone()),
        Stmt::If {
            cond,
            then_branch: failure,
            else_branch: success,
            span: span.clone(),
        },
    ]
}

fn bad(span: &Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(ErrorCode::Verify011, message.into()).at(span.clone())
}
