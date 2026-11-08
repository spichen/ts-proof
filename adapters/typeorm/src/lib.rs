//! TypeORM adapter for a narrow repository shape.
//!
//! The receiver must be named `repo` or end in `Repository`. `insert` and `save`
//! require an object literal. Entity variables, query builders, and relations
//! are rejected. The table name in the model is the receiver identifier.

use ts_proof_adapters::{AdapterMetadata, ClassifyCtx, Layer, VerificationAdapter};
use ts_proof_core::{Callee, Diagnostic, ErrorCode, Expr, Program, Span};
use ts_proof_effects::{effect_stmt, successful_write, TrustItem};
use ts_proof_vir::Stmt;

pub struct TypeOrmAdapter;

impl TypeOrmAdapter {
    pub fn new() -> Self {
        Self
    }
}

impl Default for TypeOrmAdapter {
    fn default() -> Self {
        Self
    }
}

impl VerificationAdapter for TypeOrmAdapter {
    fn metadata(&self) -> AdapterMetadata {
        AdapterMetadata {
            name: "typeorm".into(),
            version: "0.1.0".into(),
            framework: "typeorm".into(),
            supported_versions: vec!["0.3.x".into()],
            trust: "external-model".into(),
            capabilities: vec!["insert".into(), "save".into(), "delete".into(), "find".into()],
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
        let Callee::Member { object, field } = callee else {
            return Ok(None);
        };
        let Expr::Ident(repo) = object.as_ref() else {
            return Ok(None);
        };
        if !(repo == "repo" || repo.ends_with("Repository")) {
            return Ok(None);
        }
        if !matches!(field.as_str(), "insert" | "save" | "delete" | "find" | "findOne") {
            return Err(vec![bad(
                span,
                format!("unsupported TypeORM operation `{field}` on `{repo}`"),
            )]);
        }
        let fail = ctx.pure.fresh_fail(span);
        let failure = ctx.pure.on_failure(span);
        let stmts = match field.as_str() {
            "insert" | "save" => {
                let columns = object_columns(args.first(), span)?;
                let mut lowered = Vec::new();
                for (name, expr) in columns {
                    lowered.push((name, ctx.pure.pure(expr).map_err(|d| vec![d])?));
                }
                branch(
                    &format!("db.write.{repo}"),
                    fail,
                    failure,
                    successful_write(repo, &lowered, field == "insert", span.clone()),
                    span,
                )
            }
            "delete" => branch(
                &format!("db.delete.{repo}"),
                fail,
                failure,
                vec![effect_stmt(&format!("db.delete.{repo}.ok"), span.clone())],
                span,
            ),
            "find" | "findOne" => branch(
                &format!("db.read.{repo}"),
                fail,
                failure,
                vec![effect_stmt(&format!("db.read.{repo}.ok"), span.clone())],
                span,
            ),
            _ => unreachable!("operation filtered above"),
        };
        Ok(Some(stmts))
    }

    fn contracts(&self) -> Vec<TrustItem> {
        vec![TrustItem::model(
            "typeorm",
            "Only repo/Repository insert, save, delete, find, and findOne are modeled, and only with object-literal arguments. The table name is the receiver identifier. Relations, query builders, and entity identity are not modeled.",
        )]
    }
}

fn object_columns<'a>(
    arg: Option<&'a Expr>,
    span: &Span,
) -> Result<Vec<(String, &'a Expr)>, Vec<Diagnostic>> {
    let Some(Expr::Object { fields, .. }) = arg else {
        return Err(vec![bad(
            span,
            "TypeORM write requires an object literal; entity variables are unsupported",
        )]);
    };
    Ok(fields.iter().map(|(n, e)| (n.clone(), e)).collect())
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
