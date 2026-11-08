//! Names and initial values for the effect model.
//!
//! Counters record attempts. `*.ok` counters record successful completion.
//! Database ghosts distinguish an attempted write, a pending write inside an
//! open transaction, and a committed write. Missing `db.last.*` values stay
//! unconstrained so an omitted insert cannot look like a zero id.

use std::collections::BTreeSet;
use ts_proof_core::Span;
use ts_proof_vir::{BinOp, Expr, Ghost, Stmt, VirType};

pub fn trace(effect: &str) -> String {
    format!("trace.{effect}")
}

pub fn trace_ok(effect: &str) -> String {
    format!("trace.{effect}.ok")
}

pub fn is_known_request_field(field: &str) -> bool {
    matches!(
        field,
        "authenticated" | "authorized" | "agentId" | "principal" | "method" | "path"
    )
}

pub fn request_field_type(field: &str) -> Option<VirType> {
    match field {
        "authenticated" | "authorized" => Some(VirType::Bool),
        "agentId" | "principal" => Some(VirType::Int),
        "method" | "path" => Some(VirType::String),
        _ => None,
    }
}

pub fn request_var(field: &str) -> String {
    format!("request.{field}")
}

/// Ghosts that must start at a concrete value. Names that are assigned in the
/// body but are not listed here stay symbolic, which is required for
/// `db.last.*` identity checks.
pub fn concrete_initial(name: &str) -> Option<(VirType, Expr)> {
    if name.starts_with("trace.") || name.starts_with("db.committed.") || name.starts_with("db.pending.")
    {
        return Some((VirType::Int, Expr::int("0")));
    }
    match name {
        "response.status" => Some((VirType::Int, Expr::int("0"))),
        "response.committed" | "response.statusSet" | "db.tx.active" => {
            Some((VirType::Bool, Expr::Bool(false)))
        }
        "http.count" | "clock" | "response.clock" => Some((VirType::Int, Expr::int("0"))),
        "http.last_url" | "http.last_method" => Some((VirType::String, Expr::Str(String::new()))),
        _ if name.starts_with("db.seq.") => Some((VirType::Int, Expr::int("0"))),
        _ if name.starts_with("http.url.") => Some((VirType::String, Expr::Str(String::new()))),
        _ => None,
    }
}

pub fn ghosts_for(assigned: &BTreeSet<String>) -> Vec<Ghost> {
    let mut out = Vec::new();
    for name in assigned {
        if let Some((ty, init)) = concrete_initial(name) {
            out.push(Ghost {
                name: name.clone(),
                ty,
                init,
            });
        }
    }
    out
}

pub fn effect_stmt(effect: &str, span: Span) -> Stmt {
    Stmt::Effect {
        effect: effect.to_string(),
        counter: trace(effect),
        span,
    }
}

pub fn assign(name: &str, expr: Expr, span: Span) -> Stmt {
    Stmt::Assign {
        name: name.to_string(),
        expr,
        span,
    }
}

fn plus_one(name: &str) -> Expr {
    Expr::binary(BinOp::Add, Expr::var(name), Expr::int("1"))
}

/// Advance the single-request effect clock. Sequence numbers are comparable
/// only inside one modeled request.
pub fn tick(span: Span) -> Stmt {
    assign("clock", plus_one("clock"), span)
}

/// Record the clock value after one tick. A later stamp is a larger integer.
pub fn stamp(name: &str, span: Span) -> Vec<Stmt> {
    vec![tick(span.clone()), assign(name, Expr::var("clock"), span)]
}

/// Successful write. Pending while a transaction is active, otherwise committed.
/// `db.last.<table>.<column>` changes only on this success path.
pub fn successful_write(
    table: &str,
    columns: &[(String, Expr)],
    record_row: bool,
    span: Span,
) -> Vec<Stmt> {
    let pending = format!("db.pending.{table}");
    let committed = format!("db.committed.{table}");
    let mut stmts = Vec::new();
    if record_row {
        stmts.push(Stmt::If {
            cond: Expr::var("db.tx.active"),
            then_branch: vec![assign(&pending, plus_one(&pending), span.clone())],
            else_branch: vec![assign(&committed, plus_one(&committed), span.clone())],
            span: span.clone(),
        });
    }
    for (column, value) in columns {
        stmts.push(assign(
            &format!("db.last.{table}.{column}"),
            value.clone(),
            span.clone(),
        ));
    }
    stmts.extend(stamp(&format!("db.seq.{table}"), span.clone()));
    stmts.push(effect_stmt(&format!("db.write.{table}.ok"), span));
    stmts
}

pub fn commit_success(tables: &[String], span: Span) -> Vec<Stmt> {
    let mut success = Vec::new();
    for table in tables {
        let pending = format!("db.pending.{table}");
        let committed = format!("db.committed.{table}");
        success.push(assign(
            &committed,
            Expr::binary(BinOp::Add, Expr::var(&committed), Expr::var(&pending)),
            span.clone(),
        ));
        success.push(assign(&pending, Expr::int("0"), span.clone()));
    }
    success.push(assign("db.tx.active", Expr::Bool(false), span.clone()));
    success.push(effect_stmt("db.commit.ok", span));
    success
}

pub fn rollback_success(tables: &[String], span: Span) -> Vec<Stmt> {
    let mut success = Vec::new();
    for table in tables {
        success.push(assign(
            &format!("db.pending.{table}"),
            Expr::int("0"),
            span.clone(),
        ));
    }
    success.push(assign("db.tx.active", Expr::Bool(false), span.clone()));
    success.push(effect_stmt("db.rollback.ok", span));
    success
}

pub fn endpoint_request_params() -> Vec<ts_proof_vir::VirParam> {
    ["authenticated", "authorized", "agentId", "principal", "method", "path"]
        .into_iter()
        .map(|field| ts_proof_vir::VirParam {
            name: request_var(field),
            ty: request_field_type(field).expect("known field"),
        })
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustItem {
    pub category: String,
    pub component: String,
    pub assumption: String,
}

impl TrustItem {
    pub fn model(component: impl Into<String>, assumption: impl Into<String>) -> Self {
        Self {
            category: "trusted-model".into(),
            component: component.into(),
            assumption: assumption.into(),
        }
    }
}
