//! `pg` adapter. Only statically known SQL in the supported subset is modeled.
//! String concatenation is rejected. This is a trusted database model: it does
//! not prove PostgreSQL, triggers, or concurrent transactions.

use ts_proof_adapters::{AdapterMetadata, ClassifyCtx, Layer, VerificationAdapter};
use ts_proof_core::{Callee, Diagnostic, ErrorCode, Expr, Program, Span};
use ts_proof_effects::{commit_success, effect_stmt, rollback_success, successful_write, TrustItem};
use ts_proof_vir::Stmt;

pub struct PostgresAdapter;

impl PostgresAdapter {
    pub fn new() -> Self {
        Self
    }
}

impl Default for PostgresAdapter {
    fn default() -> Self {
        Self
    }
}

impl VerificationAdapter for PostgresAdapter {
    fn metadata(&self) -> AdapterMetadata {
        AdapterMetadata {
            name: "postgres".into(),
            version: "0.1.0".into(),
            framework: "pg".into(),
            supported_versions: vec!["8.x".into()],
            trust: "external-model".into(),
            capabilities: vec![
                "static-sql".into(),
                "parameters".into(),
                "select".into(),
                "insert".into(),
                "update".into(),
                "delete".into(),
                "transaction".into(),
            ],
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
        let Callee::Member { field, .. } = callee else {
            return Ok(None);
        };
        if field != "query" {
            return Ok(None);
        }
        let Some(sql_expr) = args.first() else {
            return Err(vec![unsupported(span, "pg query needs a SQL string")]);
        };
        let Expr::Str(sql) = sql_expr else {
            return Err(vec![unsupported(
                span,
                "only statically known SQL strings are modeled; concatenation is rejected",
            )]);
        };
        let params = match args.get(1) {
            None => Vec::new(),
            Some(Expr::Array { items, .. }) => {
                let mut lowered = Vec::new();
                for item in items {
                    lowered.push(ctx.pure.pure(item).map_err(|d| vec![d])?);
                }
                lowered
            }
            Some(_) => {
                return Err(vec![unsupported(
                    span,
                    "query parameters must be an array literal",
                )]);
            }
        };
        let op = parse_sql(sql, span).map_err(|d| vec![d])?;
        check_params(&op, params.len(), span).map_err(|d| vec![d])?;
        Ok(Some(emit(op, &params, ctx, span)))
    }

    fn contracts(&self) -> Vec<TrustItem> {
        vec![TrustItem::model(
            "pg",
            "SQL is interpreted as a single-connection mathematical table model. Triggers, row-level security, CHECK constraints, and concurrent transactions are not proved. Isolation is the explicitly single-request model.",
        )]
    }
}

enum Sql {
    Insert {
        table: String,
        columns: Vec<String>,
    },
    Select {
        table: String,
    },
    Update {
        table: String,
        column: String,
    },
    Delete {
        table: String,
    },
    Begin,
    Commit,
    Rollback,
}

fn emit(op: Sql, params: &[ts_proof_vir::Expr], ctx: &mut ClassifyCtx<'_>, span: &Span) -> Vec<Stmt> {
    let fail = ctx.pure.fresh_fail(span);
    let failure = ctx.pure.on_failure(span);
    match op {
        Sql::Insert { table, columns } => {
            let pairs = columns
                .into_iter()
                .zip(params.iter().cloned())
                .collect::<Vec<_>>();
            branch(
                &format!("db.write.{table}"),
                fail,
                failure,
                successful_write(&table, &pairs, true, span.clone()),
                span,
            )
        }
        Sql::Select { table } => branch(
            &format!("db.read.{table}"),
            fail,
            failure,
            vec![effect_stmt(&format!("db.read.{table}.ok"), span.clone())],
            span,
        ),
        Sql::Update { table, column } => {
            let value = params.first().cloned().unwrap_or_else(|| ts_proof_vir::Expr::int("0"));
            branch(
                &format!("db.write.{table}"),
                fail,
                failure,
                successful_write(&table, &[(column, value)], false, span.clone()),
                span,
            )
        }
        Sql::Delete { table } => branch(
            &format!("db.delete.{table}"),
            fail,
            failure,
            vec![effect_stmt(&format!("db.delete.{table}.ok"), span.clone())],
            span,
        ),
        Sql::Begin => branch(
            "db.begin",
            ts_proof_vir::Expr::or(fail, ts_proof_vir::Expr::var("db.tx.active")),
            failure,
            vec![
                ts_proof_effects::assign("db.tx.active", ts_proof_vir::Expr::Bool(true), span.clone()),
                effect_stmt("db.begin.ok", span.clone()),
            ],
            span,
        ),
        Sql::Commit => {
            let inactive = ts_proof_vir::Expr::not(ts_proof_vir::Expr::var("db.tx.active"));
            branch(
                "db.commit",
                ts_proof_vir::Expr::or(fail, inactive),
                failure,
                commit_success(ctx.tables, span.clone()),
                span,
            )
        }
        Sql::Rollback => {
            let inactive = ts_proof_vir::Expr::not(ts_proof_vir::Expr::var("db.tx.active"));
            branch(
                "db.rollback",
                ts_proof_vir::Expr::or(fail, inactive),
                failure,
                rollback_success(ctx.tables, span.clone()),
                span,
            )
        }
    }
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

fn check_params(op: &Sql, nargs: usize, span: &Span) -> Result<(), Diagnostic> {
    let expected = match op {
        Sql::Insert { columns, .. } => columns.len(),
        Sql::Update { .. } => 1,
        Sql::Select { .. } | Sql::Delete { .. } | Sql::Begin | Sql::Commit | Sql::Rollback => 0,
    };
    // SELECT/DELETE may carry a single WHERE parameter. Accept 0 or 1.
    let ok = match op {
        Sql::Select { .. } | Sql::Delete { .. } => nargs == 0 || nargs == 1,
        Sql::Update { .. } => nargs == 1 || nargs == 2,
        _ => nargs == expected,
    };
    if ok {
        Ok(())
    } else {
        Err(unsupported(
            span,
            format!("SQL placeholder count does not match the parameter array ({nargs} arguments)"),
        ))
    }
}

fn parse_sql(sql: &str, span: &Span) -> Result<Sql, Diagnostic> {
    let mut p = Parser {
        raw: sql.as_bytes(),
        i: 0,
        span: span.clone(),
    };
    p.skip();
    let op = if p.eat_kw("insert") {
        p.eat_kw("into").then_some(()).ok_or_else(|| p.err("expected INTO"))?;
        let table = p.ident().ok_or_else(|| p.err("expected table name"))?;
        p.expect_byte(b'(')?;
        let mut columns = Vec::new();
        loop {
            p.skip();
            let col = p.ident().ok_or_else(|| p.err("expected column"))?;
            columns.push(col);
            p.skip();
            if p.eat_byte(b',') {
                continue;
            }
            if p.eat_byte(b')') {
                break;
            }
            return Err(p.err("expected ',' or ')'"));
        }
        p.eat_kw("values").then_some(()).ok_or_else(|| p.err("expected VALUES"))?;
        p.expect_byte(b'(')?;
        for (idx, _) in columns.iter().enumerate() {
            p.skip();
            let n = p.placeholder().ok_or_else(|| p.err("expected $n"))?;
            if n != idx + 1 {
                return Err(p.err("placeholders must be $1, $2, ... in order"));
            }
            p.skip();
            if idx + 1 != columns.len() {
                p.expect_byte(b',')?;
            }
        }
        p.expect_byte(b')')?;
        Sql::Insert { table, columns }
    } else if p.eat_kw("select") {
        p.skip_select_list()?;
        p.eat_kw("from").then_some(()).ok_or_else(|| p.err("expected FROM"))?;
        let table = p.ident().ok_or_else(|| p.err("expected table name"))?;
        p.skip_optional_where()?;
        Sql::Select { table }
    } else if p.eat_kw("update") {
        let table = p.ident().ok_or_else(|| p.err("expected table name"))?;
        p.eat_kw("set").then_some(()).ok_or_else(|| p.err("expected SET"))?;
        let column = p.ident().ok_or_else(|| p.err("expected column"))?;
        p.expect_byte(b'=')?;
        let n = p.placeholder().ok_or_else(|| p.err("expected $1"))?;
        if n != 1 {
            return Err(p.err("UPDATE assignment must use $1"));
        }
        p.skip_optional_where()?;
        Sql::Update { table, column }
    } else if p.eat_kw("delete") {
        p.eat_kw("from").then_some(()).ok_or_else(|| p.err("expected FROM"))?;
        let table = p.ident().ok_or_else(|| p.err("expected table name"))?;
        p.skip_optional_where()?;
        Sql::Delete { table }
    } else if p.eat_kw("begin") {
        Sql::Begin
    } else if p.eat_kw("commit") {
        Sql::Commit
    } else if p.eat_kw("rollback") {
        Sql::Rollback
    } else {
        return Err(p.err("unsupported SQL statement"));
    };
    p.skip();
    if p.i != p.raw.len() {
        return Err(p.err("unsupported SQL suffix"));
    }
    Ok(op)
}

struct Parser<'a> {
    raw: &'a [u8],
    i: usize,
    span: Span,
}

impl<'a> Parser<'a> {
    fn skip(&mut self) {
        while self.i < self.raw.len() && self.raw[self.i].is_ascii_whitespace() {
            self.i += 1;
        }
    }
    fn eat_kw(&mut self, kw: &str) -> bool {
        self.skip();
        let end = self.i + kw.len();
        if end <= self.raw.len()
            && self.raw[self.i..end].eq_ignore_ascii_case(kw.as_bytes())
            && !self.raw.get(end).is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_')
        {
            self.i = end;
            true
        } else {
            false
        }
    }
    fn ident(&mut self) -> Option<String> {
        self.skip();
        let start = self.i;
        if self.i < self.raw.len() && (self.raw[self.i].is_ascii_alphabetic() || self.raw[self.i] == b'_')
        {
            self.i += 1;
            while self.i < self.raw.len()
                && (self.raw[self.i].is_ascii_alphanumeric() || self.raw[self.i] == b'_')
            {
                self.i += 1;
            }
            Some(String::from_utf8(self.raw[start..self.i].to_vec()).ok()?)
        } else {
            None
        }
    }
    fn placeholder(&mut self) -> Option<usize> {
        self.skip();
        if self.i < self.raw.len() && self.raw[self.i] == b'$' {
            self.i += 1;
            let start = self.i;
            while self.i < self.raw.len() && self.raw[self.i].is_ascii_digit() {
                self.i += 1;
            }
            std::str::from_utf8(&self.raw[start..self.i]).ok()?.parse().ok()
        } else {
            None
        }
    }
    fn eat_byte(&mut self, b: u8) -> bool {
        self.skip();
        if self.i < self.raw.len() && self.raw[self.i] == b {
            self.i += 1;
            true
        } else {
            false
        }
    }
    fn expect_byte(&mut self, b: u8) -> Result<(), Diagnostic> {
        if self.eat_byte(b) {
            Ok(())
        } else {
            Err(self.err(format!("expected '{}'", b as char)))
        }
    }
    fn skip_select_list(&mut self) -> Result<(), Diagnostic> {
        self.skip();
        if self.eat_byte(b'*') {
            return Ok(());
        }
        loop {
            if self.ident().is_none() {
                return Err(self.err("expected select list"));
            }
            self.skip();
            if !self.eat_byte(b',') {
                break;
            }
        }
        Ok(())
    }
    fn skip_optional_where(&mut self) -> Result<(), Diagnostic> {
        if !self.eat_kw("where") {
            return Ok(());
        }
        loop {
            if self.ident().is_none() {
                return Err(self.err("unsupported WHERE clause"));
            }
            self.expect_byte(b'=')?;
            if self.placeholder().is_none() {
                return Err(self.err("WHERE comparisons must use a $n parameter"));
            }
            if !self.eat_kw("and") {
                break;
            }
        }
        Ok(())
    }
    fn err(&self, message: impl Into<String>) -> Diagnostic {
        unsupported(&self.span, message)
    }
}

fn unsupported(span: &Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(ErrorCode::Verify011, message.into()).at(span.clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_insert_and_rejects_concatenation_shape() {
        let span = Span::dummy();
        let sql = parse_sql(
            "INSERT INTO tokens(agent_id, principal) VALUES($1, $2)",
            &span,
        )
        .unwrap();
        match sql {
            Sql::Insert { table, columns } => {
                assert_eq!(table, "tokens");
                assert_eq!(columns, ["agent_id", "principal"]);
            }
            _ => panic!("insert"),
        }
        assert!(parse_sql("INSERT INTO tokens VALUES($1 || $2)", &span).is_err());
    }
}
