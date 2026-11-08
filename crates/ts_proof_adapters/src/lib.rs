//! Adapter boundary. Adapters classify framework operations and emit effect VIR.
//! They do not see `tsrs` types. Unrecognized shapes are errors, not skips.

use ts_proof_core::{Diagnostic, Expr, Program, Span};
use ts_proof_effects::TrustItem;
use ts_proof_vir::Stmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdapterMetadata {
    pub name: String,
    pub version: String,
    pub framework: String,
    pub supported_versions: Vec<String>,
    pub trust: String,
    pub capabilities: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layer {
    pub kind: LayerKind,
    pub span: Span,
    pub adapter: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LayerKind {
    Middleware {
        handlers: Vec<String>,
        /// `None` means every request. `Some` is a static path prefix.
        prefix: Option<String>,
    },
    Route {
        method: String,
        path: String,
        /// Boolean guards. A false result commits a 403 and does not run handlers.
        guards: Vec<String>,
        /// Express middleware in order, or a single Nest handler. Express handlers
        /// continue only through an explicit `next()` call.
        handlers: Vec<String>,
    },
    ErrorHandler {
        name: String,
    },
}

pub struct ClassifyCtx<'a> {
    pub response_ident: Option<&'a str>,
    pub pure: &'a mut dyn PureLower,
    /// Tables written in the function currently being lowered. Commit flushes these.
    pub tables: &'a [String],
}

/// Lowers a pure expression. Implementations must reject effectful expressions.
pub trait PureLower {
    fn pure(&mut self, expr: &Expr) -> Result<ts_proof_vir::Expr, Diagnostic>;
    /// Reject effects and unsupported syntax, but allow object and array payloads
    /// whose values are not given a mathematical meaning.
    fn seal(&mut self, expr: &Expr) -> Result<(), Diagnostic>;
    fn fresh_fail(&mut self, span: &Span) -> ts_proof_vir::Expr;
    /// Statements that run when a modeled operation fails.
    /// Function bodies throw. `try` and endpoint composition set a failure flag.
    fn on_failure(&mut self, span: &Span) -> Vec<ts_proof_vir::Stmt>;
}

pub trait VerificationAdapter: Send + Sync {
    fn metadata(&self) -> AdapterMetadata;
    fn discover(&self, program: &Program) -> Result<Vec<Layer>, Vec<Diagnostic>>;
    /// `Ok(None)` means this adapter does not own the call.
    /// `Ok(Some(stmts))` replaces the call. Effectful calls must be statements
    /// or the sole expression of a `let` / `return`; the lowerer enforces that.
    fn lower_call(
        &self,
        call: &Expr,
        ctx: &mut ClassifyCtx<'_>,
    ) -> Result<Option<Vec<Stmt>>, Vec<Diagnostic>>;
    fn contracts(&self) -> Vec<TrustItem> {
        Vec::new()
    }
}

pub struct Registry {
    adapters: Vec<Box<dyn VerificationAdapter>>,
}

impl Registry {
    pub fn new(adapters: Vec<Box<dyn VerificationAdapter>>) -> Self {
        Self { adapters }
    }

    pub fn metadata(&self) -> Vec<AdapterMetadata> {
        self.adapters.iter().map(|a| a.metadata()).collect()
    }

    pub fn discover_all(&self, program: &Program) -> Result<Vec<Layer>, Vec<Diagnostic>> {
        let mut layers = Vec::new();
        let mut diags = Vec::new();
        for adapter in &self.adapters {
            match adapter.discover(program) {
                Ok(found) => layers.extend(found),
                Err(err) => diags.extend(err),
            }
        }
        if diags.is_empty() {
            Ok(layers)
        } else {
            Err(diags)
        }
    }

    pub fn lower_call(
        &self,
        call: &Expr,
        ctx: &mut ClassifyCtx<'_>,
    ) -> Result<Option<Vec<Stmt>>, Vec<Diagnostic>> {
        for adapter in &self.adapters {
            if let Some(stmts) = adapter.lower_call(call, ctx)? {
                return Ok(Some(stmts));
            }
        }
        Ok(None)
    }

    pub fn contracts(&self) -> Vec<TrustItem> {
        self.adapters.iter().flat_map(|a| a.contracts()).collect()
    }
}
