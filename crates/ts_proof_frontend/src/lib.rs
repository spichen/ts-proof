//! Discover laws, lower programs, and fail closed unless every required
//! obligation is proved.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use ts_proof_adapter_express::ExpressAdapter;
use ts_proof_adapter_fetch::FetchAdapter;
use ts_proof_adapter_nestjs::NestAdapter;
use ts_proof_adapter_postgres::PostgresAdapter;
use ts_proof_adapter_prisma::PrismaAdapter;
use ts_proof_adapter_typeorm::TypeOrmAdapter;
use ts_proof_adapters::{Layer, LayerKind, Registry};
use ts_proof_cache::{cache_dir, digest, Cache, CacheLookup};
use ts_proof_core::{
    Callee, Diagnostic, ErrorCode, Expr as Ast, External, Program, ProjectConfig, RequiredEndpoint,
    SourceFile, Stmt, CONFIG_FILE, REQUIRED_FILE, VERIFIER_VERSION,
};
use ts_proof_coverage::{assess, CoverageReport, LawStatus};
use ts_proof_diagnostics::{render_junit, render_sarif, render_text};
use ts_proof_lowering::{lower_endpoint, lower_function, with_contract};
use ts_proof_proof::check_lemmas;
use ts_proof_smt::{encode_validity, Z3};
use ts_proof_spec::lower_spec;
use ts_proof_tsrs_bridge::{emit_with_tsrs, parse_sources, typecheck};
use ts_proof_vc::{generate, solve_obligation};
use ts_proof_vir::{Expr, VirFunction};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Check,
    Prove,
    Build,
    Coverage,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutputFormat {
    Text,
    Json,
    Sarif,
    Junit,
}

impl OutputFormat {
    pub fn parse(text: &str) -> Option<Self> {
        match text {
            "text" => Some(Self::Text),
            "json" => Some(Self::Json),
            "sarif" => Some(Self::Sarif),
            "junit" => Some(Self::Junit),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct VerifyOptions {
    pub config: ProjectConfig,
    pub cache_dir: Option<PathBuf>,
    pub z3_path: Option<String>,
    pub timeout_ms: Option<u64>,
}

impl Default for VerifyOptions {
    fn default() -> Self {
        Self {
            config: ProjectConfig::default(),
            cache_dir: None,
            z3_path: None,
            timeout_ms: None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ObligationRecord {
    pub name: String,
    pub proved: bool,
    pub cached: bool,
    pub diagnostic: Option<Diagnostic>,
}

#[derive(Clone, Debug)]
pub struct Report {
    pub diagnostics: Vec<Diagnostic>,
    pub proved: Vec<String>,
    pub obligations: Vec<ObligationRecord>,
    pub coverage: CoverageReport,
    pub files: Vec<SourceFile>,
    pub cached_hits: usize,
    pub tool_error: bool,
}

impl Report {
    pub fn empty() -> Self {
        Self {
            diagnostics: Vec::new(),
            proved: Vec::new(),
            obligations: Vec::new(),
            coverage: CoverageReport::empty(),
            files: Vec::new(),
            cached_hits: 0,
            tool_error: false,
        }
    }

    pub fn ok(&self) -> bool {
        self.diagnostics.iter().all(|diag| !diag.is_failure())
    }

    pub fn exit_code(&self) -> i32 {
        if self.tool_error {
            2
        } else if self.ok() {
            0
        } else {
            1
        }
    }

    pub fn render(&self, format: OutputFormat) -> String {
        match format {
            OutputFormat::Text => self.render_text(),
            OutputFormat::Json => self.render_json(),
            OutputFormat::Sarif => render_sarif(&self.diagnostics, &self.files),
            OutputFormat::Junit => render_junit(&self.diagnostics),
        }
    }

    pub fn render_text(&self) -> String {
        let mut out = render_text(&self.diagnostics, &self.files);
        out.push_str("coverage:\n");
        out.push_str(&format!(
            "  discovered endpoints: {}\n",
            join_or_none(&self.coverage.discovered_endpoints)
        ));
        out.push_str(&format!(
            "  verified endpoints: {}\n",
            join_or_none(&self.coverage.verified_endpoints)
        ));
        out.push_str(&format!(
            "  unverified endpoints: {}\n",
            join_or_none(&self.coverage.unverified_endpoints)
        ));
        out.push_str(&format!(
            "  obligations proved: {}\n  obligations failed: {}\n  cached hits: {}\n",
            self.coverage.proved_obligations, self.coverage.failed_obligations, self.cached_hits
        ));
        if !self.proved.is_empty() {
            out.push_str("proved:\n");
            for name in &self.proved {
                out.push_str(&format!("  {name}\n"));
            }
        }
        out
    }

    fn render_json(&self) -> String {
        let value = serde_json::json!({
            "ok": self.ok(),
            "exitCode": self.exit_code(),
            "proved": self.proved,
            "cachedHits": self.cached_hits,
            "coverage": self.coverage,
            "diagnostics": self.diagnostics,
        });
        serde_json::to_string_pretty(&value).unwrap_or_else(|_| "{}".into())
    }
}

pub fn official_registry() -> Registry {
    Registry::new(vec![
        Box::new(ExpressAdapter::new()),
        Box::new(NestAdapter::new()),
        Box::new(PostgresAdapter::new()),
        Box::new(PrismaAdapter::new()),
        Box::new(TypeOrmAdapter::new()),
        Box::new(FetchAdapter::new()),
    ])
}

pub fn load_config(root: &Path) -> Result<ProjectConfig, Diagnostic> {
    let mut config = if root.join(CONFIG_FILE).is_file() {
        let path = root.join(CONFIG_FILE);
        let text = fs::read_to_string(&path).map_err(|err| config_error(&path, err.to_string()))?;
        serde_json::from_str(&text).map_err(|err| config_error(&path, err.to_string()))?
    } else {
        ProjectConfig::default()
    };
    let required = root.join(REQUIRED_FILE);
    if required.is_file() {
        let text = fs::read_to_string(&required).map_err(|err| config_error(&required, err.to_string()))?;
        let extra: Vec<RequiredEndpoint> =
            serde_json::from_str(&text).map_err(|err| config_error(&required, err.to_string()))?;
        config.required_endpoints.extend(extra);
    }
    Ok(config)
}

pub fn check_project(root: &Path, mode: Mode) -> Report {
    let config = match load_config(root) {
        Ok(config) => config,
        Err(diag) => {
            let mut report = Report::empty();
            report.diagnostics.push(diag);
            report.tool_error = true;
            return report;
        }
    };
    let mut preface = typecheck(root, config.verification.compiler_required);
    if preface.iter().any(|diag| diag.is_failure()) {
        let mut report = Report::empty();
        if mode == Mode::Build {
            preface.push(Diagnostic::new(
                ErrorCode::Verify015,
                "JavaScript was not emitted because typechecking failed",
            ));
        }
        report.diagnostics = preface;
        return report;
    }
    let sources = match read_sources(root) {
        Ok(sources) => sources,
        Err(diag) => {
            let mut report = Report::empty();
            report.diagnostics = preface;
            report.diagnostics.push(diag);
            report.tool_error = true;
            return report;
        }
    };
    if sources.is_empty() {
        let mut report = Report::empty();
        report.diagnostics = preface;
        report.diagnostics.push(Diagnostic::new(
            ErrorCode::Verify010,
            format!("no TypeScript sources under {}", root.display()),
        ));
        return report;
    }
    let pairs: Vec<(&str, &str)> = sources.iter().map(|(path, source)| (path.as_str(), source.as_str())).collect();
    let program = match parse_sources(&pairs) {
        Ok(program) => program,
        Err(diags) => {
            let mut report = Report::empty();
            report.diagnostics = preface;
            report.diagnostics.extend(diags);
            report.files = owned_files(&sources);
            return report;
        }
    };
    let options = VerifyOptions {
        config,
        cache_dir: Some(cache_dir(root)),
        z3_path: None,
        timeout_ms: None,
    };
    let mut report = verify_program(&program, &options);
    preface.append(&mut report.diagnostics);
    report.diagnostics = preface;
    if mode == Mode::Build {
        if !report.ok() || report.tool_error {
            report.diagnostics.push(Diagnostic::new(
                ErrorCode::Verify015,
                "JavaScript was not emitted because verification did not succeed",
            ));
        } else if let Err(diag) = emit_with_tsrs(root) {
            report.diagnostics.push(diag);
        }
    }
    report
}

pub fn verify_program(program: &Program, options: &VerifyOptions) -> Report {
    let mut report = Report::empty();
    report.files = program.files.clone();
    report.diagnostics.extend(policy_diagnostics(&options.config));
    let registry = official_registry();
    for item in registry.contracts() {
        report.diagnostics.push(
            Diagnostic::new(
                ErrorCode::Verify014,
                format!("{}: {}", item.component, item.assumption),
            )
            .note("trusted adapter model; this is not a proof of the external system"),
        );
    }
    for (name, external) in &program.externals {
        let effect = match external {
            External::Function { effect, .. } => effect.clone(),
            External::Namespace { methods, .. } => {
                methods
                    .iter()
                    .map(|(method, effect)| format!("{method}={effect}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            }
        };
        report.diagnostics.push(
            Diagnostic::new(
                ErrorCode::Verify014,
                format!("external `{name}` assumes {effect}"),
            )
            .note("the remote service is not proved"),
        );
    }
    report.diagnostics.extend(unexpected_top_level(program));
    let layers = match registry.discover_all(program) {
        Ok(layers) => layers,
        Err(diags) => {
            report.diagnostics.extend(diags);
            Vec::new()
        }
    };
    let discovered = discovered_routes(&layers);
    let timeout = options.timeout_ms.unwrap_or(options.config.solver.timeout_ms);
    let z3_path = options.z3_path.as_deref().or(options.config.solver.path.as_deref());
    let z3 = match Z3::discover(z3_path, timeout) {
        Ok(z3) => Some(z3),
        Err(message) => {
            report.tool_error = true;
            report.diagnostics.push(Diagnostic::new(ErrorCode::Verify006, message));
            None
        }
    };
    let mut law_status = Vec::new();
    if let Some(z3) = &z3 {
        let cache = options.cache_dir.as_ref().map(|dir| Cache::open(dir));
        let versions = registry
            .metadata()
            .iter()
            .map(|meta| format!("{}@{}", meta.name, meta.version))
            .collect::<Vec<_>>()
            .join(",");
        let sources = program
            .files
            .iter()
            .map(|file| format!("{}\n{}", file.path, file.source))
            .collect::<Vec<_>>()
            .join("\n");
        let mut engine = Engine {
            z3,
            cache,
            versions,
            sources,
            report: &mut report,
        };
        engine.function_laws(program, &registry);
        engine.endpoint_laws(program, &registry, &layers, &mut law_status);
        let lemmas = check_lemmas(program, z3);
        report.proved.extend(lemmas.proved.iter().cloned());
        report.coverage.proved_obligations += lemmas.proved.len();
        report.coverage.failed_obligations += lemmas.diagnostics.iter().filter(|d| d.is_failure()).count();
        report.diagnostics.extend(lemmas.diagnostics);
    }
    let (mut coverage, coverage_diags) = assess(&discovered, &law_status, &options.config.required_endpoints);
    coverage.proved_obligations += report.coverage.proved_obligations;
    coverage.failed_obligations += report.coverage.failed_obligations;
    coverage.trusted_assumptions = report.diagnostics.iter().filter(|d| d.code == ErrorCode::Verify014).count();
    report.coverage = coverage;
    report.diagnostics.extend(coverage_diags);
    report.cached_hits = report.obligations.iter().filter(|item| item.cached).count();
    report
}

struct Engine<'a> {
    z3: &'a Z3,
    cache: Option<Cache>,
    versions: String,
    sources: String,
    report: &'a mut Report,
}

impl Engine<'_> {
    fn function_laws(&mut self, program: &Program, registry: &Registry) {
        let mut grouped: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
        for (index, law) in program.laws.iter().enumerate() {
            grouped.entry(law.target.as_str()).or_default().push(index);
        }
        for (target, indexes) in grouped {
            let Some(func) = program.function(target) else {
                self.report.diagnostics.push(
                    Diagnostic::new(
                        ErrorCode::Verify009,
                        format!("law target `{target}` is not a function"),
                    )
                    .at(program.laws[indexes[0]].span.clone()),
                );
                continue;
            };
            let base = match lower_function(program, registry, func) {
                Ok(base) => base,
                Err(diags) => {
                    self.report.diagnostics.extend(diags);
                    continue;
                }
            };
            let params: Vec<String> = func.params.iter().map(|p| p.name.clone()).collect();
            for index in indexes {
                let law = &program.laws[index];
                let requires = match optional_formula(law.requires.as_ref(), Some(target), &params) {
                    Ok(expr) => expr,
                    Err(diag) => {
                        self.report.diagnostics.push(diag);
                        continue;
                    }
                };
                let ensures = match optional_formula(law.ensures.as_ref(), Some(target), &params) {
                    Ok(expr) => expr,
                    Err(diag) => {
                        self.report.diagnostics.push(diag);
                        continue;
                    }
                };
                let mut func = with_contract(base.clone(), requires, ensures, law.span.clone());
                func.name = law.name.clone();
                let proved = self.solve_named(&func, &law.name);
                if proved {
                    self.report.proved.push(law.name.clone());
                }
            }
        }
    }

    fn endpoint_laws(
        &mut self,
        program: &Program,
        registry: &Registry,
        layers: &[Layer],
        status: &mut Vec<LawStatus>,
    ) {
        let mut grouped: BTreeMap<(String, String), Vec<usize>> = BTreeMap::new();
        for (index, law) in program.endpoint_laws.iter().enumerate() {
            grouped
                .entry((law.method.clone(), law.path.clone()))
                .or_default()
                .push(index);
        }
        for ((method, path), indexes) in grouped {
            let base = match lower_endpoint(program, registry, &method, &path, layers) {
                Ok(base) => base,
                Err(diags) => {
                    self.report.diagnostics.extend(diags);
                    for index in indexes {
                        let law = &program.endpoint_laws[index];
                        status.push(LawStatus {
                            method: method.clone(),
                            path: path.clone(),
                            name: law.name.clone(),
                            proved: false,
                        });
                    }
                    continue;
                }
            };
            for index in indexes {
                let law = &program.endpoint_laws[index];
                let requires = match optional_formula(law.requires.as_ref(), None, &[]) {
                    Ok(expr) => expr,
                    Err(diag) => {
                        self.report.diagnostics.push(diag);
                        status.push(LawStatus {
                            method: method.clone(),
                            path: path.clone(),
                            name: law.name.clone(),
                            proved: false,
                        });
                        continue;
                    }
                };
                let ensures = match lower_spec(&law.ensures, None, &[]) {
                    Ok(formula) => formula.expr,
                    Err(diag) => {
                        self.report.diagnostics.push(diag);
                        status.push(LawStatus {
                            method: method.clone(),
                            path: path.clone(),
                            name: law.name.clone(),
                            proved: false,
                        });
                        continue;
                    }
                };
                let mut func = with_contract(base.clone(), requires, ensures, law.span.clone());
                func.name = law.name.clone();
                let proved = self.solve_named(&func, &law.name);
                if proved {
                    self.report.proved.push(law.name.clone());
                }
                status.push(LawStatus {
                    method: method.clone(),
                    path: path.clone(),
                    name: law.name.clone(),
                    proved,
                });
            }
        }
    }

    fn solve_named(&mut self, func: &VirFunction, _label: &str) -> bool {
        let obligations = match generate(func) {
            Ok(obligations) => obligations,
            Err(diag) => {
                self.fail_obligation(func.name.clone(), diag);
                return false;
            }
        };
        let mut proved = true;
        for obligation in obligations {
            let record = self.solve_obligation(obligation);
            if !record.proved {
                proved = false;
            }
            if let Some(diag) = &record.diagnostic {
                self.report.diagnostics.push(diag.clone());
            }
            if record.proved {
                self.report.coverage.proved_obligations += 1;
            } else {
                self.report.coverage.failed_obligations += 1;
            }
            self.report.obligations.push(record);
        }
        proved
    }

    fn solve_obligation(&mut self, obligation: ts_proof_vc::Obligation) -> ObligationRecord {
        let query = match encode_validity(&obligation.formula, &obligation.sorts) {
            Ok(query) => query,
            Err(diag) => {
                let diag = if diag.span.is_none() {
                    diag.at(obligation.span.clone())
                } else {
                    diag
                };
                return failed(obligation.name, diag);
            }
        };
        let key = digest(&format!(
            "{VERIFIER_VERSION}\n{}\n{}\n{}\n{}\n{}\n{}",
            self.versions,
            self.z3.version,
            self.z3.timeout.as_millis(),
            self.sources,
            obligation.name,
            query.smt
        ));
        let lookup = self
            .cache
            .as_ref()
            .map(|cache| cache.lookup(&key))
            .unwrap_or(CacheLookup::Miss);
        match lookup {
            CacheLookup::Unsat => {
                return ObligationRecord {
                    name: obligation.name,
                    proved: true,
                    cached: true,
                    diagnostic: None,
                };
            }
            CacheLookup::Invalid => {
                if let Some(cache) = &self.cache {
                    let _ = cache.forget(&key);
                }
                self.report.diagnostics.push(
                    Diagnostic::new(
                        ErrorCode::Verify012,
                        format!(
                            "proof cache entry for `{}` is not an unsat result and was not trusted",
                            obligation.name
                        ),
                    )
                    .at(obligation.span.clone())
                    .note("the obligation was recomputed; this run still fails closed"),
                );
            }
            CacheLookup::Miss => {}
        }
        let name = obligation.name.clone();
        let span = obligation.span.clone();
        let solved = solve_obligation(obligation, self.z3);
        if solved.proved {
            if let Some(cache) = &self.cache {
                let _ = cache.store_unsat(&key);
            }
            ObligationRecord {
                name,
                proved: true,
                cached: false,
                diagnostic: None,
            }
        } else {
            let diag = solved.diagnostic.unwrap_or_else(|| {
                Diagnostic::new(ErrorCode::Verify001, format!("{name} failed")).at(span)
            });
            failed(name, diag)
        }
    }

    fn fail_obligation(&mut self, name: String, diag: Diagnostic) {
        self.report.coverage.failed_obligations += 1;
        self.report.diagnostics.push(diag.clone());
        self.report.obligations.push(failed(name, diag));
    }
}

fn failed(name: String, diag: Diagnostic) -> ObligationRecord {
    ObligationRecord {
        name,
        proved: false,
        cached: false,
        diagnostic: Some(diag),
    }
}

fn optional_formula(
    spec: Option<&ts_proof_core::SpecFn>,
    target: Option<&str>,
    params: &[String],
) -> Result<Expr, Diagnostic> {
    match spec {
        None => Ok(Expr::Bool(true)),
        Some(spec) => Ok(lower_spec(spec, target, params)?.expr),
    }
}

fn discovered_routes(layers: &[Layer]) -> Vec<(String, String)> {
    layers
        .iter()
        .filter_map(|layer| match &layer.kind {
            LayerKind::Route { method, path, .. } => Some((method.clone(), path.clone())),
            _ => None,
        })
        .collect()
}

fn unexpected_top_level(program: &Program) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for stmt in &program.top_level {
        let Stmt::Expr { expr, span } = stmt else {
            out.push(Diagnostic::new(
                ErrorCode::Verify003,
                "unsupported top-level statement",
            ));
            continue;
        };
        if !is_route_registration(expr) {
            out.push(
                Diagnostic::new(
                    ErrorCode::Verify003,
                    "a top-level call is not a supported static route registration",
                )
                .at(span.clone())
                .note("registrations are declarations; other top-level calls have no semantics here"),
            );
        }
    }
    out
}

fn is_route_registration(expr: &Ast) -> bool {
    let Ast::Call { callee, .. } = expr else {
        return false;
    };
    let Callee::Member { object, field } = callee else {
        return false;
    };
    let Ast::Ident(_) = object.as_ref() else {
        return false;
    };
    matches!(
        field.to_ascii_lowercase().as_str(),
        "get" | "post" | "put" | "delete" | "patch" | "use"
    )
}

fn policy_diagnostics(config: &ProjectConfig) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    if !config.verification.required {
        out.push(Diagnostic::new(
            ErrorCode::Verify002,
            "verification.required cannot be false; ts-proof does not emit an unverified success",
        ));
    }
    if config.verification.endpoints != "all" {
        out.push(Diagnostic::new(
            ErrorCode::Verify002,
            "verification.endpoints must be \"all\"; partial endpoint coverage is not a success",
        ));
    }
    for (name, value) in [
        ("unsupported", config.verification.unsupported.as_str()),
        ("uncoveredEffects", config.verification.uncovered_effects.as_str()),
        ("unknownProofs", config.verification.unknown_proofs.as_str()),
    ] {
        if value != "error" {
            out.push(Diagnostic::new(
                ErrorCode::Verify002,
                format!("verification.{name} must be \"error\""),
            ));
        }
    }
    out
}

fn read_sources(root: &Path) -> Result<Vec<(String, String)>, Diagnostic> {
    let mut files = Vec::new();
    walk(root, root, &mut files)?;
    files.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(files)
}

fn walk(root: &Path, dir: &Path, out: &mut Vec<(String, String)>) -> Result<(), Diagnostic> {
    let entries = fs::read_dir(dir).map_err(|err| {
        Diagnostic::new(
            ErrorCode::Verify002,
            format!("cannot read {}: {err}", dir.display()),
        )
    })?;
    for entry in entries {
        let entry = entry.map_err(|err| {
            Diagnostic::new(ErrorCode::Verify002, format!("cannot read {}: {err}", dir.display()))
        })?;
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if path.is_dir() {
            if name.starts_with('.') || matches!(name.as_ref(), "node_modules" | "dist" | "target") {
                continue;
            }
            walk(root, &path, out)?;
            continue;
        }
        if !name.ends_with(".ts") || name.ends_with(".d.ts") {
            continue;
        }
        let rel = path
            .strip_prefix(root)
            .unwrap_or(&path)
            .to_string_lossy()
            .replace('\\', "/");
        let source = fs::read_to_string(&path).map_err(|err| {
            Diagnostic::new(ErrorCode::Verify002, format!("cannot read {}: {err}", path.display()))
        })?;
        out.push((rel, source));
    }
    Ok(())
}

fn owned_files(sources: &[(String, String)]) -> Vec<SourceFile> {
    sources
        .iter()
        .map(|(path, source)| SourceFile {
            path: path.clone(),
            source: source.clone(),
        })
        .collect()
}

fn config_error(path: &Path, message: String) -> Diagnostic {
    Diagnostic::new(
        ErrorCode::Verify002,
        format!("cannot read {}: {message}", path.display()),
    )
}

fn join_or_none(items: &[String]) -> String {
    if items.is_empty() {
        "(none)".into()
    } else {
        items.join(", ")
    }
}

#[cfg(test)]
mod pipeline {
    use super::*;
    use ts_proof_tsrs_bridge::parse_source;

    fn verify(source: &str) -> Report {
        let program = parse_source("sample.ts", source).unwrap_or_else(|diags| {
            panic!("{}", render_text(&diags, &[]));
        });
        let options = VerifyOptions {
            timeout_ms: Some(20_000),
            ..VerifyOptions::default()
        };
        verify_program(&program, &options)
    }

    fn assert_proved(source: &str) {
        let report = verify(source);
        assert!(report.ok(), "{}", report.render_text());
    }

    fn assert_code(source: &str, code: ErrorCode) {
        let report = verify(source);
        assert!(
            report.diagnostics.iter().any(|diag| diag.code == code),
            "{}",
            report.render_text()
        );
        assert!(!report.ok());
    }

    #[test]
    fn expiry_and_guarded_issue_prove_and_the_reversals_fail() {
        assert_proved(EXPIRY);
        assert_code(EXPIRY_REVERSED, ErrorCode::Verify001);
        assert_proved(ISSUE);
        assert_code(ISSUE_UNGUARDED, ErrorCode::Verify001);
    }

    #[test]
    fn unauthorized_request_cannot_sign_or_persist() {
        let report = verify(IAM);
        assert!(report.ok(), "{}", report.render_text());
        for name in [
            "expiryLaw",
            "issueLaw",
            "unauthorized_no_sign",
            "unauthorized_no_write",
            "identity_integrity",
            "response_after_persistence",
            "positive_ttl_increases",
        ] {
            assert!(report.proved.iter().any(|item| item == name), "{name} missing\n{}", report.render_text());
        }
    }

    const EXPIRY: &str = r#"
        function calculateExpiry(now: bigint, ttl: bigint): bigint {
            return now + ttl;
        }
        const expiryLaw = law({
            target: calculateExpiry,
            inputs: { now: int(), ttl: int() },
            requires: ({ now, ttl }) => now.gte(0).and(ttl.gt(0)),
            ensures: ({ now, ttl }) => call(calculateExpiry, now, ttl).gt(now),
        });
    "#;

    const EXPIRY_REVERSED: &str = r#"
        function calculateExpiry(now: bigint, ttl: bigint): bigint {
            return now - ttl;
        }
        const expiryLaw = law({
            target: calculateExpiry,
            requires: ({ now, ttl }) => now.gte(0).and(ttl.gt(0)),
            ensures: ({ now, ttl }) => call(calculateExpiry, now, ttl).gt(now),
        });
    "#;

    const ISSUE: &str = r#"
        const kms = externalNamespace({ signToken: "kms.sign" });
        function issueToken(authorized: boolean): null {
            if (!authorized) {
                return null;
            }
            return kms.signToken();
        }
        const issueLaw = law({
            target: issueToken,
            ensures: ({ authorized }) => implies(!authorized, trace.count("kms.sign") === 0),
        });
    "#;

    const ISSUE_UNGUARDED: &str = r#"
        const kms = externalNamespace({ signToken: "kms.sign" });
        function issueToken(authorized: boolean): null {
            kms.signToken();
            if (!authorized) {
                return null;
            }
            return null;
        }
        const issueLaw = law({
            target: issueToken,
            ensures: ({ authorized }) => implies(!authorized, trace.count("kms.sign") === 0),
        });
    "#;

    const IAM: &str = r#"
        const kms = externalNamespace({ signToken: "kms.sign" });
        const app = express();
        const pool = new Pool({});
        function calculateExpiry(now: bigint, ttl: bigint): bigint {
            return now + ttl;
        }
        const expiryLaw = law({
            target: calculateExpiry,
            inputs: { now: int(), ttl: int() },
            requires: ({ now, ttl }) => now.gte(0).and(ttl.gt(0)),
            ensures: ({ now, ttl }) => call(calculateExpiry, now, ttl).gt(now),
        });
        const expiryProof = prove(expiryLaw, ({ now, ttl }) => {
            lemma("positive_ttl_increases", ttl.gt(0).implies(now.add(ttl).gt(now)));
        });
        function issueToken(authorized: boolean): null {
            if (!authorized) {
                return null;
            }
            return kms.signToken();
        }
        const issueLaw = law({
            target: issueToken,
            ensures: ({ authorized }) => implies(!authorized, trace.count("kms.sign") === 0),
        });
        function authenticate(req, res, next) {
            if (!req.authenticated) {
                res.status(401).json({ ok: false });
                return;
            }
            next();
        }
        function authorize(req, res, next) {
            if (!req.authorized) {
                res.status(403).json({ ok: false });
                return;
            }
            next();
        }
        function mintToken(req, res) {
            if (!req.authorized) {
                res.status(403).json({ ok: false });
                return;
            }
            const expiry = calculateExpiry(req.agentId, 60);
            kms.signToken();
            pool.query("INSERT INTO tokens(agent_id, principal, expiry) VALUES($1, $2, $3)", [req.agentId, req.principal, expiry]);
            res.status(201).json({ ok: true });
        }
        app.post("/agents/:id/tokens", authenticate, authorize, mintToken);
        const unauthorizedNoSign = endpointLaw({
            method: "POST",
            path: "/agents/:id/tokens",
            name: "unauthorized_no_sign",
            ensures: ({ request, trace }) => implies(!request.authorized, trace.count("kms.sign") === 0),
        });
        const unauthorizedNoWrite = endpointLaw({
            method: "POST",
            path: "/agents/:id/tokens",
            name: "unauthorized_no_write",
            ensures: ({ request, trace }) => implies(!request.authorized, trace.count("db.write.tokens") === 0),
        });
        const identity = endpointLaw({
            method: "POST",
            path: "/agents/:id/tokens",
            name: "identity_integrity",
            ensures: ({ request, response, db }) => implies(response.status === 201, db.committed.tokens > 0 && db.last.tokens.principal === request.principal),
        });
        const persisted = endpointLaw({
            method: "POST",
            path: "/agents/:id/tokens",
            name: "response_after_persistence",
            ensures: ({ response, db }) => implies(response.status === 201, db.committed.tokens > 0 && response.clock > db.seq.tokens),
        });
    "#;

    #[test]
    fn mutations_and_unsupported_forms_fail_closed() {
        assert_code(WRITE_BEFORE_AUTH, ErrorCode::Verify001);
        assert_code(RESPONSE_BEFORE_INSERT, ErrorCode::Verify001);
        assert_code(FORGOTTEN_NEXT, ErrorCode::Verify001);
        assert_code(BAD_LEMMA, ErrorCode::Verify008);
        assert_code(DYNAMIC_SQL, ErrorCode::Verify011);
        assert_code(DYNAMIC_ROUTE, ErrorCode::Verify011);
        assert_code(PRISMA_TRANSACTION, ErrorCode::Verify011);
        assert_code(FETCH_DYNAMIC_METHOD, ErrorCode::Verify011);
        assert_code(READ_CATCH, ErrorCode::Verify002);
        assert_parse("function f(x: bigint): bigint { return x == 1; }", ErrorCode::Verify002);
        assert_parse("function f(x: bigint): bigint { return x / 1n; }", ErrorCode::Verify002);
        assert_parse("function f(): bigint { return 1.5; }", ErrorCode::Verify002);
        assert_parse("function f() { eval(\"1\"); }", ErrorCode::Verify002);
        assert_parse("function f(x: bigint): bigint { return x }", ErrorCode::Verify002);
    }

    #[test]
    fn nest_prisma_fetch_and_typeorm_subsets_prove() {
        assert_proved(NEST);
        assert_proved(PRISMA);
        assert_proved(FETCH_ALLOW);
        assert_proved(TYPEORM);
    }

    #[test]
    fn corrupt_cache_fails_even_when_the_obligation_is_valid() {
        let dir = std::env::temp_dir().join(format!(
            "ts-proof-cache-e2e-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        let _ = std::fs::remove_dir_all(&dir);
        let program = parse_source("sample.ts", EXPIRY).expect("parse");
        let options = VerifyOptions {
            timeout_ms: Some(20_000),
            cache_dir: Some(dir.clone()),
            ..VerifyOptions::default()
        };
        let first = verify_program(&program, &options);
        assert!(first.ok(), "{}", first.render_text());
        assert_eq!(first.cached_hits, 0);
        let second = verify_program(&program, &options);
        assert!(second.ok(), "{}", second.render_text());
        assert!(second.cached_hits > 0, "{}", second.render_text());
        let mut corrupted = 0;
        for entry in std::fs::read_dir(&dir).expect("cache dir") {
            let path = entry.expect("entry").path();
            if path.is_file() {
                std::fs::write(&path, b"sat\n").expect("corrupt");
                corrupted += 1;
            }
        }
        assert!(corrupted > 0);
        let third = verify_program(&program, &options);
        assert!(
            third.diagnostics.iter().any(|diag| diag.code == ErrorCode::Verify012),
            "{}",
            third.render_text()
        );
        assert!(!third.ok());
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn example_projects_prove_without_invoking_tsrs() {
        let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples");
        let projects: &[(&str, &[&str])] = &[
            ("arithmetic", &["expiryLaw", "positive_ttl_increases"]),
            ("express-basic", &["unauthenticated_is_401"]),
            ("express-postgres", &["unauthorized_no_write"]),
            ("outbound-http", &["unauthorized_no_fetch", "completed_fetch_stays_on_allowlist"]),
            ("iam-token-issuer", &[
                "expiryLaw",
                "unauthorized_no_sign",
                "unauthorized_no_write",
                "identity_integrity",
                "response_after_persistence",
                "positive_ttl_increases",
            ]),
            ("nest-guard", &["nest_unauthorized_no_sign"]),
            ("prisma-create", &["committed_row_keeps_principal"]),
            ("typeorm-insert", &["committed_row_keeps_principal"]),
        ];
        for (dir, laws) in projects {
            let report = check_project(&root.join(dir), Mode::Check);
            assert!(report.ok(), "{dir}\n{}", report.render_text());
            assert_eq!(report.exit_code(), 0, "{dir}");
            assert!(
                report.diagnostics.iter().any(|diag| diag.code == ErrorCode::Verify014),
                "{dir} hid the compiler bypass"
            );
            for law in *laws {
                assert!(
                    report.proved.iter().any(|item| item == law),
                    "{dir} missing {law}\n{}",
                    report.render_text()
                );
            }
        }
    }

    #[test]
    fn missing_tsrs_blocks_a_compiler_required_check() {
        let dir = std::env::temp_dir().join(format!("ts-proof-notsrs-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("expiry.ts"), EXPIRY).unwrap();
        let previous = std::env::var_os("TSRS_PATH");
        std::env::set_var("TSRS_PATH", "/no/such/ts-proof-tsrs");
        let report = check_project(&dir, Mode::Check);
        match previous {
            Some(value) => std::env::set_var("TSRS_PATH", value),
            None => std::env::remove_var("TSRS_PATH"),
        }
        let _ = std::fs::remove_dir_all(&dir);
        assert!(
            report.diagnostics.iter().any(|diag| diag.code == ErrorCode::Verify013),
            "{}",
            report.render_text()
        );
        assert!(!report.ok());
        assert_eq!(report.exit_code(), 1);
        assert!(report.proved.is_empty());
    }

    fn assert_parse(source: &str, code: ErrorCode) {
        let diags = parse_source("sample.ts", source).expect_err("parser accepted unsupported syntax");
        assert!(diags.iter().any(|diag| diag.code == code), "{diags:?}");
    }

    const WRITE_BEFORE_AUTH: &str = r#"
        const app = express();
        const pool = new Pool({});
        function mint(req, res) {
            pool.query("INSERT INTO tokens(agent_id) VALUES($1)", [req.agentId]);
            if (!req.authorized) {
                res.status(403).json({ ok: false });
                return;
            }
            res.status(201).json({ ok: true });
        }
        app.post("/tokens", mint);
        const unauthorizedNoWrite = endpointLaw({
            method: "POST",
            path: "/tokens",
            name: "unauthorized_no_write",
            ensures: ({ request, trace }) => implies(!request.authorized, trace.count("db.write.tokens") === 0),
        });
    "#;

    const RESPONSE_BEFORE_INSERT: &str = r#"
        const app = express();
        const pool = new Pool({});
        function mint(req, res) {
            res.status(201).json({ ok: true });
            pool.query("INSERT INTO tokens(agent_id, principal) VALUES($1, $2)", [req.agentId, req.principal]);
        }
        app.post("/tokens", mint);
        const persisted = endpointLaw({
            method: "POST",
            path: "/tokens",
            name: "response_after_persistence",
            ensures: ({ response, db }) => implies(response.status === 201, db.committed.tokens > 0 && response.clock > db.seq.tokens),
        });
    "#;

    const FORGOTTEN_NEXT: &str = r#"
        const kms = externalNamespace({ signToken: "kms.sign" });
        const app = express();
        function authorize(req, res, next) {
            if (!req.authorized) {
                res.status(403).json({ ok: false });
                return;
            }
        }
        function mint(req, res) {
            kms.signToken();
            res.status(201).json({ ok: true });
        }
        app.post("/tokens", authorize, mint);
        const authorizedSigns = endpointLaw({
            method: "POST",
            path: "/tokens",
            name: "authorized_signs",
            ensures: ({ request, trace }) => implies(request.authorized, trace.count("kms.sign") > 0),
        });
    "#;

    const BAD_LEMMA: &str = r#"
        function calculateExpiry(now: bigint, ttl: bigint): bigint {
            return now + ttl;
        }
        const expiryLaw = law({
            target: calculateExpiry,
            requires: ({ now, ttl }) => ttl.gt(0),
            ensures: ({ now, ttl }) => call(calculateExpiry, now, ttl).gt(now),
        });
        const expiryProof = prove(expiryLaw, ({ now, ttl }) => {
            lemma("bad", ttl.lt(0));
        });
    "#;

    const DYNAMIC_SQL: &str = r#"
        const pool = new Pool({});
        function write(sql: string, agentId: bigint): null {
            pool.query(sql, [agentId]);
            return null;
        }
        const writeLaw = law({
            target: write,
            ensures: ({ sql, agentId }) => agentId.eq(agentId),
        });
    "#;

    const DYNAMIC_ROUTE: &str = r#"
        const app = express();
        const path = "/tokens";
        function mint(req, res) {
            res.status(201).json({ ok: true });
        }
        app.post(path, mint);
    "#;

    const PRISMA_TRANSACTION: &str = r#"
        function save(agentId: bigint): null {
            prisma.token.$transaction([agentId]);
            return null;
        }
        const saveLaw = law({
            target: save,
            ensures: ({ agentId }) => agentId.eq(agentId),
        });
    "#;

    const FETCH_DYNAMIC_METHOD: &str = r#"
        function notify(method: string): null {
            fetch("https://kms.example/sign", { method: method });
            return null;
        }
        const notifyLaw = law({
            target: notify,
            ensures: ({ method }) => method.eq(method),
        });
    "#;

    const READ_CATCH: &str = r#"
        function f(x: bigint): bigint {
            try {
                throw 1;
            } catch (err) {
                return err;
            }
        }
        const fLaw = law({
            target: f,
            ensures: ({ x }) => x.eq(x),
        });
    "#;

    const NEST: &str = r#"
        const kms = externalNamespace({ signToken: "kms.sign" });
        function allow(req): boolean {
            return req.authorized;
        }
        @Controller("/agents")
        class Tokens {
            @UseGuards(allow)
            @Post("/tokens")
            mint(req, res) {
                kms.signToken();
                res.status(201).json({ ok: true });
            }
        }
        const nestLaw = endpointLaw({
            method: "POST",
            path: "/agents/tokens",
            name: "nest_unauthorized_no_sign",
            ensures: ({ request, trace }) => implies(!request.authorized, trace.count("kms.sign") === 0),
        });
    "#;

    const PRISMA: &str = r#"
        function save(agentId: bigint, principal: bigint): null {
            prisma.token.create({ data: { agentId: agentId, principal: principal } });
            return null;
        }
        const saveLaw = law({
            target: save,
            name: "committed_row_keeps_principal",
            ensures: ({ principal }) => implies(db.committed.token > 0, db.last.token.principal === principal),
        });
    "#;

    const FETCH_ALLOW: &str = r#"
        function notify(authorized: boolean): null {
            if (!authorized) {
                return null;
            }
            fetch("https://kms.example/sign", { method: "POST" });
            return null;
        }
        const noFetch = law({
            target: notify,
            name: "unauthorized_no_fetch",
            ensures: ({ authorized }) => implies(!authorized, trace.count("http.fetch") === 0),
        });
        const allowlist = law({
            target: notify,
            name: "completed_fetch_stays_on_allowlist",
            ensures: () => implies(trace.count("http.fetch.ok") > 0, http.last_url === "https://kms.example/sign"),
        });
    "#;

    const TYPEORM: &str = r#"
        function save(agentId: bigint, principal: bigint): null {
            tokenRepository.insert({ agentId: agentId, principal: principal });
            return null;
        }
        const saveLaw = law({
            target: save,
            name: "committed_row_keeps_principal",
            ensures: ({ principal }) => implies(db.committed.tokenRepository > 0, db.last.tokenRepository.principal === principal),
        });
    "#;
}
