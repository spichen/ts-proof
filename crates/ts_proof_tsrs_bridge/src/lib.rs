//! Compiler bridge.
//!
//! `tsrs` 0.23.0 requires Rust 1.99, so this crate does not depend on `tsrs`
//! as a Rust library. When the `tsrs` binary is on `PATH`, verified builds run
//! it as the typechecker. Programs are then parsed into an owned,
//! compiler-neutral snapshot. The parser accepts only the supported subset.
//!
//! `TS_PROOF_SKIP_TSRS=1` skips that typecheck and is reported as a trusted
//! assumption. It is not a successful typecheck.

mod lex;
mod parse;

use std::path::{Path, PathBuf};
use std::process::Command;
use ts_proof_core::{
    Diagnostic, ErrorCode, Program, TSRS_PIN_COMMIT, TSRS_PIN_VERSION, TSRS_TYPESCRIPT_VERSION,
};

pub use parse::{parse_source, parse_sources};

/// Run the pinned `tsrs` CLI in `dir` when compiler checking is required.
///
/// Returns informational [`ErrorCode::Verify014`] records for an explicit
/// bypass. Those are not failures. A missing compiler or a non-zero `tsrs`
/// status is [`ErrorCode::Verify013`].
pub fn typecheck(dir: &Path, compiler_required: bool) -> Vec<Diagnostic> {
    if !compiler_required {
        return vec![bypass(format!(
            "verification.compilerRequired is false, so tsrs {TSRS_PIN_VERSION} ({TSRS_PIN_COMMIT}, TypeScript {TSRS_TYPESCRIPT_VERSION}) was not invoked. This is a trusted assumption, not a proof that the program typechecks."
        ))];
    }
    if std::env::var("TS_PROOF_SKIP_TSRS").ok().as_deref() == Some("1") {
        return vec![bypass(format!(
            "TS_PROOF_SKIP_TSRS=1 skipped the tsrs {TSRS_PIN_VERSION} ({TSRS_PIN_COMMIT}, TypeScript {TSRS_TYPESCRIPT_VERSION}) typecheck. This is a trusted assumption, not a proof that the program typechecks."
        ))];
    }
    let Some(bin) = find_tsrs() else {
        return vec![Diagnostic::new(
            ErrorCode::Verify013,
            format!(
                "tsrs {TSRS_PIN_VERSION} ({TSRS_PIN_COMMIT}) was not found on PATH. Install that revision, or set TS_PROOF_SKIP_TSRS=1 to record an explicit bypass."
            ),
        )];
    };
    let output = Command::new(&bin)
        .arg("--version")
        .output();
    let version = match output {
        Ok(output) => String::from_utf8_lossy(&output.stdout).trim().to_string(),
        Err(err) => {
            return vec![Diagnostic::new(
                ErrorCode::Verify013,
                format!("failed to execute {}: {err}", bin.display()),
            )];
        }
    };
    if !version.contains(TSRS_PIN_VERSION) && !version.is_empty() {
        // A different installed compiler is still a typechecker. Record the
        // mismatch as a trusted assumption and continue; do not pretend the
        // pin was what ran.
        let note = bypass(format!(
            "tsrs on PATH reports `{version}`, while this verifier is pinned to {TSRS_PIN_VERSION} ({TSRS_PIN_COMMIT})."
        ));
        let mut diags = vec![note];
        diags.extend(run_tsrs(&bin, dir));
        return diags;
    }
    run_tsrs(&bin, dir)
}

fn run_tsrs(bin: &Path, dir: &Path) -> Vec<Diagnostic> {
    // `--noEmit` typechecks without writing JavaScript. Emission is a separate
    // step that runs only after required proofs succeed.
    let output = Command::new(bin)
        .arg("-p")
        .arg(dir)
        .arg("--noEmit")
        .output();
    match output {
        Ok(output) if output.status.success() => Vec::new(),
        Ok(output) => {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            let mut detail = stderr.trim().to_string();
            if detail.is_empty() {
                detail = stdout.trim().to_string();
            }
            vec![Diagnostic::new(
                ErrorCode::Verify013,
                format!("tsrs typecheck failed: {detail}"),
            )]
        }
        Err(err) => vec![Diagnostic::new(
            ErrorCode::Verify013,
            format!("failed to execute tsrs: {err}"),
        )],
    }
}

/// Invoke `tsrs` to emit JavaScript. Used only after required proofs succeed.
pub fn emit_with_tsrs(dir: &Path) -> Result<(), Diagnostic> {
    let Some(bin) = find_tsrs() else {
        return Err(Diagnostic::new(
            ErrorCode::Verify015,
            "verified build did not emit JavaScript because tsrs is not on PATH",
        ));
    };
    let output = Command::new(bin)
        .arg("-p")
        .arg(dir)
        .output()
        .map_err(|err| {
        Diagnostic::new(ErrorCode::Verify015, format!("tsrs emission failed to start: {err}"))
    })?;
    if output.status.success() {
        Ok(())
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr);
        Err(Diagnostic::new(
            ErrorCode::Verify015,
            format!("tsrs emission failed: {}", stderr.trim()),
        ))
    }
}

pub fn find_tsrs() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("TSRS_PATH") {
        return Some(PathBuf::from(path));
    }
    which("tsrs")
}

fn which(name: &str) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    for dir in std::env::split_paths(&path) {
        let candidate = dir.join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

fn bypass(message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(ErrorCode::Verify014, message.into()).note(
        "trusted assumptions are printed in the verification report and are not proofs",
    )
}

/// Parse already-read sources. This does not run `tsrs`.
pub fn parse_only(files: &[(&str, &str)]) -> Result<Program, Vec<Diagnostic>> {
    parse_sources(files)
}
