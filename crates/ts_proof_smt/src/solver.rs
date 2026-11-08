use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;
use ts_proof_vir::{Value, VirType};

use crate::model::values_from_model;
use crate::Query;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolverOutcome {
    Unsat,
    Sat(BTreeMap<String, Value>),
    Unknown,
    Timeout,
    Error(String),
}

pub struct Z3 {
    pub path: PathBuf,
    pub timeout: Duration,
    pub version: String,
}

impl Z3 {
    pub fn discover(explicit: Option<&str>, timeout_ms: u64) -> Result<Self, String> {
        let path = if let Some(explicit) = explicit {
            PathBuf::from(explicit)
        } else if let Some(found) = find_z3() {
            found
        } else {
            return Err(
                "z3 was not found on PATH, in Z3_PATH, or under Homebrew. Install Z3 and retry."
                    .into(),
            );
        };
        if !path.exists() {
            return Err(format!("z3 path does not exist: {}", path.display()));
        }
        let version = z3_version(&path).unwrap_or_else(|| "unknown".into());
        Ok(Self {
            path,
            timeout: Duration::from_millis(timeout_ms),
            version,
        })
    }

    pub fn check(&self, query: &Query) -> SolverOutcome {
        let mut cmd = Command::new(&self.path);
        cmd.arg(format!("-t:{}", self.timeout.as_millis()))
            .arg("-in")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        let mut child = match cmd.spawn() {
            Ok(child) => child,
            Err(err) => return SolverOutcome::Error(format!("failed to spawn z3: {err}")),
        };
        if let Some(mut stdin) = child.stdin.take() {
            use std::io::Write;
            if let Err(err) = stdin.write_all(query.smt.as_bytes()) {
                return SolverOutcome::Error(format!("failed to write SMT-LIB to z3: {err}"));
            }
        }
        let output = match child.wait_with_output() {
            Ok(output) => output,
            Err(err) => return SolverOutcome::Error(format!("failed to wait for z3: {err}")),
        };
        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();
        interpret(&stdout, &stderr, &query.sorts)
    }
}

fn interpret(stdout: &str, stderr: &str, sorts: &BTreeMap<String, VirType>) -> SolverOutcome {
    let text = stdout.trim();
    if text.is_empty() && !stderr.trim().is_empty() {
        if stderr.to_ascii_lowercase().contains("timeout") || stderr.contains("canceled") {
            return SolverOutcome::Timeout;
        }
        return SolverOutcome::Error(stderr.trim().to_string());
    }
    let first = text.lines().next().unwrap_or("").trim();
    if first == "unsat" {
        return SolverOutcome::Unsat;
    }
    if first == "unknown" {
        if stderr.to_ascii_lowercase().contains("timeout") || text.contains("timeout") {
            return SolverOutcome::Timeout;
        }
        return SolverOutcome::Unknown;
    }
    if first == "sat" {
        return match values_from_model(text, sorts) {
            Ok(model) => SolverOutcome::Sat(model),
            Err(err) => SolverOutcome::Error(format!("sat result but model parse failed: {err}\n{text}")),
        };
    }
    if stderr.to_ascii_lowercase().contains("timeout") {
        return SolverOutcome::Timeout;
    }
    let mut detail = text.to_string();
    if !stderr.trim().is_empty() {
        detail.push('\n');
        detail.push_str(stderr.trim());
    }
    SolverOutcome::Error(if detail.is_empty() {
        "z3 produced no output".into()
    } else {
        detail
    })
}

pub fn find_z3() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("Z3_PATH") {
        return Some(PathBuf::from(path));
    }
    if let Some(path) = which("z3") {
        return Some(path);
    }
    for candidate in [
        "/opt/homebrew/bin/z3",
        "/usr/local/bin/z3",
        "/opt/homebrew/opt/z3/bin/z3",
    ] {
        let path = PathBuf::from(candidate);
        if path.exists() {
            return Some(path);
        }
    }
    None
}

pub fn z3_version(path: &Path) -> Option<String> {
    let output = Command::new(path).arg("--version").output().ok()?;
    let text = String::from_utf8_lossy(&output.stdout).to_string();
    let line = text.lines().next().unwrap_or("").trim().to_string();
    if line.is_empty() { None } else { Some(line) }
}

fn which(bin: &str) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    for dir in std::env::split_paths(&path) {
        let candidate = dir.join(bin);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}
