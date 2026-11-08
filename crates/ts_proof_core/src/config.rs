use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RequiredEndpoint {
    pub method: String,
    pub path: String,
    pub laws: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct VerificationConfig {
    #[serde(default = "yes")]
    pub required: bool,
    /// `"all"` requires every discovered endpoint to have at least one endpoint law.
    #[serde(default = "all_endpoints")]
    pub endpoints: String,
    #[serde(default = "error_policy")]
    pub unsupported: String,
    #[serde(default = "error_policy")]
    pub uncovered_effects: String,
    #[serde(default = "error_policy")]
    pub unknown_proofs: String,
    #[serde(default = "yes")]
    pub compiler_required: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SolverConfig {
    #[serde(default)]
    pub path: Option<String>,
    #[serde(default = "default_timeout")]
    pub timeout_ms: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectConfig {
    #[serde(default)]
    pub verification: VerificationConfig,
    #[serde(default)]
    pub solver: SolverConfig,
    #[serde(default)]
    pub required_endpoints: Vec<RequiredEndpoint>,
}

fn yes() -> bool {
    true
}
fn all_endpoints() -> String {
    "all".to_string()
}
fn error_policy() -> String {
    "error".to_string()
}
fn default_timeout() -> u64 {
    10_000
}

impl Default for VerificationConfig {
    fn default() -> Self {
        Self {
            required: true,
            endpoints: all_endpoints(),
            unsupported: error_policy(),
            uncovered_effects: error_policy(),
            unknown_proofs: error_policy(),
            compiler_required: true,
        }
    }
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            path: None,
            timeout_ms: default_timeout(),
        }
    }
}

impl Default for ProjectConfig {
    fn default() -> Self {
        Self {
            verification: VerificationConfig::default(),
            solver: SolverConfig::default(),
            required_endpoints: Vec::new(),
        }
    }
}

impl ProjectConfig {
    pub fn endpoints_require_all(&self) -> bool {
        self.verification.endpoints == "all"
    }

    pub fn policy_is_error(&self, value: &str) -> bool {
        value == "error"
    }
}

/// File the CLI reads from a project root. Missing file means [`ProjectConfig::default`].
pub const CONFIG_FILE: &str = "ts-proof.config.json";
pub const REQUIRED_FILE: &str = "ts-proof.required.json";
