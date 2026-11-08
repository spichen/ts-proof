//! Endpoint coverage. A discovered route is not a verified route.
//!
//! This report does not collapse those states into a percentage.

use serde::{Deserialize, Serialize};
use ts_proof_core::{Diagnostic, ErrorCode, RequiredEndpoint};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoverageReport {
    pub discovered_endpoints: Vec<String>,
    pub verified_endpoints: Vec<String>,
    pub unverified_endpoints: Vec<String>,
    pub proved_obligations: usize,
    pub failed_obligations: usize,
    pub trusted_assumptions: usize,
}

impl CoverageReport {
    pub fn empty() -> Self {
        Self {
            discovered_endpoints: Vec::new(),
            verified_endpoints: Vec::new(),
            unverified_endpoints: Vec::new(),
            proved_obligations: 0,
            failed_obligations: 0,
            trusted_assumptions: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub struct LawStatus {
    pub method: String,
    pub path: String,
    pub name: String,
    pub proved: bool,
}

/// `discovered` is `METHOD path` pairs from adapters.
/// `laws` are endpoint laws that were actually checked.
pub fn assess(
    discovered: &[(String, String)],
    laws: &[LawStatus],
    required: &[RequiredEndpoint],
) -> (CoverageReport, Vec<Diagnostic>) {
    let mut report = CoverageReport::empty();
    let mut diags = Vec::new();
    let mut keys: Vec<(String, String)> = discovered.to_vec();
    keys.sort();
    keys.dedup();
    for (method, path) in &keys {
        let label = format!("{method} {path}");
        report.discovered_endpoints.push(label.clone());
        let matching: Vec<&LawStatus> = laws
            .iter()
            .filter(|law| law.method == *method && law.path == *path)
            .collect();
        if matching.is_empty() {
            report.unverified_endpoints.push(label.clone());
            diags.push(Diagnostic::new(
                ErrorCode::Verify010,
                format!("{label} has no endpoint law, and verification.endpoints is \"all\""),
            ));
            continue;
        }
        if matching.iter().all(|law| law.proved) {
            report.verified_endpoints.push(label);
        } else {
            report.unverified_endpoints.push(label);
        }
    }
    for item in required {
        let method = item.method.to_ascii_uppercase();
        let found = keys.iter().any(|(m, p)| m == &method && p == &item.path);
        if !found {
            diags.push(Diagnostic::new(
                ErrorCode::Verify010,
                format!("required endpoint {method} {} was not discovered", item.path),
            ));
            continue;
        }
        for name in &item.laws {
            let present = laws.iter().any(|law| {
                law.method == method && law.path == item.path && law.name == *name
            });
            if !present {
                diags.push(
                    Diagnostic::new(
                        ErrorCode::Verify010,
                        format!("required law `{name}` is missing from {method} {}", item.path),
                    )
                    .note("a required-endpoint manifest names laws that must stay in the program"),
                );
            }
        }
    }
    (report, diags)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_discovered_route_without_a_law_is_not_verified() {
        let (report, diags) = assess(&[("POST".into(), "/tokens".into())], &[], &[]);
        assert_eq!(report.verified_endpoints.len(), 0);
        assert_eq!(report.unverified_endpoints, vec!["POST /tokens".to_string()]);
        assert_eq!(diags[0].code, ErrorCode::Verify010);
    }
}
