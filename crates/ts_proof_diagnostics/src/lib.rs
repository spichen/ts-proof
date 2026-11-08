//! Source-level diagnostics in text, JSON, SARIF, and JUnit.

use ts_proof_core::{Diagnostic, ErrorCode, SourceFile, VERIFIER_VERSION};

pub fn render_text(diagnostics: &[Diagnostic], files: &[SourceFile]) -> String {
    let mut out = String::new();
    let mut failures = diagnostics.iter().filter(|d| d.is_failure());
    let mut notes = diagnostics.iter().filter(|d| !d.is_failure());
    for diag in failures.by_ref() {
        push_diag(&mut out, diag, files);
    }
    for diag in notes.by_ref() {
        push_diag(&mut out, diag, files);
    }
    out
}

fn push_diag(out: &mut String, diag: &Diagnostic, files: &[SourceFile]) {
    let kind = if diag.is_failure() { "error" } else { "note" };
    out.push_str(&format!("{kind}[{}]: {}\n", diag.code, diag.message));
    if let Some(span) = &diag.span {
        if let Some(file) = files.iter().find(|file| file.path == span.file.as_ref()) {
            let (line, col) = file.line_col(span.start);
            out.push_str(&format!("  --> {}:{}:{}\n", file.path, line, col));
            let text = file.line_text(line);
            if !text.is_empty() {
                out.push_str(&format!("{line:>4} | {text}\n"));
            }
        } else if span.file.as_ref() != "<synthetic>" {
            out.push_str(&format!("  --> {}:{}\n", span.file, span.start));
        }
    }
    if let Some(expected) = &diag.expected {
        out.push_str(&format!("  expected: {expected}\n"));
    }
    if let Some(model) = &diag.counterexample {
        out.push_str("  counterexample:\n");
        for assignment in &model.assignments {
            out.push_str(&format!("    {} = {}\n", assignment.name, assignment.value));
        }
        out.push_str("  = this is a counterexample to the encoded model\n");
    }
    for note in &diag.notes {
        out.push_str(&format!("  = note: {note}\n"));
    }
    out.push('\n');
}

pub fn render_sarif(diagnostics: &[Diagnostic], files: &[SourceFile]) -> String {
    let mut rules = Vec::new();
    for code in ErrorCode::all() {
        rules.push(serde_json::json!({
            "id": code.as_str(),
            "shortDescription": { "text": code.title() },
            "fullDescription": { "text": code.explain() },
        }));
    }
    let mut results = Vec::new();
    for diag in diagnostics {
        let level = if diag.is_failure() { "error" } else { "note" };
        let mut result = serde_json::json!({
            "ruleId": diag.code.as_str(),
            "level": level,
            "message": { "text": diag.message },
        });
        if let Some(span) = &diag.span {
            if let Some(file) = files.iter().find(|file| file.path == span.file.as_ref()) {
                let (line, col) = file.line_col(span.start);
                result["locations"] = serde_json::json!([{
                    "physicalLocation": {
                        "artifactLocation": { "uri": file.path },
                        "region": { "startLine": line, "startColumn": col }
                    }
                }]);
            }
        }
        results.push(result);
    }
    let doc = serde_json::json!({
        "version": "2.1.0",
        "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
        "runs": [{
            "tool": {
                "driver": {
                    "name": "ts-proof",
                    "version": VERIFIER_VERSION,
                    "rules": rules,
                }
            },
            "results": results,
        }]
    });
    serde_json::to_string_pretty(&doc).unwrap_or_else(|_| "{}".into())
}

pub fn render_junit(diagnostics: &[Diagnostic]) -> String {
    let failures: Vec<&Diagnostic> = diagnostics.iter().filter(|d| d.is_failure()).collect();
    let mut out = String::new();
    out.push_str(&format!(
        "<testsuite name=\"ts-proof\" tests=\"{}\" failures=\"{}\">\n",
        diagnostics.len().max(1),
        failures.len()
    ));
    if diagnostics.is_empty() {
        out.push_str("  <testcase name=\"verification\"/>\n");
    }
    for diag in diagnostics {
        let name = xml_escape(&format!("{} {}", diag.code, diag.message));
        if diag.is_failure() {
            out.push_str(&format!(
                "  <testcase name=\"{name}\"><failure message=\"{name}\">{}</failure></testcase>\n",
                xml_escape(&diag.message)
            ));
        } else {
            out.push_str(&format!(
                "  <testcase name=\"{name}\"><system-out>{}</system-out></testcase>\n",
                xml_escape(&diag.message)
            ));
        }
    }
    out.push_str("</testsuite>\n");
    out
}

fn xml_escape(text: &str) -> String {
    text.chars()
        .map(|c| match c {
            '&' => "&amp;".into(),
            '<' => "&lt;".into(),
            '>' => "&gt;".into(),
            '"' => "&quot;".into(),
            _ => c.to_string(),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ts_proof_core::Span;

    #[test]
    fn text_puts_failures_before_trusted_notes() {
        let note = Diagnostic::new(ErrorCode::Verify014, "trusted model");
        let err = Diagnostic::new(ErrorCode::Verify001, "failed").at(Span::dummy());
        let text = render_text(&[note, err], &[]);
        let error_at = text.find("error[VERIFY001]").unwrap();
        let note_at = text.find("note[VERIFY014]").unwrap();
        assert!(error_at < note_at);
    }
}
