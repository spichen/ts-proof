//! Lemma checking.
//!
//! A lemma is an obligation of its own. It is entailed by the law precondition
//! and by lemmas that have already been proved. It is not added to the
//! implementation's assumptions. A failed lemma is [`ErrorCode::Verify008`].
//! A cycle or a missing law is [`ErrorCode::Verify009`].

use std::collections::{BTreeMap, BTreeSet};
use ts_proof_core::{Diagnostic, ErrorCode, Function, Program, SpecFn, TsType};
use ts_proof_effects::{endpoint_request_params, ghosts_for};
use ts_proof_smt::Z3;
use ts_proof_spec::lower_expr;
use ts_proof_vc::verify_function;
use ts_proof_vir::{Expr, FunctionKind, VirFunction, VirParam, VirType};

#[derive(Clone, Debug)]
pub struct LemmaReport {
    pub diagnostics: Vec<Diagnostic>,
    pub proved: Vec<String>,
}

pub fn check_lemmas(program: &Program, z3: &Z3) -> LemmaReport {
    let mut report = LemmaReport {
        diagnostics: Vec::new(),
        proved: Vec::new(),
    };
    for proof in &program.proofs {
        check_proof(program, proof, z3, &mut report);
    }
    report
}

fn check_proof(
    program: &Program,
    proof: &ts_proof_core::Proof,
    z3: &Z3,
    report: &mut LemmaReport,
) {
    if proof.lemmas.is_empty() {
        report.diagnostics.push(
            Diagnostic::new(ErrorCode::Verify009, format!("proof `{}` has no lemmas", proof.name))
                .at(proof.span.clone()),
        );
        return;
    }
    let function_law = program.laws.iter().find(|law| law.name == proof.law);
    let endpoint_law = program.endpoint_laws.iter().find(|law| law.name == proof.law);
    let (requires, params, target) = match (function_law, endpoint_law) {
        (None, None) => {
            report.diagnostics.push(
                Diagnostic::new(
                    ErrorCode::Verify009,
                    format!("proof `{}` names missing law `{}`", proof.name, proof.law),
                )
                .at(proof.span.clone()),
            );
            return;
        }
        (Some(_), Some(_)) => {
            report.diagnostics.push(
                Diagnostic::new(
                    ErrorCode::Verify009,
                    format!("`{}` is both a function law and an endpoint law", proof.law),
                )
                .at(proof.span.clone()),
            );
            return;
        }
        (Some(law), None) => {
            let Some(func) = program.function(&law.target) else {
                report.diagnostics.push(
                    Diagnostic::new(
                        ErrorCode::Verify009,
                        format!("law `{}` names missing target `{}`", law.name, law.target),
                    )
                    .at(law.span.clone()),
                );
                return;
            };
            let params = match vir_params(func) {
                Ok(params) => params,
                Err(diag) => {
                    report.diagnostics.push(diag);
                    return;
                }
            };
            let names: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
            let requires = match lower_optional(law.requires.as_ref(), Some(&law.target), &names) {
                Ok(expr) => expr,
                Err(diag) => {
                    report.diagnostics.push(diag);
                    return;
                }
            };
            (requires, params, Some(law.target.clone()))
        }
        (None, Some(law)) => {
            let params = endpoint_request_params();
            let names: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
            let requires = match lower_optional(law.requires.as_ref(), None, &names) {
                Ok(expr) => expr,
                Err(diag) => {
                    report.diagnostics.push(diag);
                    return;
                }
            };
            (requires, params, None)
        }
    };
    let order = match dependency_order(&proof.lemmas) {
        Ok(order) => order,
        Err(diag) => {
            report.diagnostics.push(diag.at(proof.span.clone()));
            return;
        }
    };
    let names: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
    let explicit = proof.lemmas.iter().any(|lemma| !lemma.depends_on.is_empty());
    let mut proved_by_index: BTreeMap<usize, Expr> = BTreeMap::new();
    let mut sequential: Vec<Expr> = Vec::new();
    for index in order {
        let lemma = &proof.lemmas[index];
        let label = lemma
            .name
            .clone()
            .unwrap_or_else(|| format!("{}#{}", proof.name, index));
        let formula = match lower_expr(&lemma.expr, &names, target.as_deref(), &names, &lemma.span) {
            Ok(expr) => expr,
            Err(diag) => {
                report.diagnostics.push(diag);
                continue;
            }
        };
        let mut assumptions = vec![requires.clone()];
        if explicit {
            for dep in &lemma.depends_on {
                if let Some(pos) = proof.lemmas.iter().position(|other| other.name.as_deref() == Some(dep)) {
                    if let Some(expr) = proved_by_index.get(&pos) {
                        assumptions.push(expr.clone());
                    }
                }
            }
        } else {
            assumptions.extend(sequential.iter().cloned());
        }
        let func = lemma_function(&label, &proof.law, &params, &assumptions, &formula, lemma.span.clone());
        let solved = verify_function(&func, z3);
        if solved.iter().all(|item| item.proved) {
            report.proved.push(label);
            proved_by_index.insert(index, formula.clone());
            sequential.push(formula);
        } else {
            for item in solved {
                if let Some(mut diag) = item.diagnostic {
                    if diag.code == ErrorCode::Verify001 {
                        diag.code = ErrorCode::Verify008;
                        diag.message = format!(
                            "lemma `{label}` is not entailed by the law precondition and earlier proved lemmas"
                        );
                    }
                    report.diagnostics.push(diag);
                }
            }
        }
    }
}

fn lemma_function(
    name: &str,
    law: &str,
    params: &[VirParam],
    assumptions: &[Expr],
    formula: &Expr,
    span: ts_proof_core::Span,
) -> VirFunction {
    let requires = and_all(assumptions);
    let ensures = formula.clone();
    let mut names = BTreeSet::new();
    let mut free = BTreeMap::new();
    requires.free_vars(&mut free);
    ensures.free_vars(&mut free);
    for name in free.into_keys() {
        names.insert(name);
    }
    for param in params {
        names.remove(&param.name);
    }
    let ghosts = ghosts_for(&names);
    let display = ghosts.iter().map(|ghost| ghost.name.clone()).collect();
    VirFunction {
        name: name.to_string(),
        params: params.to_vec(),
        ghosts,
        requires,
        ensures,
        body: Vec::new(),
        span,
        display,
        kind: FunctionKind::Lemma { law: law.to_string() },
    }
}

fn and_all(exprs: &[Expr]) -> Expr {
    let mut acc = Expr::Bool(true);
    for expr in exprs {
        acc = Expr::and(acc, expr.clone());
    }
    acc
}

fn lower_optional(spec: Option<&SpecFn>, target: Option<&str>, params: &[String]) -> Result<Expr, Diagnostic> {
    match spec {
        None => Ok(Expr::Bool(true)),
        Some(spec) => Ok(ts_proof_spec::lower_spec(spec, target, params)?.expr),
    }
}

fn vir_params(func: &Function) -> Result<Vec<VirParam>, Diagnostic> {
    let mut out = Vec::new();
    for param in &func.params {
        let ty = match &param.ty {
            Some(TsType::Bool) => VirType::Bool,
            Some(TsType::Int) => VirType::Int,
            Some(TsType::String) => VirType::String,
            _ => {
                return Err(Diagnostic::new(
                    ErrorCode::Verify002,
                    format!(
                        "parameter `{}` of `{}` needs a boolean, bigint, or string type",
                        param.name, func.name
                    ),
                )
                .at(param.span.clone()));
            }
        };
        out.push(VirParam {
            name: param.name.clone(),
            ty,
        });
    }
    Ok(out)
}

fn dependency_order(lemmas: &[ts_proof_core::Lemma]) -> Result<Vec<usize>, Diagnostic> {
    if lemmas.iter().all(|lemma| lemma.depends_on.is_empty()) {
        return Ok((0..lemmas.len()).collect());
    }
    let mut index = BTreeMap::new();
    for (i, lemma) in lemmas.iter().enumerate() {
        let Some(name) = &lemma.name else {
            return Err(Diagnostic::new(
                ErrorCode::Verify009,
                "a lemma that participates in dependencies needs a name",
            ));
        };
        if index.insert(name.clone(), i).is_some() {
            return Err(Diagnostic::new(
                ErrorCode::Verify009,
                format!("duplicate lemma `{name}`"),
            ));
        }
    }
    let mut edges = vec![Vec::new(); lemmas.len()];
    for (i, lemma) in lemmas.iter().enumerate() {
        for dep in &lemma.depends_on {
            let Some(&target) = index.get(dep) else {
                return Err(Diagnostic::new(
                    ErrorCode::Verify009,
                    format!("lemma depends on unknown lemma `{dep}`"),
                ));
            };
            edges[i].push(target);
        }
    }
    let mut color = vec![0u8; lemmas.len()];
    let mut out = Vec::new();
    for start in 0..lemmas.len() {
        visit(start, &edges, &mut color, &mut out)?;
    }
    Ok(out)
}

fn visit(index: usize, edges: &[Vec<usize>], color: &mut [u8], out: &mut Vec<usize>) -> Result<(), Diagnostic> {
    if color[index] == 1 {
        return Err(Diagnostic::new(
            ErrorCode::Verify009,
            "lemma dependencies are cyclic",
        ));
    }
    if color[index] == 2 {
        return Ok(());
    }
    color[index] = 1;
    for &next in &edges[index] {
        visit(next, edges, color, out)?;
    }
    color[index] = 2;
    out.push(index);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ts_proof_core::{Expr as Ast, Function, Lemma, Law, Proof, Span};

    fn span() -> Span {
        Span::dummy()
    }

    #[test]
    fn cyclic_lemmas_are_rejected_before_the_solver() {
        let mut program = Program::empty();
        program.functions.push(Function {
            name: "unused".into(),
            params: Vec::new(),
            ret: None,
            body: Vec::new(),
            span: span(),
            is_async: false,
            decorators: Vec::new(),
            class_name: None,
            class_decorators: Vec::new(),
        });
        program.laws.push(Law {
            name: "L".into(),
            target: "unused".into(),
            requires: None,
            ensures: None,
            span: span(),
        });
        program.proofs.push(Proof {
            name: "P".into(),
            law: "L".into(),
            lemmas: vec![
                Lemma {
                    name: Some("a".into()),
                    expr: Ast::Bool(true),
                    span: span(),
                    depends_on: vec!["b".into()],
                },
                Lemma {
                    name: Some("b".into()),
                    expr: Ast::Bool(true),
                    span: span(),
                    depends_on: vec!["a".into()],
                },
            ],
            span: span(),
        });
        let z3 = Z3::discover(None, 2_000).expect("z3");
        let report = check_lemmas(&program, &z3);
        assert!(report.proved.is_empty());
        assert!(
            report.diagnostics.iter().any(|d| {
                d.code == ErrorCode::Verify009 && d.message.contains("cyclic")
            }),
            "{:?}",
            report.diagnostics
        );
    }
}
