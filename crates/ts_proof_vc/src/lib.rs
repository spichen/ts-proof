//! Symbolic execution that emits validity obligations.
//!
//! Loops use the standard invariant rule: the invariant must hold on entry,
//! the body must preserve it, and the exit state is havoced down to what the
//! invariant says. A loop without an invariant never reaches this module.
//!
//! `return` and `throw` inside a loop are rejected. Encoding them as exits
//! from an invariant rule is easy to get wrong, and the supported subset does
//! not need them.

use std::collections::{BTreeMap, BTreeSet};
use ts_proof_core::{Assignment, Counterexample, Diagnostic, ErrorCode, Span};
use ts_proof_smt::{encode_validity, eval_model, EncodedObligation, Z3};
use ts_proof_vir::{modified_vars, BinOp, Expr, FunctionKind, Stmt, VirFunction, VirType};

#[derive(Clone, Debug)]
struct Sym {
    env: BTreeMap<String, Expr>,
    types: BTreeMap<String, VirType>,
    active: Expr,
    result: Expr,
    thrown: Expr,
    pc: Expr,
}

#[derive(Clone, Debug)]
pub struct Obligation {
    pub name: String,
    pub span: Span,
    pub formula: Expr,
    pub sorts: BTreeMap<String, VirType>,
    pub display: Vec<(String, Expr)>,
    pub expected: String,
}

#[derive(Debug)]
pub struct Solved {
    pub name: String,
    pub span: Span,
    pub proved: bool,
    pub diagnostic: Option<Diagnostic>,
    pub smt: String,
}

pub fn solve_obligation(obligation: Obligation, z3: &Z3) -> Solved {
    solve(obligation, z3)
}

pub fn verify_function(func: &VirFunction, z3: &Z3) -> Vec<Solved> {
    let obligations = match generate(func) {
        Ok(obs) => obs,
        Err(diag) => {
            return vec![Solved {
                name: func.name.clone(),
                span: func.span.clone(),
                proved: false,
                diagnostic: Some(diag),
                smt: String::new(),
            }];
        }
    };
    obligations
        .into_iter()
        .map(|ob| solve(ob, z3))
        .collect()
}

pub fn generate(func: &VirFunction) -> Result<Vec<Obligation>, Diagnostic> {
    let mut types = BTreeMap::new();
    let mut env = BTreeMap::new();
    let mut params = BTreeSet::new();
    for p in &func.params {
        types.insert(p.name.clone(), p.ty);
        env.insert(p.name.clone(), Expr::var(&p.name));
        params.insert(p.name.clone());
    }
    for g in &func.ghosts {
        types.insert(g.name.clone(), g.ty);
        env.insert(g.name.clone(), g.init.clone());
    }
    types.insert("thrown".into(), VirType::Bool);
    let initial = env.clone();
    let mut st = Sym {
        env,
        types,
        active: Expr::Bool(true),
        result: Expr::var("result"),
        thrown: Expr::Bool(false),
        pc: func.requires.clone(),
    };
    let mut gen = Gen {
        obligations: Vec::new(),
        params,
        initial,
        loop_id: 0,
        func_name: func.name.clone(),
        defs: Vec::new(),
        ssa_types: BTreeMap::new(),
        temp_id: 0,
    };
    // Path condition is named once so later clones do not copy the whole tree.
    st.pc = gen.define(&mut st.types, st.pc);
    let st = gen.block(&func.body, st)?;
    let expected = func.ensures.to_string();
    let post = gen.subst_post(&func.ensures, &st);
    let mut display = Vec::new();
    for p in &func.params {
        display.push((p.name.clone(), Expr::var(&p.name)));
    }
    for name in &func.display {
        if name == "result" {
            display.push(("result".into(), st.result.clone()));
        } else if name == "thrown" {
            display.push(("thrown".into(), st.thrown.clone()));
        } else if let Some(expr) = st.env.get(name) {
            display.push((name.clone(), expr.clone()));
        } else {
            display.push((name.clone(), Expr::var(name)));
        }
    }
    if !func.display.iter().any(|n| n == "result") && matches!(func.kind, FunctionKind::Function) {
        display.push(("result".into(), st.result.clone()));
    }
    let formula = gen.close(Expr::implies(st.pc.clone(), post));
    let sorts = gen.merged_sorts(&st.types);
    gen.obligations.push(Obligation {
        name: format!("{}:post", func.name),
        span: func.span.clone(),
        formula,
        sorts,
        display,
        expected,
    });
    Ok(gen.obligations)
}

struct Gen {
    obligations: Vec<Obligation>,
    params: BTreeSet<String>,
    initial: BTreeMap<String, Expr>,
    loop_id: u32,
    func_name: String,
    /// Equalities `ssa.N = expr`. Each expr mentions only earlier names, so
    /// substituting them back is the fully inlined symbolic state.
    defs: Vec<Expr>,
    ssa_types: BTreeMap<String, VirType>,
    temp_id: u32,
}

impl Gen {
    fn block(&mut self, stmts: &[Stmt], mut st: Sym) -> Result<Sym, Diagnostic> {
        for stmt in stmts {
            st = self.stmt(stmt, st)?;
        }
        Ok(st)
    }

    fn stmt(&mut self, stmt: &Stmt, mut st: Sym) -> Result<Sym, Diagnostic> {
        match stmt {
            Stmt::Assign { name, expr, .. } => {
                self.assign(&mut st, name, expr);
                if let Some(ty) = guess_assigned_type(expr, &st.types) {
                    bind_type(&mut st.types, name, ty);
                }
                Ok(st)
            }
            Stmt::Effect { counter, .. } => {
                let increment = Expr::binary(BinOp::Add, Expr::var(counter), Expr::int("1"));
                self.assign(&mut st, counter, &increment);
                bind_type(&mut st.types, counter, VirType::Int);
                Ok(st)
            }
            Stmt::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let cond_v = self.define(&mut st.types, cond.subst(&st.env));
                let mut then_st = st.clone();
                let then_active = Expr::and(st.active.clone(), cond_v.clone());
                then_st.active = self.define(&mut then_st.types, then_active);
                let then_st = self.block(then_branch, then_st)?;
                let mut else_st = st.clone();
                let else_active = Expr::and(st.active.clone(), Expr::not(cond_v.clone()));
                else_st.active = self.define(&mut else_st.types, else_active);
                let else_st = self.block(else_branch, else_st)?;
                Ok(join(self, &st, &cond_v, then_st, else_st))
            }
            Stmt::Return { expr, .. } => {
                let val = match expr {
                    Some(e) => e.subst(&st.env),
                    // A missing value is unit. An untyped free variable here makes
                    // the join ill-sorted once definitions are part of the query.
                    // Mixing unit with an integer result is rejected while sorting.
                    None => Expr::Bool(false),
                };
                let val = self.define(&mut st.types, val);
                st.result = self.define(
                    &mut st.types,
                    Expr::ite(st.active.clone(), val, st.result.clone()),
                );
                st.active = Expr::Bool(false);
                Ok(st)
            }
            Stmt::Throw { .. } => {
                st.thrown = self.define(
                    &mut st.types,
                    Expr::ite(st.active.clone(), Expr::Bool(true), st.thrown.clone()),
                );
                st.active = Expr::Bool(false);
                Ok(st)
            }
            Stmt::While {
                cond,
                invariant,
                modified,
                body,
                span,
            } => self.while_stmt(cond, invariant, modified, body, span.clone(), st),
        }
    }

    fn while_stmt(
        &mut self,
        cond: &Expr,
        invariant: &Expr,
        modified: &[String],
        body: &[Stmt],
        span: Span,
        mut st: Sym,
    ) -> Result<Sym, Diagnostic> {
        if exits(body) {
            return Err(Diagnostic::new(
                ErrorCode::Verify002,
                "return or throw inside a loop is outside the supported subset",
            )
            .at(span)
            .note("the invariant rule used here does not treat loop-body exits as function exits"));
        }
        let entry = Expr::implies(
            Expr::and(st.pc.clone(), st.active.clone()),
            invariant.subst(&st.env),
        );
        self.push_side(&st, format!("{}:loop{}:entry", self.func_name, self.loop_id), span.clone(), entry, invariant);
        let mut mods = modified.to_vec();
        for name in modified_vars(body) {
            if !mods.contains(&name) {
                mods.push(name);
            }
        }
        self.loop_id += 1;
        let id = self.loop_id;
        let mut fresh = st.env.clone();
        for name in &mods {
            let havoc = format!("havoc.{id}.{name}");
            fresh.insert(name.clone(), Expr::var(&havoc));
            if let Some(ty) = st.types.get(name).copied() {
                st.types.insert(havoc, ty);
            }
        }
        let mut pst = st.clone();
        pst.env = fresh;
        pst.active = Expr::Bool(true);
        pst.pc = self.define(
            &mut pst.types,
            Expr::and(
                st.pc.clone(),
                Expr::and(invariant.subst(&pst.env), cond.subst(&pst.env)),
            ),
        );
        pst.thrown = Expr::Bool(false);
        let after = self.block(body, pst)?;
        let preserved = Expr::implies(
            Expr::and(after.pc.clone(), after.active.clone()),
            invariant.subst(&after.env),
        );
        self.push_side(
            &after,
            format!("{}:loop{id}:preserve", self.func_name),
            span,
            preserved,
            invariant,
        );
        let mut exit_env = st.env.clone();
        for name in &mods {
            let exit_name = format!("exit.{id}.{name}");
            let prev = st.env.get(name).cloned().unwrap_or_else(|| Expr::var(name));
            let value = self.define(
                &mut st.types,
                Expr::ite(st.active.clone(), Expr::var(&exit_name), prev),
            );
            exit_env.insert(name.clone(), value);
            if let Some(ty) = st.types.get(name).copied() {
                st.types.insert(exit_name, ty);
            }
        }
        let inv_exit = invariant.subst(&exit_env);
        let cond_exit = cond.subst(&exit_env);
        st.pc = self.define(
            &mut st.types,
            Expr::and(
                st.pc.clone(),
                Expr::implies(
                    st.active.clone(),
                    Expr::and(inv_exit, Expr::not(cond_exit)),
                ),
            ),
        );
        st.env = exit_env;
        Ok(st)
    }

    fn push_side(&mut self, st: &Sym, name: String, span: Span, formula: Expr, expected: &Expr) {
        let formula = self.close(formula);
        self.obligations.push(Obligation {
            name,
            span,
            formula,
            sorts: self.merged_sorts(&st.types),
            display: Vec::new(),
            expected: expected.to_string(),
        });
    }

    fn assign(&mut self, st: &mut Sym, name: &str, rhs: &Expr) {
        let new_v = self.define(&mut st.types, rhs.subst(&st.env));
        let prev = st
            .env
            .get(name)
            .cloned()
            .unwrap_or_else(|| Expr::var(name));
        let value = self.define(&mut st.types, Expr::ite(st.active.clone(), new_v, prev));
        st.env.insert(name.to_string(), value);
    }

    /// Bind a compound expression to a fresh name. Joins then copy that name
    /// instead of cloning a tree that doubles at every branch. Literals and
    /// variables are already small and stay inline. The recorded equality is
    /// assumed by later obligations, which is sound because the name is fresh
    /// and the expression does not mention it.
    fn define(&mut self, types: &mut BTreeMap<String, VirType>, expr: Expr) -> Expr {
        match expr {
            Expr::Var(_) | Expr::Bool(_) | Expr::Int(_) | Expr::Str(_) => expr,
            other => {
                let ty = guess_assigned_type(&other, types)
                    .or_else(|| guess_assigned_type(&other, &self.ssa_types));
                let name = format!("ssa.{}", self.temp_id);
                self.temp_id += 1;
                if let Some(ty) = ty {
                    types.insert(name.clone(), ty);
                    self.ssa_types.insert(name.clone(), ty);
                }
                self.defs.push(Expr::eq(Expr::var(&name), other));
                Expr::var(name)
            }
        }
    }

    fn close(&self, formula: Expr) -> Expr {
        Expr::implies(conjoin(&self.defs), formula)
    }

    fn merged_sorts(&self, extra: &BTreeMap<String, VirType>) -> BTreeMap<String, VirType> {
        let mut sorts = extra.clone();
        for (name, ty) in &self.ssa_types {
            sorts.entry(name.clone()).or_insert(*ty);
        }
        sorts
    }

    /// Parameters and `old.*` keep their initial values. `result` and `thrown`
    /// are the final symbolic values. Every other name is final state.
    fn subst_post(&self, expr: &Expr, st: &Sym) -> Expr {
        match expr {
            Expr::Var(name) if name == "result" => st.result.clone(),
            Expr::Var(name) if name == "thrown" => st.thrown.clone(),
            Expr::Var(name) if self.params.contains(name) => self
                .initial
                .get(name)
                .cloned()
                .unwrap_or_else(|| Expr::var(name)),
            Expr::Var(name) => {
                if let Some(rest) = name.strip_prefix("old.") {
                    self.initial
                        .get(rest)
                        .cloned()
                        .unwrap_or_else(|| Expr::var(rest))
                } else {
                    st.env
                        .get(name)
                        .cloned()
                        .unwrap_or_else(|| Expr::var(name))
                }
            }
            Expr::Unary(op, e) => match op {
                ts_proof_vir::UnaryOp::Not => Expr::not(self.subst_post(e, st)),
                ts_proof_vir::UnaryOp::Neg => Expr::neg(self.subst_post(e, st)),
            },
            Expr::Binary(op, l, r) => {
                Expr::binary(*op, self.subst_post(l, st), self.subst_post(r, st))
            }
            Expr::Ite {
                cond,
                then_expr,
                else_expr,
            } => Expr::ite(
                self.subst_post(cond, st),
                self.subst_post(then_expr, st),
                self.subst_post(else_expr, st),
            ),
            other => other.clone(),
        }
    }
}

fn join(gen: &mut Gen, parent: &Sym, cond: &Expr, then_st: Sym, else_st: Sym) -> Sym {
    let mut types = parent.types.clone();
    types.extend(then_st.types.clone());
    types.extend(else_st.types);
    let guard_t = gen.define(&mut types, Expr::and(parent.active.clone(), cond.clone()));
    let guard_e = gen.define(
        &mut types,
        Expr::and(parent.active.clone(), Expr::not(cond.clone())),
    );
    let mut keys = BTreeSet::new();
    keys.extend(parent.env.keys().cloned());
    keys.extend(then_st.env.keys().cloned());
    keys.extend(else_st.env.keys().cloned());
    let mut env = BTreeMap::new();
    for key in keys {
        let p = parent
            .env
            .get(&key)
            .cloned()
            .unwrap_or_else(|| Expr::var(&key));
        let t = then_st.env.get(&key).cloned().unwrap_or_else(|| p.clone());
        let e = else_st.env.get(&key).cloned().unwrap_or_else(|| p.clone());
        env.insert(
            key,
            gen.define(
                &mut types,
                Expr::ite(guard_t.clone(), t, Expr::ite(guard_e.clone(), e, p)),
            ),
        );
    }
    let active = gen.define(
        &mut types,
        Expr::ite(
            guard_t.clone(),
            then_st.active,
            Expr::ite(guard_e.clone(), else_st.active, parent.active.clone()),
        ),
    );
    let result = gen.define(
        &mut types,
        Expr::ite(
            guard_t.clone(),
            then_st.result.clone(),
            Expr::ite(guard_e.clone(), else_st.result, parent.result.clone()),
        ),
    );
    let thrown = gen.define(
        &mut types,
        Expr::ite(
            guard_t,
            then_st.thrown,
            Expr::ite(guard_e, else_st.thrown, parent.thrown.clone()),
        ),
    );
    Sym {
        env,
        types,
        active,
        result,
        thrown,
        pc: parent.pc.clone(),
    }
}

/// Balanced conjunction. A right-nested chain of thousands of definitions
/// overflows the solver's parser; a balanced tree does not change the meaning.
fn conjoin(defs: &[Expr]) -> Expr {
    match defs {
        [] => Expr::Bool(true),
        [one] => one.clone(),
        more => {
            let mid = more.len() / 2;
            Expr::and(conjoin(&more[..mid]), conjoin(&more[mid..]))
        }
    }
}

fn exits(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Return { .. } | Stmt::Throw { .. } => true,
        Stmt::If {
            then_branch,
            else_branch,
            ..
        } => exits(then_branch) || exits(else_branch),
        Stmt::While { body, .. } => exits(body),
        Stmt::Assign { .. } | Stmt::Effect { .. } => false,
    })
}

fn guess_assigned_type(expr: &Expr, types: &BTreeMap<String, VirType>) -> Option<VirType> {
    match expr {
        Expr::Bool(_) => Some(VirType::Bool),
        Expr::Int(_) => Some(VirType::Int),
        Expr::Str(_) => Some(VirType::String),
        Expr::Var(name) => types.get(name).copied(),
        Expr::Unary(ts_proof_vir::UnaryOp::Not, _) => Some(VirType::Bool),
        Expr::Unary(ts_proof_vir::UnaryOp::Neg, _) => Some(VirType::Int),
        Expr::Binary(op, _, _) => match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul => Some(VirType::Int),
            BinOp::And | BinOp::Or | BinOp::Implies | BinOp::Eq | BinOp::Ne | BinOp::Lt
            | BinOp::Le | BinOp::Gt | BinOp::Ge => Some(VirType::Bool),
        },
        Expr::Ite { then_expr, .. } => guess_assigned_type(then_expr, types),
    }
}

fn bind_type(types: &mut BTreeMap<String, VirType>, name: &str, ty: VirType) {
    types.entry(name.to_string()).or_insert(ty);
}

fn solve(ob: Obligation, z3: &Z3) -> Solved {
    let encoded = match encode_validity(&ob.formula, &ob.sorts) {
        Ok(query) => EncodedObligation {
            name: ob.name.clone(),
            span: ob.span.clone(),
            validity: ob.formula.clone(),
            query,
            display: ob.display.clone(),
            expected: ob.expected.clone(),
        },
        Err(diag) => {
            return Solved {
                name: ob.name,
                span: ob.span,
                proved: false,
                diagnostic: Some(diag),
                smt: String::new(),
            };
        }
    };
    let smt = encoded.query.smt.clone();
    match z3.check(&encoded.query) {
        ts_proof_smt::SolverOutcome::Unsat => Solved {
            name: ob.name,
            span: ob.span,
            proved: true,
            diagnostic: None,
            smt,
        },
        ts_proof_smt::SolverOutcome::Sat(model) => {
            let mut assignments = Vec::new();
            let mut seen = BTreeSet::new();
            for (name, expr) in &encoded.display {
                if let Some(value) = eval_model(expr, &model) {
                    seen.insert(name.clone());
                    assignments.push(Assignment {
                        name: name.clone(),
                        value: value.to_string(),
                    });
                }
            }
            for (name, value) in &model {
                if seen.contains(name) || is_internal(name) {
                    continue;
                }
                assignments.push(Assignment {
                    name: name.clone(),
                    value: value.to_string(),
                });
            }
            let diag = Diagnostic::new(
                ErrorCode::Verify001,
                format!("{} failed", encoded.name),
            )
            .at(encoded.span)
            .expected(&encoded.expected)
            .with_counterexample(Counterexample { assignments })
            .note("this is a counterexample to the encoded model, not a runtime test");
            Solved {
                name: encoded.name,
                span: ob.span,
                proved: false,
                diagnostic: Some(diag),
                smt,
            }
        }
        ts_proof_smt::SolverOutcome::Unknown => Solved {
            name: ob.name,
            span: ob.span.clone(),
            proved: false,
            diagnostic: Some(
                Diagnostic::new(ErrorCode::Verify005, "solver returned unknown").at(ob.span),
            ),
            smt,
        },
        ts_proof_smt::SolverOutcome::Timeout => Solved {
            name: ob.name,
            span: ob.span.clone(),
            proved: false,
            diagnostic: Some(
                Diagnostic::new(ErrorCode::Verify004, "solver timed out").at(ob.span),
            ),
            smt,
        },
        ts_proof_smt::SolverOutcome::Error(message) => Solved {
            name: ob.name,
            span: ob.span.clone(),
            proved: false,
            diagnostic: Some(Diagnostic::new(ErrorCode::Verify006, message).at(ob.span)),
            smt,
        },
    }
}

fn is_internal(name: &str) -> bool {
    name.starts_with("havoc.")
        || name.starts_with("exit.")
        || name.starts_with("fail.")
        || name.starts_with("result")
        || name.starts_with("__")
        || name.starts_with("ssa.")
}

#[cfg(test)]
mod tests {
    use super::*;
    use ts_proof_smt::find_z3;
    use ts_proof_vir::{Ghost, VirParam};

    fn z3() -> Z3 {
        Z3::discover(None, 10_000).unwrap_or_else(|err| panic!("{err}"))
    }

    fn span() -> Span {
        Span::dummy()
    }

    fn param(name: &str, ty: VirType) -> VirParam {
        VirParam {
            name: name.into(),
            ty,
        }
    }

    #[test]
    fn expiry_proves_and_reversed_arithmetic_fails() {
        let _ = find_z3().expect("z3 is required");
        let solver = z3();
        let good = expiry(Expr::binary(
            BinOp::Add,
            Expr::var("now"),
            Expr::var("ttl"),
        ));
        let solved = verify_function(&good, &solver);
        assert!(solved.iter().all(|s| s.proved), "{solved:?}");

        let bad = expiry(Expr::binary(
            BinOp::Sub,
            Expr::var("now"),
            Expr::var("ttl"),
        ));
        let solved = verify_function(&bad, &solver);
        let post = solved.iter().find(|s| s.name.ends_with(":post")).unwrap();
        assert!(!post.proved);
        let diag = post.diagnostic.as_ref().unwrap();
        assert_eq!(diag.code, ErrorCode::Verify001);
        let ce = diag.counterexample.as_ref().unwrap();
        assert!(ce.assignments.iter().any(|a| a.name == "ttl"));
        assert!(ce.assignments.iter().any(|a| a.name == "result"));
    }

    #[test]
    fn long_conditional_chain_stays_provable() {
        let solver = z3();
        let mut params = Vec::new();
        let mut body = vec![Stmt::Assign {
            name: "x".into(),
            expr: Expr::int("0"),
            span: span(),
        }];
        let mut all_false = Expr::Bool(true);
        for i in 0..30 {
            let flag = format!("p{i}");
            params.push(param(&flag, VirType::Bool));
            all_false = Expr::and(all_false, Expr::not(Expr::var(&flag)));
            body.push(Stmt::If {
                cond: Expr::var(&flag),
                then_branch: vec![Stmt::Assign {
                    name: "x".into(),
                    expr: Expr::binary(BinOp::Add, Expr::var("x"), Expr::int("1")),
                    span: span(),
                }],
                else_branch: vec![],
                span: span(),
            });
        }
        let func = VirFunction {
            name: "chain".into(),
            params,
            ghosts: vec![],
            requires: Expr::Bool(true),
            ensures: Expr::implies(all_false, Expr::eq(Expr::var("x"), Expr::int("0"))),
            body,
            span: span(),
            display: vec!["x".into()],
            kind: FunctionKind::Function,
        };
        let solved = verify_function(&func, &solver);
        assert!(
            solved.iter().all(|s| s.proved),
            "{}",
            solved
                .iter()
                .filter(|s| !s.proved)
                .map(|s| format!("{}: {:?}", s.name, s.diagnostic))
                .collect::<Vec<_>>()
                .join("\n")
        );
        let bytes = solved.iter().map(|s| s.smt.len()).max().unwrap_or(0);
        assert!(bytes < 200_000, "smt grew to {bytes} bytes");
    }

    #[test]
    fn authorization_guard_controls_the_effect() {
        let solver = z3();
        let good = issue(true);
        assert!(verify_function(&good, &solver).iter().all(|s| s.proved));
        let bad = issue(false);
        let solved = verify_function(&bad, &solver);
        assert!(solved.iter().any(|s| !s.proved));
    }

    #[test]
    fn loop_invariant_proves_a_counter() {
        let solver = z3();
        // i = 0; s = 0; while i < n invariant i <= n && s === i { s = s + 1; i = i + 1 } return s
        // requires n >= 0 ensures result === n
        let body_loop = vec![
            Stmt::Assign {
                name: "s".into(),
                expr: Expr::binary(BinOp::Add, Expr::var("s"), Expr::int("1")),
                span: span(),
            },
            Stmt::Assign {
                name: "i".into(),
                expr: Expr::binary(BinOp::Add, Expr::var("i"), Expr::int("1")),
                span: span(),
            },
        ];
        let inv = Expr::and(
            Expr::binary(BinOp::Le, Expr::var("i"), Expr::var("n")),
            Expr::eq(Expr::var("s"), Expr::var("i")),
        );
        let func = VirFunction {
            name: "count".into(),
            params: vec![param("n", VirType::Int)],
            ghosts: vec![],
            requires: Expr::binary(BinOp::Ge, Expr::var("n"), Expr::int("0")),
            ensures: Expr::eq(Expr::var("result"), Expr::var("n")),
            body: vec![
                Stmt::Assign {
                    name: "i".into(),
                    expr: Expr::int("0"),
                    span: span(),
                },
                Stmt::Assign {
                    name: "s".into(),
                    expr: Expr::int("0"),
                    span: span(),
                },
                Stmt::While {
                    cond: Expr::binary(BinOp::Lt, Expr::var("i"), Expr::var("n")),
                    invariant: inv,
                    modified: vec!["i".into(), "s".into()],
                    body: body_loop,
                    span: span(),
                },
                Stmt::Return {
                    expr: Some(Expr::var("s")),
                    span: span(),
                },
            ],
            span: span(),
            display: vec!["n".into(), "result".into()],
            kind: FunctionKind::Function,
        };
        let solved = verify_function(&func, &solver);
        assert!(
            solved.iter().all(|s| s.proved),
            "{}",
            solved
                .iter()
                .filter(|s| !s.proved)
                .map(|s| format!("{}: {:?}", s.name, s.diagnostic))
                .collect::<Vec<_>>()
                .join("\n")
        );
    }

    fn expiry(returned: Expr) -> VirFunction {
        VirFunction {
            name: "calculateExpiry".into(),
            params: vec![param("now", VirType::Int), param("ttl", VirType::Int)],
            ghosts: vec![],
            requires: Expr::and(
                Expr::binary(BinOp::Ge, Expr::var("now"), Expr::int("0")),
                Expr::binary(BinOp::Gt, Expr::var("ttl"), Expr::int("0")),
            ),
            ensures: Expr::binary(BinOp::Gt, Expr::var("result"), Expr::var("now")),
            body: vec![Stmt::Return {
                expr: Some(returned),
                span: span(),
            }],
            span: span(),
            display: vec!["now".into(), "ttl".into(), "result".into()],
            kind: FunctionKind::Function,
        }
    }

    fn issue(guarded: bool) -> VirFunction {
        let effect = Stmt::Effect {
            effect: "kms.sign".into(),
            counter: "trace.kms.sign".into(),
            span: span(),
        };
        let body = if guarded {
            vec![Stmt::If {
                cond: Expr::not(Expr::var("authorized")),
                then_branch: vec![Stmt::Return {
                    expr: Some(Expr::int("0")),
                    span: span(),
                }],
                else_branch: vec![
                    effect,
                    Stmt::Return {
                        expr: Some(Expr::int("1")),
                        span: span(),
                    },
                ],
                span: span(),
            }]
        } else {
            vec![
                effect,
                Stmt::Return {
                    expr: Some(Expr::int("1")),
                    span: span(),
                },
            ]
        };
        VirFunction {
            name: "issueToken".into(),
            params: vec![param("authorized", VirType::Bool)],
            ghosts: vec![Ghost {
                name: "trace.kms.sign".into(),
                ty: VirType::Int,
                init: Expr::int("0"),
            }],
            requires: Expr::Bool(true),
            ensures: Expr::implies(
                Expr::not(Expr::var("authorized")),
                Expr::eq(Expr::var("trace.kms.sign"), Expr::int("0")),
            ),
            body,
            span: span(),
            display: vec!["authorized".into(), "trace.kms.sign".into(), "result".into()],
            kind: FunctionKind::Function,
        }
    }
}
