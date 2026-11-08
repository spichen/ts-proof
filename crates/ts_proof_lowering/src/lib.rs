//! Lower the supported TypeScript subset into VIR.
//!
//! Effectful calls are kept. A call with no contract, adapter, or external
//! declaration is an error. Middleware continues only through `next()`:
//! fall-through is not `next()`, and `return` stops only that middleware.
//! `next(err)` enters the error handler. A thrown exception aborts the chain.

use std::collections::{BTreeMap, BTreeSet};
use ts_proof_adapters::{ClassifyCtx, Layer, LayerKind, PureLower, Registry};
use ts_proof_core::{
    Callee, Diagnostic, ErrorCode, Expr as Ast, External, Function, Program, Span, Stmt as AstStmt,
    TsType, UnaryOp,
};
use ts_proof_effects::{
    assign, effect_stmt, endpoint_request_params, ghosts_for, request_field_type, request_var, stamp,
};
use ts_proof_vir::{modified_vars, Expr, FunctionKind, Stmt, VirFunction, VirParam, VirType};

pub fn referenced_tables(program: &Program) -> Vec<String> {
    let mut tables = BTreeSet::new();
    for func in &program.functions {
        scan_stmts(&func.body, &mut tables);
    }
    tables.into_iter().collect()
}

pub fn lower_function(
    program: &Program,
    registry: &Registry,
    func: &Function,
) -> Result<VirFunction, Vec<Diagnostic>> {
    let mut params = Vec::new();
    for p in &func.params {
        params.push(VirParam {
            name: p.name.clone(),
            ty: math_type(&p.ty, &p.span)?,
        });
    }
    let tables = referenced_tables(program);
    let mut lower = Lower::new(program, registry, tables);
    lower.params = params.iter().map(|p| p.name.clone()).collect();
    let body = lower.lower_block(&func.body).map_err(|d| vec![d])?;
    Ok(finish(
        func.name.clone(),
        params,
        Expr::Bool(true),
        Expr::Bool(true),
        body,
        func.span.clone(),
        FunctionKind::Function,
        &[],
    ))
}

/// Replace the contract and rebuild ghost initialization from the body and the
/// formulas. Names that appear only in a law must still receive their concrete
/// initial value; otherwise a missing effect looks like a free variable.
pub fn with_contract(func: VirFunction, requires: Expr, ensures: Expr, span: Span) -> VirFunction {
    let kind = func.kind.clone();
    let display = func.display.clone();
    finish(
        func.name,
        func.params,
        requires,
        ensures,
        func.body,
        span,
        kind,
        &display,
    )
}

pub fn lower_endpoint(
    program: &Program,
    registry: &Registry,
    method: &str,
    path: &str,
    layers: &[Layer],
) -> Result<VirFunction, Vec<Diagnostic>> {
    let (guards, handlers, errors) = chain_for(method, path, layers)?;
    let tables = referenced_tables(program);
    let mut lower = Lower::new(program, registry, tables);
    let error_stmts = match errors.as_slice() {
        [] => vec![Stmt::Throw {
            span: Span::dummy(),
        }],
        [name] => {
            let func = program.function(name).ok_or_else(|| {
                vec![missing(name)]
            })?;
            lower.lower_handler(func, Vec::new(), vec![Stmt::Throw { span: func.span.clone() }])?
        }
        _ => {
            return Err(vec![Diagnostic::new(
                ErrorCode::Verify011,
                "multiple error handlers are outside the supported subset",
            )]);
        }
    };
    let mut body = lower.chain(&handlers, 0, error_stmts)?;
    for guard in guards.iter().rev() {
        body = lower.wrap_guard(guard, body)?;
    }
    Ok(finish(
        format!("{method} {path}"),
        endpoint_request_params(),
        Expr::Bool(true),
        Expr::Bool(true),
        body,
        Span::dummy(),
        FunctionKind::Endpoint {
            method: method.to_string(),
            path: path.to_string(),
        },
        &[],
    ))
}

fn chain_for(
    method: &str,
    path: &str,
    layers: &[Layer],
) -> Result<(Vec<String>, Vec<String>, Vec<String>), Vec<Diagnostic>> {
    let mut guards = Vec::new();
    let mut handlers = Vec::new();
    let mut errors = Vec::new();
    let mut found = false;
    for layer in layers {
        match &layer.kind {
            LayerKind::ErrorHandler { name } => errors.push(name.clone()),
            LayerKind::Middleware { handlers: hs, prefix } => {
                if found {
                    continue;
                }
                let applies = match prefix {
                    None => true,
                    Some(pre) => prefix_matches(pre, path),
                };
                if applies {
                    handlers.extend(hs.clone());
                }
            }
            LayerKind::Route {
                method: m,
                path: p,
                guards: g,
                handlers: hs,
            } => {
                if m.eq_ignore_ascii_case(method) && p == path {
                    if found {
                        return Err(vec![Diagnostic::new(
                            ErrorCode::Verify011,
                            format!("duplicate route {method} {path}"),
                        )]);
                    }
                    found = true;
                    guards.extend(g.clone());
                    handlers.extend(hs.clone());
                }
            }
        }
    }
    if !found {
        return Err(vec![Diagnostic::new(
            ErrorCode::Verify010,
            format!("no discovered route matches {method} {path}"),
        )]);
    }
    Ok((guards, handlers, errors))
}

fn prefix_matches(prefix: &str, path: &str) -> bool {
    if prefix.is_empty() || prefix == "/" {
        return true;
    }
    let pre = segments(prefix);
    let route = segments(path);
    if pre.len() > route.len() {
        return false;
    }
    pre.iter().zip(route.iter()).all(|(a, b)| a == b || a.starts_with(':') || b.starts_with(':'))
}

fn segments(path: &str) -> Vec<&str> {
    path.split('/').filter(|s| !s.is_empty()).collect()
}

struct Lower<'a> {
    program: &'a Program,
    registry: &'a Registry,
    tables: Vec<String>,
    locals: BTreeSet<String>,
    params: BTreeSet<String>,
    request: Option<String>,
    response: Option<String>,
    next_param: Option<String>,
    continuation: Vec<Stmt>,
    error_continuation: Vec<Stmt>,
    done: Option<String>,
    result_slot: Option<String>,
    failure: Option<String>,
    /// Catch bindings are in scope syntactically, but their values are not
    /// modeled. A read is rejected instead of becoming a free boolean.
    catch_names: BTreeSet<String>,
    stack: Vec<String>,
    fresh: u32,
}

impl<'a> Lower<'a> {
    fn new(program: &'a Program, registry: &'a Registry, tables: Vec<String>) -> Self {
        Self {
            program,
            registry,
            tables,
            locals: BTreeSet::new(),
            params: BTreeSet::new(),
            request: None,
            response: None,
            next_param: None,
            continuation: Vec::new(),
            error_continuation: Vec::new(),
            done: None,
            result_slot: None,
            failure: None,
            catch_names: BTreeSet::new(),
            stack: Vec::new(),
            fresh: 0,
        }
    }

    fn chain(
        &mut self,
        handlers: &[String],
        index: usize,
        error: Vec<Stmt>,
    ) -> Result<Vec<Stmt>, Vec<Diagnostic>> {
        if index == handlers.len() {
            return Ok(Vec::new());
        }
        let cont = self.chain(handlers, index + 1, error.clone())?;
        let func = self
            .program
            .function(&handlers[index])
            .ok_or_else(|| vec![missing(&handlers[index])])?
            .clone();
        self.lower_handler(&func, cont, error)
    }

    fn lower_handler(
        &mut self,
        func: &Function,
        continuation: Vec<Stmt>,
        error: Vec<Stmt>,
    ) -> Result<Vec<Stmt>, Vec<Diagnostic>> {
        let saved = self.snapshot();
        let (request, response, next_param) = classify_params(func);
        self.request = request;
        self.response = response;
        self.next_param = next_param;
        self.continuation = continuation;
        self.error_continuation = error;
        self.locals.clear();
        self.catch_names.clear();
        let prefix = format!("h{}.", self.alloc());
        let body = prefix_locals(&func.body, &prefix).map_err(|d| vec![d])?;
        let done = self.fresh_name("done");
        self.done = Some(done.clone());
        self.result_slot = None;
        let mut stmts = vec![assign(&done, Expr::Bool(false), func.span.clone())];
        stmts.extend(self.lower_block(&body).map_err(|d| vec![d])?);
        self.restore(saved);
        Ok(stmts)
    }

    fn wrap_guard(&mut self, name: &str, cont: Vec<Stmt>) -> Result<Vec<Stmt>, Vec<Diagnostic>> {
        let func = self
            .program
            .function(name)
            .ok_or_else(|| vec![missing(name)])?
            .clone();
        let saved = self.snapshot();
        let (request, _, _) = classify_params(&func);
        self.request = request.clone();
        self.response = None;
        self.next_param = None;
        self.continuation.clear();
        self.error_continuation.clear();
        let arg_name = request.unwrap_or_else(|| "req".into());
        let arg = Ast::Ident(arg_name);
        let produced = self
            .inline_user(&func, &[arg], true)
            .map_err(|d| vec![d])?;
        self.restore(saved);
        if produced.effectful && produced.value.is_none() {
            return Err(vec![bad(
                &func.span,
                "a guard must return a boolean",
            )]);
        }
        let Some(value) = produced.value else {
            return Err(vec![bad(&func.span, "a guard must return a boolean")]);
        };
        let mut deny = vec![
            assign("response.status", Expr::int("403"), func.span.clone()),
            assign("response.statusSet", Expr::Bool(true), func.span.clone()),
            assign("response.committed", Expr::Bool(true), func.span.clone()),
        ];
        deny.extend(stamp("response.clock", func.span.clone()));
        let mut stmts = produced.stmts;
        stmts.push(Stmt::If {
            cond: Expr::not(value),
            then_branch: deny,
            else_branch: cont,
            span: func.span,
        });
        Ok(stmts)
    }

    fn lower_block(&mut self, stmts: &[AstStmt]) -> Result<Vec<Stmt>, Diagnostic> {
        let mut out = Vec::new();
        for stmt in stmts {
            let lowered = self.lower_stmt(stmt)?;
            out.extend(self.guarded(lowered));
        }
        Ok(out)
    }

    fn lower_stmt(&mut self, stmt: &AstStmt) -> Result<Vec<Stmt>, Diagnostic> {
        match stmt {
            AstStmt::Let { name, init, span } => {
                if !self.locals.insert(name.clone()) {
                    return Err(bad(span, format!("`{name}` is declared twice")));
                }
                if let Some(produced) = self.as_call(init)? {
                    if produced.effectful {
                        return Err(bad(
                            span,
                            "an effectful call cannot be bound; its result is not modeled",
                        ));
                    }
                    let Some(value) = produced.value else {
                        return Err(bad(span, "this call has no mathematical result"));
                    };
                    let mut stmts = produced.stmts;
                    stmts.push(assign(name, value, span.clone()));
                    return Ok(stmts);
                }
                Ok(vec![assign(name, self.pure(init)?, span.clone())])
            }
            AstStmt::Assign { name, expr, span } => {
                if !self.locals.contains(name) && !self.params.contains(name) {
                    return Err(bad(span, format!("assignment to unknown `{name}`")));
                }
                Ok(vec![assign(name, self.pure(expr)?, span.clone())])
            }
            AstStmt::If {
                cond,
                then_body,
                else_body,
                span,
            } => {
                let cond = self.pure(cond)?;
                let then_branch = self.lower_block(then_body)?;
                let else_branch = self.lower_block(else_body)?;
                Ok(vec![Stmt::If {
                    cond,
                    then_branch,
                    else_branch,
                    span: span.clone(),
                }])
            }
            AstStmt::Return { expr, span } => self.lower_return(expr.as_ref(), span),
            AstStmt::Throw { span } => {
                if self.failure.is_some() || self.done.is_some() {
                    let mut stmts = self.on_failure(span);
                    if let Some(done) = &self.done {
                        if self.failure.is_none() {
                            stmts = vec![assign(done, Expr::Bool(true), span.clone())];
                        }
                    }
                    // A throw inside try sets the catch flag. A throw inside a
                    // middleware, outside try, aborts the composed request.
                    if self.failure.is_none() && self.done.is_some() {
                        return Ok(vec![Stmt::Throw { span: span.clone() }]);
                    }
                    return Ok(stmts);
                }
                Ok(vec![Stmt::Throw { span: span.clone() }])
            }
            AstStmt::While {
                cond,
                invariant,
                body,
                span,
            } => {
                let Some(inv) = invariant else {
                    return Err(Diagnostic::new(
                        ErrorCode::Verify007,
                        "a while loop needs a // @invariant annotation",
                    )
                    .at(span.clone()));
                };
                let cond = self.pure(cond)?;
                let invariant = self.pure(inv)?;
                let body = self.lower_block(body)?;
                if exits(&body) {
                    return Err(Diagnostic::new(
                        ErrorCode::Verify002,
                        "return or throw inside a loop is outside the supported subset",
                    )
                    .at(span.clone()));
                }
                Ok(vec![Stmt::While {
                    cond,
                    invariant,
                    modified: modified_vars(&body),
                    body,
                    span: span.clone(),
                }])
            }
            AstStmt::Expr { expr, span } => {
                if let Some(produced) = self.as_call(expr)? {
                    if produced.value.is_some() && !produced.effectful && produced.stmts.is_empty() {
                        return Ok(Vec::new());
                    }
                    return Ok(produced.stmts);
                }
                let _ = self.pure(expr).map_err(|d| d.at_if_empty(span))?;
                Ok(Vec::new())
            }
            AstStmt::Try {
                body,
                catch_param,
                catch_body,
                span,
            } => {
                if self.locals.contains(catch_param) || self.params.contains(catch_param) {
                    return Err(bad(span, format!("`{catch_param}` is already declared")));
                }
                let flag = self.fresh_name("caught");
                let saved = self.failure.clone();
                self.failure = Some(flag.clone());
                let mut stmts = vec![assign(&flag, Expr::Bool(false), span.clone())];
                stmts.extend(self.lower_block(body)?);
                self.failure = saved;
                self.catch_names.insert(catch_param.clone());
                let catch_stmts = self.lower_block(catch_body)?;
                self.catch_names.remove(catch_param);
                stmts.push(Stmt::If {
                    cond: Expr::var(&flag),
                    then_branch: catch_stmts,
                    else_branch: Vec::new(),
                    span: span.clone(),
                });
                Ok(stmts)
            }
            AstStmt::Next { span, .. } => Err(bad(
                span,
                "internal next statement is not produced by the parser",
            )),
        }
    }

    fn lower_return(&mut self, expr: Option<&Ast>, span: &Span) -> Result<Vec<Stmt>, Diagnostic> {
        let mut stmts = Vec::new();
        let value = if let Some(expr) = expr {
            if matches!(expr, Ast::Null) {
                None
            } else if let Some(produced) = self.as_call(expr)? {
                if produced.effectful && produced.value.is_some() {
                    return Err(bad(span, "an effectful call's result cannot be returned"));
                }
                stmts.extend(produced.stmts);
                if produced.effectful {
                    None
                } else {
                    produced.value
                }
            } else {
                Some(self.pure(expr)?)
            }
        } else {
            None
        };
        if let Some(done) = self.done.clone() {
            if let (Some(slot), Some(value)) = (self.result_slot.clone(), value.clone()) {
                stmts.push(assign(&slot, value, span.clone()));
            }
            stmts.push(assign(&done, Expr::Bool(true), span.clone()));
            return Ok(stmts);
        }
        stmts.push(Stmt::Return {
            expr: value,
            span: span.clone(),
        });
        Ok(stmts)
    }

    fn as_call(&mut self, expr: &Ast) -> Result<Option<Produced>, Diagnostic> {
        let Ast::Call { .. } = expr else {
            return Ok(None);
        };
        self.lower_invocation(expr).map(Some)
    }

    fn lower_invocation(&mut self, expr: &Ast) -> Result<Produced, Diagnostic> {
        let Ast::Call { callee, args, span } = expr else {
            return Err(bad(&Span::dummy(), "expected a call"));
        };
        if self.is_next(callee) {
            return self.lower_next(args, span);
        }
        if let Some(arg) = promise_method(callee, args, "resolve") {
            return self.promise_resolve(arg, span);
        }
        if promise_method(callee, args, "reject").is_some() {
            self.seal_args(args)?;
            return Ok(Produced {
                stmts: self.on_failure(span),
                value: None,
                effectful: true,
            });
        }
        if let Some(effect) = self.external_effect(callee, span)? {
            return Ok(Produced {
                stmts: self.effect_call(&effect, span),
                value: None,
                effectful: true,
            });
        }
        match self.dispatch(expr)? {
            Some(stmts) => {
                return Ok(Produced {
                    stmts,
                    value: None,
                    effectful: true,
                })
            }
            None => {}
        }
        if let Some(func) = self.user_fn(callee).cloned() {
            return self.inline_user(&func, args, true);
        }
        Err(Diagnostic::new(
            ErrorCode::Verify003,
            "unmodeled call",
        )
        .at(span.clone())
        .note("declare an external effect, call a verified function, or use a supported adapter"))
    }

    fn lower_next(&mut self, args: &[Ast], span: &Span) -> Result<Produced, Diagnostic> {
        match args.len() {
            0 => Ok(Produced {
                stmts: self.continuation.clone(),
                value: None,
                effectful: true,
            }),
            1 => {
                self.seal(&args[0])?;
                Ok(Produced {
                    stmts: self.error_continuation.clone(),
                    value: None,
                    effectful: true,
                })
            }
            _ => Err(bad(span, "next accepts zero arguments or a single error")),
        }
    }

    fn promise_resolve(&mut self, arg: &Ast, span: &Span) -> Result<Produced, Diagnostic> {
        let _ = span;
        self.seal(arg)?;
        if matches!(arg, Ast::Null) || matches!(arg, Ast::Object { .. } | Ast::Array { .. }) {
            return Ok(Produced {
                stmts: Vec::new(),
                value: None,
                effectful: false,
            });
        }
        Ok(Produced {
            stmts: Vec::new(),
            value: Some(self.pure(arg)?),
            effectful: false,
        })
    }

    fn inline_user(
        &mut self,
        func: &Function,
        args: &[Ast],
        want_value: bool,
    ) -> Result<Produced, Diagnostic> {
        if func.params.iter().any(|p| p.name == "next") {
            return Err(bad(
                &func.span,
                format!("`{}` is middleware; it is composed by next(), not called", func.name),
            ));
        }
        if func.params.len() != args.len() {
            return Err(bad(
                &func.span,
                format!(
                    "`{}` expects {} arguments",
                    func.name,
                    func.params.len()
                ),
            ));
        }
        if self.stack.iter().any(|n| n == &func.name) {
            return Err(bad(&func.span, "recursive calls are outside the supported subset"));
        }
        if let Some(value) = self.try_pure_subst(func, args)? {
            return Ok(Produced {
                stmts: Vec::new(),
                value: Some(value),
                effectful: false,
            });
        }
        self.stack.push(func.name.clone());
        let mut map = BTreeMap::new();
        for (param, arg) in func.params.iter().zip(args) {
            map.insert(param.name.clone(), arg.clone());
        }
        let body = subst_stmts(&func.body, &map);
        let prefix = format!("i{}.", self.alloc());
        let body = prefix_locals(&body, &prefix)?;
        let saved = self.snapshot();
        let slot = if want_value {
            Some(self.fresh_name("ret"))
        } else {
            None
        };
        let done = self.fresh_name("done");
        self.result_slot = slot.clone();
        self.done = Some(done.clone());
        self.next_param = None;
        self.continuation.clear();
        self.error_continuation.clear();
        self.locals.clear();
        self.catch_names.clear();
        let mut stmts = vec![assign(&done, Expr::Bool(false), func.span.clone())];
        stmts.extend(self.lower_block(&body)?);
        let effectful = contains_effect(&stmts);
        self.stack.pop();
        self.restore(saved);
        if effectful && want_value {
            return Err(bad(
                &func.span,
                format!("`{}` has effects, so its result cannot be used as a value", func.name),
            ));
        }
        Ok(Produced {
            value: slot.map(Expr::var),
            stmts,
            effectful,
        })
    }

    fn try_pure_subst(&mut self, func: &Function, args: &[Ast]) -> Result<Option<Expr>, Diagnostic> {
        let [AstStmt::Return { expr: Some(body), .. }] = func.body.as_slice() else {
            return Ok(None);
        };
        if expr_calls_effect(body) {
            return Ok(None);
        }
        let mut map = BTreeMap::new();
        for (param, arg) in func.params.iter().zip(args) {
            map.insert(param.name.clone(), arg.clone());
        }
        let substituted = subst_expr(body, &map);
        if expr_calls_effect(&substituted) {
            return Ok(None);
        }
        match self.pure(&substituted) {
            Ok(value) => Ok(Some(value)),
            Err(_) => Ok(None),
        }
    }

    fn effect_call(&mut self, effect: &str, span: &Span) -> Vec<Stmt> {
        let fail = self.fresh_fail(span);
        let failure = self.on_failure(span);
        vec![
            effect_stmt(effect, span.clone()),
            Stmt::If {
                cond: fail,
                then_branch: failure,
                else_branch: vec![effect_stmt(&format!("{effect}.ok"), span.clone())],
                span: span.clone(),
            },
        ]
    }

    fn dispatch(&mut self, call: &Ast) -> Result<Option<Vec<Stmt>>, Diagnostic> {
        let registry = self.registry;
        let response = self.response.clone();
        let tables = self.tables.clone();
        let mut ctx = ClassifyCtx {
            response_ident: response.as_deref(),
            pure: self,
            tables: &tables,
        };
        registry
            .lower_call(call, &mut ctx)
            .map_err(flatten)
    }

    fn external_effect(&self, callee: &Callee, span: &Span) -> Result<Option<String>, Diagnostic> {
        match callee {
            Callee::Ident(name) => match self.program.externals.get(name) {
                Some(External::Function { effect, .. }) => Ok(Some(effect.clone())),
                Some(External::Namespace { .. }) => Err(bad(span, format!("`{name}` is a namespace"))),
                None => Ok(None),
            },
            Callee::Member { object, field } => {
                let Ast::Ident(name) = object.as_ref() else {
                    return Ok(None);
                };
                match self.program.externals.get(name) {
                    Some(External::Namespace { methods, .. }) => {
                        if let Some(effect) = methods.get(field) {
                            Ok(Some(effect.clone()))
                        } else {
                            Err(bad(span, format!("`{name}.{field}` is not a declared external")))
                        }
                    }
                    _ => Ok(None),
                }
            }
        }
    }

    fn user_fn(&self, callee: &Callee) -> Option<&Function> {
        let Callee::Ident(name) = callee else {
            return None;
        };
        self.program.function(name)
    }

    fn is_next(&self, callee: &Callee) -> bool {
        match (callee, &self.next_param) {
            (Callee::Ident(name), Some(next)) => name == next,
            _ => false,
        }
    }

    fn pure_math(&mut self, expr: &Ast) -> Result<Expr, Diagnostic> {
        let span = expr.span_hint().cloned().unwrap_or_else(Span::dummy);
        match expr {
            Ast::Bool(v) => Ok(Expr::bool(*v)),
            Ast::Int(n) => Ok(Expr::int(n)),
            Ast::Str(s) => Ok(Expr::Str(s.clone())),
            Ast::Null => Err(bad(&span, "null is not a mathematical value")),
            Ast::Ident(name) => self.lookup(name, &span),
            Ast::Unary { op, expr, span: _ } => {
                let v = self.pure_math(expr)?;
                Ok(match op {
                    UnaryOp::Not => Expr::not(v),
                    UnaryOp::Neg => Expr::neg(v),
                })
            }
            Ast::Binary { op, left, right, .. } => {
                let l = self.pure_math(left)?;
                let r = self.pure_math(right)?;
                Ok(Expr::binary(map_op(*op), l, r))
            }
            Ast::Ternary {
                cond,
                then_expr,
                else_expr,
                ..
            } => Ok(Expr::ite(
                self.pure_math(cond)?,
                self.pure_math(then_expr)?,
                self.pure_math(else_expr)?,
            )),
            Ast::Member { object, field, span } => self.member(object, field, span),
            Ast::Call { .. } => {
                if let Some(produced) = self.as_call(expr)? {
                    if produced.effectful || !produced.stmts.is_empty() {
                        return Err(bad(&span, "effectful calls cannot be used as values"));
                    }
                    return produced
                        .value
                        .ok_or_else(|| bad(&span, "this call has no mathematical result"));
                }
                Err(bad(&span, "unsupported call"))
            }
            Ast::Array { span, .. } | Ast::Object { span, .. } | Ast::Arrow { span, .. } => {
                Err(bad(span, "this value is not a boolean, integer, or string"))
            }
        }
    }

    fn lookup(&self, name: &str, span: &Span) -> Result<Expr, Diagnostic> {
        if self.catch_names.contains(name) {
            return Err(bad(
                span,
                "the caught error value is not modeled; reading it would be a free variable",
            ));
        }
        if self.locals.contains(name) || self.params.contains(name) {
            return Ok(Expr::var(name));
        }
        if let Some(decl) = self.program.consts.iter().find(|c| c.name == name) {
            return match &decl.expr {
                Ast::Int(n) => Ok(Expr::int(n)),
                Ast::Bool(v) => Ok(Expr::bool(*v)),
                Ast::Str(s) => Ok(Expr::Str(s.clone())),
                _ => Err(bad(span, format!("`{name}` is not a literal constant"))),
            };
        }
        Err(Diagnostic::new(
            ErrorCode::Verify003,
            format!("`{name}` is not a parameter, local, or literal constant"),
        )
        .at(span.clone()))
    }

    fn member(&self, object: &Ast, field: &str, span: &Span) -> Result<Expr, Diagnostic> {
        let Ast::Ident(name) = object else {
            return Err(bad(span, "only `request.field` reads are supported"));
        };
        if self.request.as_deref() == Some(name.as_str()) {
            if request_field_type(field).is_none() {
                return Err(bad(
                    span,
                    format!("`{field}` is not a supported request field"),
                ));
            }
            return Ok(Expr::var(request_var(field)));
        }
        Err(bad(span, format!("unsupported field `{name}.{field}`")))
    }

    fn seal_args(&mut self, args: &[Ast]) -> Result<(), Diagnostic> {
        for arg in args {
            self.seal(arg)?;
        }
        Ok(())
    }

    fn guarded(&self, stmts: Vec<Stmt>) -> Vec<Stmt> {
        if stmts.is_empty() {
            return stmts;
        }
        let mut cond = None;
        if let Some(done) = &self.done {
            cond = Some(Expr::not(Expr::var(done)));
        }
        if let Some(flag) = &self.failure {
            let bit = Expr::not(Expr::var(flag));
            cond = Some(match cond {
                Some(prev) => Expr::and(prev, bit),
                None => bit,
            });
        }
        let Some(cond) = cond else {
            return stmts;
        };
        let span = span_of(&stmts).unwrap_or_else(Span::dummy);
        vec![Stmt::If {
            cond,
            then_branch: stmts,
            else_branch: Vec::new(),
            span,
        }]
    }

    fn fresh_name(&mut self, prefix: &str) -> String {
        let id = self.alloc();
        format!("{prefix}.{id}")
    }

    fn alloc(&mut self) -> u32 {
        let id = self.fresh;
        self.fresh += 1;
        id
    }

    fn snapshot(&self) -> Snap {
        Snap {
            locals: self.locals.clone(),
            request: self.request.clone(),
            response: self.response.clone(),
            next_param: self.next_param.clone(),
            continuation: self.continuation.clone(),
            error_continuation: self.error_continuation.clone(),
            done: self.done.clone(),
            result_slot: self.result_slot.clone(),
            failure: self.failure.clone(),
            catch_names: self.catch_names.clone(),
        }
    }

    fn restore(&mut self, snap: Snap) {
        self.locals = snap.locals;
        self.request = snap.request;
        self.response = snap.response;
        self.next_param = snap.next_param;
        self.continuation = snap.continuation;
        self.error_continuation = snap.error_continuation;
        self.done = snap.done;
        self.result_slot = snap.result_slot;
        self.failure = snap.failure;
        self.catch_names = snap.catch_names;
    }
}

impl PureLower for Lower<'_> {
    fn pure(&mut self, expr: &Ast) -> Result<Expr, Diagnostic> {
        self.pure_math(expr)
    }

    fn seal(&mut self, expr: &Ast) -> Result<(), Diagnostic> {
        match expr {
            Ast::Bool(_) | Ast::Int(_) | Ast::Str(_) | Ast::Null | Ast::Ident(_) => Ok(()),
            Ast::Unary { expr, .. } | Ast::Member { object: expr, .. } => self.seal(expr),
            Ast::Binary { left, right, .. } => {
                self.seal(left)?;
                self.seal(right)
            }
            Ast::Ternary {
                cond,
                then_expr,
                else_expr,
                ..
            } => {
                self.seal(cond)?;
                self.seal(then_expr)?;
                self.seal(else_expr)
            }
            Ast::Array { items, .. } => {
                for item in items {
                    self.seal(item)?;
                }
                Ok(())
            }
            Ast::Object { fields, .. } => {
                for (_, value) in fields {
                    self.seal(value)?;
                }
                Ok(())
            }
            Ast::Arrow { span, .. } => Err(bad(span, "arrows are verification syntax")),
            Ast::Call { span, .. } => {
                let produced = self.lower_invocation(expr)?;
                if produced.effectful || contains_effect(&produced.stmts) {
                    Err(bad(span, "an effect cannot be hidden in a payload"))
                } else {
                    Ok(())
                }
            }
        }
    }

    fn fresh_fail(&mut self, _span: &Span) -> Expr {
        Expr::var(self.fresh_name("fail"))
    }

    fn on_failure(&mut self, span: &Span) -> Vec<Stmt> {
        if let Some(flag) = &self.failure {
            vec![assign(flag, Expr::Bool(true), span.clone())]
        } else {
            vec![Stmt::Throw { span: span.clone() }]
        }
    }
}

struct Produced {
    stmts: Vec<Stmt>,
    value: Option<Expr>,
    effectful: bool,
}

struct Snap {
    locals: BTreeSet<String>,
    request: Option<String>,
    response: Option<String>,
    next_param: Option<String>,
    continuation: Vec<Stmt>,
    error_continuation: Vec<Stmt>,
    done: Option<String>,
    result_slot: Option<String>,
    failure: Option<String>,
    catch_names: BTreeSet<String>,
}

fn finish(
    name: String,
    params: Vec<VirParam>,
    requires: Expr,
    ensures: Expr,
    body: Vec<Stmt>,
    span: Span,
    kind: FunctionKind,
    extra_display: &[String],
) -> VirFunction {
    let mut names = BTreeSet::new();
    for name in modified_vars(&body) {
        names.insert(name);
    }
    collect_stmts(&body, &mut names);
    collect_expr(&requires, &mut names);
    collect_expr(&ensures, &mut names);
    for param in &params {
        names.remove(&param.name);
    }
    let ghosts = ghosts_for(&names);
    let mut display: Vec<String> = extra_display.to_vec();
    for ghost in &ghosts {
        if !display.contains(&ghost.name) {
            display.push(ghost.name.clone());
        }
    }
    VirFunction {
        name,
        params,
        ghosts,
        requires,
        ensures,
        body,
        span,
        display,
        kind,
    }
}

fn classify_params(func: &Function) -> (Option<String>, Option<String>, Option<String>) {
    let mut request = None;
    let mut response = None;
    let mut next = None;
    for param in &func.params {
        match param.name.as_str() {
            "req" | "request" => request = Some(param.name.clone()),
            "res" | "response" => response = Some(param.name.clone()),
            "next" => next = Some(param.name.clone()),
            _ => {}
        }
    }
    (request, response, next)
}

fn math_type(ty: &Option<TsType>, span: &Span) -> Result<VirType, Vec<Diagnostic>> {
    let kind = match ty {
        Some(TsType::Bool) => VirType::Bool,
        Some(TsType::Int) => VirType::Int,
        Some(TsType::String) => VirType::String,
        Some(TsType::Named(name)) => {
            return Err(vec![bad(
                span,
                format!("parameter type `{name}` is outside the supported subset; use boolean, bigint, or string"),
            )]);
        }
        _ => {
            return Err(vec![bad(
                span,
                "parameters of a verified function need a boolean, bigint, or string annotation",
            )]);
        }
    };
    Ok(kind)
}

fn map_op(op: ts_proof_core::BinOp) -> ts_proof_vir::BinOp {
    use ts_proof_core::BinOp::*;
    match op {
        Add => ts_proof_vir::BinOp::Add,
        Sub => ts_proof_vir::BinOp::Sub,
        Mul => ts_proof_vir::BinOp::Mul,
        Eq => ts_proof_vir::BinOp::Eq,
        Ne => ts_proof_vir::BinOp::Ne,
        Lt => ts_proof_vir::BinOp::Lt,
        Le => ts_proof_vir::BinOp::Le,
        Gt => ts_proof_vir::BinOp::Gt,
        Ge => ts_proof_vir::BinOp::Ge,
        And => ts_proof_vir::BinOp::And,
        Or => ts_proof_vir::BinOp::Or,
    }
}

fn promise_method<'a>(callee: &Callee, args: &'a [Ast], field: &str) -> Option<&'a Ast> {
    let Callee::Member { object, field: got } = callee else {
        return None;
    };
    let Ast::Ident(name) = object.as_ref() else {
        return None;
    };
    if name == "Promise" && got == field && args.len() == 1 {
        Some(&args[0])
    } else {
        None
    }
}

fn contains_effect(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Effect { .. } => true,
        Stmt::If {
            then_branch,
            else_branch,
            ..
        } => contains_effect(then_branch) || contains_effect(else_branch),
        Stmt::While { body, .. } => contains_effect(body),
        Stmt::Assign { .. } | Stmt::Return { .. } | Stmt::Throw { .. } => false,
    })
}

fn exits(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
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

fn expr_calls_effect(expr: &Ast) -> bool {
    match expr {
        Ast::Call { callee, .. } => !matches!(callee, Callee::Ident(name) if name != "eval"),
        Ast::Unary { expr, .. } | Ast::Member { object: expr, .. } => expr_calls_effect(expr),
        Ast::Binary { left, right, .. } => expr_calls_effect(left) || expr_calls_effect(right),
        Ast::Ternary {
            cond,
            then_expr,
            else_expr,
            ..
        } => expr_calls_effect(cond) || expr_calls_effect(then_expr) || expr_calls_effect(else_expr),
        Ast::Array { items, .. } => items.iter().any(expr_calls_effect),
        Ast::Object { fields, .. } => fields.iter().any(|(_, v)| expr_calls_effect(v)),
        Ast::Arrow { body, .. } => expr_calls_effect(body),
        Ast::Bool(_) | Ast::Int(_) | Ast::Str(_) | Ast::Null | Ast::Ident(_) => false,
    }
}

fn subst_stmts(stmts: &[AstStmt], map: &BTreeMap<String, Ast>) -> Vec<AstStmt> {
    stmts.iter().map(|stmt| subst_stmt(stmt, map)).collect()
}

fn subst_stmt(stmt: &AstStmt, map: &BTreeMap<String, Ast>) -> AstStmt {
    match stmt {
        AstStmt::Let { name, init, span } => AstStmt::Let {
            name: name.clone(),
            init: subst_expr(init, map),
            span: span.clone(),
        },
        AstStmt::Assign { name, expr, span } => AstStmt::Assign {
            name: name.clone(),
            expr: subst_expr(expr, map),
            span: span.clone(),
        },
        AstStmt::If {
            cond,
            then_body,
            else_body,
            span,
        } => AstStmt::If {
            cond: subst_expr(cond, map),
            then_body: subst_stmts(then_body, map),
            else_body: subst_stmts(else_body, map),
            span: span.clone(),
        },
        AstStmt::Return { expr, span } => AstStmt::Return {
            expr: expr.as_ref().map(|e| subst_expr(e, map)),
            span: span.clone(),
        },
        AstStmt::While {
            cond,
            invariant,
            body,
            span,
        } => AstStmt::While {
            cond: subst_expr(cond, map),
            invariant: invariant.as_ref().map(|e| subst_expr(e, map)),
            body: subst_stmts(body, map),
            span: span.clone(),
        },
        AstStmt::Expr { expr, span } => AstStmt::Expr {
            expr: subst_expr(expr, map),
            span: span.clone(),
        },
        AstStmt::Try {
            body,
            catch_param,
            catch_body,
            span,
        } => AstStmt::Try {
            body: subst_stmts(body, map),
            catch_param: catch_param.clone(),
            catch_body: subst_stmts(catch_body, map),
            span: span.clone(),
        },
        other => other.clone(),
    }
}

fn subst_expr(expr: &Ast, map: &BTreeMap<String, Ast>) -> Ast {
    match expr {
        Ast::Ident(name) => map.get(name).cloned().unwrap_or_else(|| expr.clone()),
        Ast::Unary { op, expr, span } => Ast::Unary {
            op: *op,
            expr: Box::new(subst_expr(expr, map)),
            span: span.clone(),
        },
        Ast::Binary { op, left, right, span } => Ast::Binary {
            op: *op,
            left: Box::new(subst_expr(left, map)),
            right: Box::new(subst_expr(right, map)),
            span: span.clone(),
        },
        Ast::Ternary {
            cond,
            then_expr,
            else_expr,
            span,
        } => Ast::Ternary {
            cond: Box::new(subst_expr(cond, map)),
            then_expr: Box::new(subst_expr(then_expr, map)),
            else_expr: Box::new(subst_expr(else_expr, map)),
            span: span.clone(),
        },
        Ast::Member { object, field, span } => Ast::Member {
            object: Box::new(subst_expr(object, map)),
            field: field.clone(),
            span: span.clone(),
        },
        Ast::Call { callee, args, span } => Ast::Call {
            callee: subst_callee(callee, map),
            args: args.iter().map(|a| subst_expr(a, map)).collect(),
            span: span.clone(),
        },
        Ast::Array { items, span } => Ast::Array {
            items: items.iter().map(|a| subst_expr(a, map)).collect(),
            span: span.clone(),
        },
        Ast::Object { fields, span } => Ast::Object {
            fields: fields
                .iter()
                .map(|(k, v)| (k.clone(), subst_expr(v, map)))
                .collect(),
            span: span.clone(),
        },
        Ast::Arrow { params, body, span } => Ast::Arrow {
            params: params.clone(),
            body: Box::new(subst_expr(body, map)),
            span: span.clone(),
        },
        other => other.clone(),
    }
}

fn subst_callee(callee: &Callee, map: &BTreeMap<String, Ast>) -> Callee {
    match callee {
        Callee::Ident(name) if !map.contains_key(name) => Callee::Ident(name.clone()),
        Callee::Ident(name) => match map.get(name) {
            Some(Ast::Ident(renamed)) => Callee::Ident(renamed.clone()),
            _ => Callee::Ident(name.clone()),
        },
        Callee::Member { object, field } => Callee::Member {
            object: Box::new(subst_expr(object, map)),
            field: field.clone(),
        },
    }
}

fn prefix_locals(stmts: &[AstStmt], prefix: &str) -> Result<Vec<AstStmt>, Diagnostic> {
    let mut map = BTreeMap::new();
    collect_lets(stmts, prefix, &mut map)?;
    Ok(rename_stmts(stmts, &map))
}

fn collect_lets(
    stmts: &[AstStmt],
    prefix: &str,
    map: &mut BTreeMap<String, String>,
) -> Result<(), Diagnostic> {
    for stmt in stmts {
        match stmt {
            AstStmt::Let { name, span, .. } => {
                if map.contains_key(name) {
                    return Err(bad(span, format!("`{name}` is declared twice")));
                }
                map.insert(name.clone(), format!("{prefix}{name}"));
            }
            AstStmt::If { then_body, else_body, .. } => {
                collect_lets(then_body, prefix, map)?;
                collect_lets(else_body, prefix, map)?;
            }
            AstStmt::While { body, .. } => collect_lets(body, prefix, map)?,
            AstStmt::Try { body, catch_body, .. } => {
                collect_lets(body, prefix, map)?;
                collect_lets(catch_body, prefix, map)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn rename_stmts(stmts: &[AstStmt], map: &BTreeMap<String, String>) -> Vec<AstStmt> {
    stmts.iter().map(|stmt| rename_stmt(stmt, map)).collect()
}

fn rename_stmt(stmt: &AstStmt, map: &BTreeMap<String, String>) -> AstStmt {
    match stmt {
        AstStmt::Let { name, init, span } => AstStmt::Let {
            name: rename(name, map),
            init: rename_expr(init, map),
            span: span.clone(),
        },
        AstStmt::Assign { name, expr, span } => AstStmt::Assign {
            name: rename(name, map),
            expr: rename_expr(expr, map),
            span: span.clone(),
        },
        AstStmt::If {
            cond,
            then_body,
            else_body,
            span,
        } => AstStmt::If {
            cond: rename_expr(cond, map),
            then_body: rename_stmts(then_body, map),
            else_body: rename_stmts(else_body, map),
            span: span.clone(),
        },
        AstStmt::Return { expr, span } => AstStmt::Return {
            expr: expr.as_ref().map(|e| rename_expr(e, map)),
            span: span.clone(),
        },
        AstStmt::While {
            cond,
            invariant,
            body,
            span,
        } => AstStmt::While {
            cond: rename_expr(cond, map),
            invariant: invariant.as_ref().map(|e| rename_expr(e, map)),
            body: rename_stmts(body, map),
            span: span.clone(),
        },
        AstStmt::Expr { expr, span } => AstStmt::Expr {
            expr: rename_expr(expr, map),
            span: span.clone(),
        },
        AstStmt::Try {
            body,
            catch_param,
            catch_body,
            span,
        } => AstStmt::Try {
            body: rename_stmts(body, map),
            catch_param: rename(catch_param, map),
            catch_body: rename_stmts(catch_body, map),
            span: span.clone(),
        },
        other => other.clone(),
    }
}

fn rename_expr(expr: &Ast, map: &BTreeMap<String, String>) -> Ast {
    let ast_map: BTreeMap<String, Ast> = map
        .iter()
        .map(|(k, v)| (k.clone(), Ast::Ident(v.clone())))
        .collect();
    subst_expr(expr, &ast_map)
}

fn rename(name: &str, map: &BTreeMap<String, String>) -> String {
    map.get(name).cloned().unwrap_or_else(|| name.to_string())
}

fn collect_stmts(stmts: &[Stmt], out: &mut BTreeSet<String>) {
    for stmt in stmts {
        match stmt {
            Stmt::Assign { name, expr, .. } => {
                out.insert(name.clone());
                collect_expr(expr, out);
            }
            Stmt::Effect { counter, .. } => {
                out.insert(counter.clone());
            }
            Stmt::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                collect_expr(cond, out);
                collect_stmts(then_branch, out);
                collect_stmts(else_branch, out);
            }
            Stmt::Return { expr, .. } => {
                if let Some(expr) = expr {
                    collect_expr(expr, out);
                }
            }
            Stmt::While {
                cond,
                invariant,
                body,
                ..
            } => {
                collect_expr(cond, out);
                collect_expr(invariant, out);
                collect_stmts(body, out);
            }
            Stmt::Throw { .. } => {}
        }
    }
}

fn collect_expr(expr: &Expr, out: &mut BTreeSet<String>) {
    match expr {
        Expr::Var(name) => {
            out.insert(name.clone());
        }
        Expr::Unary(_, e) => collect_expr(e, out),
        Expr::Binary(_, l, r) => {
            collect_expr(l, out);
            collect_expr(r, out);
        }
        Expr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_expr(cond, out);
            collect_expr(then_expr, out);
            collect_expr(else_expr, out);
        }
        Expr::Bool(_) | Expr::Int(_) | Expr::Str(_) => {}
    }
}

fn scan_stmts(stmts: &[AstStmt], tables: &mut BTreeSet<String>) {
    for stmt in stmts {
        match stmt {
            AstStmt::Let { init, .. } | AstStmt::Assign { expr: init, .. } => scan_expr(init, tables),
            AstStmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                scan_expr(cond, tables);
                scan_stmts(then_body, tables);
                scan_stmts(else_body, tables);
            }
            AstStmt::Return { expr, .. } => {
                if let Some(expr) = expr {
                    scan_expr(expr, tables);
                }
            }
            AstStmt::While { cond, invariant, body, .. } => {
                scan_expr(cond, tables);
                if let Some(inv) = invariant {
                    scan_expr(inv, tables);
                }
                scan_stmts(body, tables);
            }
            AstStmt::Expr { expr, .. } => scan_expr(expr, tables),
            AstStmt::Try { body, catch_body, .. } => {
                scan_stmts(body, tables);
                scan_stmts(catch_body, tables);
            }
            AstStmt::Throw { .. } | AstStmt::Next { .. } => {}
        }
    }
}

fn scan_expr(expr: &Ast, tables: &mut BTreeSet<String>) {
    match expr {
        Ast::Str(sql) => {
            for table in sql_tables(sql) {
                tables.insert(table);
            }
        }
        Ast::Call { callee, args, .. } => {
            if let Callee::Member { object, field: _ } = callee {
                if let Ast::Member { object, field: model, .. } = object.as_ref() {
                    if let Ast::Ident(root) = object.as_ref() {
                        if root == "prisma" {
                            tables.insert(model.clone());
                        }
                    }
                }
                if let Ast::Ident(repo) = object.as_ref() {
                    if repo == "repo" || repo.ends_with("Repository") {
                        tables.insert(repo.clone());
                    }
                }
            }
            for arg in args {
                scan_expr(arg, tables);
            }
        }
        Ast::Unary { expr, .. } | Ast::Member { object: expr, .. } => scan_expr(expr, tables),
        Ast::Binary { left, right, .. } => {
            scan_expr(left, tables);
            scan_expr(right, tables);
        }
        Ast::Ternary {
            cond,
            then_expr,
            else_expr,
            ..
        } => {
            scan_expr(cond, tables);
            scan_expr(then_expr, tables);
            scan_expr(else_expr, tables);
        }
        Ast::Array { items, .. } => {
            for item in items {
                scan_expr(item, tables);
            }
        }
        Ast::Object { fields, .. } => {
            for (_, value) in fields {
                scan_expr(value, tables);
            }
        }
        Ast::Arrow { body, .. } => scan_expr(body, tables),
        Ast::Bool(_) | Ast::Int(_) | Ast::Null | Ast::Ident(_) => {}
    }
}

fn sql_tables(sql: &str) -> Vec<String> {
    let parts: Vec<&str> = sql.split_whitespace().collect();
    let mut out = Vec::new();
    for window in parts.windows(2) {
        let key = window[0].trim_end_matches(';').to_ascii_lowercase();
        if matches!(key.as_str(), "into" | "update" | "from") {
            if let Some(name) = ident_prefix(window[1]) {
                out.push(name.to_string());
            }
        }
    }
    out
}

fn ident_prefix(token: &str) -> Option<&str> {
    let end = token
        .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .unwrap_or(token.len());
    let name = &token[..end];
    if name.is_empty() { None } else { Some(name) }
}

fn span_of(stmts: &[Stmt]) -> Option<Span> {
    stmts.iter().find_map(|stmt| match stmt {
        Stmt::Assign { span, .. }
        | Stmt::If { span, .. }
        | Stmt::Return { span, .. }
        | Stmt::Throw { span }
        | Stmt::While { span, .. }
        | Stmt::Effect { span, .. } => Some(span.clone()),
    })
}

fn flatten(errs: Vec<Diagnostic>) -> Diagnostic {
    let mut iter = errs.into_iter();
    let Some(mut first) = iter.next() else {
        return Diagnostic::new(ErrorCode::Verify011, "adapter failed without a diagnostic");
    };
    for extra in iter {
        first = first.note(format!("{}: {}", extra.code, extra.message));
    }
    first
}

fn bad(span: &Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(ErrorCode::Verify002, message.into()).at(span.clone())
}

fn missing(name: &str) -> Diagnostic {
    Diagnostic::new(ErrorCode::Verify003, format!("unknown function `{name}`"))
}

trait AtIfEmpty {
    fn at_if_empty(self, span: &Span) -> Diagnostic;
}

impl AtIfEmpty for Diagnostic {
    fn at_if_empty(self, span: &Span) -> Diagnostic {
        if self.span.is_none() {
            self.at(span.clone())
        } else {
            self
        }
    }
}
