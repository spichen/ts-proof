//! Recursive-descent parser for the fail-closed TypeScript subset.
//!
//! Semicolons are required. Specification arrows are syntax, not callbacks.
//! `prove` block bodies are lemma lists. Everything else that this grammar
//! does not accept is a diagnostic, not an implicit skip.

use crate::lex::{lex, Tok, Token};
use std::collections::BTreeMap;
use ts_proof_core::{
    BinOp, Callee, ConstDecl, Diagnostic, EndpointLaw, ErrorCode, Expr, External, Function, Law,
    Lemma, Param, Program, Proof, SourceFile, Span, SpecFn, Stmt, TsType, UnaryOp, Decorator,
};

pub fn parse_source(path: &str, source: &str) -> Result<Program, Vec<Diagnostic>> {
    let tokens = lex(path, source).map_err(|d| vec![d])?;
    let mut p = Parser {
        tokens,
        i: 0,
        file: path.to_string(),
        source: source.to_string(),
    };
    p.parse_file().map_err(|d| vec![d])
}

pub fn parse_sources(files: &[(&str, &str)]) -> Result<Program, Vec<Diagnostic>> {
    let mut merged = Program::empty();
    let mut diags = Vec::new();
    for (path, source) in files {
        match parse_source(path, source) {
            Ok(program) => {
                if let Err(d) = merge(&mut merged, program) {
                    diags.extend(d);
                }
            }
            Err(d) => diags.extend(d),
        }
    }
    if diags.is_empty() {
        Ok(merged)
    } else {
        Err(diags)
    }
}

fn merge(into: &mut Program, program: Program) -> Result<(), Vec<Diagnostic>> {
    let mut diags = Vec::new();
    for f in &program.functions {
        if into.function(&f.name).is_some() {
            diags.push(err(&f.span, format!("duplicate function `{}`", f.name)));
        }
    }
    for law in &program.laws {
        if into.laws.iter().any(|e| e.name == law.name) {
            diags.push(err(&law.span, format!("duplicate law `{}`", law.name)));
        }
    }
    for law in &program.endpoint_laws {
        if into.endpoint_laws.iter().any(|e| e.name == law.name) {
            diags.push(err(&law.span, format!("duplicate endpoint law `{}`", law.name)));
        }
    }
    for proof in &program.proofs {
        if into.proofs.iter().any(|e| e.name == proof.name) {
            diags.push(err(&proof.span, format!("duplicate proof `{}`", proof.name)));
        }
    }
    for c in &program.consts {
        if into.consts.iter().any(|e| e.name == c.name)
            || into.laws.iter().any(|l| l.name == c.name)
            || into.endpoint_laws.iter().any(|l| l.name == c.name)
            || into.proofs.iter().any(|p| p.name == c.name)
            || into.externals.contains_key(&c.name)
        {
            diags.push(err(&c.span, format!("duplicate binding `{}`", c.name)));
        }
    }
    if !diags.is_empty() {
        return Err(diags);
    }
    into.files.extend(program.files);
    into.functions.extend(program.functions);
    into.consts.extend(program.consts);
    into.top_level.extend(program.top_level);
    into.laws.extend(program.laws);
    into.endpoint_laws.extend(program.endpoint_laws);
    into.proofs.extend(program.proofs);
    into.externals.extend(program.externals);
    Ok(())
}

struct Parser {
    tokens: Vec<Token>,
    i: usize,
    file: String,
    source: String,
}

impl Parser {
    fn parse_file(&mut self) -> Result<Program, Diagnostic> {
        let mut program = Program::empty();
        program.files.push(SourceFile {
            path: self.file.clone(),
            source: self.source.clone(),
        });
        while !self.is(Tok::Eof) {
            self.item(&mut program)?;
        }
        Ok(program)
    }

    fn item(&mut self, program: &mut Program) -> Result<(), Diagnostic> {
        self.eat_semi();
        if self.is(Tok::Eof) {
            return Ok(());
        }
        if self.eat_ident("import") {
            if self.is(Tok::LParen) {
                return self.fail("import() is outside the supported subset");
            }
            self.skip_import()?;
            return Ok(());
        }
        let exported = self.eat_ident("export");
        if exported && self.eat_ident("default") {
            return self.fail("default exports are outside the supported subset");
        }
        let decorators = self.decorators()?;
        if self.eat_ident("async") {
            self.expect_ident("function")?;
            program.functions.push(self.function(true, decorators, None, Vec::new())?);
            return Ok(());
        }
        if self.eat_ident("function") {
            if !decorators.is_empty() {
                return self.fail("function declarations do not take decorators in this subset");
            }
            program.functions.push(self.function(false, Vec::new(), None, Vec::new())?);
            return Ok(());
        }
        if self.eat_ident("class") {
            self.class(decorators, program)?;
            return Ok(());
        }
        if !decorators.is_empty() {
            return self.fail("decorators are only supported on classes and methods");
        }
        if self.eat_ident("const") || self.eat_ident("let") {
            self.binding(program)?;
            return Ok(());
        }
        if self.is_ident("interface") || self.is_ident("enum") || self.is_ident("type") || self.is_ident("namespace")
        {
            return self.fail("type-only declarations are outside the supported subset");
        }
        let expr = self.expr()?;
        let span = expr.span_hint().cloned().unwrap_or_else(|| self.here());
        self.expect(&Tok::Semi, "expected ';' after expression statement")?;
        program.top_level.push(Stmt::Expr { expr, span });
        Ok(())
    }

    fn class(&mut self, decorators: Vec<Decorator>, program: &mut Program) -> Result<(), Diagnostic> {
        let name = self.ident()?;
        let name_span = self.prev_span();
        self.expect(&Tok::LBrace, "expected '{' to open a class")?;
        while !self.is(Tok::RBrace) && !self.is(Tok::Eof) {
            let method_decs = self.decorators()?;
            if self.eat_ident("constructor") {
                return self.fail("constructors are outside the supported subset");
            }
            let is_async = self.eat_ident("async");
            let method = self.ident()?;
            if matches!(method.as_str(), "public" | "private" | "protected" | "readonly" | "static") {
                return self.fail("parameter properties and access modifiers are outside the supported subset");
            }
            let mut func = self.function_after_name(method, is_async, method_decs)?;
            func.class_name = Some(name.clone());
            func.class_decorators = decorators.clone();
            func.name = format!("{name}.{}", func.name);
            program.functions.push(func);
        }
        self.expect(&Tok::RBrace, "expected '}' to close a class")?;
        let _ = name_span;
        Ok(())
    }

    fn function(
        &mut self,
        is_async: bool,
        decorators: Vec<Decorator>,
        class_name: Option<String>,
        class_decorators: Vec<Decorator>,
    ) -> Result<Function, Diagnostic> {
        let name = self.ident()?;
        let mut func = self.function_after_name(name, is_async, decorators)?;
        func.class_name = class_name;
        func.class_decorators = class_decorators;
        Ok(func)
    }

    fn function_after_name(
        &mut self,
        name: String,
        is_async: bool,
        decorators: Vec<Decorator>,
    ) -> Result<Function, Diagnostic> {
        let start = self.prev_span();
        self.expect(&Tok::LParen, "expected '(' after a function name")?;
        let params = self.params()?;
        self.expect(&Tok::RParen, "expected ')' after parameters")?;
        let ret = if self.eat(&Tok::Colon) {
            Some(self.ts_type()?)
        } else {
            None
        };
        self.expect(&Tok::LBrace, "expected '{' to open a function body")?;
        let body = self.block_stmts()?;
        self.expect(&Tok::RBrace, "expected '}' to close a function body")?;
        let end = self.prev_span();
        Ok(Function {
            name,
            params,
            ret,
            body,
            span: span_merge(&start, &end),
            is_async,
            decorators,
            class_name: None,
            class_decorators: Vec::new(),
        })
    }

    fn params(&mut self) -> Result<Vec<Param>, Diagnostic> {
        let mut out = Vec::new();
        if self.is(Tok::RParen) {
            return Ok(out);
        }
        loop {
            let name = self.ident()?;
            let span = self.prev_span();
            if self.is(Tok::Question) {
                return self.fail("optional parameters are outside the supported subset");
            }
            let ty = if self.eat(&Tok::Colon) {
                Some(self.ts_type()?)
            } else {
                None
            };
            out.push(Param { name, ty, span });
            if !self.eat(&Tok::Comma) {
                break;
            }
            if self.is(Tok::RParen) {
                break;
            }
        }
        Ok(out)
    }

    fn ts_type(&mut self) -> Result<TsType, Diagnostic> {
        let ty = self.ts_primary()?;
        if self.eat(&Tok::OrOr) || self.eat_ident_token_pipe() {
            return self.fail("union types other than `T | null` are outside the supported subset");
        }
        if self.is_ident_raw("|") {
            return self.fail("union types are outside the supported subset");
        }
        // `T | null` uses the `|` token, which the lexer rejects as bitwise OR.
        // Accept the two-character form by... the lexer already errors on a single `|`.
        // So `T | null` cannot be lexed. Documented limitation: nullable is written
        // only if we special-case. The lexer rejects `|`. Callers that need
        // `Token | null` should use a supported annotation or omit it.
        Ok(ty)
    }

    fn ts_primary(&mut self) -> Result<TsType, Diagnostic> {
        let name = self.ident()?;
        let ty = match name.as_str() {
            "boolean" | "bool" => TsType::Bool,
            "bigint" => TsType::Int,
            "string" => TsType::String,
            "void" => TsType::Void,
            "null" | "undefined" => TsType::Null,
            "number" => {
                return self.fail("the number type is outside the supported subset; use bigint");
            }
            "any" | "unknown" | "never" | "object" | "symbol" => {
                return self.fail(format!("type `{name}` is outside the supported subset"));
            }
            "Promise" => {
                self.expect(&Tok::Lt, "expected '<' after Promise")?;
                let inner = self.ts_primary()?;
                self.expect(&Tok::Gt, "expected '>' after a Promise type argument")?;
                TsType::Promise(Box::new(inner))
            }
            other => TsType::Named(other.to_string()),
        };
        Ok(ty)
    }

    fn binding(&mut self, program: &mut Program) -> Result<(), Diagnostic> {
        let name = self.ident()?;
        let span = self.prev_span();
        if self.eat(&Tok::Colon) {
            let _ = self.ts_type()?;
        }
        self.expect(&Tok::Eq, "expected '=' in a const binding")?;
        if self.is_ident("prove") {
            let proof = self.prove(&name, &span)?;
            self.expect(&Tok::Semi, "expected ';' after prove")?;
            program.proofs.push(proof);
            return Ok(());
        }
        let expr = self.expr()?;
        self.expect(&Tok::Semi, "expected ';' after a const binding")?;
        if let Some(external) = self.as_external(&expr)? {
            program.externals.insert(name, external);
            return Ok(());
        }
        if let Some(law) = self.as_law(&name, &expr)? {
            program.laws.push(law);
            return Ok(());
        }
        if let Some(law) = self.as_endpoint_law(&name, &expr)? {
            program.endpoint_laws.push(law);
            return Ok(());
        }
        if !trusted_const(&expr) && contains_call(&expr) {
            return Err(err(
                &span,
                "a top-level call must be express(), Router(), new Pool(...), or a LAW/PROOF declaration",
            ));
        }
        program.consts.push(ConstDecl { name, expr, span });
        Ok(())
    }

    fn prove(&mut self, name: &str, span: &Span) -> Result<Proof, Diagnostic> {
        self.expect_ident("prove")?;
        self.expect(&Tok::LParen, "expected '(' after prove")?;
        let law = self.ident()?;
        self.expect(&Tok::Comma, "expected a law name and a proof arrow")?;
        let _params = self.arrow_params()?;
        self.expect(&Tok::LBrace, "expected '{' to open a proof body")?;
        let mut lemmas = Vec::new();
        while !self.is(Tok::RBrace) && !self.is(Tok::Eof) {
            self.expect_ident("lemma")?;
            let lemma_span = self.prev_span();
            self.expect(&Tok::LParen, "expected '(' after lemma")?;
            let (lemma_name, expr) = if self.is_str() {
                let n = self.string()?;
                self.expect(&Tok::Comma, "expected an expression after a lemma name")?;
                (Some(n), self.expr()?)
            } else {
                (None, self.expr()?)
            };
            self.expect(&Tok::RParen, "expected ')' after a lemma")?;
            self.expect(&Tok::Semi, "expected ';' after a lemma")?;
            lemmas.push(Lemma {
                name: lemma_name,
                expr,
                span: lemma_span,
                depends_on: Vec::new(),
            });
        }
        self.expect(&Tok::RBrace, "expected '}' to close a proof body")?;
        self.expect(&Tok::RParen, "expected ')' after prove")?;
        if lemmas.is_empty() {
            return Err(err(span, "a proof must contain at least one lemma"));
        }
        Ok(Proof {
            name: name.to_string(),
            law,
            lemmas,
            span: span.clone(),
        })
    }

    fn as_external(&self, expr: &Expr) -> Result<Option<External>, Diagnostic> {
        let Expr::Call { callee, args, span } = expr else {
            return Ok(None);
        };
        let Callee::Ident(name) = callee else {
            return Ok(None);
        };
        if name == "external" {
            let Some(Expr::Str(effect)) = args.first() else {
                return Err(err(span, "external() needs an effect-name string"));
            };
            if args.len() != 1 {
                return Err(err(span, "external() takes one string"));
            }
            check_effect(effect, span)?;
            return Ok(Some(External::Function {
                effect: effect.clone(),
                span: span.clone(),
            }));
        }
        if name == "externalNamespace" {
            let Some(Expr::Object { fields, .. }) = args.first() else {
                return Err(err(span, "externalNamespace() needs an object literal"));
            };
            if args.len() != 1 {
                return Err(err(span, "externalNamespace() takes one object"));
            }
            let mut methods = BTreeMap::new();
            for (method, value) in fields {
                let Expr::Str(effect) = value else {
                    return Err(err(span, format!("external method `{method}` needs a string effect name")));
                };
                check_effect(effect, span)?;
                methods.insert(method.clone(), effect.clone());
            }
            return Ok(Some(External::Namespace {
                methods,
                span: span.clone(),
            }));
        }
        Ok(None)
    }

    fn as_law(&self, binding: &str, expr: &Expr) -> Result<Option<Law>, Diagnostic> {
        let Some((args, span)) = call_named(expr, "law") else {
            return Ok(None);
        };
        let fields = object_fields(args, span, "law")?;
        reject_unknown(&fields, &["target", "inputs", "requires", "ensures", "name"], span)?;
        let target = match fields.get("target") {
            Some(Expr::Ident(name)) => name.clone(),
            _ => return Err(err(span, "law.target must be a function name")),
        };
        if let Some(inputs) = fields.get("inputs") {
            check_inputs(inputs, span)?;
        }
        let requires = optional_spec(fields.get("requires").copied(), span, "requires")?;
        let ensures = optional_spec(fields.get("ensures").copied(), span, "ensures")?;
        if ensures.is_none() && requires.is_none() {
            return Err(err(span, "a law needs requires or ensures"));
        }
        let name = match fields.get("name") {
            Some(Expr::Str(n)) => n.clone(),
            Some(_) => return Err(err(span, "law.name must be a string")),
            None => binding.to_string(),
        };
        let _ = name;
        Ok(Some(Law {
            name: binding.to_string(),
            target,
            requires,
            ensures,
            span: span.clone(),
        }))
    }

    fn as_endpoint_law(&self, binding: &str, expr: &Expr) -> Result<Option<EndpointLaw>, Diagnostic> {
        let Some((args, span)) = call_named(expr, "endpointLaw") else {
            return Ok(None);
        };
        let fields = object_fields(args, span, "endpointLaw")?;
        reject_unknown(
            &fields,
            &["method", "path", "name", "requires", "ensures"],
            span,
        )?;
        let method = match fields.get("method") {
            Some(Expr::Str(m)) => m.to_ascii_uppercase(),
            _ => return Err(err(span, "endpointLaw.method must be a string")),
        };
        let path = match fields.get("path") {
            Some(Expr::Str(p)) => p.clone(),
            _ => return Err(err(span, "endpointLaw.path must be a string literal")),
        };
        if path.contains('*') {
            return Err(err(span, "wildcard endpoint paths are unsupported"));
        }
        let name = match fields.get("name") {
            Some(Expr::Str(n)) => n.clone(),
            Some(_) => return Err(err(span, "endpointLaw.name must be a string")),
            None => binding.to_string(),
        };
        let requires = optional_spec(fields.get("requires").copied(), span, "requires")?;
        let ensures = match optional_spec(fields.get("ensures").copied(), span, "ensures")? {
            Some(spec) => spec,
            None => return Err(err(span, "endpointLaw.ensures is required")),
        };
        Ok(Some(EndpointLaw {
            name,
            method,
            path,
            requires,
            ensures,
            span: span.clone(),
        }))
    }

    fn block_stmts(&mut self) -> Result<Vec<Stmt>, Diagnostic> {
        let mut out = Vec::new();
        while !self.is(Tok::RBrace) && !self.is(Tok::Eof) {
            self.eat_semi();
            if self.is(Tok::RBrace) {
                break;
            }
            out.push(self.stmt()?);
        }
        Ok(out)
    }

    fn stmt(&mut self) -> Result<Stmt, Diagnostic> {
        if self.is_ident("function") || self.is_ident("class") || self.is_ident("async") {
            return self.fail("nested functions are outside the supported subset");
        }
        if self.eat_ident("const") || self.eat_ident("let") {
            if self.is(Tok::LBrace) || self.is(Tok::LBrack) {
                return self.fail("destructuring bindings are outside the supported subset");
            }
            let name = self.ident()?;
            let span = self.prev_span();
            if self.eat(&Tok::Colon) {
                let _ = self.ts_type()?;
            }
            self.expect(&Tok::Eq, "expected '=' in a binding")?;
            let init = self.expr()?;
            self.expect(&Tok::Semi, "expected ';' after a binding")?;
            return Ok(Stmt::Let { name, init, span });
        }
        if self.eat_ident("return") {
            let span = self.prev_span();
            let expr = if self.is(Tok::Semi) {
                None
            } else {
                Some(self.expr()?)
            };
            self.expect(&Tok::Semi, "expected ';' after return")?;
            return Ok(Stmt::Return { expr, span });
        }
        if self.eat_ident("throw") {
            let span = self.prev_span();
            if !self.is(Tok::Semi) {
                let _ = self.expr()?;
            }
            self.expect(&Tok::Semi, "expected ';' after throw")?;
            return Ok(Stmt::Throw { span });
        }
        if self.eat_ident("if") {
            return self.if_stmt();
        }
        if self.eat_ident("while") {
            return self.while_stmt();
        }
        if self.eat_ident("try") {
            return self.try_stmt();
        }
        if self.eat_ident("for") || self.eat_ident("switch") || self.eat_ident("do") {
            return self.fail("for, switch, and do are outside the supported subset");
        }
        if self.is_ident("var") {
            return self.fail("var is outside the supported subset; use const or let");
        }
        // Assignment `name = expr`, or an expression statement.
        if self.is_assign_target() {
            let name = self.ident()?;
            let span = self.prev_span();
            self.expect(&Tok::Eq, "expected '='")?;
            let expr = self.expr()?;
            self.expect(&Tok::Semi, "expected ';' after an assignment")?;
            return Ok(Stmt::Assign { name, expr, span });
        }
        let expr = self.expr()?;
        let span = expr.span_hint().cloned().unwrap_or_else(|| self.here());
        self.expect(&Tok::Semi, "expected ';' after an expression statement")?;
        Ok(Stmt::Expr { expr, span })
    }

    fn is_assign_target(&self) -> bool {
        let Some(Tok::Ident(_)) = self.kind() else {
            return false;
        };
        matches!(self.tokens.get(self.i + 1).map(|t| &t.kind), Some(Tok::Eq))
    }

    fn if_stmt(&mut self) -> Result<Stmt, Diagnostic> {
        let span = self.prev_span();
        self.expect(&Tok::LParen, "expected '(' after if")?;
        let cond = self.expr()?;
        self.expect(&Tok::RParen, "expected ')' after an if condition")?;
        let then_body = self.brace_or_stmt()?;
        let else_body = if self.eat_ident("else") {
            if self.eat_ident("if") {
                vec![self.if_stmt()?]
            } else {
                self.brace_or_stmt()?
            }
        } else {
            Vec::new()
        };
        Ok(Stmt::If {
            cond,
            then_body,
            else_body,
            span,
        })
    }

    fn while_stmt(&mut self) -> Result<Stmt, Diagnostic> {
        let span = self.prev_span();
        self.expect(&Tok::LParen, "expected '(' after while")?;
        let cond = self.expr()?;
        self.expect(&Tok::RParen, "expected ')' after a while condition")?;
        self.expect(&Tok::LBrace, "expected '{' to open a while body")?;
        let invariant = if let Some(Tok::Invariant(text)) = self.kind().cloned() {
            self.bump();
            Some(parse_invariant(&self.file, &text, &self.prev_span())?)
        } else {
            None
        };
        let body = self.block_stmts()?;
        self.expect(&Tok::RBrace, "expected '}' to close a while body")?;
        Ok(Stmt::While {
            cond,
            invariant,
            body,
            span,
        })
    }

    fn try_stmt(&mut self) -> Result<Stmt, Diagnostic> {
        let span = self.prev_span();
        self.expect(&Tok::LBrace, "expected '{' after try")?;
        let body = self.block_stmts()?;
        self.expect(&Tok::RBrace, "expected '}' after a try body")?;
        self.expect_ident("catch")?;
        self.expect(&Tok::LParen, "expected '(' after catch")?;
        let catch_param = self.ident()?;
        self.expect(&Tok::RParen, "expected ')' after a catch binding")?;
        self.expect(&Tok::LBrace, "expected '{' to open a catch body")?;
        let catch_body = self.block_stmts()?;
        self.expect(&Tok::RBrace, "expected '}' to close a catch body")?;
        Ok(Stmt::Try {
            body,
            catch_param,
            catch_body,
            span,
        })
    }

    fn brace_or_stmt(&mut self) -> Result<Vec<Stmt>, Diagnostic> {
        if self.eat(&Tok::LBrace) {
            let body = self.block_stmts()?;
            self.expect(&Tok::RBrace, "expected '}'")?;
            Ok(body)
        } else {
            Ok(vec![self.stmt()?])
        }
    }

    fn decorators(&mut self) -> Result<Vec<Decorator>, Diagnostic> {
        let mut out = Vec::new();
        while self.eat(&Tok::At) {
            let span = self.prev_span();
            let name = self.ident()?;
            let args = if self.eat(&Tok::LParen) {
                let args = self.arg_list()?;
                self.expect(&Tok::RParen, "expected ')' after decorator arguments")?;
                args
            } else {
                Vec::new()
            };
            out.push(Decorator { name, args, span });
        }
        Ok(out)
    }

    fn expr(&mut self) -> Result<Expr, Diagnostic> {
        self.ternary()
    }

    fn ternary(&mut self) -> Result<Expr, Diagnostic> {
        let cond = self.or_expr()?;
        if self.eat(&Tok::Question) {
            let span = self.prev_span();
            let then_expr = self.expr()?;
            self.expect(&Tok::Colon, "expected ':' in a conditional expression")?;
            let else_expr = self.ternary()?;
            return Ok(Expr::Ternary {
                cond: Box::new(cond),
                then_expr: Box::new(then_expr),
                else_expr: Box::new(else_expr),
                span,
            });
        }
        Ok(cond)
    }

    fn or_expr(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.and_expr()?;
        while self.eat(&Tok::OrOr) {
            let span = self.prev_span();
            let right = self.and_expr()?;
            left = bin(BinOp::Or, left, right, span);
        }
        Ok(left)
    }

    fn and_expr(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.eq_expr()?;
        while self.eat(&Tok::AndAnd) {
            let span = self.prev_span();
            let right = self.eq_expr()?;
            left = bin(BinOp::And, left, right, span);
        }
        Ok(left)
    }

    fn eq_expr(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.rel()?;
        loop {
            let op = if self.eat(&Tok::EqEqEq) {
                BinOp::Eq
            } else if self.eat(&Tok::NotEqEq) {
                BinOp::Ne
            } else {
                break;
            };
            let span = self.prev_span();
            let right = self.rel()?;
            left = bin(op, left, right, span);
        }
        Ok(left)
    }

    fn rel(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.add()?;
        loop {
            let op = if self.eat(&Tok::Lt) {
                BinOp::Lt
            } else if self.eat(&Tok::Le) {
                BinOp::Le
            } else if self.eat(&Tok::Gt) {
                BinOp::Gt
            } else if self.eat(&Tok::Ge) {
                BinOp::Ge
            } else {
                break;
            };
            let span = self.prev_span();
            let right = self.add()?;
            left = bin(op, left, right, span);
        }
        Ok(left)
    }

    fn add(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.mul()?;
        loop {
            let op = if self.eat(&Tok::Plus) {
                BinOp::Add
            } else if self.eat(&Tok::Minus) {
                BinOp::Sub
            } else {
                break;
            };
            let span = self.prev_span();
            let right = self.mul()?;
            left = bin(op, left, right, span);
        }
        Ok(left)
    }

    fn mul(&mut self) -> Result<Expr, Diagnostic> {
        let mut left = self.unary()?;
        while self.eat(&Tok::Star) {
            let span = self.prev_span();
            let right = self.unary()?;
            left = bin(BinOp::Mul, left, right, span);
        }
        Ok(left)
    }

    fn unary(&mut self) -> Result<Expr, Diagnostic> {
        if self.eat_ident("await") {
            return self.unary();
        }
        if self.eat_ident("new") {
            let span = self.prev_span();
            let name = self.ident()?;
            if name != "Pool" {
                return Err(err(&span, "only `new Pool(...)` is a supported constructor"));
            }
            self.expect(&Tok::LParen, "expected '(' after Pool")?;
            let args = self.arg_list()?;
            self.expect(&Tok::RParen, "expected ')' after Pool arguments")?;
            return Ok(Expr::Call {
                callee: Callee::Ident("Pool".into()),
                args,
                span,
            });
        }
        if self.eat(&Tok::Bang) {
            let span = self.prev_span();
            let expr = self.unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Not,
                expr: Box::new(expr),
                span,
            });
        }
        if self.eat(&Tok::Minus) {
            let span = self.prev_span();
            let expr = self.unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(expr),
                span,
            });
        }
        if self.eat_ident("typeof") || self.eat_ident("void") || self.eat_ident("delete") {
            return self.fail("typeof, void, and delete are outside the supported subset");
        }
        self.postfix()
    }

    fn postfix(&mut self) -> Result<Expr, Diagnostic> {
        let mut expr = self.primary()?;
        loop {
            if self.eat(&Tok::Dot) {
                let span = self.prev_span();
                let field = self.ident()?;
                if self.is(Tok::LParen) {
                    self.bump();
                    let args = self.arg_list()?;
                    self.expect(&Tok::RParen, "expected ')' after arguments")?;
                    expr = Expr::Call {
                        callee: Callee::Member {
                            object: Box::new(expr),
                            field,
                        },
                        args,
                        span,
                    };
                } else {
                    expr = Expr::Member {
                        object: Box::new(expr),
                        field,
                        span,
                    };
                }
            } else if self.is(Tok::LParen) {
                let span = expr.span_hint().cloned().unwrap_or_else(|| self.here());
                self.bump();
                let args = self.arg_list()?;
                self.expect(&Tok::RParen, "expected ')' after arguments")?;
                let callee = match expr {
                    Expr::Ident(name) => Callee::Ident(name),
                    _ => {
                        return Err(err(
                            &span,
                            "only named functions and methods can be called",
                        ));
                    }
                };
                expr = Expr::Call { callee, args, span };
            } else {
                break;
            }
        }
        Ok(expr)
    }

    fn primary(&mut self) -> Result<Expr, Diagnostic> {
        if self.is_arrow_start() {
            return self.arrow_expr();
        }
        let start = self.here();
        match self.kind().cloned() {
            Some(Tok::Ident(name)) => {
                self.bump();
                match name.as_str() {
                    "true" => Ok(Expr::Bool(true)),
                    "false" => Ok(Expr::Bool(false)),
                    "null" | "undefined" => Ok(Expr::Null),
                    "eval" => Err(err(&self.prev_span(), "eval is outside the supported subset")),
                    _ => Ok(Expr::Ident(name)),
                }
            }
            Some(Tok::Int(n)) => {
                self.bump();
                Ok(Expr::Int(n))
            }
            Some(Tok::Str(s)) => {
                self.bump();
                Ok(Expr::Str(s))
            }
            Some(Tok::LParen) => {
                self.bump();
                let expr = self.expr()?;
                self.expect(&Tok::RParen, "expected ')'")?;
                Ok(expr)
            }
            Some(Tok::LBrack) => {
                self.bump();
                let mut items = Vec::new();
                if !self.is(Tok::RBrack) {
                    loop {
                        items.push(self.expr()?);
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                        if self.is(Tok::RBrack) {
                            break;
                        }
                    }
                }
                self.expect(&Tok::RBrack, "expected ']'")?;
                Ok(Expr::Array {
                    items,
                    span: span_merge(&start, &self.prev_span()),
                })
            }
            Some(Tok::LBrace) => self.object(start),
            Some(Tok::Invariant(_)) => self.fail("@invariant belongs at the start of a while body"),
            _ => self.fail("expected an expression"),
        }
    }

    fn object(&mut self, start: Span) -> Result<Expr, Diagnostic> {
        self.expect(&Tok::LBrace, "expected '{'")?;
        let mut fields = Vec::new();
        if !self.is(Tok::RBrace) {
            loop {
                let key = if self.is_str() {
                    self.string()?
                } else {
                    self.ident()?
                };
                self.expect(&Tok::Colon, "expected ':' in an object literal")?;
                let value = self.expr()?;
                fields.push((key, value));
                if !self.eat(&Tok::Comma) {
                    break;
                }
                if self.is(Tok::RBrace) {
                    break;
                }
            }
        }
        self.expect(&Tok::RBrace, "expected '}'")?;
        Ok(Expr::Object {
            fields,
            span: span_merge(&start, &self.prev_span()),
        })
    }

    fn is_arrow_start(&self) -> bool {
        match self.kind() {
            Some(Tok::Ident(_)) => matches!(self.tokens.get(self.i + 1).map(|t| &t.kind), Some(Tok::Arrow)),
            Some(Tok::LParen) => self.looks_like_arrow_params(),
            _ => false,
        }
    }

    fn looks_like_arrow_params(&self) -> bool {
        let mut i = self.i + 1;
        let mut depth = 1;
        while i < self.tokens.len() {
            match &self.tokens[i].kind {
                Tok::LParen | Tok::LBrace | Tok::LBrack => depth += 1,
                Tok::RParen | Tok::RBrace | Tok::RBrack => {
                    depth -= 1;
                    if depth == 0 {
                        return matches!(self.tokens.get(i + 1).map(|t| &t.kind), Some(Tok::Arrow));
                    }
                }
                Tok::Eof => return false,
                _ => {}
            }
            i += 1;
        }
        false
    }

    fn arrow_expr(&mut self) -> Result<Expr, Diagnostic> {
        let span = self.here();
        let params = self.arrow_params()?;
        if self.is(Tok::LBrace) {
            return self.fail("this arrow needs an expression body; proof arrows belong in prove(...)");
        }
        let body = self.expr()?;
        Ok(Expr::Arrow {
            params,
            body: Box::new(body),
            span,
        })
    }

    fn arrow_params(&mut self) -> Result<Vec<String>, Diagnostic> {
        if let Some(Tok::Ident(_)) = self.kind() {
            if matches!(self.tokens.get(self.i + 1).map(|t| &t.kind), Some(Tok::Arrow)) {
                let name = self.ident()?;
                self.expect(&Tok::Arrow, "expected '=>'" )?;
                return Ok(vec![name]);
            }
        }
        self.expect(&Tok::LParen, "expected '(' before arrow parameters")?;
        let mut params = Vec::new();
        if self.eat(&Tok::LBrace) {
            if !self.is(Tok::RBrace) {
                loop {
                    params.push(self.ident()?);
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                    if self.is(Tok::RBrace) {
                        break;
                    }
                }
            }
            self.expect(&Tok::RBrace, "expected '}' after destructured parameters")?;
            self.expect(&Tok::RParen, "expected ')' after arrow parameters")?;
            self.expect(&Tok::Arrow, "expected '=>'" )?;
            return Ok(params);
        }
        if !self.is(Tok::RParen) {
            loop {
                params.push(self.ident()?);
                if self.eat(&Tok::Colon) {
                    let _ = self.ts_type()?;
                }
                if !self.eat(&Tok::Comma) {
                    break;
                }
                if self.is(Tok::RParen) {
                    break;
                }
            }
        }
        self.expect(&Tok::RParen, "expected ')' after arrow parameters")?;
        self.expect(&Tok::Arrow, "expected '=>'" )?;
        Ok(params)
    }

    fn arg_list(&mut self) -> Result<Vec<Expr>, Diagnostic> {
        let mut args = Vec::new();
        if self.is(Tok::RParen) {
            return Ok(args);
        }
        loop {
            args.push(self.expr()?);
            if !self.eat(&Tok::Comma) {
                break;
            }
            if self.is(Tok::RParen) {
                break;
            }
        }
        Ok(args)
    }

    fn skip_import(&mut self) -> Result<(), Diagnostic> {
        let mut depth = 0;
        while !self.is(Tok::Eof) {
            if depth == 0 && self.is(Tok::Semi) {
                self.bump();
                return Ok(());
            }
            match self.kind() {
                Some(Tok::LParen | Tok::LBrace | Tok::LBrack) => depth += 1,
                Some(Tok::RParen | Tok::RBrace | Tok::RBrack) => depth -= 1,
                _ => {}
            }
            self.bump();
        }
        self.fail("unterminated import")
    }

    fn eat_ident(&mut self, name: &str) -> bool {
        if self.is_ident(name) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect_ident(&mut self, name: &str) -> Result<(), Diagnostic> {
        if self.eat_ident(name) {
            Ok(())
        } else {
            self.fail(format!("expected `{name}`"))
        }
    }

    fn ident(&mut self) -> Result<String, Diagnostic> {
        match self.kind().cloned() {
            Some(Tok::Ident(name)) => {
                self.bump();
                Ok(name)
            }
            _ => self.fail("expected an identifier"),
        }
    }

    fn string(&mut self) -> Result<String, Diagnostic> {
        match self.kind().cloned() {
            Some(Tok::Str(s)) => {
                self.bump();
                Ok(s)
            }
            _ => self.fail("expected a string"),
        }
    }

    fn is_str(&self) -> bool {
        matches!(self.kind(), Some(Tok::Str(_)))
    }

    fn is_ident(&self, name: &str) -> bool {
        matches!(self.kind(), Some(Tok::Ident(n)) if n == name)
    }

    fn is_ident_raw(&self, name: &str) -> bool {
        self.is_ident(name)
    }

    fn eat_ident_token_pipe(&mut self) -> bool {
        false
    }

    fn is(&self, kind: Tok) -> bool {
        match (self.kind(), &kind) {
            (Some(Tok::Eof), Tok::Eof) => true,
            (Some(a), b) => std::mem::discriminant(a) == std::mem::discriminant(b) && !matches!(a, Tok::Ident(_) | Tok::Str(_) | Tok::Int(_) | Tok::Invariant(_)),
            _ => false,
        }
    }

    fn eat(&mut self, kind: &Tok) -> bool {
        if self.is(kind.clone()) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn eat_semi(&mut self) {
        while self.is(Tok::Semi) {
            self.bump();
        }
    }

    fn expect(&mut self, kind: &Tok, message: &str) -> Result<(), Diagnostic> {
        if self.eat(kind) {
            Ok(())
        } else {
            self.fail(message)
        }
    }

    fn kind(&self) -> Option<&Tok> {
        self.tokens.get(self.i).map(|t| &t.kind)
    }

    fn bump(&mut self) {
        if self.i < self.tokens.len() {
            self.i += 1;
        }
    }

    fn here(&self) -> Span {
        self.tokens
            .get(self.i)
            .map(|t| t.span.clone())
            .unwrap_or_else(|| Span::new(&self.file, 0, 0))
    }

    fn prev_span(&self) -> Span {
        self.tokens
            .get(self.i.saturating_sub(1))
            .map(|t| t.span.clone())
            .unwrap_or_else(|| self.here())
    }

    fn fail<T>(&self, message: impl Into<String>) -> Result<T, Diagnostic> {
        Err(err(&self.here(), message))
    }
}

fn parse_invariant(file: &str, text: &str, span: &Span) -> Result<Expr, Diagnostic> {
    let wrapped = format!("({text})");
    let tokens = lex(file, &wrapped)?;
    let mut p = Parser {
        tokens,
        i: 0,
        file: file.to_string(),
        source: wrapped,
    };
    let expr = p.expr().map_err(|d| {
        err(span, format!("could not parse @invariant: {}", d.message))
    })?;
    Ok(expr)
}

fn bin(op: BinOp, left: Expr, right: Expr, span: Span) -> Expr {
    Expr::Binary {
        op,
        left: Box::new(left),
        right: Box::new(right),
        span,
    }
}

fn err(span: &Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::new(ErrorCode::Verify002, message.into()).at(span.clone())
}

fn span_merge(a: &Span, b: &Span) -> Span {
    Span::new(a.file.clone(), a.start, b.end.max(a.end))
}

fn call_named<'a>(expr: &'a Expr, name: &str) -> Option<(&'a [Expr], &'a Span)> {
    let Expr::Call { callee, args, span } = expr else {
        return None;
    };
    let Callee::Ident(n) = callee else {
        return None;
    };
    if n == name {
        Some((args, span))
    } else {
        None
    }
}

fn object_fields<'a>(
    args: &'a [Expr],
    span: &Span,
    what: &str,
) -> Result<BTreeMap<&'a str, &'a Expr>, Diagnostic> {
    if args.len() != 1 {
        return Err(err(span, format!("{what}() takes one object literal")));
    }
    let Expr::Object { fields, .. } = &args[0] else {
        return Err(err(span, format!("{what}() takes an object literal")));
    };
    let mut map = BTreeMap::new();
    for (key, value) in fields {
        if map.insert(key.as_str(), value).is_some() {
            return Err(err(span, format!("duplicate field `{key}`")));
        }
    }
    Ok(map)
}

fn reject_unknown(fields: &BTreeMap<&str, &Expr>, allowed: &[&str], span: &Span) -> Result<(), Diagnostic> {
    for key in fields.keys() {
        if !allowed.contains(key) {
            return Err(err(span, format!("unsupported field `{key}`")));
        }
    }
    Ok(())
}

fn optional_spec(expr: Option<&Expr>, span: &Span, what: &str) -> Result<Option<SpecFn>, Diagnostic> {
    let Some(expr) = expr else {
        return Ok(None);
    };
    let Expr::Arrow { params, body, span: arrow_span } = expr else {
        return Err(err(span, format!("{what} must be an arrow")));
    };
    Ok(Some(SpecFn {
        params: params.clone(),
        body: body.as_ref().clone(),
        span: arrow_span.clone(),
    }))
}

fn check_inputs(expr: &Expr, span: &Span) -> Result<(), Diagnostic> {
    let Expr::Object { fields, .. } = expr else {
        return Err(err(span, "inputs must be an object of type markers"));
    };
    for (name, value) in fields {
        let Expr::Call { callee, args, .. } = value else {
            return Err(err(span, format!("input `{name}` must be int(), bool(), or string()")));
        };
        let Callee::Ident(marker) = callee else {
            return Err(err(span, format!("input `{name}` must be a type marker")));
        };
        if !matches!(marker.as_str(), "int" | "bool" | "string" | "bigint") || !args.is_empty() {
            return Err(err(span, format!("input `{name}` must be int(), bool(), or string()")));
        }
    }
    Ok(())
}

fn check_effect(effect: &str, span: &Span) -> Result<(), Diagnostic> {
    if effect.is_empty()
        || !effect
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '.' || c == '_')
    {
        return Err(err(span, format!("unsupported effect name `{effect}`")));
    }
    Ok(())
}

fn trusted_const(expr: &Expr) -> bool {
    match expr {
        Expr::Call { callee, .. } => match callee {
            Callee::Ident(name) => matches!(name.as_str(), "express" | "Router" | "Pool"),
            _ => false,
        },
        _ => !contains_call(expr),
    }
}

fn contains_call(expr: &Expr) -> bool {
    match expr {
        Expr::Call { .. } => true,
        Expr::Unary { expr, .. } | Expr::Member { object: expr, .. } => contains_call(expr),
        Expr::Binary { left, right, .. } => contains_call(left) || contains_call(right),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
            ..
        } => contains_call(cond) || contains_call(then_expr) || contains_call(else_expr),
        Expr::Array { items, .. } => items.iter().any(contains_call),
        Expr::Object { fields, .. } => fields.iter().any(|(_, v)| contains_call(v)),
        Expr::Arrow { body, .. } => contains_call(body),
        Expr::Bool(_) | Expr::Int(_) | Expr::Str(_) | Expr::Null | Expr::Ident(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_expiry_law_route_query_and_prisma() {
        let src = r#"
            function calculateExpiry(now: bigint, ttl: bigint): bigint {
                return now + ttl;
            }
            const expiryLaw = law({
                target: calculateExpiry,
                inputs: { now: int(), ttl: int() },
                requires: ({ now, ttl }) => now.gte(0).and(ttl.gt(0)),
                ensures: ({ now, ttl }) => call(calculateExpiry, now, ttl).gt(now),
            });
            const app = express();
            const pool = new Pool({});
            app.post("/agents/:id/tokens", authenticate, authorize, mintToken);
            pool.query("INSERT INTO tokens(agent_id) VALUES($1)", [agentId]);
            prisma.token.create({ data: { agentId: agentId } });
        "#;
        let program = parse_source("sample.ts", src).expect("parse");
        assert!(program.function("calculateExpiry").is_some());
        assert_eq!(program.laws.len(), 1);
        assert!(program.laws[0].ensures.is_some());
        assert_eq!(program.top_level.len(), 3);
    }

    #[test]
    fn rejects_abstract_equality_division_floats_eval_and_asi() {
        assert!(parse_source("a.ts", "function f(x: bigint): bigint { return x == 1; }").is_err());
        assert!(parse_source("a.ts", "function f(x: bigint): bigint { return x / 1n; }").is_err());
        assert!(parse_source("a.ts", "function f(): bigint { return 1.5; }").is_err());
        assert!(parse_source("a.ts", "function f() { eval(\"1\"); }").is_err());
        assert!(parse_source("a.ts", "function f(x: bigint): bigint { return x }").is_err());
    }
}
