//! Fail-closed lexer for the supported TypeScript subset.
//!
//! `==` and `!=` are errors. `/` is an error outside comments. Numeric literals
//! are mathematical integers; a decimal point or exponent is rejected.

use std::sync::Arc;
use ts_proof_core::{Diagnostic, ErrorCode, Span};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    Ident(String),
    Str(String),
    Int(String),
    /// Expression text of a `// @invariant` comment.
    Invariant(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBrack,
    RBrack,
    Comma,
    Colon,
    Semi,
    Dot,
    Question,
    Arrow,
    Eq,
    EqEqEq,
    NotEqEq,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Star,
    AndAnd,
    OrOr,
    Bang,
    At,
    Eof,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub kind: Tok,
    pub span: Span,
}

pub fn lex(file: &str, source: &str) -> Result<Vec<Token>, Diagnostic> {
    let mut lx = Lexer {
        file: Arc::from(file),
        src: source,
        i: 0,
    };
    let mut out = Vec::new();
    loop {
        let tok = lx.next()?;
        let done = matches!(tok.kind, Tok::Eof);
        out.push(tok);
        if done {
            break;
        }
    }
    Ok(out)
}

struct Lexer<'a> {
    file: Arc<str>,
    src: &'a str,
    i: usize,
}

impl<'a> Lexer<'a> {
    fn next(&mut self) -> Result<Token, Diagnostic> {
        if let Some(inv) = self.skip_ignorable()? {
            return Ok(inv);
        }
        let start = self.i;
        let Some(c) = self.peek_char() else {
            return Ok(self.tok(Tok::Eof, start));
        };
        let kind = match c {
            '(' => self.simple(Tok::LParen),
            ')' => self.simple(Tok::RParen),
            '{' => self.simple(Tok::LBrace),
            '}' => self.simple(Tok::RBrace),
            '[' => self.simple(Tok::LBrack),
            ']' => self.simple(Tok::RBrack),
            ',' => self.simple(Tok::Comma),
            ':' => self.simple(Tok::Colon),
            ';' => self.simple(Tok::Semi),
            '@' => self.simple(Tok::At),
            '?' => {
                self.bump();
                if self.peek_char() == Some('.') {
                    return self.fail(start, "optional chaining is outside the supported subset");
                }
                Tok::Question
            }
            '.' => {
                self.bump();
                if self.peek_char() == Some('.') {
                    return self.fail(start, "spread syntax is outside the supported subset");
                }
                Tok::Dot
            }
            '+' => {
                self.bump();
                if self.peek_char() == Some('+') {
                    return self.fail(start, "increment is outside the supported subset");
                }
                Tok::Plus
            }
            '-' => {
                self.bump();
                if self.peek_char() == Some('-') {
                    return self.fail(start, "decrement is outside the supported subset");
                }
                Tok::Minus
            }
            '*' => self.simple(Tok::Star),
            '&' => {
                self.bump();
                if self.eat('&') {
                    Tok::AndAnd
                } else {
                    return self.fail(start, "bitwise AND is outside the supported subset");
                }
            }
            '|' => {
                self.bump();
                if self.eat('|') {
                    Tok::OrOr
                } else {
                    return self.fail(start, "bitwise OR is outside the supported subset");
                }
            }
            '!' => {
                self.bump();
                if self.eat('=') {
                    if self.eat('=') {
                        Tok::NotEqEq
                    } else {
                        return self.fail(start, "abstract inequality != is rejected; use !==");
                    }
                } else {
                    Tok::Bang
                }
            }
            '=' => {
                self.bump();
                if self.eat('>') {
                    Tok::Arrow
                } else if self.eat('=') {
                    if self.eat('=') {
                        Tok::EqEqEq
                    } else {
                        return self.fail(start, "abstract equality == is rejected; use ===");
                    }
                } else {
                    Tok::Eq
                }
            }
            '<' => {
                self.bump();
                if self.eat('=') {
                    Tok::Le
                } else {
                    Tok::Lt
                }
            }
            '>' => {
                self.bump();
                if self.eat('=') {
                    Tok::Ge
                } else {
                    Tok::Gt
                }
            }
            '/' => return self.fail(start, "division is outside the supported subset"),
            '%' | '^' | '~' => {
                return self.fail(start, "bitwise and remainder operators are outside the supported subset");
            }
            '`' => return self.fail(start, "template strings are outside the supported subset"),
            '"' | '\'' => self.string(start)?,
            c if c.is_ascii_digit() => self.number(start)?,
            c if is_ident_start(c) => self.ident(start),
            c => return self.fail(start, format!("unsupported character {c:?}")),
        };
        Ok(self.tok(kind, start))
    }

    fn simple(&mut self, kind: Tok) -> Tok {
        self.bump();
        kind
    }

    /// Skip whitespace and ordinary comments. A `// @invariant` comment is a token.
    fn skip_ignorable(&mut self) -> Result<Option<Token>, Diagnostic> {
        loop {
            while self.peek_char().is_some_and(|c| c.is_whitespace()) {
                self.bump();
            }
            if self.starts_with("//") {
                let start = self.i;
                self.i += 2;
                let text_at = self.i;
                while self.peek_char().is_some_and(|c| c != '\n') {
                    self.bump();
                }
                let text = self.src[text_at..self.i].trim();
                if let Some(inv) = text.strip_prefix("@invariant") {
                    let inv = inv.trim();
                    if inv.is_empty() {
                        return Err(self.error(start, "@invariant needs an expression"));
                    }
                    return Ok(Some(Token {
                        kind: Tok::Invariant(inv.to_string()),
                        span: self.span(start),
                    }));
                }
                continue;
            }
            if self.starts_with("/*") {
                let start = self.i;
                self.i += 2;
                while !self.starts_with("*/") {
                    if self.peek_char().is_none() {
                        return Err(self.error(start, "unterminated block comment"));
                    }
                    self.bump();
                }
                let body = &self.src[start + 2..self.i];
                self.i += 2;
                if body.contains("@invariant") {
                    return Err(self.error(start, "put @invariant in a line comment"));
                }
                continue;
            }
            return Ok(None);
        }
    }

    fn string(&mut self, start: usize) -> Result<Tok, Diagnostic> {
        let quote = self.bump().unwrap();
        let mut out = String::new();
        loop {
            let Some(c) = self.bump() else {
                return Err(self.error(start, "unterminated string"));
            };
            if c == quote {
                break;
            }
            if c == '\\' {
                let Some(esc) = self.bump() else {
                    return Err(self.error(start, "unterminated string escape"));
                };
                let ch = match esc {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    '\\' => '\\',
                    '"' => '"',
                    '\'' => '\'',
                    other => {
                        return Err(self.error(start, format!("unsupported string escape \\{other}")));
                    }
                };
                out.push(ch);
            } else if c == '\n' {
                return Err(self.error(start, "unterminated string"));
            } else {
                out.push(c);
            }
        }
        Ok(Tok::Str(out))
    }

    fn number(&mut self, start: usize) -> Result<Tok, Diagnostic> {
        while self.peek_char().is_some_and(|c| c.is_ascii_digit()) {
            self.bump();
        }
        if self.peek_char().is_some_and(|c| c == '.' || c == 'e' || c == 'E') {
            return Err(self.error(
                start,
                "number literals are outside the supported subset; use bigint or an integer literal",
            ));
        }
        if self.peek_char() == Some('n') {
            self.bump();
        }
        let raw = &self.src[start..self.i];
        let digits = raw.strip_suffix('n').unwrap_or(raw);
        let canon = ts_proof_core::canon_int(digits).ok_or_else(|| {
            self.error(start, "invalid integer literal")
        })?;
        Ok(Tok::Int(canon))
    }

    fn ident(&mut self, start: usize) -> Tok {
        while self.peek_char().is_some_and(is_ident_continue) {
            self.bump();
        }
        Tok::Ident(self.src[start..self.i].to_string())
    }

    fn peek_char(&self) -> Option<char> {
        self.src[self.i..].chars().next()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek_char()?;
        self.i += c.len_utf8();
        Some(c)
    }

    fn eat(&mut self, c: char) -> bool {
        if self.peek_char() == Some(c) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn starts_with(&self, s: &str) -> bool {
        self.src[self.i..].starts_with(s)
    }

    fn span(&self, start: usize) -> Span {
        Span::new(self.file.clone(), start as u32, self.i as u32)
    }

    fn tok(&self, kind: Tok, start: usize) -> Token {
        Token {
            kind,
            span: self.span(start),
        }
    }

    fn error(&self, start: usize, message: impl Into<String>) -> Diagnostic {
        Diagnostic::new(ErrorCode::Verify002, message.into()).at(self.span(start))
    }

    fn fail<T>(&self, start: usize, message: impl Into<String>) -> Result<T, Diagnostic> {
        Err(self.error(start, message))
    }
}

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || c == '$'
}

fn is_ident_continue(c: char) -> bool {
    is_ident_start(c) || c.is_ascii_digit()
}
