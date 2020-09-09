use crate::term::{Env, MvarId, Name, Term, Type};
use core::ops::Range;
use once_cell::sync::Lazy;
use regex::Regex;
use std::collections::HashMap;
use thiserror::Error;

#[derive(Debug, Clone)]
pub struct SourceInfo<'a> {
    line: usize,   // 1-origin
    column: usize, // 1-origin
    range: Range<usize>,
    input: &'a str,
    filename: &'a str,
}

impl<'a> SourceInfo<'a> {
    fn eof(input: &'a str, filename: &'a str) -> Self {
        let range = {
            let last = input.chars().count();
            last..last
        };
        let (line, column) = {
            let mut lines = input.lines();
            let last_line = lines.by_ref().last().unwrap();
            (lines.count() + 1, last_line.chars().count() + 1)
        };
        Self {
            range,
            input,
            line,
            column,
            filename,
        }
    }

    fn as_str(&self) -> &str {
        self.input
            .get(self.range.clone())
            .expect("invalid token position")
    }
}

impl<'a> std::fmt::Display for SourceInfo<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:{}:{}\n\n", self.filename, self.line, self.column)?;
        write!(
            f,
            "{}\n",
            self.input
                .lines()
                .nth(self.line - 1)
                .expect("invalid line number")
        )?;
        write!(
            f,
            "{}{}\n",
            std::iter::repeat(' ')
                .take(self.column - 1)
                .collect::<String>(),
            std::iter::repeat('^')
                .take(self.input.get(self.range.clone()).unwrap().chars().count())
                .collect::<String>()
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TokenKind {
    Ident,  // e.g. "foo", "α", "Prop"
    Symbol, // e.g. "+", ":", "λ", ",", "_"
}

#[derive(Debug, Clone)]
pub struct Token<'a> {
    kind: TokenKind,
    source_info: SourceInfo<'a>,
}

impl<'a> Token<'a> {
    fn is_ident(&self) -> bool {
        self.kind == TokenKind::Ident
    }

    fn is_symbol(&self) -> bool {
        self.kind == TokenKind::Symbol
    }

    fn as_str(&self) -> &str {
        self.source_info.as_str()
    }
}

impl<'a> std::fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?} {}\n{}", self.kind, self.as_str(), self.source_info)
    }
}

#[derive(Debug, Clone)]
pub struct Lex<'a> {
    input: &'a str,
    position: usize,
    line: usize,
    column: usize,
    filename: &'a str,
}

#[derive(Debug, Clone)]
pub struct LexError {
    line: usize,
    column: usize,
    filename: String,
}

impl From<Lex<'_>> for LexError {
    fn from(lex: Lex<'_>) -> Self {
        Self {
            line: lex.line,
            column: lex.column,
            filename: lex.filename.to_owned(),
        }
    }
}

impl std::fmt::Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "unrecognizable character at line {}, column {}, in file {}",
            self.line, self.column, self.filename
        )
    }
}

impl std::error::Error for LexError {}

impl<'a> Lex<'a> {
    fn new(input: &'a str, filename: &'a str) -> Self {
        Self {
            input,
            position: 0,
            line: 1,
            column: 1,
            filename,
        }
    }

    fn advance(&mut self, bytes: usize) -> SourceInfo<'a> {
        let source_info = SourceInfo {
            range: self.position..self.position + bytes,
            line: self.line,
            column: self.column,
            input: self.input,
            filename: self.filename,
        };
        let text = &self.input[self.position..self.position + bytes];
        self.position += bytes;
        for c in text.chars() {
            if c == '\n' {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
        }
        source_info
    }
}

impl<'a> Iterator for Lex<'a> {
    type Item = std::result::Result<Token<'a>, LexError>;
    fn next(&mut self) -> Option<Self::Item> {
        #[derive(PartialEq, Eq, Debug)]
        enum Kind {
            Space,
            Ident,
            Symbol,
        };

        static RE: Lazy<Regex> = Lazy::new(|| {
            let s = &[
                (Kind::Space, r"\s+|--.*|/-(?s:.*?)-/"),
                (
                    Kind::Ident,
                    r"[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*",
                ),
                (
                    Kind::Symbol,
                    r"\(|\)|\{|\}|[\p{Symbol}\p{Punctuation}&&[^(){}]]+",
                ),
            ]
            .iter()
            .map(|(kind, re)| format!("(?P<{:?}>{})", kind, re))
            .collect::<Vec<_>>()
            .join("|");
            regex::Regex::new(&format!("^(?:{})", s)).unwrap()
        });

        loop {
            if self.input.len() == self.position {
                return None;
            }
            let cap = match RE.captures(&self.input[self.position..]) {
                None => return Some(Err(self.clone().into())),
                Some(cap) => cap,
            };
            // change the position of the cursor
            let source_info = self.advance(cap.get(0).unwrap().range().count());
            if cap.name(&format!("{:?}", Kind::Space)).is_none() {
                let text = source_info.as_str();

                let kind = if cap.name(&format!("{:?}", Kind::Ident)).is_some() {
                    match text {
                        "λ" | "_" => TokenKind::Symbol,
                        _ => TokenKind::Ident,
                    }
                } else {
                    assert!(cap.name(&format!("{:?}", Kind::Symbol)).is_some());
                    TokenKind::Symbol
                };
                return Some(Ok(Token { kind, source_info }));
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Fixity {
    Infixl,
    Nofix,
    Prefix,
}

#[derive(Debug, Clone)]
pub struct Operator {
    fixity: Fixity,
    prec: usize,
    entity: String,
}

#[derive(Default)]
pub struct TokenTable {
    led: HashMap<String, Operator>,
    nud: HashMap<String, Operator>,
}

enum Led {
    App,
    Imp,
    Eq,
    User(Operator),
}

impl Led {
    fn prec(&self) -> usize {
        match self {
            Self::App => 1024,
            Self::Imp => 25,
            Self::Eq => 50,
            Self::User(op) => op.prec,
        }
    }
}

enum Nud {
    Var,
    Abs,
    Forall,
    Paren,
    User(Operator),
}

impl TokenTable {
    fn get_led(&self, token: &Token) -> Option<Led> {
        match token.kind {
            TokenKind::Ident => Some(Led::App),
            TokenKind::Symbol => {
                let lit = token.as_str();
                match self.led.get(lit) {
                    Some(op) => Some(Led::User(op.clone())),
                    None => match lit {
                        "→" => Some(Led::Imp),
                        "=" => Some(Led::Eq),
                        _ => {
                            if self.get_nud(token).is_some() {
                                Some(Led::App)
                            } else {
                                None
                            }
                        }
                    },
                }
            }
        }
    }

    fn get_nud(&self, token: &Token) -> Option<Nud> {
        match token.kind {
            TokenKind::Ident => Some(Nud::Var),
            TokenKind::Symbol => {
                let lit = token.as_str();
                match lit {
                    "(" => Some(Nud::Paren),
                    "λ" => Some(Nud::Abs),
                    "∀" => Some(Nud::Forall),
                    _ => self.nud.get(token.as_str()).map(|op| Nud::User(op.clone())),
                }
            }
        }
    }
}

#[derive(Debug, Error)]
pub enum ParseError<'a> {
    #[error("parse error: {message} at {source_info}")]
    Parse {
        message: String,
        source_info: SourceInfo<'a>,
    },
    #[error("unexpected end of input")]
    Eof,
}

struct Parse<'a> {
    lex: Lex<'a>,
    token_table: TokenTable,
    env: Env<'a>,
}

impl<'a> Parse<'a> {
    fn new(input: &'a str, filename: &'a str, token_table: TokenTable, env: Env<'a>) -> Self {
        Self {
            lex: Lex::new(input, filename),
            token_table,
            env,
        }
    }

    fn fail<R>(token: Token<'a>, message: impl Into<String>) -> Result<R, ParseError> {
        Err(ParseError::Parse {
            message: message.into(),
            source_info: token.source_info,
        })
    }
    fn eof_error(&self) -> ParseError<'a> {
        ParseError::Eof
    }

    fn optional<F, R>(&mut self, f: F) -> Option<R>
    where
        F: FnOnce(&mut Self) -> Result<R, ParseError<'a>>,
    {
        let state = self.lex.clone();
        match f(self) {
            Ok(m) => Some(m),
            Err(_err) => {
                self.lex = state;
                None
            }
        }
    }

    fn peek_opt(&mut self) -> Option<Token<'a>> {
        self.optional(|this| this.peek())
    }
    fn peek(&mut self) -> Result<Token<'a>, ParseError<'a>> {
        self.lex
            .clone()
            .next()
            .transpose()
            .expect("lex error")
            .ok_or_else(|| self.eof_error())
    }
    fn advance(&mut self) {
        self.lex
            .next()
            .expect("unchecked advance")
            .expect("lex error");
    }
    fn any_token(&mut self) -> Result<Token<'a>, ParseError<'a>> {
        self.lex
            .next()
            .transpose()
            .expect("lex error")
            .ok_or_else(|| self.eof_error())
    }

    fn ident(&mut self) -> Result<Token<'a>, ParseError<'a>> {
        let token = self.any_token()?;
        if !token.is_ident() {
            return Self::fail(token, "expected identifier");
        }
        Ok(token)
    }
    fn ident_opt(&mut self) -> Option<Token<'a>> {
        if let Some(token) = self.peek_opt() {
            if token.is_ident() {
                self.advance();
                return Some(token);
            }
        }
        None
    }
    fn symbol(&mut self) -> Result<Token<'a>, ParseError<'a>> {
        let token = self.any_token()?;
        if !token.is_symbol() {
            return Self::fail(token, "expected symbol");
        }
        Ok(token)
    }
    fn expect_symbol(&mut self, sym: &str) -> Result<(), ParseError<'a>> {
        let token = self.any_token()?;
        if token.kind == TokenKind::Symbol && token.as_str() == sym {
            return Ok(());
        }
        Self::fail(token, format!("expected symbol '{}'", sym))
    }
    fn expect_symbol_opt(&mut self, sym: &str) -> Option<Token<'a>> {
        if let Some(token) = self.peek_opt() {
            if token.kind == TokenKind::Symbol && token.as_str() == sym {
                self.advance();
                return Some(token);
            }
        }
        None
    }

    fn name(&mut self) -> Result<Name, ParseError<'a>> {
        self.ident()
            .map(|token| Name::Named(token.as_str().to_owned()))
    }

    fn type_primary(&mut self) -> Result<Type, ParseError<'a>> {
        let token = self.any_token()?;
        if token.is_ident() {
            let id = token.as_str();
            Ok(Type::Base(Name::Named(id.to_owned())))
        } else if token.is_symbol() && token.as_str() == "(" {
            let t = self.r#type()?;
            self.expect_symbol(")")?;
            Ok(t)
        } else {
            unimplemented!()
        }
    }

    fn r#type(&mut self) -> Result<Type, ParseError<'a>> {
        let t = self.type_primary()?;
        if let Some(token) = self.peek_opt() {
            if token.is_symbol() && token.as_str() == "→" {
                self.advance();
                return Ok(Type::Arrow(t.into(), self.r#type()?.into()));
            }
        }
        Ok(t)
    }

    fn parameter(&mut self, _token: Token) -> Result<(Vec<Name>, Type), ParseError<'a>> {
        let mut idents = vec![Name::Named(self.ident()?.as_str().to_owned())];
        while let Some(ident) = self.ident_opt() {
            idents.push(Name::Named(ident.as_str().to_owned()));
        }
        // TODO: allow declarations with no explict types
        self.expect_symbol(":")?;
        let t = self.r#type()?;
        self.expect_symbol(")")?;
        Ok((idents, t))
    }

    fn parameters(&mut self) -> Result<Vec<(Name, Type)>, ParseError<'a>> {
        let mut params = vec![];
        while let Some(token) = self.expect_symbol_opt("(") {
            let (names, t) = self.parameter(token)?;
            for name in names {
                params.push((name, t.clone()));
            }
        }
        Ok(params)
    }

    fn term(&mut self) -> Result<Term, ParseError<'a>> {
        self.subterm(0)
    }

    fn term_abs(&mut self, _token: Token) -> Result<Term, ParseError<'a>> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        let mut m = self.subterm(0)?;
        if params.is_empty() {
            unimplemented!("empty binding");
        }
        for (name, t) in params.into_iter().rev() {
            m.mk_abs(&name, t);
        }
        Ok(m)
    }

    fn term_forall(&mut self, _token: Token) -> Result<Term, ParseError<'a>> {
        todo!()
        // let vars = self.parameters()?;
        // self.expect_symbol(",")?;
        // let body = self.subterm(0)?;
        // if vars.is_empty() {
        //     unimplemented!("empty binding");
        // }
        // Ok(vars
        //     .into_iter()
        //     .rev()
        //     .fold(body, |m, (var, t)| m.into_forall(&var, t)))
    }

    fn term_var(&mut self, token: Token, entity: Option<String>) -> Term {
        let name = match entity {
            None => Name::Named(token.as_str().to_owned()),
            Some(s) => Name::Named(s),
        };
        if let Some(scheme) = self.env.get_const(&name) {
            Term::Const(
                name,
                (0..scheme.arity())
                    .map(|_| Type::Mvar(MvarId::fresh()))
                    .collect(),
            )
        } else {
            Term::Fvar(name)
        }
    }

    fn subterm(&mut self, rbp: usize) -> Result<Term, ParseError<'a>> {
        let token = self.any_token()?;
        // nud
        let nud = match self.token_table.get_nud(&token) {
            None => unimplemented!("nud unknown: {}", token),
            Some(nud) => nud,
        };
        let mut left = match nud {
            Nud::Var => self.term_var(token, None),
            Nud::Abs => self.term_abs(token)?,
            Nud::Paren => {
                let m = self.subterm(0)?;
                self.expect_symbol(")")?;
                m
            }
            Nud::Forall => self.term_forall(token)?,
            Nud::User(op) => match op.fixity {
                Fixity::Nofix => self.term_var(token, Some(op.entity)),
                Fixity::Prefix => {
                    let mut m = self.term_var(token, Some(op.entity));
                    let arg = self.subterm(op.prec)?;
                    m.mk_app(arg);
                    m
                }
                _ => unreachable!(),
            },
        };
        while let Some(token) = self.peek_opt() {
            let led = match self.token_table.get_led(&token) {
                None => break,
                Some(led) => led,
            };
            let prec = led.prec();
            if rbp >= prec {
                break;
            }
            match led {
                Led::App => {
                    let right = self.subterm(led.prec())?;
                    left.mk_app(right);
                }
                Led::Imp => {
                    todo!()
                    // self.advance();
                    // let right = self.subterm(led.prec() - 1)?;
                    // left = Term::Imp(left.into(), right.into());
                }
                Led::Eq => {
                    todo!()
                    // self.advance();
                    // let right = self.subterm(led.prec())?;
                    // left = Term::Eq(left.into(), right.into());
                }
                Led::User(op) => match op.fixity {
                    Fixity::Infixl => {
                        self.advance();
                        let mut f = self.term_var(token, Some(op.entity));
                        let right = self.subterm(prec)?;
                        f.mk_app(left);
                        f.mk_app(right);
                        left = f;
                    }
                    _ => unreachable!(),
                },
            }
        }
        Ok(left)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_term(input: &str) -> Term {
        let mut parser = Parse::new(input, "", TokenTable::default(), Env::default());
        parser.term().unwrap()
    }

    #[test]
    fn parse() {
        println!("{:?}", parse_term("λ (x : ℕ → ℕ), x y"))
    }
}
