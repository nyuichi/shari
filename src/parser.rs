use core::ops::Range;
use once_cell::sync::Lazy;
use regex::Regex;
use std::collections::HashMap;
use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Name(pub String);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Var(Name),
    Arrow(Box<Type>, Box<Type>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(Name),
    Abs(Name, Option<Type>, Box<Term>),
    App(Box<Term>, Box<Term>),
}

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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Fixity {
    Infixl,
    Infixr,
    Nofix,
    Prefix,
}

#[derive(Debug, Clone)]
struct Operator {
    fixity: Fixity,
    prec: usize,
    entity: String,
}

#[derive(Default)]
pub struct TokenTable {
    led: HashMap<String, Operator>,
    nud: HashMap<String, Operator>,
}

impl TokenTable {
    pub fn add(&mut self, symbol: &str, fixity: Fixity, prec: usize, entity: &str) {
        let op = Operator {
            fixity,
            prec,
            entity: entity.to_owned(),
        };
        match fixity {
            Fixity::Infixl | Fixity::Infixr => {
                if let Some(_) = self.led.insert(symbol.to_owned(), op) {
                    todo!()
                }
            }
            Fixity::Nofix | Fixity::Prefix => {
                if let Some(_) = self.nud.insert(symbol.to_owned(), op) {
                    todo!()
                }
            }
        };
    }
}

enum Led {
    App,
    User(Operator),
}

impl Led {
    fn prec(&self) -> usize {
        match self {
            Self::App => 1024,
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
    #[error("unexpected end of input at {source_info}")]
    Eof { source_info: SourceInfo<'a> },
}

pub struct Parser<'a> {
    lex: Lex<'a>,
    token_table: &'a TokenTable,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str, filename: &'a str, token_table: &'a TokenTable) -> Self {
        Self {
            lex: Lex::new(input, filename),
            token_table,
        }
    }

    fn fail<R>(token: Token<'a>, message: impl Into<String>) -> Result<R, ParseError> {
        Err(ParseError::Parse {
            message: message.into(),
            source_info: token.source_info,
        })
    }
    fn eof_error(&self) -> ParseError<'a> {
        ParseError::Eof {
            source_info: SourceInfo::eof(self.lex.input, self.lex.filename),
        }
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

    fn type_primary(&mut self) -> Result<Type, ParseError<'a>> {
        let token = self.any_token()?;
        if token.is_ident() {
            let id = token.as_str();
            Ok(Type::Var(Name(id.to_owned())))
        } else if token.is_symbol() && token.as_str() == "(" {
            let t = self.r#type()?;
            self.expect_symbol(")")?;
            Ok(t)
        } else {
            todo!()
        }
    }

    pub fn r#type(&mut self) -> Result<Type, ParseError<'a>> {
        let t = self.type_primary()?;
        if let Some(token) = self.peek_opt() {
            if token.is_symbol() && token.as_str() == "→" {
                self.advance();
                return Ok(Type::Arrow(t.into(), self.r#type()?.into()));
            }
        }
        Ok(t)
    }

    /// typed parameters e.g. `"(x y : T)"`
    fn parameter(&mut self, _token: Token) -> Result<(Vec<Name>, Type), ParseError<'a>> {
        let mut idents = vec![Name(self.ident()?.as_str().to_owned())];
        while let Some(ident) = self.ident_opt() {
            idents.push(Name(ident.as_str().to_owned()));
        }
        // TODO: allow declarations with no explict types
        self.expect_symbol(":")?;
        let t = self.r#type()?;
        self.expect_symbol(")")?;
        Ok((idents, t))
    }

    fn parameters(&mut self) -> Result<Vec<(Name, Option<Type>)>, ParseError<'a>> {
        let mut params = vec![];
        loop {
            if let Some(token) = self.expect_symbol_opt("(") {
                let (names, t) = self.parameter(token)?;
                for name in names {
                    params.push((name, Some(t.clone())));
                }
            } else if let Some(token) = self.ident_opt() {
                params.push((Name(token.as_str().to_owned()), None));
            } else {
                break;
            }
        }
        Ok(params)
    }

    pub fn term(&mut self) -> Result<Term, ParseError<'a>> {
        self.subterm(0)
    }

    fn term_abs(&mut self, _token: Token) -> Result<Term, ParseError<'a>> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        let mut m = self.subterm(0)?;
        if params.is_empty() {
            todo!("empty binding");
        }
        for (name, t) in params.into_iter().rev() {
            m = Term::Abs(name, t, Box::new(m));
        }
        Ok(m)
    }

    fn term_forall(&mut self, _token: Token) -> Result<Term, ParseError<'a>> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        let mut m = self.subterm(0)?;
        if params.is_empty() {
            todo!("empty binding");
        }
        for (name, t) in params.into_iter().rev() {
            m = Term::App(
                Box::new(Term::Var(Name("forall".to_owned()))),
                Box::new(Term::Abs(name, t, Box::new(m))),
            );
        }
        Ok(m)
    }

    fn term_var(&mut self, token: Token, entity: Option<String>) -> Term {
        let name = match entity {
            None => Name(token.as_str().to_owned()),
            Some(s) => Name(s),
        };
        Term::Var(name)
    }

    fn subterm(&mut self, rbp: usize) -> Result<Term, ParseError<'a>> {
        let token = self.any_token()?;
        // nud
        let nud = match self.token_table.get_nud(&token) {
            None => todo!("nud unknown: {}", token),
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
                    let fun = self.term_var(token, Some(op.entity));
                    let arg = self.subterm(op.prec)?;
                    Term::App(Box::new(fun), Box::new(arg))
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
                    left = Term::App(Box::new(left), Box::new(right));
                }
                Led::User(op) => {
                    let prec = match op.fixity {
                        Fixity::Infixl => prec,
                        Fixity::Infixr => prec - 1,
                        _ => unreachable!(),
                    };
                    self.advance();
                    let fun = self.term_var(token, Some(op.entity));
                    let right = self.subterm(prec)?;
                    left = Term::App(
                        Box::new(Term::App(Box::new(fun), Box::new(left))),
                        Box::new(right),
                    );
                }
            }
        }
        Ok(left)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    pub fn parse_term(input: &str) -> Term {
        let token_table = TokenTable::default();
        let mut parser = Parser::new(input, "", &token_table);
        parser.term().unwrap()
    }

    #[test]
    fn parse() {
        println!("{:?}", parse_term("λ (x : ℕ → ℕ), x y"));
        println!("{:?}", parse_term("p → (p → q) → q"));
        println!("{:?}", parse_term("λ x y, ∀ P, P x → P y"));
    }
}
