use crate::term::{MvarId, Name, Term, Type};
use core::ops::Range;
use once_cell::sync::Lazy;
use regex::Regex;
use std::{collections::HashMap, mem, sync::Arc};
use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefCommand {
    pub name: Name,
    pub r#type: Type,
    pub term: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckCommand {
    pub term: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InfixrCommand {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InfixlCommand {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InfixCommand {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrefixCommand {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NofixCommand {
    pub op: String,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstCommand {
    pub name: Name,
    pub r#type: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxiomCommand {
    pub name: Name,
    pub prop: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Command {
    DefCmd(DefCommand),
    CheckCmd(CheckCommand),
    InfixrCmd(InfixrCommand),
    InfixlCmd(InfixlCommand),
    InfixCmd(InfixCommand),
    PrefixCmd(PrefixCommand),
    NofixCmd(NofixCommand),
    ConstCmd(ConstCommand),
    AxiomCmd(AxiomCommand),
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
        writeln!(
            f,
            "{}",
            self.input
                .lines()
                .nth(self.line - 1)
                .expect("invalid line number")
        )?;
        writeln!(
            f,
            "{}{}",
            " ".repeat(self.column - 1),
            "^".repeat(self.input.get(self.range.clone()).unwrap().chars().count())
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TokenKind {
    Ident,   // e.g. "foo", "α", "Prop"
    Symbol,  // e.g. "+", ":", "λ", ",", "_"
    NumLit,  // e.g. 42
    Keyword, // e.g. "def", "#check"
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

    fn is_num_lit(&self) -> bool {
        self.kind == TokenKind::NumLit
    }

    fn is_keyword(&self) -> bool {
        self.kind == TokenKind::Keyword
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

#[derive(Debug, Clone, Copy)]
struct LexState {
    position: usize,
    line: usize,
    column: usize,
}

#[derive(Debug, Clone, Error)]
#[error("unrecognizable character at line {line}, column {column}, in file \"{filename}\"")]
pub struct LexError<'a> {
    line: usize,
    column: usize,
    filename: &'a str,
}

impl<'a> From<Lex<'a>> for LexError<'a> {
    fn from(lex: Lex<'a>) -> Self {
        Self {
            line: lex.line,
            column: lex.column,
            filename: lex.filename,
        }
    }
}

impl<'a> Lex<'a> {
    pub fn new(input: &'a str, filename: &'a str) -> Self {
        Self {
            input,
            position: 0,
            line: 1,
            column: 1,
            filename,
        }
    }

    fn save(&self) -> LexState {
        LexState {
            position: self.position,
            line: self.line,
            column: self.column,
        }
    }

    fn restore(&mut self, state: LexState) {
        self.position = state.position;
        self.line = state.line;
        self.column = state.column;
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
    type Item = std::result::Result<Token<'a>, LexError<'a>>;
    fn next(&mut self) -> Option<Self::Item> {
        #[derive(PartialEq, Eq, Debug)]
        enum Kind {
            Space,
            Ident,
            Symbol,
            NumLit,
        }

        static RE: Lazy<Regex> = Lazy::new(|| {
            let s = &[
                (Kind::Space, r"\s+|--.*|/-(?s:.*?)-/"),
                (
                    Kind::Ident,
                    r"#?[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*",
                ),
                (
                    Kind::Symbol,
                    r"\(|\)|\{|\}|[\p{Symbol}\p{Punctuation}&&[^(){}]]+",
                ),
                (Kind::NumLit, r"0|[1-9][0-9]*"),
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
                None => return Some(Err(LexError::from(self.clone()))),
                Some(cap) => cap,
            };
            // change the position of the cursor
            let source_info = self.advance(cap.get(0).unwrap().range().count());
            if cap.name(&format!("{:?}", Kind::Space)).is_none() {
                let text = source_info.as_str();

                let kind;
                if cap.name(&format!("{:?}", Kind::Ident)).is_some() {
                    match text {
                        "λ" | "_" => {
                            kind = TokenKind::Symbol;
                        }
                        "def" | "#check" | "infix" | "infixr" | "infixl" | "prefix" | "nofix"
                        | "constant" | "lemma" | "meta" | "inductive" | "type" | "axiom"
                        | "class" | "eval" => {
                            kind = TokenKind::Keyword;
                        }
                        _ => {
                            kind = TokenKind::Ident;
                        }
                    }
                } else if cap.name(&format!("{:?}", Kind::NumLit)).is_some() {
                    kind = TokenKind::NumLit;
                } else {
                    assert!(cap.name(&format!("{:?}", Kind::Symbol)).is_some());
                    kind = TokenKind::Symbol;
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
    entity: Name,
}

#[derive(Default)]
pub struct TokenTable {
    led: HashMap<String, Operator>,
    nud: HashMap<String, Operator>,
}

impl TokenTable {
    pub fn add(&mut self, symbol: &str, fixity: Fixity, prec: usize, entity: Name) {
        let op = Operator {
            fixity,
            prec,
            entity,
        };
        match fixity {
            Fixity::Infixl | Fixity::Infixr => {
                if self.led.insert(symbol.to_owned(), op).is_some() {
                    todo!()
                }
            }
            Fixity::Nofix | Fixity::Prefix => {
                if self.nud.insert(symbol.to_owned(), op).is_some() {
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
    Exists,
    Paren,
    User(Operator),
    NumLit,
}

impl TokenTable {
    fn get_led(&self, token: &Token) -> Option<Led> {
        match token.kind {
            TokenKind::Ident => Some(Led::App),
            TokenKind::Symbol => {
                let lit = token.as_str();
                match self.led.get(lit) {
                    Some(op) => Some(Led::User(op.clone())),
                    None => {
                        if self.get_nud(token).is_some() {
                            Some(Led::App)
                        } else {
                            None
                        }
                    }
                }
            }
            TokenKind::NumLit => Some(Led::App),
            TokenKind::Keyword => None,
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
                    "∃" => Some(Nud::Exists),
                    _ => self.nud.get(token.as_str()).map(|op| Nud::User(op.clone())),
                }
            }
            TokenKind::NumLit => Some(Nud::NumLit),
            TokenKind::Keyword => None,
        }
    }
}

#[derive(Debug, Error)]
pub enum ParseError<'a> {
    #[error("{lex_error}")]
    Lex { lex_error: LexError<'a> },
    #[error("parse error: {message} at {source_info}")]
    Parse {
        message: String,
        source_info: SourceInfo<'a>,
    },
    #[error("unexpected end of input at {source_info}")]
    Eof { source_info: SourceInfo<'a> },
}

// Since LexError is not 'static we only want #[from] and don't need #[source],
// but this is impossible because #[from] attibute always implies #[source].
// So I am implementing it manually.
impl<'a> From<LexError<'a>> for ParseError<'a> {
    fn from(err: LexError<'a>) -> Self {
        Self::Lex { lex_error: err }
    }
}

pub struct Parser<'a, 'b> {
    lex: &'b mut Lex<'a>,
    token_table: &'b TokenTable,
}

impl<'a, 'b> Parser<'a, 'b> {
    pub fn new(lex: &'b mut Lex<'a>, token_table: &'b TokenTable) -> Self {
        Self { lex, token_table }
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
        let state = self.lex.save();
        match f(self) {
            Ok(m) => Some(m),
            Err(_err) => {
                self.lex.restore(state);
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
            .transpose()?
            .ok_or_else(|| self.eof_error())
    }

    fn advance(&mut self) {
        self.lex
            .next()
            .expect("unchecked advance")
            .expect("impossible lex error! probably due to unchecked advance");
    }

    pub fn eof(&mut self) -> Result<(), ParseError<'a>> {
        if let Some(token) = self.peek_opt() {
            Self::fail(token, "expected EOF but tokens remain")?;
        }
        Ok(())
    }

    pub fn eof_opt(&mut self) -> bool {
        self.peek_opt().is_none()
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

    fn num_lit(&mut self) -> Result<Token<'a>, ParseError<'a>> {
        let token = self.any_token()?;
        if !token.is_num_lit() {
            return Self::fail(token, "expected numeral literal");
        }
        Ok(token)
    }

    fn keyword(&mut self) -> Result<Token<'a>, ParseError<'a>> {
        let token = self.any_token()?;
        if !token.is_keyword() {
            return Self::fail(token, "expected keyword");
        }
        Ok(token)
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

    pub fn name(&mut self) -> Result<Name, ParseError<'a>> {
        Ok(Name::Str(self.ident()?.as_str().to_owned()))
    }

    fn name_opt(&mut self) -> Option<Name> {
        self.ident_opt()
            .map(|token| Name::Str(token.as_str().to_owned()))
    }

    fn type_primary(&mut self) -> Result<Type, ParseError<'a>> {
        if let Some(name) = self.name_opt() {
            return Ok(Type::Fvar(name));
        }
        let token = self.any_token()?;
        if token.is_symbol() && token.as_str() == "(" {
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
                return Ok(Type::Arrow(Arc::new((t, self.r#type()?))));
            }
        }
        Ok(t)
    }

    /// typed parameters e.g. `"(x y : T)"`
    fn parameter(&mut self, _token: Token) -> Result<(Vec<Name>, Type), ParseError<'a>> {
        let mut idents = vec![];
        // needs at least one parameter
        idents.push(self.name()?);
        while let Some(name) = self.name_opt() {
            idents.push(name);
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
            } else if let Some(name) = self.name_opt() {
                params.push((name, None));
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
            let t = t.unwrap_or_else(|| Type::Mvar(MvarId::fresh()));
            m.r#abstract(vec![(name, t)]);
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
            let t = t.unwrap_or_else(|| Type::Mvar(MvarId::fresh()));
            m.r#abstract(vec![(name, t)]);
            let f = mem::take(&mut m);
            m = Term::Const(Type::Mvar(MvarId::fresh()), Name::Str("forall".to_owned()));
            m.curry(vec![f]);
        }
        Ok(m)
    }

    fn term_exists(&mut self, _token: Token) -> Result<Term, ParseError<'a>> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        let mut m = self.subterm(0)?;
        if params.is_empty() {
            todo!("empty binding");
        }
        for (name, t) in params.into_iter().rev() {
            let t = t.unwrap_or_else(|| Type::Mvar(MvarId::fresh()));
            m.r#abstract(vec![(name, t)]);
            let f = mem::take(&mut m);
            m = Term::Const(Type::Mvar(MvarId::fresh()), Name::Str("exists".to_owned()));
            m.curry(vec![f]);
        }
        Ok(m)
    }

    fn term_var(&mut self, token: Token, entity: Option<Name>) -> Term {
        let name = match entity {
            None => Name::Str(token.as_str().to_owned()),
            Some(s) => s,
        };
        Term::Fvar(Type::Mvar(MvarId::fresh()), name)
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
            Nud::Exists => self.term_exists(token)?,
            Nud::User(op) => match op.fixity {
                Fixity::Nofix => self.term_var(token, Some(op.entity)),
                Fixity::Prefix => {
                    let mut fun = self.term_var(token, Some(op.entity));
                    let arg = self.subterm(op.prec)?;
                    fun.curry(vec![arg]);
                    fun
                }
                _ => unreachable!(),
            },
            Nud::NumLit => todo!(),
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
                    left.curry(vec![right])
                }
                Led::User(op) => {
                    let prec = match op.fixity {
                        Fixity::Infixl => prec,
                        Fixity::Infixr => prec - 1,
                        _ => unreachable!(),
                    };
                    self.advance();
                    let mut fun = self.term_var(token, Some(op.entity));
                    let right = self.subterm(prec)?;
                    fun.curry(vec![left, right]);
                    left = fun;
                }
            }
        }
        Ok(left)
    }

    fn def_cmd(&mut self, _token: Token) -> Result<DefCommand, ParseError<'a>> {
        let name = self.name()?;
        let mut params = vec![];
        while let Some(token) = self.expect_symbol_opt("(") {
            let (names, t) = self.parameter(token)?;
            for name in names {
                params.push((name, t.clone()));
            }
        }
        self.expect_symbol(":")?;
        let mut t = self.r#type()?;
        self.expect_symbol(":=")?;
        let mut m = self.term()?;
        for (var, ty) in params.into_iter().rev() {
            m.r#abstract(vec![(var, ty.clone())]);
            t = Type::Arrow(Arc::new((ty, t)));
        }
        Ok(DefCommand {
            name,
            r#type: t,
            term: m,
        })
    }

    fn check_cmd(&mut self, _token: Token) -> Result<CheckCommand, ParseError<'a>> {
        let m = self.term()?;
        Ok(CheckCommand { term: m })
    }

    fn infixr_cmd(&mut self, _token: Token) -> Result<InfixrCommand, ParseError<'a>> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(InfixrCommand {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn infixl_cmd(&mut self, _token: Token) -> Result<InfixlCommand, ParseError<'a>> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(InfixlCommand {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn infix_cmd(&mut self, _token: Token) -> Result<InfixCommand, ParseError<'a>> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(InfixCommand {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn prefix_cmd(&mut self, _token: Token) -> Result<PrefixCommand, ParseError<'a>> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(PrefixCommand {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn nofix_cmd(&mut self, _token: Token) -> Result<NofixCommand, ParseError<'a>> {
        let op = self.symbol()?;
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(NofixCommand {
            op: op.as_str().to_owned(),
            entity,
        })
    }

    fn const_cmd(&mut self, _token: Token) -> Result<ConstCommand, ParseError<'a>> {
        let name = self.name()?;
        self.expect_symbol(":")?;
        let t = self.r#type()?;
        Ok(ConstCommand { name, r#type: t })
    }

    fn axiom_cmd(&mut self, _token: Token) -> Result<AxiomCommand, ParseError<'a>> {
        let name = self.name()?;
        self.expect_symbol(":")?;
        let m = self.term()?;
        Ok(AxiomCommand { name, prop: m })
    }

    pub fn command(&mut self) -> Result<Command, ParseError<'a>> {
        let keyword = self.keyword()?;
        let cmd;
        match keyword.as_str() {
            "def" => {
                let def_cmd = self.def_cmd(keyword)?;
                cmd = Command::DefCmd(def_cmd);
            }
            "#check" => {
                let check_cmd = self.check_cmd(keyword)?;
                cmd = Command::CheckCmd(check_cmd);
            }
            "infixr" => {
                let infixr_cmd = self.infixr_cmd(keyword)?;
                cmd = Command::InfixrCmd(infixr_cmd);
            }
            "infixl" => {
                let infixl_cmd = self.infixl_cmd(keyword)?;
                cmd = Command::InfixlCmd(infixl_cmd);
            }
            "infix" => {
                let infix_cmd = self.infix_cmd(keyword)?;
                cmd = Command::InfixCmd(infix_cmd);
            }
            "prefix" => {
                let prefix_cmd = self.prefix_cmd(keyword)?;
                cmd = Command::PrefixCmd(prefix_cmd);
            }
            "nofix" => {
                let nofix_cmd = self.nofix_cmd(keyword)?;
                cmd = Command::NofixCmd(nofix_cmd);
            }
            "constant" => {
                let const_cmd = self.const_cmd(keyword)?;
                cmd = Command::ConstCmd(const_cmd);
            }
            "axiom" => {
                let axiom_cmd = self.axiom_cmd(keyword)?;
                cmd = Command::AxiomCmd(axiom_cmd);
            }
            "inductive" | "lemma" | "type" | "class" | "meta" | "#eval" => {
                todo!()
            }
            _ => {
                return Self::fail(keyword, "expected command");
            }
        }
        Ok(cmd)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    pub fn parse_term(input: &str) -> Term {
        let mut lex = Lex::new(input, "");
        let token_table = TokenTable::default();
        let mut parser = Parser::new(&mut lex, &token_table);
        parser.term().unwrap()
    }

    pub fn parse_cmd(input: &str) -> Command {
        let mut lex = Lex::new(input, "");
        let token_table = TokenTable::default();
        let mut parser = Parser::new(&mut lex, &token_table);
        parser.command().unwrap()
    }

    #[test]
    fn parse() {
        println!("{:?}", parse_term("λ (x : ℕ → ℕ), x y"));
        println!("{:?}", parse_term("p → (p → q) → q"));
        println!("{:?}", parse_term("λ x y, ∀ P, P x → P y"));

        println!("{:?}", parse_cmd("def id₁ (x : α) : α := x"));
        println!("{:?}", parse_cmd("#check (λ (x : Prop), x)"));
        println!("{:?}", parse_cmd("infixr + : 50 := add"));
    }
}
