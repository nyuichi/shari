use crate::cmd::{
    Cmd, CmdAxiom, CmdDef, CmdInfix, CmdInfixl, CmdInfixr, CmdNofix, CmdPrefix, Fixity, Operator,
};
use crate::kernel::proof::{
    mk_proof_assump, mk_proof_const, mk_proof_conv, mk_proof_forall_elim, mk_proof_forall_intro,
    mk_proof_imp_elim, mk_proof_imp_intro, Proof, Prop,
};
use crate::kernel::tt::{
    mk_app, mk_const, mk_fresh_type_mvar, mk_local, mk_path_beta, mk_path_congr_abs,
    mk_path_congr_app, mk_path_delta, mk_path_refl, mk_path_symm, mk_path_trans, mk_type_arrow,
    mk_type_const, mk_type_local, Name, Path, Term, Type,
};

use anyhow::bail;
use core::ops::Range;
use once_cell::sync::Lazy;
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::mem;
use thiserror::Error;

#[derive(Debug, Clone)]
pub struct SourceInfo<'a> {
    line: usize,   // 1-origin
    column: usize, // 1-origin
    range: Range<usize>,
    input: &'a str,
}

impl<'a> SourceInfo<'a> {
    fn eof(input: &'a str) -> Self {
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
        }
    }

    fn as_str(&self) -> &str {
        self.input
            .get(self.range.clone())
            .expect("invalid token position")
    }
}

impl<'a> Display for SourceInfo<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:{}\n\n", self.line, self.column)?;
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
            "^".repeat(
                self.input
                    .get(self.range.clone())
                    .unwrap_or("")
                    .chars()
                    .count()
            )
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TokenKind {
    Ident,  // e.g. "foo", "α", "Prop", "foo.bar.baz"
    Symbol, // e.g. "+", ":", "λ", ",", "_"
    NumLit, // e.g. "0", "42"
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

    fn as_str(&self) -> &str {
        self.source_info.as_str()
    }
}

impl<'a> Display for Token<'a> {
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
}

#[derive(Debug, Clone, Copy)]
struct LexState {
    position: usize,
    line: usize,
    column: usize,
}

#[derive(Debug, Clone, Error)]
#[error("unrecognizable character at line {line}, column {column}")]
pub struct LexError {
    line: usize,
    column: usize,
}

impl<'a> From<Lex<'a>> for LexError {
    fn from(lex: Lex<'a>) -> Self {
        Self {
            line: lex.line,
            column: lex.column,
        }
    }
}

impl<'a> Lex<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            position: 0,
            line: 1,
            column: 1,
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
            NumLit,
        }

        static RE: Lazy<Regex> = Lazy::new(|| {
            let s = &[
                (Kind::Space, r"\s+|--.*|/-"),
                (
                    Kind::Ident,
                    r"[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*(\.[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*)*",
                ),
                (
                    Kind::Symbol,
                    r"[(){}⟨⟩⟪⟫,]|\.\{|\$\{|[\p{Symbol}\p{Punctuation}&&[^(){}⟨⟩⟪⟫,]]+",
                ),
                (Kind::NumLit, r"0|[1-9][0-9]*"),
            ]
            .iter()
            .map(|(kind, re)| format!("(?P<{:?}>{})", kind, re))
            .collect::<Vec<_>>()
            .join("|");
            regex::Regex::new(&format!("^(?:{})", s)).unwrap()
        });

        static RE_BLOCK_COMMENT: Lazy<Regex> =
            Lazy::new(|| regex::Regex::new("^(?s:.*?)(?:(?P<start>/-)|(?P<end>-/))").unwrap());

        loop {
            if self.input.len() == self.position {
                return None;
            }
            let cap = match RE.captures(&self.input[self.position..]) {
                None => return Some(Err(LexError::from(self.clone()))),
                Some(cap) => cap,
            };

            // skip whitespaces
            if let Some(m) = cap.name(&format!("{:?}", Kind::Space)) {
                self.advance(m.range().count());
                if m.as_str() == "/-" {
                    let mut nest = 1;
                    while nest != 0 {
                        if self.input.len() == self.position {
                            return None;
                        }
                        let cap = match RE_BLOCK_COMMENT.captures(&self.input[self.position..]) {
                            None => return Some(Err(LexError::from(self.clone()))),
                            Some(cap) => cap,
                        };
                        if cap.name("start").is_some() {
                            nest += 1;
                            self.advance(cap.get(0).unwrap().range().count());
                        } else {
                            assert!(cap.name("end").is_some());
                            nest -= 1;
                            self.advance(cap.get(0).unwrap().range().count());
                        }
                    }
                }
                continue;
            }

            // change the position of the cursor
            let source_info = self.advance(cap.get(0).unwrap().range().count());
            let text = source_info.as_str();

            let kind;
            if cap.name(&format!("{:?}", Kind::Ident)).is_some() {
                match text {
                    "λ" | "_" => {
                        kind = TokenKind::Symbol;
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

#[derive(Default, Debug, Clone)]
pub struct TokenTable {
    led: HashMap<String, Operator>,
    nud: HashMap<String, Operator>,
}

impl TokenTable {
    pub fn add(&mut self, op: Operator) -> anyhow::Result<()> {
        match op.fixity {
            Fixity::Infix | Fixity::Infixl | Fixity::Infixr => {
                let sym = op.symbol.clone();
                if self.led.insert(sym, op).is_some() {
                    bail!("symbol already defined")
                }
            }
            Fixity::Nofix | Fixity::Prefix => {
                let sym = op.symbol.clone();
                if self.nud.insert(sym, op).is_some() {
                    bail!("symbol already defined")
                }
            }
        };
        Ok(())
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
    Uexists,
    Paren,
    Bracket,
    Brace,
    Hole,
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
        }
    }

    fn get_nud(&self, token: &Token) -> Option<Nud> {
        match token.kind {
            TokenKind::Ident => Some(Nud::Var),
            TokenKind::Symbol => {
                let lit = token.as_str();
                match lit {
                    "(" => Some(Nud::Paren),
                    "⟨" => Some(Nud::Bracket),
                    "λ" => Some(Nud::Abs),
                    "∀" => Some(Nud::Forall),
                    "∃" => Some(Nud::Exists),
                    "∃!" => Some(Nud::Uexists),
                    "{" => Some(Nud::Brace),
                    "${" => Some(Nud::Hole),
                    _ => self.nud.get(token.as_str()).map(|op| Nud::User(op.clone())),
                }
            }
            TokenKind::NumLit => Some(Nud::NumLit),
        }
    }
}

#[derive(Debug, Error)]
pub enum ParseError {
    #[error("{lex_error}")]
    Lex { lex_error: LexError },
    #[error("parse error: {message} at {source_info}")]
    Parse {
        message: String,
        source_info: String,
    },
    #[error("unexpected end of input at {source_info}")]
    Eof { source_info: String },
}

// Since LexError is not 'static we only want #[from] and don't need #[source],
// but this is impossible because #[from] attibute always implies #[source].
// So I am implementing it manually.
impl From<LexError> for ParseError {
    fn from(err: LexError) -> Self {
        Self::Lex { lex_error: err }
    }
}

#[derive(Debug, Default, Clone)]
pub struct Context {
    pub type_consts: HashSet<Name>,
    // mapping name to type arity
    pub consts: HashMap<Name, usize>,
}

pub struct Parser<'a, 'b> {
    lex: &'b mut Lex<'a>,
    tt: &'b TokenTable,
    ctx: &'b Context,
    locals: Vec<Name>,
    allow_holes: bool,
    pub holes: Vec<Name>,
    pub type_holes: Vec<Name>,
}

impl<'a, 'b> Parser<'a, 'b> {
    pub fn new(
        lex: &'b mut Lex<'a>,
        tt: &'b TokenTable,
        ctx: &'b Context,
        allow_holes: bool,
    ) -> Self {
        Self {
            lex,
            tt,
            ctx,
            locals: vec![],
            allow_holes,
            holes: vec![],
            type_holes: vec![],
        }
    }

    fn fail<R>(token: Token<'a>, message: impl Into<String>) -> Result<R, ParseError> {
        Err(ParseError::Parse {
            message: message.into(),
            source_info: token.source_info.to_string(),
        })
    }

    fn eof_error(&self) -> ParseError {
        ParseError::Eof {
            source_info: SourceInfo::eof(self.lex.input).to_string(),
        }
    }

    fn optional<F, R>(&mut self, f: F) -> Option<R>
    where
        F: FnOnce(&mut Self) -> Result<R, ParseError>,
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

    fn peek(&mut self) -> Result<Token<'a>, ParseError> {
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

    pub fn eof(&mut self) -> Result<(), ParseError> {
        if let Some(token) = self.peek_opt() {
            Self::fail(token, "expected EOF but tokens remain")?;
        }
        Ok(())
    }

    fn any_token(&mut self) -> Result<Token<'a>, ParseError> {
        self.lex
            .next()
            .transpose()
            .expect("lex error")
            .ok_or_else(|| self.eof_error())
    }

    fn ident(&mut self) -> Result<Token<'a>, ParseError> {
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

    fn symbol(&mut self) -> Result<Token<'a>, ParseError> {
        let token = self.any_token()?;
        if !token.is_symbol() {
            return Self::fail(token, "expected symbol");
        }
        Ok(token)
    }

    fn expect_symbol(&mut self, sym: &str) -> Result<(), ParseError> {
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

    fn num_lit(&mut self) -> Result<Token<'a>, ParseError> {
        let token = self.any_token()?;
        if !token.is_num_lit() {
            return Self::fail(token, "expected numeral literal");
        }
        Ok(token)
    }

    fn name(&mut self) -> Result<Name, ParseError> {
        Ok(Name::try_from(self.ident()?.as_str()).expect("logic flaw"))
    }

    fn name_opt(&mut self) -> Option<Name> {
        self.ident_opt()
            .map(|token| Name::try_from(token.as_str()).expect("logic flaw"))
    }

    fn type_hole(&mut self, token: Token<'a>) -> Result<Type, ParseError> {
        if !self.allow_holes {
            return Self::fail(token, "hole not allowed in this mode");
        }
        self.expect_symbol("}")?;
        let name = Name::fresh();
        self.type_holes.push(name);
        Ok(mk_type_local(name))
    }

    fn type_primary(&mut self) -> Result<Type, ParseError> {
        let token = self.any_token()?;
        if token.is_ident() {
            let name: Name = token.as_str().try_into().expect("logic flaw");
            match self.ctx.type_consts.get(&name) {
                Some(_) => Ok(mk_type_const(name)),
                None => Ok(mk_type_local(name)),
            }
        } else if token.is_symbol() && token.as_str() == "(" {
            let t = self.ty()?;
            self.expect_symbol(")")?;
            Ok(t)
        } else if token.is_symbol() && token.as_str() == "${" {
            self.type_hole(token)
        } else {
            Self::fail(token, "expected a primary type expression")
        }
    }

    pub fn ty(&mut self) -> Result<Type, ParseError> {
        self.subty(0)
    }

    fn subty(&mut self, rbp: usize) -> Result<Type, ParseError> {
        let mut t = self.type_primary()?;
        while let Some(token) = self.peek_opt() {
            if token.is_symbol() && token.as_str() == "→" {
                if rbp >= 25 {
                    break;
                }
                self.advance();
                t = mk_type_arrow(t, self.subty(24)?);
            } else if token.is_ident()
                || (token.is_symbol() && token.as_str() == "(")
                || (token.is_symbol() && token.as_str() == "${")
            {
                if rbp >= 1024 {
                    break;
                }
                t.apply([self.subty(1024)?]);
            } else {
                break;
            }
        }
        Ok(t)
    }

    /// typed parameters e.g. `"(x y : T)"`
    fn parameter(&mut self, _token: Token) -> Result<(Vec<Name>, Type), ParseError> {
        let mut idents = vec![];
        // needs at least one parameter
        idents.push(self.name()?);
        while let Some(name) = self.name_opt() {
            idents.push(name);
        }
        self.expect_symbol(":")?;
        let t = self.ty()?;
        self.expect_symbol(")")?;
        Ok((idents, t))
    }

    fn parameters(&mut self) -> Result<Vec<(Name, Option<Type>)>, ParseError> {
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

    pub fn term(&mut self) -> Result<Term, ParseError> {
        self.subterm(0)
    }

    fn term_opt(&mut self) -> Option<Term> {
        self.optional(|this| this.term())
    }

    fn term_abs(&mut self, token: Token<'a>) -> Result<Term, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            return Self::fail(token, "empty binding");
        }
        let mut binders = vec![];
        for (name, ty) in params {
            let ty = match ty {
                Some(ty) => ty,
                None => mk_fresh_type_mvar(),
            };
            binders.push((name, ty));
        }
        for (name, _) in &binders {
            self.locals.push(*name);
        }
        let mut m = self.subterm(0)?;
        for _ in 0..binders.len() {
            self.locals.pop();
        }
        for (name, t) in binders.into_iter().rev() {
            m.abs(name, t, name);
        }
        Ok(m)
    }

    // TODO remove
    fn mk_const_unchecked(&self, name: &str) -> Term {
        let ty_arity = self
            .ctx
            .consts
            .get(&name.try_into().unwrap())
            .copied()
            .unwrap_or_else(|| panic!("unknown constant: {name}"));
        let mut ty_args = vec![];
        for _ in 0..ty_arity {
            ty_args.push(mk_fresh_type_mvar());
        }
        mk_const(Name::try_from(name).expect("invalid name"), ty_args)
    }

    fn term_forall(&mut self, token: Token<'a>) -> Result<Term, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            return Self::fail(token, "empty binding");
        }
        let mut binders = vec![];
        for (name, ty) in params {
            let ty = match ty {
                Some(ty) => ty,
                None => mk_fresh_type_mvar(),
            };
            binders.push((name, ty));
        }
        for (name, _) in &binders {
            self.locals.push(*name);
        }
        let mut m = self.subterm(0)?;
        for _ in 0..binders.len() {
            self.locals.pop();
        }
        for (name, t) in binders.into_iter().rev() {
            m.abs(name, t, name);
            let f = mem::take(&mut m);
            m = self.mk_const_unchecked("forall");
            m.apply(vec![f]);
        }
        Ok(m)
    }

    fn term_exists(&mut self, token: Token<'a>) -> Result<Term, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            return Self::fail(token, "empty binding");
        }
        let mut binders = vec![];
        for (name, ty) in params {
            let ty = match ty {
                Some(ty) => ty,
                None => mk_fresh_type_mvar(),
            };
            binders.push((name, ty));
        }
        for (name, _) in &binders {
            self.locals.push(*name);
        }
        let mut m = self.subterm(0)?;
        for _ in 0..binders.len() {
            self.locals.pop();
        }
        for (name, t) in binders.into_iter().rev() {
            m.abs(name, t, name);
            let f = mem::take(&mut m);
            m = self.mk_const_unchecked("exists");
            m.apply(vec![f]);
        }
        Ok(m)
    }

    fn term_uexists(&mut self, token: Token<'a>) -> Result<Term, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            return Self::fail(token, "empty binding");
        }
        let mut binders = vec![];
        for (name, ty) in params {
            let ty = match ty {
                Some(ty) => ty,
                None => mk_fresh_type_mvar(),
            };
            binders.push((name, ty));
        }
        for (name, _) in &binders {
            self.locals.push(*name);
        }
        let mut m = self.subterm(0)?;
        for _ in 0..binders.len() {
            self.locals.pop();
        }
        for (name, t) in binders.into_iter().rev() {
            m.abs(name, t, name);
            let f = mem::take(&mut m);
            m = self.mk_const_unchecked("uexists");
            m.apply(vec![f]);
        }
        Ok(m)
    }

    fn term_setsep(&mut self, _token: Token<'a>) -> Result<Term, ParseError> {
        let name = self.name()?;
        self.expect_symbol("|")?;
        let t = mk_fresh_type_mvar();
        self.locals.push(name);
        let mut m = self.subterm(0)?;
        self.locals.pop();
        m.abs(name, t, name);
        self.expect_symbol("}")?;
        Ok(m)
    }

    fn term_var(&mut self, token: Token<'a>, entity: Option<Name>) -> Result<Term, ParseError> {
        let name = match entity {
            None => Name::try_from(token.as_str()).expect("logic flaw"),
            Some(s) => s,
        };
        for x in self.locals.iter().rev() {
            if x == &name {
                return Ok(mk_local(name));
            }
        }
        let Some(ty_arity) = self.ctx.consts.get(&name).copied() else {
            return Ok(mk_local(name));
        };
        let mut ty_args = vec![];
        if let Some(_token) = self.expect_symbol_opt(".{") {
            if self.expect_symbol_opt("}").is_none() {
                loop {
                    ty_args.push(self.ty()?);
                    if self.expect_symbol_opt(",").is_none() {
                        break;
                    }
                }
                self.expect_symbol("}")?;
            }
        } else {
            for _ in 0..ty_arity {
                ty_args.push(mk_fresh_type_mvar());
            }
        }
        Ok(mk_const(name, ty_args))
    }

    fn term_hole(&mut self, token: Token<'a>) -> Result<Term, ParseError> {
        if !self.allow_holes {
            return Self::fail(token, "hole not allowed in this mode");
        }
        self.expect_symbol("}")?;
        let name = Name::fresh();
        self.holes.push(name);
        Ok(mk_local(name))
    }

    fn subterm(&mut self, rbp: usize) -> Result<Term, ParseError> {
        let token = self.any_token()?;
        // nud
        let nud = match self.tt.get_nud(&token) {
            None => todo!("nud unknown: {}", token),
            Some(nud) => nud,
        };
        let mut left = match nud {
            Nud::Var => self.term_var(token, None)?,
            Nud::Abs => self.term_abs(token)?,
            Nud::Paren => {
                let m = self.subterm(0)?;
                self.expect_symbol(")")?;
                m
            }
            Nud::Bracket => {
                let mut terms = vec![];
                while let Some(m) = self.term_opt() {
                    terms.push(m);
                    if self.expect_symbol_opt(",").is_none() {
                        break;
                    }
                }
                self.expect_symbol("⟩")?;
                // right associative encoding:
                // ⟨⟩ ⇒ star
                // ⟨m⟩ ⇒ m
                // ⟨m,n,l⟩ ⇒ ⟨m, ⟨n, l⟩⟩
                match terms.len() {
                    0 => self.mk_const_unchecked("star"),
                    1 => terms.pop().unwrap(),
                    _ => {
                        let mut m = terms.pop().unwrap();
                        for n in terms.into_iter().rev() {
                            let mut x = self.mk_const_unchecked("pair");
                            x.apply(vec![n, m]);
                            m = x;
                        }
                        m
                    }
                }
            }
            Nud::Forall => self.term_forall(token)?,
            Nud::Exists => self.term_exists(token)?,
            Nud::Uexists => self.term_uexists(token)?,
            Nud::Brace => self.term_setsep(token)?,
            Nud::Hole => self.term_hole(token)?,
            Nud::User(op) => match op.fixity {
                Fixity::Nofix => self.term_var(token, Some(op.entity))?,
                Fixity::Prefix => {
                    let mut fun = self.term_var(token, Some(op.entity))?;
                    let arg = self.subterm(op.prec)?;
                    fun.apply(vec![arg]);
                    fun
                }
                Fixity::Infix | Fixity::Infixl | Fixity::Infixr => unreachable!(),
            },
            Nud::NumLit => Self::fail(token, "numeric literal is unsupported")?,
        };
        while let Some(token) = self.peek_opt() {
            let led = match self.tt.get_led(&token) {
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
                    left.apply(vec![right]);
                }
                Led::User(op) => {
                    let prec = match op.fixity {
                        Fixity::Infix | Fixity::Infixl => prec,
                        Fixity::Infixr => prec - 1,
                        Fixity::Nofix | Fixity::Prefix => unreachable!("op = {op:?}"),
                    };
                    self.advance();
                    let mut fun = self.term_var(token, Some(op.entity))?;
                    let right = self.subterm(prec)?;
                    fun.apply(vec![left, right]);
                    left = fun;
                }
            }
        }
        Ok(left)
    }

    fn prop(&mut self) -> Result<Prop, ParseError> {
        Ok(Prop {
            target: self.term()?,
        })
    }

    // pub fn proof(&mut self) -> Result<Proof, ParseError> {
    //     if let Some(_) = self.expect_symbol_opt("(") {
    //         let h = self.proof()?;
    //         self.expect_symbol(")")?;
    //         return Ok(h);
    //     }
    //     let keyword = self.ident()?;
    //     match keyword.as_str() {
    //         "assump" => {
    //             let prop = self.prop()?;
    //             Ok(mk_proof_assump(prop))
    //         }
    //         "imp_intro" => {
    //             let prop = self.prop()?;
    //             self.expect_symbol(",")?;
    //             let proof = self.proof()?;
    //             Ok(mk_proof_imp_intro(prop, proof))
    //         }
    //         "imp_elim" => {
    //             let h1 = self.proof()?;
    //             self.expect_symbol(",")?;
    //             let h2 = self.proof()?;
    //             Ok(mk_proof_imp_elim(h1, h2))
    //         }
    //         "forall_intro" => {
    //             let params = self.parameters()?;
    //             self.expect_symbol(",")?;
    //             let mut proof = self.proof()?;
    //             for (name, ty) in params.into_iter().rev() {
    //                 let ty = match ty {
    //                     Some(t) => t,
    //                     None => mk_fresh_type_mvar(),
    //                 };
    //                 proof = mk_proof_forall_intro(name, ty, proof);
    //             }
    //             Ok(proof)
    //         }
    //         "forall_elim" => {
    //             let m = self.term()?;
    //             self.expect_symbol(",")?;
    //             let h = self.proof()?;
    //             Ok(mk_proof_forall_elim(m, h))
    //         }
    //         "conv" => {
    //             let path = self.path()?;
    //             self.expect_symbol(",")?;
    //             let h = self.proof()?;
    //             Ok(mk_proof_conv(path, h))
    //         }
    //         _ => {
    //             let name = Name::intern(keyword.as_str()).unwrap();
    //             let mut ty_args = vec![];
    //             if let Some(_token) = self.expect_symbol_opt(".{") {
    //                 if self.expect_symbol_opt("}").is_none() {
    //                     loop {
    //                         ty_args.push(self.ty()?);
    //                         if self.expect_symbol_opt(",").is_none() {
    //                             break;
    //                         }
    //                     }
    //                     self.expect_symbol("}")?;
    //                 }
    //             }
    //             Ok(mk_proof_const(name, ty_args))
    //         }
    //     }
    // }

    // pub fn path(&mut self) -> Result<Path, ParseError> {
    //     if let Some(_) = self.expect_symbol_opt("(") {
    //         let h = self.path()?;
    //         println!("{h}");
    //         self.expect_symbol(")")?;
    //         return Ok(h);
    //     }
    //     let keyword = self.ident()?;
    //     match keyword.as_str() {
    //         "refl" => {
    //             let m = self.term()?;
    //             Ok(mk_path_refl(m))
    //         }
    //         "symm" => {
    //             let path = self.path()?;
    //             Ok(mk_path_symm(path))
    //         }
    //         "trans" => {
    //             let h1 = self.path()?;
    //             self.expect_symbol(",")?;
    //             let h2 = self.path()?;
    //             Ok(mk_path_trans(h1, h2))
    //         }
    //         "congr_app" => {
    //             let h1 = self.path()?;
    //             self.expect_symbol(",")?;
    //             let h2 = self.path()?;
    //             Ok(mk_path_congr_app(h1, h2))
    //         }
    //         "congr_abs" => {
    //             let x = self.name()?;
    //             self.expect_symbol(",")?;
    //             let t = self.ty()?;
    //             self.expect_symbol(",")?;
    //             let h = self.path()?;
    //             Ok(mk_path_congr_abs(x, t, h))
    //         }
    //         "beta" => {
    //             let m = self.term()?;
    //             Ok(mk_path_beta(m))
    //         }
    //         "delta" => {
    //             let name = self.name()?;
    //             let mut ty_args = vec![];
    //             if let Some(_token) = self.expect_symbol_opt(".{") {
    //                 if self.expect_symbol_opt("}").is_none() {
    //                     loop {
    //                         ty_args.push(self.ty()?);
    //                         if self.expect_symbol_opt(",").is_none() {
    //                             break;
    //                         }
    //                     }
    //                     self.expect_symbol("}")?;
    //                 }
    //             }
    //             Ok(mk_path_delta(name, ty_args))
    //         }
    //         _ => Self::fail(keyword, "unknown path expression")?,
    //     }
    // }

    pub fn cmd(&mut self) -> Result<Cmd, ParseError> {
        let keyword = self.ident()?;
        let cmd = match keyword.as_str() {
            "infixr" => {
                let infixr_cmd = self.infixr_cmd(keyword)?;
                Cmd::Infixr(infixr_cmd)
            }
            "infixl" => {
                let infixl_cmd = self.infixl_cmd(keyword)?;
                Cmd::Infixl(infixl_cmd)
            }
            "infix" => {
                let infix_cmd = self.infix_cmd(keyword)?;
                Cmd::Infix(infix_cmd)
            }
            "prefix" => {
                let prefix_cmd = self.prefix_cmd(keyword)?;
                Cmd::Prefix(prefix_cmd)
            }
            "nofix" => {
                let nofix_cmd = self.nofix_cmd(keyword)?;
                Cmd::Nofix(nofix_cmd)
            }
            "def" => {
                let def_cmd = self.def_cmd(keyword)?;
                Cmd::Def(def_cmd)
            }
            "axiom" => {
                let axiom_cmd = self.axiom_cmd(keyword)?;
                Cmd::Axiom(axiom_cmd)
            }
            // "lemma" => {
            //     let lemma_cmd = self.lemma_cmd(keyword)?;
            //     Cmd::Lemma(lemma_cmd)
            // }
            _ => {
                return Self::fail(keyword, "expected command");
            }
        };
        Ok(cmd)
    }

    fn infixr_cmd(&mut self, _token: Token) -> Result<CmdInfixr, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(CmdInfixr {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn infixl_cmd(&mut self, _token: Token) -> Result<CmdInfixl, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(CmdInfixl {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn infix_cmd(&mut self, _token: Token) -> Result<CmdInfix, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(CmdInfix {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn prefix_cmd(&mut self, _token: Token) -> Result<CmdPrefix, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(CmdPrefix {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn nofix_cmd(&mut self, _token: Token) -> Result<CmdNofix, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(CmdNofix {
            op: op.as_str().to_owned(),
            entity,
        })
    }

    fn def_cmd(&mut self, _token: Token) -> Result<CmdDef, ParseError> {
        let name = self.name()?;
        let mut local_types = vec![];
        if let Some(_token) = self.expect_symbol_opt(".{") {
            if self.expect_symbol_opt("}").is_none() {
                loop {
                    let token = self.ident()?;
                    let tv = Name::intern(token.as_str()).unwrap();
                    for v in &local_types {
                        if &tv == v {
                            return Self::fail(token, "duplicate type variable")?;
                        }
                    }
                    local_types.push(tv);
                    if self.expect_symbol_opt(",").is_none() {
                        break;
                    }
                }
                self.expect_symbol("}")?;
            }
        }
        let mut params = vec![];
        while let Some(token) = self.expect_symbol_opt("(") {
            let (names, t) = self.parameter(token)?;
            for name in names {
                params.push((name, t.clone()));
            }
        }
        self.expect_symbol(":")?;
        let mut t = self.ty()?;
        self.expect_symbol(":=")?;
        let mut m = self.term()?;
        for (var, ty) in params.into_iter().rev() {
            m.abs(var, ty.clone(), var);
            t = mk_type_arrow(ty, t);
        }
        Ok(CmdDef {
            name,
            local_types,
            ty: t,
            target: m,
        })
    }

    fn axiom_cmd(&mut self, _token: Token) -> Result<CmdAxiom, ParseError> {
        let name = self.name()?;
        let mut local_types = vec![];
        if let Some(_token) = self.expect_symbol_opt(".{") {
            if self.expect_symbol_opt("}").is_none() {
                loop {
                    let token = self.ident()?;
                    let tv = Name::intern(token.as_str()).unwrap();
                    for v in &local_types {
                        if &tv == v {
                            return Self::fail(token, "duplicate type variable")?;
                        }
                    }
                    local_types.push(tv);
                    if self.expect_symbol_opt(",").is_none() {
                        break;
                    }
                }
                self.expect_symbol("}")?;
            }
        }
        let mut params = vec![];
        while let Some(token) = self.expect_symbol_opt("(") {
            let (names, t) = self.parameter(token)?;
            for name in names {
                params.push((name, t.clone()));
            }
        }
        self.expect_symbol(":")?;
        let mut m = self.term()?;
        for (var, ty) in params.into_iter().rev() {
            m.abs(var, ty.clone(), var);
            m = mk_app(self.mk_const_unchecked("forall"), m);
        }
        Ok(CmdAxiom {
            name,
            local_types,
            target: Prop { target: m },
        })
    }

    // fn lemma_cmd(&mut self, _token: Token) -> Result<CmdLemma, ParseError> {
    //     let name = self.name()?;
    //     let mut local_types = vec![];
    //     if let Some(_token) = self.expect_symbol_opt(".{") {
    //         if self.expect_symbol_opt("}").is_none() {
    //             loop {
    //                 let token = self.ident()?;
    //                 let tv = Name::intern(token.as_str()).unwrap();
    //                 for v in &local_types {
    //                     if &tv == v {
    //                         return Self::fail(token, "duplicate type variable")?;
    //                     }
    //                 }
    //                 local_types.push(tv);
    //                 if self.expect_symbol_opt(",").is_none() {
    //                     break;
    //                 }
    //             }
    //             self.expect_symbol("}")?;
    //         }
    //     }
    //     let mut params = vec![];
    //     while let Some(token) = self.expect_symbol_opt("(") {
    //         let (names, t) = self.parameter(token)?;
    //         for name in names {
    //             params.push((name, t.clone()));
    //         }
    //     }
    //     self.expect_symbol(":")?;
    //     let mut m = self.term()?;
    //     self.expect_symbol(":=")?;
    //     let mut proof = self.proof()?;
    //     for (var, ty) in params.into_iter().rev() {
    //         m.abs(var, ty.clone(), var);
    //         m = mk_app(self.mk_const_unchecked("forall"), m);
    //         proof = mk_proof_forall_intro(var, ty, proof);
    //     }
    //     let target = Prop { target: m };
    //     Ok(CmdLemma {
    //         name,
    //         local_types,
    //         target,
    //         proof,
    //     })
    // }
}

// #[test]
// fn test_parse() {
//     use crate::env::{DeclConst, TermDecl};
//     use crate::kernel::proof::mk_type_prop;

//     let ops = [
//         Operator {
//             symbol: "⊤".to_owned(),
//             fixity: Fixity::Nofix,
//             prec: usize::MAX,
//             entity: "top".try_into().unwrap(),
//         },
//         Operator {
//             symbol: "∧".to_owned(),
//             fixity: Fixity::Infixr,
//             prec: 35,
//             entity: "and".try_into().unwrap(),
//         },
//         Operator {
//             symbol: "¬".to_owned(),
//             fixity: Fixity::Prefix,
//             prec: 40,
//             entity: "not".try_into().unwrap(),
//         },
//     ];

//     let mut env = Env::new_kernel();
//     for op in ops {
//         env.add_notation(op).unwrap();
//     }

//     env.add_term_decl(
//         "top".try_into().unwrap(),
//         TermDecl::Const(DeclConst {
//             local_types: vec![],
//             ty: mk_type_prop(),
//         }),
//     )
//     .unwrap();

//     env.add_term_decl(
//         "not".try_into().unwrap(),
//         TermDecl::Const(DeclConst {
//             local_types: vec![],
//             ty: mk_type_arrow(mk_type_prop(), mk_type_prop()),
//         }),
//     )
//     .unwrap();

//     env.add_term_decl(
//         "and".try_into().unwrap(),
//         TermDecl::Const(DeclConst {
//             local_types: vec![],
//             ty: mk_type_arrow(
//                 mk_type_prop(),
//                 mk_type_arrow(mk_type_prop(), mk_type_prop()),
//             ),
//         }),
//     )
//     .unwrap();

//     struct Display<'a> {
//         env: &'a Env,
//         m: Term,
//     }

//     impl<'a> std::fmt::Display for Display<'a> {
//         fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//             Printer::new(self.env).fmt_term(&self.m, f)
//         }
//     }

//     let roundtrip = |s: &str| -> String {
//         let mut lex = Lex::new(s);
//         let mut parser = Parser::new(&mut lex, &env, false);
//         let m = parser.term().unwrap();
//         parser.eof().unwrap();
//         Display { env: &env, m }.to_string()
//     };

//     insta::assert_snapshot!(roundtrip("λ (x : α), x"), @"λ (x : α), x");
//     insta::assert_snapshot!(roundtrip("λ (p q r : Prop), p q r"), @"λ (p : Prop), λ (q : Prop), λ (r : Prop), p q r");
//     insta::assert_snapshot!(roundtrip("λ (φ ψ : Prop), (λ (f : Prop → Prop → Prop), f φ ψ) = (λ (f : Prop → Prop → Prop), f ⊤ ⊤)"), @"λ (φ : Prop), λ (ψ : Prop), (λ (f : Prop → Prop → Prop), f φ ψ) = λ (f : Prop → Prop → Prop), f ⊤ ⊤");
//     insta::assert_snapshot!(roundtrip("λ (p q : Prop), p = (p ∧ q)"), @"λ (p : Prop), λ (q : Prop), p = (p ∧ q)");
//     insta::assert_snapshot!(roundtrip("λ (a b : Prop), (¬a) = b"), @"λ (a : Prop), λ (b : Prop), (¬a) = b");
//     insta::assert_snapshot!(roundtrip("λ (a b : Prop), ¬a = b"), @"λ (a : Prop), λ (b : Prop), ¬a = b");
//     insta::assert_snapshot!(roundtrip("λ (x : w), eq.{u → v} x"), @"λ (x : w), eq.{u → v} x");
// }

// impl FromStr for Type {
//     type Err = ParseError;

//     fn from_str(s: &str) -> Result<Self, Self::Err> {
//         let mut lex = Lex::new(s);
//         let env = Env::get();
//         let mut parser = Parser::new(&mut lex, &env, false);
//         let ty = parser.ty()?;
//         parser.eof()?;
//         Ok(ty)
//     }
// }

// impl FromStr for Term {
//     type Err = ParseError;

//     fn from_str(s: &str) -> Result<Self, Self::Err> {
//         let mut lex = Lex::new(s);
//         let env = Env::get();
//         let mut parser = Parser::new(&mut lex, &env, false);
//         let m = parser.term()?;
//         parser.eof()?;
//         Ok(m)
//     }
// }
