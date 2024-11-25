use std::ops::Range;
use std::sync::LazyLock;

use regex::Regex;
use thiserror::Error;

#[derive(Debug, Clone)]
pub struct SourceInfo<'a> {
    line: usize,   // 1-origin
    column: usize, // 1-origin
    range: Range<usize>,
    input: &'a str,
}

impl<'a> SourceInfo<'a> {
    pub fn eof(input: &'a str) -> Self {
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

impl<'a> std::fmt::Display for SourceInfo<'a> {
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
pub enum TokenKind {
    Ident,   // e.g. "foo", "α", "Prop", "foo.bar.baz"
    Symbol,  // e.g. "+", ":", "λ", ",", "_"
    NumLit,  // e.g. "0", "42"
    Keyword, // e.g. "infixr", "def", "lemma"
}

#[derive(Debug, Clone)]
pub struct Token<'a> {
    pub kind: TokenKind,
    pub source_info: SourceInfo<'a>,
}

impl<'a> Token<'a> {
    pub fn is_ident(&self) -> bool {
        self.kind == TokenKind::Ident
    }

    pub fn is_symbol(&self) -> bool {
        self.kind == TokenKind::Symbol
    }

    pub fn is_num_lit(&self) -> bool {
        self.kind == TokenKind::NumLit
    }

    pub fn is_keyword(&self) -> bool {
        self.kind == TokenKind::Keyword
    }

    pub fn as_str(&self) -> &str {
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
}

#[derive(Debug, Clone, Copy)]
pub struct LexState {
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

    pub fn input(&self) -> &'a str {
        self.input
    }

    pub fn save(&self) -> LexState {
        LexState {
            position: self.position,
            line: self.line,
            column: self.column,
        }
    }

    pub fn restore(&mut self, state: LexState) {
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

        static RE: LazyLock<Regex> = LazyLock::new(|| {
            let s = &[
                (Kind::Space, r"\s+|--.*|/-"),
                (
                    Kind::Ident,
                    r"[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*(\.[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*)*",
                ),
                (
                    Kind::Symbol,
                    r"[(){}\[\]⟨⟩⟪⟫,]|\.\{|\$\{|[\p{Symbol}\p{Punctuation}&&[^(){}\[\]⟨⟩⟪⟫,.]]+",
                ),
                (Kind::NumLit, r"0|[1-9][0-9]*"),
            ]
            .iter()
            .map(|(kind, re)| format!("(?P<{:?}>{})", kind, re))
            .collect::<Vec<_>>()
            .join("|");
            regex::Regex::new(&format!("^(?:{})", s)).unwrap()
        });

        static RE_BLOCK_COMMENT: LazyLock<Regex> =
            LazyLock::new(|| regex::Regex::new("^(?s:.*?)(?:(?P<start>/-)|(?P<end>-/))").unwrap());

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
                    "infixr" | "nofix" | "infixl" | "infix" | "prefix" | "axiom" | "def"
                    | "lemma" | "const" | "type" => {
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
