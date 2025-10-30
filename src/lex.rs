use std::iter::FusedIterator;
use std::ops::Range;
use std::sync::{Arc, LazyLock};

use regex::Regex;
use thiserror::Error;

#[derive(Debug)]
pub struct File {
    name: String,
    contents: String,
    lines: Vec<usize>,
}

impl File {
    pub fn new(name: impl Into<String>, contents: impl Into<String>) -> Self {
        let name = name.into();
        let contents = contents.into();
        let mut lines = vec![0];
        for (idx, ch) in contents.char_indices() {
            if ch == '\n' {
                lines.push(idx + ch.len_utf8());
            }
        }
        Self {
            name,
            contents,
            lines,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn contents(&self) -> &str {
        &self.contents
    }

    pub fn len(&self) -> usize {
        self.contents.len()
    }

    pub fn is_empty(&self) -> bool {
        self.contents.is_empty()
    }

    pub fn line_column_at(&self, offset: usize) -> (usize, usize) {
        let offset = offset.min(self.contents.len());
        let line_index = match self.lines.binary_search(&offset) {
            Ok(index) => index,
            Err(index) => index.saturating_sub(1),
        };
        let line_start = *self
            .lines
            .get(line_index)
            .expect("at least one line start is recorded");
        let column = self.contents[line_start..offset].chars().count() + 1;
        (line_index + 1, column)
    }

    pub fn line(&self, line: usize) -> &str {
        if line == 0 || line > self.lines.len() {
            return "";
        }
        let start = self.lines[line - 1];
        let end = if let Some(next_start) = self.lines.get(line) {
            let mut end = *next_start;
            if end > start && self.contents.as_bytes()[end - 1] == b'\n' {
                end -= 1;
            }
            end
        } else {
            self.contents.len()
        };
        &self.contents[start..end]
    }
}

#[derive(Debug, Clone)]
pub struct Span {
    pub file: Arc<File>,
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(file: Arc<File>, start: usize, end: usize) -> Self {
        Self { file, start, end }
    }

    pub fn to_source_info(&self) -> SourceInfo {
        SourceInfo {
            range: self.start..self.end,
            file: Arc::clone(&self.file),
        }
    }
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_source_info())
    }
}

impl PartialEq for Span {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.file, &other.file) && self.start == other.start && self.end == other.end
    }
}

impl Eq for Span {}

#[derive(Debug, Clone)]
pub struct SourceInfo {
    range: Range<usize>,
    file: Arc<File>,
}

impl SourceInfo {
    pub fn new(file: Arc<File>, range: Range<usize>) -> Self {
        Self { range, file }
    }

    pub fn eof(file: Arc<File>) -> Self {
        let len = file.len();
        let start = len.saturating_sub(1);
        Self::new(file, start..len)
    }

    fn as_str(&self) -> &str {
        self.file
            .contents()
            .get(self.range.clone())
            .expect("invalid token position")
    }

    pub fn line_column(&self) -> (usize, usize) {
        self.file.line_column_at(self.range.start)
    }
}

impl std::fmt::Display for SourceInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let (line, column) = self.line_column();
        writeln!(f, "{}:{}:{}\n", self.file.name(), line, column)?;
        let line_text = self.file.line(line);
        writeln!(f, "{}", line_text)?;
        writeln!(
            f,
            "{}{}",
            " ".repeat(column - 1),
            "^".repeat(std::cmp::max(1, self.as_str().chars().count()))
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    Ident,   // e.g. "foo", "α", "Prop"
    Field,   // e.g. ".foo", ".α"
    Symbol,  // e.g. "+", ":", "λ", ",", "_", "..."
    NumLit,  // e.g. "0", "42"
    Keyword, // e.g. "infixr", "def", "lemma"
}

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub source_info: SourceInfo,
}

impl Token {
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

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?} {}\n{}", self.kind, self.as_str(), self.source_info)
    }
}

#[derive(Debug, Clone)]
pub struct Lex {
    file: Arc<File>,
    position: usize,
}

#[derive(Debug, Clone, Copy)]
pub struct LexState {
    position: usize,
}

#[derive(Debug, Clone, Error)]
#[error("unrecognizable character at {source_info}")]
pub struct LexError {
    source_info: SourceInfo,
}

impl From<Lex> for LexError {
    fn from(lex: Lex) -> Self {
        let start = std::cmp::min(lex.position, lex.file.len());
        let end = if start < lex.file.len() {
            let rest = &lex.file.contents()[start..];
            rest.chars()
                .next()
                .map(|c| start + c.len_utf8())
                .unwrap_or(start)
        } else {
            start
        };
        Self {
            source_info: SourceInfo::new(lex.file, start..end),
        }
    }
}

impl Lex {
    pub fn new(file: Arc<File>) -> Self {
        Self { file, position: 0 }
    }

    pub fn input(&self) -> &Arc<File> {
        &self.file
    }

    pub fn save(&self) -> LexState {
        LexState {
            position: self.position,
        }
    }

    pub fn restore(&mut self, state: LexState) {
        self.position = state.position;
    }

    fn advance(&mut self, bytes: usize) -> SourceInfo {
        let source_info =
            SourceInfo::new(Arc::clone(&self.file), self.position..self.position + bytes);
        self.position += bytes;
        source_info
    }

    pub fn is_eof(&self) -> bool {
        self.clone().next().is_none()
    }

    pub fn span_since(&self, start: LexState) -> Span {
        Span::new(Arc::clone(&self.file), start.position, self.position)
    }
}

impl Iterator for Lex {
    type Item = std::result::Result<Token, LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        #[derive(PartialEq, Eq, Debug)]
        enum Kind {
            Space,
            Ident,
            Field,
            Symbol,
            NumLit,
        }

        static RE: LazyLock<Regex> = LazyLock::new(|| {
            let s = &[
                (Kind::Space, r"\s+|--.*|/-"),
                (
                    Kind::Ident,
                    r"[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_']*",
                ),
                (
                    Kind::Field,
                    r"\.[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_']*",
                ),
                (
                    Kind::Symbol,
                    r"[(){}\[\]«»,]|:=|∃!|\.0|\.1|\.\{|\$\{|[\p{Symbol}\p{Punctuation}&&[^(){}\[\]«»,.]]|\.\.\.",
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
            if self.file.len() == self.position {
                return None;
            }
            let input = Arc::clone(&self.file);
            let cap = match RE.captures(&input.contents()[self.position..]) {
                None => return Some(Err(LexError::from(self.clone()))),
                Some(cap) => cap,
            };

            // skip whitespaces
            if let Some(m) = cap.name(&format!("{:?}", Kind::Space)) {
                self.advance(m.range().count());
                if m.as_str() == "/-" {
                    let mut nest = 1;
                    while nest != 0 {
                        if self.file.len() == self.position {
                            return None;
                        }
                        let cap = match RE_BLOCK_COMMENT
                            .captures(&self.file.contents()[self.position..])
                        {
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
                    | "lemma" | "const" | "type" | "local" | "inductive" | "structure"
                    | "instance" | "class" | "as" => {
                        kind = TokenKind::Keyword;
                    }
                    _ => {
                        kind = TokenKind::Ident;
                    }
                }
            } else if cap.name(&format!("{:?}", Kind::Field)).is_some() {
                kind = TokenKind::Field;
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

impl FusedIterator for Lex {}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize(input: &str) -> Vec<Token> {
        let file = Arc::new(File::new("<test>", input.to_owned()));
        Lex::new(file)
            .map(|token| token.expect("lexing failed"))
            .collect()
    }

    #[test]
    fn ident_with_apostrophe() {
        let tokens = tokenize("x'");
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].kind, TokenKind::Ident);
        assert_eq!(tokens[0].as_str(), "x'");
    }

    #[test]
    fn dotted_ident_is_split_into_segments() {
        let tokens = tokenize("foo.bar");
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].kind, TokenKind::Ident);
        assert_eq!(tokens[0].as_str(), "foo");
        assert_eq!(tokens[1].kind, TokenKind::Field);
        assert_eq!(tokens[1].as_str(), ".bar");
    }

    #[test]
    fn dotted_ident_allows_whitespace_before_segment() {
        let tokens = tokenize("foo .bar");
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].kind, TokenKind::Ident);
        assert_eq!(tokens[0].as_str(), "foo");
        assert_eq!(tokens[1].kind, TokenKind::Field);
        assert_eq!(tokens[1].as_str(), ".bar");
    }

    #[test]
    fn dotted_ident_with_apostrophe() {
        let tokens = tokenize("foo.bar'");
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].kind, TokenKind::Ident);
        assert_eq!(tokens[0].as_str(), "foo");
        assert_eq!(tokens[1].kind, TokenKind::Field);
        assert_eq!(tokens[1].as_str(), ".bar'");
    }

    #[test]
    fn dot_followed_by_whitespace_is_invalid() {
        let file = Arc::new(File::new("<test>", "foo . bar"));
        let mut lex = Lex::new(file);
        let first = lex
            .next()
            .expect("first token")
            .expect("lexing first token");
        assert_eq!(first.kind, TokenKind::Ident);
        assert_eq!(first.as_str(), "foo");
        assert!(matches!(lex.next(), Some(Err(_))));
    }

    #[test]
    fn ident_cannot_start_with_apostrophe() {
        let tokens = tokenize("'foo");
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].kind, TokenKind::Symbol);
        assert_eq!(tokens[0].as_str(), "'");
        assert_eq!(tokens[1].kind, TokenKind::Ident);
        assert_eq!(tokens[1].as_str(), "foo");
    }
}
