use std::iter::FusedIterator;
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

    pub fn eof(file: Arc<File>) -> Self {
        let len = file.len();
        let start = len.saturating_sub(1);
        Self::new(file, start, len)
    }

    pub fn as_str(&self) -> &str {
        self.file
            .contents()
            .get(self.start..self.end)
            .expect("invalid token position")
    }

    pub fn line_column(&self) -> (usize, usize) {
        self.file.line_column_at(self.start)
    }
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

impl PartialEq for Span {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.file, &other.file) && self.start == other.start && self.end == other.end
    }
}

impl Eq for Span {}

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
    pub span: Span,
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
        self.span.as_str()
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?} {}\n{}", self.kind, self.as_str(), self.span)
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
#[error("unrecognizable character at {span}")]
pub struct LexError {
    span: Span,
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
            span: Span::new(lex.file, start, end),
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

    fn advance(&mut self, bytes: usize) -> Span {
        let span = Span::new(Arc::clone(&self.file), self.position, self.position + bytes);
        self.position += bytes;
        span
    }

    pub fn is_eof(&self) -> bool {
        self.clone().next().is_none()
    }

    pub fn span_since(&self, start: LexState) -> Span {
        Span::new(Arc::clone(&self.file), start.position, self.position)
    }

    fn skip_block_comment(&mut self) -> Result<(), LexError> {
        let mut nest = 1;
        let len = self.file.len();

        while nest != 0 {
            if self.position >= len {
                return Err(LexError::from(self.clone()));
            }

            let rest = &self.file.contents()[self.position..];
            let bytes = rest.as_bytes();
            let mut offset = 0;
            loop {
                if offset + 1 >= bytes.len() {
                    return Err(LexError::from(self.clone()));
                }
                match (bytes[offset], bytes[offset + 1]) {
                    (b'/', b'-') => {
                        self.position += offset + 2;
                        nest += 1;
                        break;
                    }
                    (b'-', b'/') => {
                        self.position += offset + 2;
                        nest -= 1;
                        break;
                    }
                    _ => {
                        offset += 1;
                    }
                }
            }
        }

        Ok(())
    }
}

impl Iterator for Lex {
    type Item = std::result::Result<Token, LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        // Avoid capturing because of performance issue
        static RE: LazyLock<Regex> = LazyLock::new(|| {
            regex::Regex::new(concat!(
                r"^(?:",
                r"\s+|--.*|/-|", // Whitespace and Comments
                r"[\p{Alphabetic}_][\p{Alphabetic}\p{Number}_']*|", // Ident
                r"\.[\p{Alphabetic}_][\p{Alphabetic}\p{Number}_']*|", // Field
                r"[(){}\[\]«»,]|:=|∃!|\.0|\.1|\.\{|\$\{|[\p{Symbol}\p{Punctuation}&&[^(){}\[\]«»,.]]|\.\.\.|", // Symbol
                r"0|[1-9][0-9]*", // NumLit
                r")"
            ))
            .unwrap()
        });

        loop {
            if self.file.len() == self.position {
                return None;
            }

            let contents = self.file.contents();
            let Some(m) = RE.find(&contents[self.position..]) else {
                return Some(Err(LexError::from(self.clone())));
            };

            debug_assert_eq!(m.start(), 0);
            let text = m.as_str();

            if text.chars().next().is_some_and(char::is_whitespace) {
                self.position += m.end();
                continue;
            }

            if text.starts_with("--") {
                self.position += m.end();
                continue;
            }

            if text == "/-" {
                self.position += m.end();
                match self.skip_block_comment() {
                    Ok(()) => continue,
                    Err(err) => return Some(Err(err)),
                }
            }

            let first = text.chars().next().expect("token text should not be empty");
            let kind = if text
                .strip_prefix('.')
                .and_then(|rest| rest.chars().next())
                .is_some_and(|c| c == '_' || c.is_alphabetic())
            {
                TokenKind::Field
            } else if first == '_' || first.is_alphabetic() {
                match text {
                    "λ" | "_" => TokenKind::Symbol,
                    "infixr" | "nofix" | "infixl" | "infix" | "prefix" | "axiom" | "def"
                    | "lemma" | "const" | "type" | "inductive" | "structure" | "instance"
                    | "class" | "as" => TokenKind::Keyword,
                    _ => TokenKind::Ident,
                }
            } else if first.is_ascii_digit() {
                TokenKind::NumLit
            } else {
                TokenKind::Symbol
            };
            let span = self.advance(m.end());
            return Some(Ok(Token { kind, span }));
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
