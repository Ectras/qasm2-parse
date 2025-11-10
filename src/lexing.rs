use std::{
    fs, io,
    ops::Range,
    path::{Path, PathBuf},
    rc::Rc,
};

use logos::{Lexer, Logos, Skip};
use self_cell::self_cell;
use thiserror::Error;

/// A built-in file with standard definitions for QASM2 programs.
static QELIB: &str = include_str!("qelib1.inc");

#[derive(Error, Default, Debug, Clone, PartialEq)]
pub enum LexingError {
    #[error("unclosed block comment")]
    UnclosedComment,
    #[default]
    #[error("unknown symbol")]
    UnknownSymbol,
}

/// Finds the next closing block comment token (`*/`) and skips to it. If none is
/// found, reads until the end and returns an error.
fn skip_to_closing_comment_token(lex: &mut Lexer<TokenKind>) -> Result<Skip, LexingError> {
    if let Some(closing) = lex.remainder().find("*/") {
        // Found closing token, skip to it (inclusive token itself)
        lex.bump(closing + "*/".len());
        Ok(Skip)
    } else {
        // Skip all remaining input and emit an error
        lex.bump(lex.remainder().len());
        Err(LexingError::UnclosedComment)
    }
}

#[derive(Logos, Debug, Clone, Copy, PartialEq)]
#[logos(skip r"[ \t\r\n\f]+")]
#[logos(skip r"//[^\n]*")]
#[logos(subpattern int = "0|[1-9][0-9]*")]
#[logos(subpattern fexp = "[eE][+-]?(?&int)")]
#[logos(error = LexingError)]
pub enum TokenKind {
    #[token("OPENQASM")]
    OPENQASM,
    #[token("include")]
    Include,
    #[token("qreg")]
    Qreg,
    #[token("creg")]
    Creg,
    #[token("opaque")]
    Opaque,
    #[token("reset")]
    Reset,
    #[token("measure")]
    Measure,
    #[token("barrier")]
    Barrier,
    #[token("if", priority = 5)]
    If,
    #[token("pi", priority = 5)]
    Pi,
    #[token("U")]
    U,
    #[token("CX")]
    CX,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token(";")]
    Semicolon,
    #[token(",")]
    Comma,
    #[token(".")]
    Dot,
    #[token("->")]
    Arrow,
    #[token("==")]
    Equals,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Asterisk,
    #[token("/")]
    Slash,
    #[token("^")]
    Caret,
    #[token("sin", priority = 5)]
    Sin,
    #[token("cos", priority = 5)]
    Cos,
    #[token("tan", priority = 5)]
    Tan,
    #[token("exp", priority = 5)]
    Exp,
    #[token("ln", priority = 5)]
    Ln,
    #[token("sqrt")]
    Sqrt,
    #[regex("(?&int)")]
    Integer,
    #[regex("(?&int)(?&fexp)|[.][0-9]+(?&fexp)?|(?&int)[.][0-9]*(?&fexp)?")]
    Float,
    #[regex("\"[^\"\r\t\n]*\"")]
    String,
    #[regex("[a-z][A-Za-z0-9_]*")]
    Identifier,
    #[token("/*", |lex| skip_to_closing_comment_token(lex))]
    BlockComment,
    Eof,
}

impl TokenKind {
    fn is_non_trivial(&self) -> bool {
        matches!(
            self,
            TokenKind::Integer | TokenKind::Float | TokenKind::String | TokenKind::Identifier
        )
    }
}

/// A token with location information.
#[derive(Debug)]
pub struct Token {
    /// The type of this token.
    kind: TokenKind,
    //// The span in bytes in the source.
    span: Range<usize>,
    /// The text of this token if non-trivial (is `None` for e.g. SEMICOLON, DOT, ...)
    text: Option<String>,
    /// The file this token originates from, if any (is `None` if parsing directly from a `&str`).
    file: Option<Rc<PathBuf>>,
}

struct TokenKindLexer<'a>(Lexer<'a, TokenKind>);

self_cell!(
    struct OwningLexer {
        owner: String,
        #[not_covariant]
        dependent: TokenKindLexer,
    }
);

impl OwningLexer {
    /// Creates a new lexer that owns the string it lexes.
    pub fn lexer(text: String) -> Self {
        OwningLexer::new(text, |t| TokenKindLexer(TokenKind::lexer(t)))
    }
}

/// A lexer for lexing multiple files.
///
/// If lexing should continue from a new file, call [`MultiLexer::source_file`].
/// It will then return tokens from this file until it has been read completely and
/// then continue with the previous file. If all files have been read, a final "End
/// of file" token will be emitted.
pub struct MultiLexer {
    lexers: Vec<(Option<Rc<PathBuf>>, OwningLexer)>,
    emitted_eof: bool,
}

impl MultiLexer {
    fn new() -> Self {
        Self {
            lexers: Vec::with_capacity(2),
            emitted_eof: false,
        }
    }

    /// Creates a new lexer by reading from a file.
    pub fn from_file<P>(path: P) -> io::Result<Self>
    where
        P: AsRef<Path>,
    {
        let path = path.as_ref().as_os_str().to_str().unwrap();
        let mut this = MultiLexer::new();
        this.source_file(path)?;
        Ok(this)
    }

    /// Creates a new lexer by reading the given text.
    pub fn from_text(text: String) -> Self {
        let mut this = MultiLexer::new();
        let lexer = OwningLexer::lexer(text);
        this.lexers.push((None, lexer));
        this
    }

    /// Reads the contents of a new file and adds it on top of the lexer stack.
    fn source_file(&mut self, filepath: &str) -> io::Result<()> {
        let path = PathBuf::from(filepath);
        let (path, source) = if filepath == "qelib1.inc" {
            (path, QELIB.to_owned())
        } else {
            let path = path.canonicalize().unwrap();
            let text = fs::read_to_string(&path)?;
            (path, text)
        };
        let path = Some(Rc::new(path));
        let lexer = OwningLexer::lexer(source);
        self.lexers.push((path, lexer));
        Ok(())
    }
}

impl Iterator for MultiLexer {
    type Item = Result<Token, LexingError>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // Get the current lexer (or return EoF / None if there are none)
            let Some((source, lexer)) = self.lexers.last_mut() else {
                if !self.emitted_eof {
                    self.emitted_eof = true;
                    return Some(Ok(Token {
                        kind: TokenKind::Eof,
                        span: 0..0,
                        text: None,
                        file: None,
                    }));
                } else {
                    return None;
                }
            };

            // Get the next token
            let token = lexer.with_dependent_mut(|_, lexer| {
                lexer.0.next().map(|kind_result| {
                    kind_result.map(|kind| Token {
                        kind,
                        span: lexer.0.span(),
                        text: kind.is_non_trivial().then(|| lexer.0.slice().to_owned()),
                        file: source.to_owned(),
                    })
                })
            });

            // If the current lexer is exhausted, pop it and try again
            if token.is_none() {
                self.lexers.pop();
            } else {
                return token;
            }
        }
    }
}
