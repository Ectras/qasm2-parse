use logos::{Lexer, Logos, Skip};

/// A built-in file with standard definitions for QASM2 programs.
static QELIB: &str = include_str!("qelib1.inc");

#[derive(Default, Debug, Clone, PartialEq)]
pub enum LexingError {
    UnclosedComment,
    #[default]
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

#[derive(Logos, Debug, Clone, PartialEq)]
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
