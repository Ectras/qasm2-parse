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
fn skip_to_closing_comment_token(lex: &mut Lexer<Token>) -> Result<Skip, LexingError> {
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
pub enum Token {
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
    // TODO: better error handling
    #[regex("(?&int)", |lex| lex.slice().parse::<i64>().unwrap())]
    Integer(i64),
    #[regex("(?&int)(?&fexp)|[.][0-9]+(?&fexp)?|(?&int)[.][0-9]*(?&fexp)?", |lex| lex.slice().parse::<f64>().unwrap())]
    Float(f64),
    #[regex("\"[^\"\r\t\n]*\"", |lex| lex.slice()[1..lex.slice().len() - 1].to_owned())]
    String(String),
    #[regex("[a-z][A-Za-z0-9_]*", |lex| lex.slice().to_owned())]
    Identifier(String),
    #[token("/*", |lex| skip_to_closing_comment_token(lex))]
    BlockComment,
    Eof,
}

/// Lexes a file at the given `path`, adding the tokens to the `tokens` vec.
///
/// The file `"qelib1.inc"` is built-in and while not be loaded from disk but provided
/// directly.
fn lex_file(path: &str, tokens: &mut Vec<Token>) -> Result<(), LexingError> {
    let contents = if path == "qelib1.inc" {
        QELIB
    } else {
        &std::fs::read_to_string(path).unwrap()
    };
    lex_str(contents, tokens)
}

/// Lexes the given `code`, adding the tokens to the `tokens` vec.
fn lex_str(code: &str, tokens: &mut Vec<Token>) -> Result<(), LexingError> {
    // Construct the lexer
    let mut lexer = Token::lexer(code);

    // Collect the tokens
    let mut found_include = false;
    while let Some(token) = lexer.next() {
        let token = token?;
        match token {
            // TODO: prevent cyclic includes
            Token::Include => found_include = true,
            Token::String(inner) if found_include => {
                found_include = false;
                lex_file(&inner, tokens)?;
            }
            _ => {
                found_include = false;
                tokens.push(token);
            }
        }
    }
    Ok(())
}

/// Lexes the given `code`, returning the list of tokens.
pub fn lex(code: &str) -> Result<Vec<Token>, LexingError> {
    let mut tokens = Vec::new();
    lex_str(code, &mut tokens)?;
    tokens.push(Token::Eof);
    Ok(tokens)
}
