use lazy_static::lazy_static;
use regex::Regex;
use std::fmt::Display;
use thiserror::Error;

lazy_static! {
    static ref idre: Regex =
        Regex::new(r"^[a-zA-Z_]\w*\b").expect("failure creating identifier regex");
    static ref constre: Regex = Regex::new(r"^[0-9]+\b").expect("failure creating const regex");
}

#[derive(Clone, Error, Debug)]
pub enum LexError {
    Unrecognized { strang: String },
}

impl Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unrecognized { strang } => write!(
                f,
                "(!) Lexer error: Unrecognized syntax on string: {}",
                strang
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
/// Type representing individual tokens.
/// Tree structure should not be here.
pub enum Token {
    Identifier { val: String }, // [a-zA-Z_]\w*\b
    Constant { val: i32 },      // [0-9]+\b
    TyKeyword { ty: Type },     // whatever keyword followed by \b
    RetKeyword,                 // return\b
    OpenParens,                 // \(
    CloseParens,                // \)
    OpenBrace,                  // {
    CloseBrace,                 // }
    Semicolon,                  // ;
    Minus,                      // -
    MinusMinus,                 // --
    Tilde,                      // ~
    Plus,                       // +
    Asterisk,                   // *
    FSlash,                     // /
    Percent,                    // %
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Identifier { val } => write!(f, "Identifier string (val = {})", val),
            Self::Constant { val } => write!(f, "Constant token (val = {})", val),
            Self::TyKeyword { ty } => write!(f, "Type keyword (ty = {})", ty),
            Self::RetKeyword => write!(f, "Return keyword"),
            Self::OpenParens => write!(f, "( symbol"),
            Self::CloseParens => write!(f, ") symbol"),
            Self::OpenBrace => write!(f, "{{ symbol"),
            Self::CloseBrace => write!(f, "}} symbol"),
            Self::Semicolon => write!(f, "; symbol"),
            Self::Minus => write!(f, "- symbol"),
            Self::MinusMinus => write!(f, "-- symbol"),
            Self::Tilde => write!(f, "~ symbol"),
            Self::Plus => write!(f, "+ symbol"),
            Self::Asterisk => write!(f, "* symbol"),
            Self::FSlash => write!(f, "/ symbol"),
            Self::Percent => write!(f, "% symbol"),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
/// Type for types supported by the compiler.
/// Only useful in tokenizing.
pub enum Type {
    Int,
    Void,
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => write!(f, "int"),
            Type::Void => write!(f, "void"),
        }
    }
}

/// Tokenize function, literally translating a source file
/// into a stream of tokens.
pub fn tokenize(source: String) -> Result<Vec<Token>, LexError> {
    let mut strang = source.as_str().trim();
    let mut tokens = Vec::new();

    while !(strang.is_empty()) {
        strang = strang.trim_start();
        tokens.push(if let Some(mat) = idre.find(strang) {
            strang = strang.trim_start_matches(mat.as_str());
            check_for_keywords(mat.as_str())
        } else if let Some(mat) = constre.find(strang) {
            strang = strang.trim_start_matches(mat.as_str());
            Token::Constant {
                val: mat.as_str().parse().unwrap(),
            }
        } else if strang.starts_with(r"(") {
            strang = strang.strip_prefix(r"(").unwrap();
            Token::OpenParens
        } else if strang.starts_with(r")") {
            strang = strang.strip_prefix(r")").unwrap();
            Token::CloseParens
        } else if strang.starts_with(r"{") {
            strang = strang.strip_prefix(r"{").unwrap();
            Token::OpenBrace
        } else if strang.starts_with(r"}") {
            strang = strang.strip_prefix(r"}").unwrap();
            Token::CloseBrace
        } else if strang.starts_with(r";") {
            strang = strang.strip_prefix(r";").unwrap();
            Token::Semicolon
        } else if strang.starts_with(r"--") {
            strang = strang.strip_prefix(r"--").unwrap();
            Token::MinusMinus
        } else if strang.starts_with(r"-") {
            strang = strang.strip_prefix(r"-").unwrap();
            Token::Minus
        } else if strang.starts_with(r"~") {
            strang = strang.strip_prefix(r"~").unwrap();
            Token::Tilde
        } else if strang.starts_with(r"+") {
            strang = strang.strip_prefix(r"+").unwrap();
            Token::Plus
        } else if strang.starts_with(r"*") {
            strang = strang.strip_prefix(r"*").unwrap();
            Token::Asterisk
        } else if strang.starts_with(r"/") {
            strang = strang.strip_prefix(r"/").unwrap();
            Token::FSlash
        } else if strang.starts_with(r"%") {
            strang = strang.strip_prefix(r"%").unwrap();
            Token::Percent
        } else {
            return Err(LexError::Unrecognized {
                strang: strang.to_string(),
            });
        });
    }

    Ok(tokens)
}

fn check_for_keywords(strang: &str) -> Token {
    match strang {
        s if s.starts_with("int") => Token::TyKeyword { ty: Type::Int },
        s if s.starts_with("void") => Token::TyKeyword { ty: Type::Void },
        s if s.starts_with("return") => Token::RetKeyword,
        _ => Token::Identifier {
            val: String::from(strang),
        },
    }
}

#[test]
fn test_lex_nested_cmp() {
    let source = String::from("int main(void) { return ~(~(~2)); }");
    let tokens = tokenize(source).unwrap();
    let expected = vec![
        Token::TyKeyword { ty: Type::Int },
        Token::Identifier {
            val: String::from("main"),
        },
        Token::OpenParens,
        Token::TyKeyword { ty: Type::Void },
        Token::CloseParens,
        Token::OpenBrace,
        Token::RetKeyword,
        Token::Tilde,
        Token::OpenParens,
        Token::Tilde,
        Token::OpenParens,
        Token::Tilde,
        Token::Constant { val: 2 },
        Token::CloseParens,
        Token::CloseParens,
        Token::Semicolon,
        Token::CloseBrace,
    ];
    assert_eq!(tokens, expected);
}
