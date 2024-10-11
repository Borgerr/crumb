use lazy_static::lazy_static;
use regex::Regex;
use std::{fmt::Display, str::FromStr};
use thiserror::Error;

lazy_static! {
    static ref idre: Regex =    // identifiers
        Regex::new(r"^[a-zA-Z_]\w*\b").expect("failure creating identifier regex");
    static ref constre: Regex = Regex::new(r"^[0-9]+\b").expect("failure creating const regex");    // constants
    static ref single_char_re: Regex =    // single char tokens
        Regex::new(r"^(\(|\)|\{|\}|;|\-|~|\+|\*|\/|%|&|\||\^)").expect("failure creating single_charre regex");
    static ref double_char_re: Regex = Regex::new(r"^(?:\-|\+|>|<){2}").expect("failure creating double_charre regex");
    // ^ double char tokens; may have some weirdness with multiple matches?
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
    Ampersand,                  // &
    Pipe,                       // |
    Caret,                      // ^
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
            Token::Ampersand => write!(f, "& symbol"),
            Token::Pipe => write!(f, "| symbol"),
            Token::Caret => write!(f, "^ symbol"),
        }
    }
}

impl FromStr for Token {
    type Err = LexError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            r"(" => Ok(Self::OpenParens),
            r")" => Ok(Self::CloseParens),
            r"{" => Ok(Self::OpenBrace),
            r"}" => Ok(Self::CloseBrace),
            r";" => Ok(Self::Semicolon),
            r"-" => Ok(Self::Minus),
            r"--" => Ok(Self::MinusMinus),
            r"~" => Ok(Self::Tilde),
            r"+" => Ok(Self::Plus),
            r"*" => Ok(Self::Asterisk),
            r"/" => Ok(Self::FSlash),
            r"%" => Ok(Self::Percent),
            r"&" => Ok(Self::Ampersand),
            r"|" => Ok(Self::Pipe),
            r"^" => Ok(Self::Caret),
            _ => Err(LexError::Unrecognized {
                strang: s.to_string(),
            }),
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
            strang = strang.strip_prefix(mat.as_str()).unwrap();
            Token::Constant {
                val: mat.as_str().parse().unwrap(),
            }
        } else if let Some(mat) = double_char_re.find(strang) {
            strang = strang.strip_prefix(mat.as_str()).unwrap();
            Token::from(mat.as_str().parse().unwrap())
        } else if let Some(mat) = single_char_re.find(strang) {
            strang = strang.strip_prefix(mat.as_str()).unwrap();
            Token::from(mat.as_str().parse().unwrap())
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
        "int" => Token::TyKeyword { ty: Type::Int },
        "void" => Token::TyKeyword { ty: Type::Void },
        "return" => Token::RetKeyword,
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

#[test]
fn test_parenthesis() {
    let source = String::from("(())");
    let tokens = tokenize(source).unwrap();
    let expected = vec![
        Token::OpenParens,
        Token::OpenParens,
        Token::CloseParens,
        Token::CloseParens,
    ];
    assert_eq!(tokens, expected);
}

/// tests the independent lexing of all operators
/// BE SURE TO CHANGE THIS TEST WITH MORE OPERATORS
#[test]
fn test_lex_operators() {
    let source = String::from(r"( ) { } ; - -- ~ + * / % & | ^");
    let tokens = tokenize(source).unwrap();
    let expected = vec![
        Token::OpenParens,
        Token::CloseParens,
        Token::OpenBrace,
        Token::CloseBrace,
        Token::Semicolon,
        Token::Minus,
        Token::MinusMinus,
        Token::Tilde,
        Token::Plus,
        Token::Asterisk,
        Token::FSlash,
        Token::Percent,
        Token::Ampersand,
        Token::Pipe,
        Token::Caret,
    ];
    assert_eq!(tokens, expected);
}
