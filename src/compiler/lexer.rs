use lazy_static::lazy_static;
use regex::Regex;
use std::{fmt::Display, fs};

lazy_static! {}

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
        }
    }
}

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
pub fn tokenize(input_file: String) -> Vec<Token> {
    let idre = Regex::new(r"^[a-zA-Z_]\w*\b").expect("failure creating identifier regex");
    let constre = Regex::new(r"^[0-9]+\b").expect("failure creating const regex");
    let s = fs::read_to_string(input_file).expect("(!) Error reading file");
    let mut strang = s.as_str().trim();
    let mut tokens = Vec::new();

    while !(strang.is_empty()) {
        strang = strang.trim_start();
        tokens.push(if let Some(mat) = idre.find(strang) {
            strang = strang.trim_start_matches(mat.as_str());
            check_for_keywords(mat.as_str())
        } else if let Some(mat) = constre.find(strang) {
            strang = strang.trim_start_matches(mat.as_str());
            Token::Constant {
                val: mat.as_str().parse().expect(&format!(
                    "failure parsing constant {} as integer",
                    mat.as_str()
                )),
            }
        } else if strang.starts_with(r"(") {
            strang = strang.trim_start_matches(r"(");
            Token::OpenParens
        } else if strang.starts_with(r")") {
            strang = strang.trim_start_matches(r")");
            Token::CloseParens
        } else if strang.starts_with(r"{") {
            strang = strang.trim_start_matches(r"{");
            Token::OpenBrace
        } else if strang.starts_with(r"}") {
            strang = strang.trim_start_matches(r"}");
            Token::CloseBrace
        } else if strang.starts_with(r";") {
            strang = strang.trim_start_matches(r";");
            Token::Semicolon
        } else {
            panic!("Syntax error with strang = {}", strang);
        });
    }

    tokens
}

fn check_for_keywords(strang: &str) -> Token {
    match strang {
        s if s.starts_with("int") => Token::TyKeyword { ty: Type::Int },
        s if s.starts_with("void") => Token::TyKeyword { ty: Type::Void },
        s if s.starts_with("return") => Token::RetKeyword,
        _ => Token::Identifier {
            val: strang.to_string(),
        },
    }
}
