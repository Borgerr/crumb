use lazy_static::lazy_static;
use regex::Regex;
use std::{fmt::Display, fs};

lazy_static! {
    static ref idre: Regex =
        Regex::new(r"[a-zA-Z_]\w*\b").expect("failure creating identifier regex");
    static ref constre: Regex = Regex::new(r"[0-9]+\b").expect("failure creating const regex");
    static ref intre: Regex = Regex::new(r"int\b").expect("failure creating int type regex");
    static ref voidre: Regex = Regex::new(r"void\b").expect("failure creating void type regex");
    static ref retre: Regex =
        Regex::new(r"return\b").expect("failure creating return keyword regex");
    static ref oparenre: Regex = Regex::new(r"\(").expect("failure creating open paren regex");
    static ref cloparenre: Regex = Regex::new(r"\)").expect("failure creating close paren regex");
    static ref obracere: Regex = Regex::new(r"{").expect("failure creating open brace regex");
    static ref clobracere: Regex = Regex::new(r"}").expect("failure creating close brace regex");
    static ref sclnre: Regex = Regex::new(r";").expect("failure creating semicolon regex");
}

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
    // while input isn't empty:
    //  if input starts with whitespace:
    //      trim whitespace from start of input
    //  else:
    //      find longest match at start of input for any regex in Table 1-1
    //      if no match found, raise an error
    //      convert matching substring into a token
    //      remove matching substring from start of input
    let s = fs::read_to_string(input_file).expect("(!) Error reading file");
    let mut strang = s.as_str().trim();
    let mut returned = Vec::new();

    while !(strang.is_empty()) {
        strang = strang.trim_start();
        returned.push(match strang {
            s if idre.is_match(s) => {
                println!("IDENTIFIER s = {}", s);
                strang = strang.trim_start_matches(idre.find(s).unwrap().as_str());
                check_for_keywords(s)
            }
            s if constre.is_match(s) => {
                println!("CONSTANT s = {}", s);
                strang = strang.trim_start_matches(s);
                Token::Constant {
                    val: s
                        .parse()
                        .expect(&format!("failure parsing constant {} as integer", s)),
                }
            }
            s if oparenre.is_match(s) => {
                println!("OPEN PAREN s = {}", s);
                strang = strang.trim_start_matches("(");
                Token::OpenParens
            }
            s if cloparenre.is_match(s) => {
                println!("CLOSE PAREN s = {}", s);
                strang = strang.trim_start_matches(")");
                Token::CloseParens
            }
            s if obracere.is_match(s) => {
                println!("OPEN BRACE s = {}", s);
                strang = strang.trim_start_matches("{{");
                Token::OpenBrace
            }
            s if clobracere.is_match(s) => {
                println!("CLOSE BRACE s = {}", s);
                strang = strang.trim_start_matches("}}");
                Token::CloseBrace
            }
            s if sclnre.is_match(s) => {
                println!("SEMICOLON s = {}", s);
                strang = strang.trim_start_matches(";");
                Token::Semicolon
            }
            _ => panic!("Parse error with string {}", strang),
        });
    }

    returned.reverse();
    returned
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
