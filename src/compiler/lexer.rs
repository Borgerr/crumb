use regex::Regex;
use std::fs;

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

/// Type for types supported by the compiler.
/// Only useful in tokenizing.
pub enum Type {
    Int,
    Void,
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
    let plaintext = fs::read_to_string(input_file).expect("(!) Error reading file");
    let token_strs = plaintext.split_ascii_whitespace();

    let idre = Regex::new(r"[a-zA-Z_]\w*\b").expect("failure on identifier regex creation");
    let constre = Regex::new(r"[0-9]+\b").expect("failure on constant regex creation");
    let intre = Regex::new(r"int\b").expect("failure on int keyword regex creation");
    let voidre = Regex::new(r"void\b").expect("failure on void keyword regex creation");
    let retre = Regex::new(r"return\b").expect("failure on return regex generation");
    let oparenre = Regex::new(r"\(").expect("failure on open paren regex generation");
    let cloparenre = Regex::new(r"\)").expect("failure on close paren regex creation");
    let obracere = Regex::new(r"{").expect("failure on open brace regex creation");
    let clobracere = Regex::new(r"}").expect("failure on close brace regex creation");
    let semicolonre = Regex::new(r";").expect("failure on semicolon regex creation");

    token_strs
        .map(|s| {
            if idre.is_match(s) {
                Token::Identifier { val: s.to_owned() }
            } else if constre.is_match(s) {
                Token::Constant {
                    val: s
                        .parse()
                        .expect("failure on converting int string to int constant"),
                }
            } else if intre.is_match(s) {
                Token::TyKeyword { ty: Type::Int }
            } else if voidre.is_match(s) {
                Token::TyKeyword { ty: Type::Void }
            } else if retre.is_match(s) {
                Token::RetKeyword
            } else if oparenre.is_match(s) {
                Token::OpenParens
            } else if cloparenre.is_match(s) {
                Token::CloseParens
            } else if obracere.is_match(s) {
                Token::OpenBrace
            } else if clobracere.is_match(s) {
                Token::CloseBrace
            } else if semicolonre.is_match(s) {
                Token::Semicolon
            } else {
                todo!("determine error handling behavior")
            }
        })
        .collect()
}
