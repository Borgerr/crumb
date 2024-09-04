mod lexer;
use std::fmt::Display;

use lexer::tokenize;
mod parser;
use parser::parse;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum CompileError {
    Lex { e: lexer::LexError },
}

impl Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Lex { e } => write!(f, "{}", e),
        }
    }
}

/// Compiling. IAFM.
/// ### Parameters
/// - l: bool, stop after lexing
/// - p: bool, stop after parsing
/// - c: bool, stop after assembly code generation
pub fn compile(input_file: String, l: bool, p: bool, c: bool) -> Result<String, CompileError> {
    let res = tokenize(input_file);
    if let Err(e) = res {
        return Err(CompileError::Lex { e });
    }
    if l {
        return Ok("magic words".to_string());
    }
    let mut iter = res.clone().unwrap().into_iter();
    while let Some(t) = iter.next() {
        println!("TOKEN!!! {}", t);
    }

    let res = parse(res.unwrap());

    match res {
        Ok(t) => println!("RETURNED VALID AST t = {}", t),
        Err(e) => println!("RETURNED ERROR e = {}", e),
    }

    Ok(String::from("COMPILE RETURNED WOOHOO!!!"))
}
