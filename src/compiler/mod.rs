mod lexer;
use std::fmt::Display;

use lexer::tokenize;
mod parser;
use parser::parse;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum CompileError {
    Parse { e: lexer::ParseError },
}

impl Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Parse { e } => write!(f, "{}", e),
        }
    }
}

/// Compiling. IAFM.
pub fn compile(
    input_file: String,
    lex: bool,
    parse: bool,
    codegen: bool,
) -> Result<String, CompileError> {
    let res = tokenize(input_file);
    if let Err(e) = res {
        return Err(CompileError::Parse { e });
    }
    if lex {
        return Ok("magic words".to_string());
    }
    let mut iter = res.clone().unwrap().into_iter();
    while let Some(t) = iter.next() {
        println!("TOKEN!!! {}", t);
    }

    Ok(String::from("COMPILE RETURNED WOOHOO!!!"))
}
