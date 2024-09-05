use std::{fmt::Display, fs};

pub mod lexer;
use lexer::tokenize;

pub mod parser;
use parser::parse;
use thiserror::Error;

pub mod codegen;

#[derive(Error, Debug)]
pub enum CompileError {
    Lex { e: lexer::LexError },
    Parse { e: parser::ParseError },
}

impl Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Lex { e } => write!(f, "{}", e),
            Self::Parse { e } => write!(f, "{}", e),
        }
    }
}

/// Compiling. IAFM.
/// ### Parameters
/// - l: bool, stop after lexing
/// - p: bool, stop after parsing
/// - c: bool, stop after assembly code generation
pub fn compile(input_file: String, l: bool, p: bool, c: bool) -> Result<String, CompileError> {
    let source = fs::read_to_string(input_file).expect("(!) Error reading file");
    let res = tokenize(source);
    if let Err(e) = res {
        return Err(CompileError::Lex { e });
    } else if l {
        let mut it = res.unwrap().into_iter();
        while let Some(t) = it.next() {
            println!("TOKEN!!! {}", t);
        }
        return Ok(String::from("magic words"));
    }
    let res = parse(res.unwrap());

    if let Err(e) = res {
        return Err(CompileError::Parse { e });
    } else if p {
        match res {
            Ok(t) => println!("RETURNED VALID ProgramC t = {}", t),
            Err(e) => println!("RETURNED ERROR e = {}", e),
        }
        return Ok(String::from("magic words"));
    }

    Ok(String::from("COMPILE RETURNED WOOHOO!!!"))
}
