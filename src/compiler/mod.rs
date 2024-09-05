use std::{fmt::Display, fs};
use thiserror::Error;

pub mod lexer;
use lexer::tokenize;

pub mod parser;
use parser::parse;

pub mod asmgen;
use asmgen::{emit_asm, gen_asm};

#[derive(Error, Debug)]
pub enum CompileError {
    Lex { e: lexer::LexError },
    Parse { e: parser::ParseError },
    FileRead { e: std::io::Error },
}

impl Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Lex { e } => write!(f, "{}", e),
            Self::Parse { e } => write!(f, "{}", e),
            Self::FileRead { e } => write!(f, "{}", e),
        }
    }
}

/// Compiling. IAFM.
/// ### Parameters
/// - input_file: path to file to compile
/// - l: bool, stop after lexing
/// - p: bool, stop after parsing
/// - c: bool, stop after assembly code generation
pub fn compile(input_file: String, l: bool, p: bool, c: bool) -> Result<String, CompileError> {
    let source = match fs::read_to_string(input_file.clone()) {
        Ok(s) => s,
        Err(e) => return Err(CompileError::FileRead { e }),
    };

    let tokens = match tokenize(source) {
        Err(e) => return Err(CompileError::Lex { e }),
        Ok(ts) => {
            if l {
                ts.into_iter().for_each(|t| println!("TOKEN!!! {}", t));
                return Ok(String::from("magic words"));
            } else {
                ts
            }
        }
    };

    let c_ast = match parse(tokens) {
        Err(e) => return Err(CompileError::Parse { e }),
        Ok(ast) => {
            if p {
                println!("VALID AST RETURNED: {}", ast);
                return Ok(String::from("magic words"));
            } else {
                ast
            }
        }
    };
    let asm_ast = gen_asm(c_ast);
    if c {
        println!("GENERATED ASSEMBLY: {}", asm_ast);
        return Ok(String::from("Magic words"));
    } else if let Err(e) = emit_asm(asm_ast, format!("{}.i", input_file)) {
        return Err(todo!("determine error"));
    }

    Ok(String::from("COMPILE RETURNED WOOHOO!!!"))
}
