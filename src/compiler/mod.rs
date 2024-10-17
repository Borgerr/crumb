use std::{fmt::Display, fs};
use thiserror::Error;

pub mod lexer;
use lexer::tokenize;

pub mod parser;
use parser::parse;

pub mod tacky;

pub mod asmgen;
use asmgen::{emit_asm, gen_asm};

use crate::Args;

#[derive(Error, Debug)]
pub enum CompileError {
    Lex(lexer::LexError),
    Parse(parser::ParseError),
    FileIo(std::io::Error),
}

impl Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Lex(e) => write!(f, "{}", e),
            Self::Parse(e) => write!(f, "{}", e),
            Self::FileIo(e) => write!(f, "{}", e),
        }
    }
}

/// Compiling. IAFM.
/// ### Parameters
/// - input_file: path to file to compile
/// - l: bool, stop after lexing
/// - p: bool, stop after parsing
/// - c: bool, stop after assembly code generation
pub fn compile(input_file: String, args: Args) -> Result<String, CompileError> {
    let source = match fs::read_to_string(format!("{}.i", input_file)) {
        Ok(s) => s,
        Err(e) => return Err(CompileError::FileIo(e)),
    };

    let tokens = match tokenize(source) {
        Err(e) => return Err(CompileError::Lex(e)),
        Ok(ts) => {
            if args.lex {
                ts.into_iter().for_each(|t| println!("TOKEN!!! {}", t));
                return Ok(String::from("magic words"));
            } else {
                ts
            }
        }
    };

    let c_ast = match parse(tokens) {
        Err(e) => return Err(CompileError::Parse(e)),
        Ok(ast) => {
            if args.parse {
                println!("VALID AST RETURNED: {}", ast);
                return Ok(String::from("magic words"));
            } else {
                ast
            }
        }
    };
    let tacky = tacky::TackyEmitter::gen_tacky(c_ast);
    if args.tacky {
        return Ok(String::from("magic words"));
    }
    let asm_ast = gen_asm(tacky);
    if args.codegen {
        println!("GENERATED ASSEMBLY: {}", asm_ast);
        return Ok(String::from("magic words"));
    }
    if let Err(e) = emit_asm(asm_ast, format!("{}.s", input_file)) {
        return Err(CompileError::FileIo(e));
    }

    Ok(format!("{}.s", input_file))
}
