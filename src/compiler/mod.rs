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
    Lex(#[from] lexer::LexError),
    Parse(#[from] parser::ParseError),
    FileIo(#[from] std::io::Error),
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
    let source = fs::read_to_string(format!("{}.i", input_file))?;

    let tokens = tokenize(source)?;
    if args.lex {
        tokens.into_iter().for_each(|t| println!("TOKEN!!! {}", t));
        return Ok(String::from("magic words"));
    }

    let c_ast = parse(tokens)?;
    if args.parse {
        println!("VALID AST RETURNED: {}", c_ast);
        return Ok(String::from("magic words"));
    }

    let tacky = tacky::TackyEmitter::gen_tacky(c_ast);
    if args.tacky {
        return Ok(String::from("magic words"));
    }

    let asm_ast = gen_asm(tacky);
    if args.codegen {
        println!("GENERATED ASSEMBLY: {}", asm_ast);
        return Ok(String::from("magic words"));
    }

    emit_asm(asm_ast, format!("{}.s", input_file))?;

    Ok(format!("{}.s", input_file))
}
