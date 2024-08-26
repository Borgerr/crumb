mod lexer;
use lexer::{tokenize, Token};

/// Compiling. IAFM.
pub fn compile(input_file: String, lex: bool, parse: bool, codegen: bool) -> String {
    let tokens = tokenize(input_file);
    todo!("Currently only working on the compiler driver");
}
