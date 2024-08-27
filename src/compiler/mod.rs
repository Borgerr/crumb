mod lexer;
use lexer::{tokenize, Token};

/// Compiling. IAFM.
pub fn compile(input_file: String, lex: bool, parse: bool, codegen: bool) -> String {
    let mut iter = tokenize(input_file).into_iter();
    while let Some(t) = iter.next() {
        println!("TOKEN!!! {}", t);
    }

    String::from("COMPILE RETURNED WOOHOO!!!")
}
