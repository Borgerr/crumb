use std::fs;

use super::asmgen::*;

pub fn emit(asmprog: ProgramAsm, output_file: String) {
    let syntax = asm_syntax(asmprog);
}

fn asm_syntax(asmprog: ProgramAsm) -> String {
    let mut syntax = String::from("");

    syntax
}
