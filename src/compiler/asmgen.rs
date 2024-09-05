use std::{fmt::Display, fs};

use super::parser::*;

/* ABSTRACT GRAMMAR: (as of v0.1.0)
 * program = Program(function_definition)
 * function_definition = Function(identifier name, instruction* instructions)
 * instruction = Mov(operand src, operand dst) | Ret
 * operand = Imm(int) | Register
*/

#[derive(PartialEq, Debug)]
pub struct ProgramAsm {
    pub function: Box<FunDefAsm>,
}

impl Display for ProgramAsm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}\n\t.section .note.GNU-stack,\"\",@progbits",
            *self.function
        )
    }
}

#[derive(PartialEq, Debug)]
pub struct FunDefAsm {
    pub identifier: String,
    pub instructions: Vec<InstructionAsm>,
}

impl Display for FunDefAsm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\t.globl {}\n{}:{}", self.identifier, self.identifier, {
            let mut format_instrs = String::from("");
            self.instructions
                .clone()
                .into_iter()
                .for_each(|i| format_instrs.push_str(&format!("\n\t{}", i)));
            format_instrs
        })
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum InstructionAsm {
    Mov { src: OperandAsm, dst: OperandAsm },
    Ret,
}

impl Display for InstructionAsm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Mov { src, dst } => write!(f, "movl {}, {}", src, dst),
            Self::Ret => write!(f, "ret"),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum OperandAsm {
    Imm { int: i32 },
    Reg { r: Register },
}

impl Display for OperandAsm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Imm { int } => write!(f, "${}", int),
            Self::Reg { r } => write!(f, "{}", r),
        }
    }
}

/// General purpose registers for x86-64.
/// As of v0.1.0, only eax, the 32b accumulator.
#[derive(PartialEq, Debug, Clone)]
pub enum Register {
    EAX,
}

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EAX => write!(f, "%eax"),
        }
    }
}

/// Converts ASM AST to syntax and writes to output file
pub fn emit_asm(asmprog: ProgramAsm, output_file: String) -> std::io::Result<()> {
    fs::write(output_file, format!("{}", asmprog))?;
    Ok(())
}

pub fn gen_asm(cprog: ProgramC) -> ProgramAsm {
    ProgramAsm {
        function: Box::new(translate_fundef(*cprog.function)),
    }
}

fn translate_fundef(cfundef: FunDefC) -> FunDefAsm {
    FunDefAsm {
        identifier: cfundef.identifier,
        instructions: translate_statement(*cfundef.statement),
    }
}

fn translate_statement(cstate: StatementC) -> Vec<InstructionAsm> {
    match cstate {
        StatementC::Return { exp } => match *exp {
            ExpC::Const { c } => vec![
                InstructionAsm::Mov {
                    src: OperandAsm::Imm { int: c },
                    dst: OperandAsm::Reg { r: Register::EAX },
                },
                InstructionAsm::Ret,
            ],
        },
    }
}
