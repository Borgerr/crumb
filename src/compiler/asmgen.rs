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

#[derive(PartialEq, Debug)]
pub struct FunDefAsm {
    pub identifier: String,
    pub instructions: Vec<InstructionAsm>,
}

#[derive(PartialEq, Debug)]
pub enum InstructionAsm {
    Mov { src: OperandAsm, dst: OperandAsm },
    Ret,
}

#[derive(PartialEq, Debug)]
pub enum OperandAsm {
    Imm { int: i32 },
    Reg { r: Register },
}

/// General purpose registers for x86-64.
/// As of v0.1.0, only eax, the 32b accumulator.
#[derive(PartialEq, Debug)]
pub enum Register {
    EAX,
}

pub fn asmgen(cprog: ProgramC) -> ProgramAsm {
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
