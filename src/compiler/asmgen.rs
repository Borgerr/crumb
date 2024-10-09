use std::{collections::HashMap, fmt::Display, fs};

use super::{parser::UnaryOp, tacky::*};

/// x86-64 program
/// ### Grammar as of v0.1.0
/// ```text
/// program = Program(function_definition)
/// ```
#[derive(PartialEq, Debug)]
pub struct ProgramAsm {
    pub function: Box<FunDefAsm>,
}

impl Display for ProgramAsm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}\n\t.section .note.GNU-stack,\"\",@progbits\n",
            *self.function
        )
    }
}

/// x86-64 function definition
/// ### Grammar as of v0.1.0
/// ```text
/// function_definition = Function(identifier, instruction* body)
/// ```
#[derive(PartialEq, Debug)]
pub struct FunDefAsm {
    pub identifier: String,
    pub instructions: Vec<InstructionAsm>,
}

impl Display for FunDefAsm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "\t.globl {}\n{}:\n\tpushq %rbp\n\tmovq %rsp, %rbp{}", // including prologue
            self.identifier,
            self.identifier,
            {
                let mut format_instrs = String::from("");
                self.instructions
                    .clone()
                    .into_iter()
                    .for_each(|i| format_instrs.push_str(&format!("\n\t{}", i)));
                format_instrs
            }
        )
    }
}

/// x86-64 instruction
/// ### Grammar as of v0.1.1
/// ```text
/// instruction = Mov(operand src, operand dst)
///             | Unary(unary_operator, operand)
///             | AllocateStack(int)
///             | Ret
/// ```
#[derive(PartialEq, Debug, Clone)]
pub enum InstructionAsm {
    Mov { src: OperandAsm, dst: OperandAsm },
    Ret,
    Unary { unop: UnaryOp, operand: OperandAsm },
    AllocStack { off: i32 },
}

impl Display for InstructionAsm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Mov { src, dst } => write!(f, "movl {}, {}", src, dst),
            Self::Ret => write!(f, "movq %rbp, %rsp\n\tpopq %rbp\n\tret"), // including epilogue
            Self::Unary { unop, operand } => match unop {
                UnaryOp::Negate => write!(f, "negl {}", operand),
                UnaryOp::BitwiseComplement => write!(f, "notl {}", operand),
            },
            Self::AllocStack { off } => write!(f, "subq ${}, %rsp", -1 * off),
        }
    }
}

/// x86-64 operand
/// ### Grammar as of v0.1.1
/// ```text
/// operand = Imm(int) | Reg(reg) | Pseudo(identifier) | Stack(int)
/// ```
#[derive(PartialEq, Debug, Clone, Copy)]
pub enum OperandAsm {
    Imm { int: i32 },
    Reg { r: Register },
    Pseudo { id: u16 },
    Stack { off: i32 },
}

impl Display for OperandAsm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Imm { int } => write!(f, "${}", int),
            Self::Reg { r } => write!(f, "{}", r),
            Self::Stack { off } => write!(f, "{}(%rbp)", off),
            Self::Pseudo { id } => panic!("display format called on a pseudo operand id: {}", id),
        }
    }
}

/// x86-64 registers
/// ### Used registers as of v0.1.1
/// - AX
/// - R10
#[derive(PartialEq, Debug, Clone, Copy)]
pub enum Register {
    AX,
    R10,
}

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AX => write!(f, "%eax"),
            Self::R10 => write!(f, "%r10d"),
        }
    }
}

/// Converts ASM AST to syntax and writes to output file
pub fn emit_asm(asmprog: ProgramAsm, output_file: String) -> std::io::Result<()> {
    fs::write(output_file, format!("{}", asmprog))
}

pub fn gen_asm(tacky_prog: ProgramTacky) -> ProgramAsm {
    ProgramAsm {
        function: Box::new(translate_fundef(*tacky_prog.function)),
    }
}

fn translate_fundef(tacky_fundef: FunDefTacky) -> FunDefAsm {
    let pseudo_instrs = translate_with_pseudo(tacky_fundef.instructions);
    let mut tmp_resolver = TmpVarResolver::new();
    let resolved_instrs = pseudo_instrs
        .into_iter()
        .map(|i| tmp_resolver.resolve_temps(i))
        .collect();
    let fixed_instrs = fix_up_instrs(resolved_instrs, tmp_resolver.get_min_used());
    FunDefAsm {
        identifier: tacky_fundef.identifier,
        instructions: fixed_instrs,
    }
}

fn fix_up_instrs(resolved_instrs: Vec<InstructionAsm>, min_used: i32) -> Vec<InstructionAsm> {
    let mut res = Vec::with_capacity(resolved_instrs.len() + 1);
    if min_used != 0 {
        res.push(InstructionAsm::AllocStack { off: min_used });
    }

    for instr in resolved_instrs.into_iter() {
        match instr {
            InstructionAsm::Mov { src, dst } => match src {
                OperandAsm::Stack { off: _ } => match dst {
                    OperandAsm::Stack { off: _ } => res.append(&mut vec![
                        InstructionAsm::Mov {
                            src,
                            dst: OperandAsm::Reg { r: Register::R10 },
                        },
                        InstructionAsm::Mov {
                            src: OperandAsm::Reg { r: Register::R10 },
                            dst,
                        },
                    ]),
                    _ => res.push(instr),
                },
                _ => res.push(instr),
            },
            _ => res.push(instr),
        }
    }

    res
}

/// resolves temporary, or pseudo operands, to use an actual operand.
struct TmpVarResolver {
    min: i32,
    min_used: i32,
    id_to_off: HashMap<u16, i32>,
}

impl TmpVarResolver {
    fn new() -> Self {
        TmpVarResolver {
            min: -4,
            min_used: 0,
            id_to_off: HashMap::new(),
        }
    }

    fn get_min_used(&mut self) -> i32 {
        self.min_used
    }

    fn resolve_temps(&mut self, instr: InstructionAsm) -> InstructionAsm {
        match instr {
            InstructionAsm::Mov { src, dst } => InstructionAsm::Mov {
                src: self.temp_to_stack(src),
                dst: self.temp_to_stack(dst),
            },
            InstructionAsm::Unary { unop, operand } => InstructionAsm::Unary {
                unop,
                operand: self.temp_to_stack(operand),
            },
            _ => instr,
        }
    }

    fn temp_to_stack(&mut self, op: OperandAsm) -> OperandAsm {
        match op {
            OperandAsm::Pseudo { id } => match self.id_to_off.get(&id) {
                Some(off) => OperandAsm::Stack { off: *off },
                None => {
                    self.min_used = self.min;
                    self.min -= 4;
                    self.id_to_off.insert(id, self.min_used);
                    OperandAsm::Stack { off: self.min_used }
                }
            },
            _ => op,
        }
    }
}

fn translate_with_pseudo(tacky_instrs: Vec<InstructionTacky>) -> Vec<InstructionAsm> {
    let mut res = Vec::with_capacity(tacky_instrs.len() * 2);

    for tacky_instr in tacky_instrs.into_iter() {
        match tacky_instr {
            InstructionTacky::Ret { v } => res.append(&mut vec![
                InstructionAsm::Mov {
                    src: translate_valtacky(v),
                    dst: OperandAsm::Reg { r: Register::AX },
                },
                InstructionAsm::Ret,
            ]),
            InstructionTacky::Unary { op, src, dst } => {
                let src = translate_valtacky(src);
                let dst = translate_valtacky(dst);
                res.append(&mut vec![
                    InstructionAsm::Mov {
                        src,
                        dst: dst.clone(),
                    },
                    InstructionAsm::Unary {
                        unop: op,
                        operand: dst,
                    },
                ])
            }
            _ => todo!(),
        }
    }

    res
}

fn translate_valtacky(tval: ValTacky) -> OperandAsm {
    match tval {
        ValTacky::Const { int } => OperandAsm::Imm { int },
        ValTacky::TmpVar { no } => OperandAsm::Pseudo { id: no },
    }
}
