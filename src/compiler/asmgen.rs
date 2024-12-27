use std::{collections::HashMap, fmt::Display, fs};

use super::{
    parser::{BinaryOp, UnaryOp},
    tacky::*,
};

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
/// ### Grammar as of v0.1.3
/// ```text
/// instruction = Mov(operand src, operand dst)
///             | Unary(unary_operator, operand)
///             | Binary(binary_operator, operand, operand)
///             | Idiv(operand)
///             | Cdq
///             | AllocateStack(int)
///             | Ret
///             | Cmp(operand, operand)
///             | Jmp(identifier)
///             | JmpCC(cond_code, identifier)
///             | SetCC(cond_code, operand)
///             | Label(identifier)
/// ```
#[derive(PartialEq, Debug, Clone)]
pub enum InstructionAsm {
    Mov {
        src: OperandAsm,
        dst: OperandAsm,
    },
    Ret,
    Unary {
        unop: UnaryOp,
        operand: OperandAsm,
    },
    AllocStack {
        off: i32,
    },
    Binary {
        binop: BinaryOp,
        src: OperandAsm,
        dst: OperandAsm,
    },
    Idiv {
        operand: OperandAsm,
    },
    Cdq,
    Cmp {
        op1: OperandAsm,
        op2: OperandAsm,
    },
    Jmp(Identifier),
    JmpCC(CondCode, Identifier),
    SetCC(CondCode, OperandAsm),
    Label(Identifier),
}

impl Display for InstructionAsm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Mov { src, dst } => write!(f, "movl {}, {}", src, dst),
            Self::Ret => write!(f, "movq %rbp, %rsp\n\tpopq %rbp\n\tret"), // including epilogue
            Self::Unary { unop, operand } => match unop {
                UnaryOp::Negate => write!(f, "negl {}", operand),
                UnaryOp::BitwiseComplement => write!(f, "notl {}", operand),
                UnaryOp::Not => todo!(),
            },
            Self::AllocStack { off } => write!(f, "subq ${}, %rsp", -1 * off),
            Self::Cdq => write!(f, "cdq"),
            Self::Binary { binop, src, dst } => match binop {
                BinaryOp::Add => write!(f, "addl {}, {}", src, dst),
                BinaryOp::Subtract => write!(f, "subl {}, {}", src, dst),
                BinaryOp::Multiply => write!(f, "imull {}, {}", src, dst),
                BinaryOp::BitwiseAnd => write!(f, "andl {}, {}", src, dst),
                BinaryOp::BitwiseOr => write!(f, "orl {}, {}", src, dst),
                BinaryOp::BitwiseXor => write!(f, "xorl {}, {}", src, dst),
                _ => panic!(
                    "unsupported BinaryOp variant stored in InstructionAsm::Binary {:?}",
                    self
                ),
            },
            Self::Idiv { operand } => write!(f, "idivl {}", operand),
            _ => todo!("implement for other instructions"),
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

impl Into<OperandAsm> for ValTacky {
    fn into(self) -> OperandAsm {
        match self {
            ValTacky::Const { int } => OperandAsm::Imm { int },
            ValTacky::TmpVar { no } => OperandAsm::Pseudo { id: no },
        }
    }
}

/// x86-64 registers
/// ### Used registers as of v0.1.2
/// - AX
/// - R10
/// - DX
/// - R11
#[derive(PartialEq, Debug, Clone, Copy)]
pub enum Register {
    AX,
    R10,
    DX,
    R11,
}

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AX => write!(f, "%eax"),
            Self::R10 => write!(f, "%r10d"),
            Self::DX => write!(f, "%edx"),
            Self::R11 => write!(f, "%r11d"),
        }
    }
}

/// x86-64 condition codes
/// ### Used Condition codes as of v0.1.2
/// - Equal
/// - Not equal
/// - Greater
/// - Greater or equal
/// - Less
/// - Less or equal
#[derive(PartialEq, Debug, Clone, Copy)]
pub enum CondCode {
    E,
    NE,
    G,
    GE,
    L,
    LE,
}

impl Display for CondCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
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

/// fixes up instructions so that non-pseudo operands are correct for different instructions.
/// Assumes that pseudo-operands have already been resolved.
fn fix_up_instrs(resolved_instrs: Vec<InstructionAsm>, min_used: i32) -> Vec<InstructionAsm> {
    let mut res = Vec::with_capacity(resolved_instrs.len() + 1);
    if min_used != 0 {
        res.push(InstructionAsm::AllocStack { off: min_used });
    }

    for instr in resolved_instrs.into_iter() {
        match instr {
            InstructionAsm::Mov { src, dst } => {
                if matches!(src, OperandAsm::Stack { off: _ })
                    && matches!(dst, OperandAsm::Stack { off: _ })
                {
                    res.append(&mut vec![
                        InstructionAsm::Mov {
                            src,
                            dst: OperandAsm::Reg { r: Register::R10 },
                        },
                        InstructionAsm::Mov {
                            src: OperandAsm::Reg { r: Register::R10 },
                            dst,
                        },
                    ])
                } else {
                    res.push(instr)
                }
            }
            InstructionAsm::Binary {
                binop: _,
                src: _,
                dst: _,
            } => resolve_binary(instr, &mut res),
            InstructionAsm::Idiv { operand } => match operand {
                OperandAsm::Imm { int } => res.append(&mut vec![
                    InstructionAsm::Mov {
                        src: OperandAsm::Imm { int },
                        dst: OperandAsm::Reg { r: Register::R10 },
                    },
                    InstructionAsm::Idiv {
                        operand: OperandAsm::Reg { r: Register::R10 },
                    },
                ]),
                _ => res.push(instr),
            },
            _ => res.push(instr),
        }
    }

    res
}

fn resolve_binary(instr: InstructionAsm, instrs: &mut Vec<InstructionAsm>) {
    if let InstructionAsm::Binary { binop, src, dst } = &instr {
        match binop {
            BinaryOp::Multiply => instrs.append(&mut vec![
                InstructionAsm::Mov {
                    src: *dst,
                    dst: OperandAsm::Reg { r: Register::R11 },
                },
                InstructionAsm::Binary {
                    binop: *binop,
                    src: *src,
                    dst: OperandAsm::Reg { r: Register::R11 },
                },
                InstructionAsm::Mov {
                    src: OperandAsm::Reg { r: Register::R11 },
                    dst: *dst,
                },
            ]),
            _ => {
                if matches!(src, OperandAsm::Stack { off: _ })
                    && matches!(dst, OperandAsm::Stack { off: _ })
                {
                    instrs.append(&mut vec![
                        InstructionAsm::Mov {
                            src: *src,
                            dst: OperandAsm::Reg { r: Register::R10 },
                        },
                        InstructionAsm::Binary {
                            binop: *binop,
                            src: OperandAsm::Reg { r: Register::R10 },
                            dst: *dst,
                        },
                    ])
                } else {
                    instrs.push(instr)
                }
            }
        }
    }
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
            InstructionAsm::Binary { binop, src, dst } => InstructionAsm::Binary {
                binop,
                src: self.temp_to_stack(src),
                dst: self.temp_to_stack(dst),
            },
            InstructionAsm::Idiv { operand } => InstructionAsm::Idiv {
                operand: self.temp_to_stack(operand),
            },
            _ => instr,
        }
    }

    fn temp_to_stack(&mut self, operand: OperandAsm) -> OperandAsm {
        match operand {
            OperandAsm::Pseudo { id } => match self.id_to_off.get(&id) {
                Some(off) => OperandAsm::Stack { off: *off },
                None => {
                    self.min_used = self.min;
                    self.min -= 4;
                    self.id_to_off.insert(id, self.min_used);
                    OperandAsm::Stack { off: self.min_used }
                }
            },
            _ => operand,
        }
    }
}

/// Initial TACKY translation that relies on pseudo operands.
fn translate_with_pseudo(tacky_instrs: Vec<InstructionTacky>) -> Vec<InstructionAsm> {
    let mut res: Vec<InstructionAsm> = Vec::with_capacity(tacky_instrs.len() * 2);

    for tacky_instr in tacky_instrs.into_iter() {
        match tacky_instr {
            InstructionTacky::Ret { v } => res.append(&mut vec![
                InstructionAsm::Mov {
                    src: v.into(),
                    dst: OperandAsm::Reg { r: Register::AX },
                },
                InstructionAsm::Ret,
            ]),
            InstructionTacky::Unary { op, src, dst } => {
                let src: OperandAsm = src.into();
                let dst: OperandAsm = dst.into();
                match op {
                    UnaryOp::Not => res.append(&mut vec![
                        InstructionAsm::Cmp {
                            op1: OperandAsm::Imm { int: 0 },
                            op2: src,
                        },
                        InstructionAsm::Mov {
                            src: OperandAsm::Imm { int: 0 },
                            dst,
                        },
                        InstructionAsm::SetCC(CondCode::E, dst),
                    ]),
                    _ => res.append(&mut vec![
                        InstructionAsm::Mov { src, dst: dst },
                        InstructionAsm::Unary {
                            unop: op,
                            operand: dst,
                        },
                    ]),
                }
            }
            InstructionTacky::Binary {
                op,
                src1,
                src2,
                dst,
            } => {
                let src1 = src1.into();
                let src2 = src2.into();
                let dst = dst.into();
                match op {
                    BinaryOp::Divide => res.append(&mut vec![
                        InstructionAsm::Mov {
                            src: src1,
                            dst: OperandAsm::Reg { r: Register::AX },
                        },
                        InstructionAsm::Cdq,
                        InstructionAsm::Idiv { operand: src2 },
                        InstructionAsm::Mov {
                            src: OperandAsm::Reg { r: Register::AX },
                            dst,
                        },
                    ]),
                    BinaryOp::Remainder => res.append(&mut vec![
                        InstructionAsm::Mov {
                            src: src1,
                            dst: OperandAsm::Reg { r: Register::AX },
                        },
                        InstructionAsm::Cdq,
                        InstructionAsm::Idiv { operand: src2 },
                        InstructionAsm::Mov {
                            src: OperandAsm::Reg { r: Register::DX },
                            dst,
                        },
                    ]),
                    BinaryOp::And
                    | BinaryOp::Or
                    | BinaryOp::Equal
                    | BinaryOp::NotEqual
                    | BinaryOp::Geq
                    | BinaryOp::GreaterThan
                    | BinaryOp::Leq
                    | BinaryOp::LessThan => translate_logical_binary(src1, src2, dst, op, &mut res),
                    _ => res.append(&mut vec![
                        InstructionAsm::Mov { src: src1, dst },
                        InstructionAsm::Binary {
                            binop: op,
                            src: src2,
                            dst,
                        },
                    ]),
                }
            }
            InstructionTacky::JumpIfZero { src, target } => res.append(&mut vec![
                InstructionAsm::Cmp {
                    op1: OperandAsm::Imm { int: 0 },
                    op2: src.into(),
                },
                InstructionAsm::JmpCC(CondCode::E, target),
            ]),
            InstructionTacky::JumpIfNotZero { src, target } => res.append(&mut vec![
                InstructionAsm::Cmp {
                    op1: OperandAsm::Imm { int: 0 },
                    op2: src.into(),
                },
                InstructionAsm::JmpCC(CondCode::NE, target),
            ]),
            InstructionTacky::Label(l) => res.push(InstructionAsm::Label(l)),
            _ => todo!("support other TACKY"),
        }
    }

    res
}

/// Helper function for translating logical binary instructions with pseudo operands.
///
/// `op` is assumed to only ever be a logical binary operator, and guaranteed from `translate_with_pseudo`.
fn translate_logical_binary(
    src1: OperandAsm,
    src2: OperandAsm,
    dst: OperandAsm,
    op: BinaryOp,
    res: &mut Vec<InstructionAsm>,
) {
    match op {
        BinaryOp::And => todo!(),
        BinaryOp::Or => todo!(),
        _ => res.append(&mut vec![
            InstructionAsm::Cmp {
                op1: src2,
                op2: src1,
            },
            InstructionAsm::Mov {
                src: OperandAsm::Imm { int: 0 },
                dst,
            },
            InstructionAsm::SetCC(
                match op {
                    BinaryOp::Equal => CondCode::E,
                    BinaryOp::Leq => CondCode::LE,
                    BinaryOp::Geq => CondCode::GE,
                    BinaryOp::LessThan => CondCode::L,
                    BinaryOp::GreaterThan => CondCode::G,
                    BinaryOp::NotEqual => CondCode::NE,
                    _ => {
                        panic!("if this panics, this is a crazy problem with rustc. make an issue.")
                    }
                },
                dst,
            ),
        ]),
    }
}
