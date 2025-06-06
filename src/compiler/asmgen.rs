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
                UnaryOp::Not => todo!("Double check if this should be reachable or not"),
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
            InstructionAsm::Cmp { op1, op2 } => write!(f, "cmpl {}, {}", op1, op2),
            InstructionAsm::Jmp(label) => write!(f, "jmp .L{}", label),
            InstructionAsm::JmpCC(cond_code, label) => write!(f, "j{} .L{}", cond_code, label),
            InstructionAsm::SetCC(cond_code, label) => write!(f, "set{} {}", cond_code, label),
            InstructionAsm::Label(label) => write!(f, ".L{}:", label), // .L label used for local labels
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

impl Into<OperandAsm> for i32 {
    fn into(self) -> OperandAsm {
        OperandAsm::Imm { int: self }
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
/// ### Used Condition codes as of v0.1.3
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
        match self {
            CondCode::E => write!(f, "e"),
            CondCode::NE => write!(f, "ne"),
            CondCode::G => write!(f, "g"),
            CondCode::GE => write!(f, "ge"),
            CondCode::L => write!(f, "l"),
            CondCode::LE => write!(f, "le"),
        }
    }
}

/// Converts ASM AST to syntax and writes to output file
pub fn emit_asm(asmprog: ProgramAsm, output_file: String) -> std::io::Result<()> {
    fs::write(output_file, format!("{}", asmprog))
}

/// Generates an ASM program structure from a TACKY structure.
pub fn gen_asm(tacky_prog: ProgramTacky) -> ProgramAsm {
    ProgramAsm {
        function: Box::new(translate_fundef(*tacky_prog.function)),
    }
}

/// Translates a function definition from its TACKY representation.
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
            }
            | InstructionAsm::Cmp { op1: _, op2: _ } => resolve_binary(instr, &mut res),
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

/// Takes a binary operation and modifies the instructions vector in place.
/// Imagine this as being a branch in `fix_up_instrs`.
fn resolve_binary(instr: InstructionAsm, instrs: &mut Vec<InstructionAsm>) {
    match &instr {
        InstructionAsm::Binary { binop, src, dst } => match binop {
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
        },
        InstructionAsm::Cmp { op1, op2 } => {
            if matches!(op1, OperandAsm::Stack { off: _ })
                && matches!(op2, OperandAsm::Stack { off: _ })
            {
                instrs.append(&mut vec![
                    InstructionAsm::Mov {
                        src: *op1,
                        dst: OperandAsm::Reg { r: Register::R10 },
                    },
                    InstructionAsm::Cmp {
                        op1: OperandAsm::Reg { r: Register::R10 },
                        op2: *op2,
                    },
                ])
            } else {
                instrs.push(instr)
            }
        }
        _ => (),
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

    /// Main driver for actually resolving temporary variables into stack references.
    fn resolve_temps(&mut self, instr: InstructionAsm) -> InstructionAsm {
        match instr {
            InstructionAsm::Mov { src, dst } => InstructionAsm::Mov {
                src: self.temp_to_stack(src),
                dst: self.temp_to_stack(dst),
            },
            InstructionAsm::Unary { unop, operand } => {
                //println!("(!) unop --> {}", unop);
                InstructionAsm::Unary {
                    unop,
                    operand: self.temp_to_stack(operand),
                }
            }
            InstructionAsm::Binary { binop, src, dst } => InstructionAsm::Binary {
                binop,
                src: self.temp_to_stack(src),
                dst: self.temp_to_stack(dst),
            },
            InstructionAsm::Idiv { operand } => InstructionAsm::Idiv {
                operand: self.temp_to_stack(operand),
            },
            InstructionAsm::Cmp { op1, op2 } => InstructionAsm::Cmp {
                op1: self.temp_to_stack(op1),
                op2: self.temp_to_stack(op2),
            },
            InstructionAsm::SetCC(cc, operand) => {
                InstructionAsm::SetCC(cc, self.temp_to_stack(operand))
            }
            _ => instr,
        }
    }

    fn temp_to_stack(&mut self, operand: OperandAsm) -> OperandAsm {
        // TODO: this is definitely way too complicated.
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
                    // NOT case:
                    // e.g. !1
                    // represented as:
                    // ```rust
                    // InstructionTacky::Unary {
                    //   op: UnaryOp::Not,
                    //   src: ValTacky::Const { int: 1 },
                    //   dst: ValTacky::TmpVar { no: 0 },
                    // },
                    // ```
                    // here becomes:
                    // ```rust
                    // vec![
                    //   InstructionAsm::Cmp {
                    //     op1: OperandAsm::Imm{ int: 0 },
                    //     op2: src,    // where src is 1.into<ValTacky>()
                    //   },
                    //   InstructionAsm::Mov {
                    //     src: OperandAsm::Imm { int: 0 },
                    //     dst,     // where dst is ValTacky::TmpVar { no: 0 },
                    //   },
                    //   InstructionAsm::SetCC(CondCode::E, dst),
                    // ];
                    // ```
                    UnaryOp::Not => res.append(&mut vec![
                        // TODO: it's insufficient to just plop the source into the Cmp instruction
                        // because of Tacky like !1 --> Simple unary op Not of 1, we get a result
                        // Cmpl $0, $1.
                        // ^^ This is invalid syntax.
                        // We either need to reorganize how src ends up here (likely more difficult than what's worth)
                        // or Mov the source somewhere before the Cmp

                        /* POSSIBLE FIX:
                        InstructionAsm::Mov {
                            src: src.into(),
                            dst: OperandAsm::Reg { r: Register::AX },
                        },
                        InstructionAsm::Cmp {
                            op1: OperandAsm::Imm { int: 0 },
                            op2: OperandAsm::Reg { r: Register::AX },
                        },
                        */
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
                    UnaryOp::BitwiseComplement | UnaryOp::Negate => res.append(&mut vec![
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
                    BinaryOp::Equal // at this point, And and Or should be translated to conditional jumps
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
            InstructionTacky::Copy { src, dst } => res.push(InstructionAsm::Mov {
                src: src.into(),
                dst: dst.into(),
            }),
            InstructionTacky::Jump { target } => res.push(InstructionAsm::Jmp(target)),
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
    res.append(&mut vec![
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
    ])
}

/// ## TESTS THE FOLLOWING TRANSLATION
/// ## TACKY (input):
/// ```text
/// v1 = 1
/// JumpIfZero(v1, false_label0)
/// v2 = 2
/// JumpIfZero(v2, false_label0)
/// result = 1
/// Jump(end0)
/// Label(false_label0)
/// result = 0
/// Label(end0)
/// ```
#[test]
fn translate_and_from_tacky() {
    let tacky: Vec<InstructionTacky> = vec![
        // following evaluating the first expression; do we need to change to some tmp var?
        InstructionTacky::Copy {
            src: 1.into(),
            dst: ValTacky::TmpVar { no: 0 },
        },
        InstructionTacky::JumpIfZero {
            src: ValTacky::TmpVar { no: 0 },
            target: Identifier::from("false_label0"),
        },
        InstructionTacky::Copy {
            src: 2.into(),
            dst: ValTacky::TmpVar { no: 1 },
        },
        // following evaluating the second expression; do we need to change to some tmp var?
        InstructionTacky::JumpIfZero {
            src: ValTacky::TmpVar { no: 1 },
            target: Identifier::from("false_label0"),
        },
        InstructionTacky::Copy {
            src: 1.into(),
            dst: ValTacky::TmpVar { no: 2 },
        },
        InstructionTacky::Jump {
            target: Identifier::from("end0"),
        },
        InstructionTacky::Label(Identifier::from("false_label0")),
        InstructionTacky::Copy {
            src: 0.into(),
            dst: ValTacky::TmpVar { no: 2 },
        },
        InstructionTacky::Label(Identifier::from("end0")),
        InstructionTacky::Ret {
            v: ValTacky::TmpVar { no: 2 },
        },
    ];

    let instrs: Vec<InstructionAsm> = vec![
        // following evaluating the first expression; do we need to change to some tmp var?
        InstructionAsm::Mov {
            src: 1.into(),
            dst: ValTacky::TmpVar { no: 0 }.into(),
        },
        InstructionAsm::Cmp {
            // START OF JUMPIFZERO
            op1: 0.into(),
            op2: ValTacky::TmpVar { no: 0 }.into(),
        },
        InstructionAsm::JmpCC(CondCode::E, Identifier::from("false_label0")), // END OF JUMPIFZERO
        InstructionAsm::Mov {
            src: 2.into(),
            dst: ValTacky::TmpVar { no: 1 }.into(),
        },
        // following evaluating the second expression; do we need to change to some tmp var?
        InstructionAsm::Cmp {
            // START OF JUMPIFZERO
            op1: 0.into(),
            op2: ValTacky::TmpVar { no: 1 }.into(),
        },
        InstructionAsm::JmpCC(CondCode::E, Identifier::from("false_label0")), // END OF JUMPIFZERO
        InstructionAsm::Mov {
            src: 1.into(),
            dst: ValTacky::TmpVar { no: 2 }.into(),
        },
        InstructionAsm::Jmp(Identifier::from("end0")),
        InstructionAsm::Label(Identifier::from("false_label0")),
        InstructionAsm::Mov {
            src: 0.into(),
            dst: ValTacky::TmpVar { no: 2 }.into(),
        },
        InstructionAsm::Label(Identifier::from("end0")),
        // START OF RET
        InstructionAsm::Mov {
            src: ValTacky::TmpVar { no: 2 }.into(),
            dst: OperandAsm::Reg { r: Register::AX },
        },
        InstructionAsm::Ret,
        // END OF RET
    ];

    assert_eq!(translate_with_pseudo(tacky), instrs);
}

// ------------------------
// PSEUDO TRANSLATION TESTS
// ------------------------

#[test]
fn translate_bitwisenot_with_pseudo() {
    let inp = vec![InstructionTacky::Unary {
        op: UnaryOp::BitwiseComplement,
        src: ValTacky::Const { int: 1 },
        dst: ValTacky::TmpVar { no: 0 },
    }];
    let expected_out = vec![
        InstructionAsm::Mov {
            src: 1.into(),
            dst: ValTacky::TmpVar { no: 0 }.into(),
        },
        InstructionAsm::Unary {
            unop: UnaryOp::BitwiseComplement,
            operand: ValTacky::TmpVar { no: 0 }.into(),
        },
    ];

    let res = translate_with_pseudo(inp);
    assert_eq!(res, expected_out);
}

#[test]
fn translate_lognot_with_pseudo() {
    let inp = vec![InstructionTacky::Unary {
        op: UnaryOp::Not,
        src: ValTacky::Const { int: 1 },
        dst: ValTacky::TmpVar { no: 0 },
    }];
    let expected_out = vec![
        InstructionAsm::Cmp {
            op1: 0.into(),
            op2: 1.into(),
        },
        InstructionAsm::Mov {
            src: 0.into(),
            dst: ValTacky::TmpVar { no: 0 }.into(),
        },
        InstructionAsm::SetCC(CondCode::E, ValTacky::TmpVar { no: 0 }.into()),
    ];

    let res = translate_with_pseudo(inp);
    assert_eq!(res, expected_out);
}

#[test]
fn resolve_mov() {
    let mut tmp_resolver = TmpVarResolver::new();
    let mov_with_pseudo = InstructionAsm::Mov {
        src: 1.into(),
        dst: ValTacky::TmpVar { no: 0 }.into(),
    };

    let expected_out = InstructionAsm::Mov {
        src: 1.into(),
        dst: OperandAsm::Stack { off: -4 },
    };

    assert_eq!(tmp_resolver.resolve_temps(mov_with_pseudo), expected_out);
}

#[test]
fn resolve_setcc() {
    let mut tmp_resolver = TmpVarResolver::new();
    let setcc_with_pseudo = InstructionAsm::SetCC(CondCode::E, ValTacky::TmpVar { no: 0 }.into());

    let expected_out = InstructionAsm::SetCC(CondCode::E, OperandAsm::Stack { off: -4 });

    assert_eq!(tmp_resolver.resolve_temps(setcc_with_pseudo), expected_out);
}
