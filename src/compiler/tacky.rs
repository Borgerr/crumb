use super::parser::*;

/// TACKY program
/// ### Grammar as of v0.1.1
/// `program = Program(function_definition)`
#[derive(PartialEq, Debug)]
pub struct ProgramTacky {
    pub function: Box<FunDefTacky>,
}

/// TACKY function definition
/// ### Grammar as of v0.1.1
/// `function_definition = Function(identifier, instruction* body)`
#[derive(PartialEq, Debug)]
pub struct FunDefTacky {
    pub identifier: String,
    pub instructions: Vec<InstructionTacky>,
}

/// TACKY instruction
/// ### Grammar as of v0.1.2
/// ```text
/// instruction = Return(val)
///             | Unary(unary_operator, val src, val dst)
///             | Binary(binary_operator, val src1, val src2, val dst)
/// ```
#[derive(PartialEq, Debug)]
pub enum InstructionTacky {
    Ret {
        v: ValTacky,
    },
    Unary {
        op: UnaryOp,
        src: ValTacky,
        dst: ValTacky,
    },
    Binary {
        op: BinaryOp,
        src1: ValTacky,
        src2: ValTacky,
        dst: ValTacky,
    },
}

/// TACKY value
/// ### Grammar as of v0.1.1
/// `val = Constant(int) | Var(identifier)`
#[derive(PartialEq, Debug, Clone)]
pub enum ValTacky {
    Const { int: i32 },
    TmpVar { no: u16 },
}

/// Keeps track of various data
/// within TACKY representation.
pub struct TackyEmitter {
    tmp_no: u16,
}

impl TackyEmitter {
    pub fn new() -> Self {
        TackyEmitter { tmp_no: 0 }
    }
    pub fn gen_tacky(cprog: ProgramC) -> ProgramTacky {
        ProgramTacky {
            function: Box::new(Self::new().translate_fundef(*cprog.function)),
        }
    }

    fn translate_fundef(&mut self, cfundef: FunDefC) -> FunDefTacky {
        FunDefTacky {
            identifier: cfundef.identifier,
            instructions: self.translate_statement(*cfundef.statement),
        }
    }

    fn translate_statement(&mut self, cstate: StatementC) -> Vec<InstructionTacky> {
        let mut instrs = Vec::new();
        match cstate {
            StatementC::Return { exp } => {
                let v = self.translate_expression(*exp, &mut instrs);
                instrs.push(InstructionTacky::Ret { v });
            }
        };
        instrs
    }

    fn translate_expression(&mut self, cexp: Exp, instrs: &mut Vec<InstructionTacky>) -> ValTacky {
        match cexp {
            Exp::Const { c } => ValTacky::Const { int: c },
            Exp::Unary { op, exp } => {
                let src = self.translate_expression(*exp, instrs);
                let dst = self.get_new_tmpvar();
                instrs.push(InstructionTacky::Unary {
                    op,
                    src,
                    dst: dst.clone(),
                });
                dst
            }
            Exp::Binary { op, l_exp, r_exp } => {
                let src1 = self.translate_expression(*l_exp, instrs);
                let src2 = self.translate_expression(*r_exp, instrs);
                let dst = self.get_new_tmpvar();
                instrs.push(InstructionTacky::Binary {
                    op,
                    src1,
                    src2,
                    dst: dst.clone(),
                });
                dst
            }
        }
    }

    fn get_new_tmpvar(&mut self) -> ValTacky {
        self.tmp_no += 1;
        ValTacky::TmpVar {
            no: self.tmp_no - 1,
        }
    }
}

/// ## TESTS THE FOLLOWING TRANSLATION
/// ### C (AST input):
/// ```c
/// return 3;
/// ```text
/// ### TACKY (output):
/// ```
/// Return(Constant(3))
/// ```
#[test]
fn translate_return() {
    let return_three = StatementC::Return {
        exp: Box::new(Exp::Const { c: 3 }),
    };
    assert_eq!(
        TackyEmitter::new().translate_statement(return_three),
        vec![InstructionTacky::Ret {
            v: ValTacky::Const { int: 3 }
        }]
    );
}

/// ## TESTS THE FOLLOWING TRANSLATION
/// ### C (AST input):
/// ```c
/// return ~2;  // or `return ~(2);`
/// ```text
/// ### TACKY (output):
/// ```
/// Unary(Complement, Constant(2), Var("tmp.0"))
/// Return(Var("tmp.0"))
/// ```
#[test]
fn translate_return_complement() {
    let return_comp_two = StatementC::Return {
        exp: Box::new(Exp::Unary {
            op: UnaryOp::BitwiseComplement,
            exp: Box::new(Exp::Const { c: 2 }),
        }),
    };
    assert_eq!(
        TackyEmitter::new().translate_statement(return_comp_two),
        vec![
            InstructionTacky::Unary {
                op: UnaryOp::BitwiseComplement,
                src: ValTacky::Const { int: 2 },
                dst: ValTacky::TmpVar { no: 0 }
            },
            InstructionTacky::Ret {
                v: ValTacky::TmpVar { no: 0 }
            }
        ]
    );
}

/// ## TESTS THE FOLLOWING TRANSLATION
/// ### C (AST input):
/// ```c
/// return -(~(-2));
/// ```
/// ### TACKY (output):
/// ```text
/// Unary(Negate, Constant(8), Var("tmp.0"))
/// Unary(Complement, Var("tmp.0"), Var("tmp.1"))
/// Unary(Negate, Var("tmp.1"), Var("tmp.2"))
/// Return(Var("tmp.2"))
/// ```
#[test]
fn translate_threefold_unary() {
    let return_negcompneg_eight = StatementC::Return {
        exp: Box::new(Exp::Unary {
            op: UnaryOp::Negate,
            exp: Box::new(Exp::Unary {
                op: UnaryOp::BitwiseComplement,
                exp: Box::new(Exp::Unary {
                    op: UnaryOp::Negate,
                    exp: Box::new(Exp::Const { c: 8 }),
                }),
            }),
        }),
    };
    assert_eq!(
        TackyEmitter::new().translate_statement(return_negcompneg_eight),
        vec![
            InstructionTacky::Unary {
                op: UnaryOp::Negate,
                src: ValTacky::Const { int: 8 },
                dst: ValTacky::TmpVar { no: 0 }
            },
            InstructionTacky::Unary {
                op: UnaryOp::BitwiseComplement,
                src: ValTacky::TmpVar { no: 0 },
                dst: ValTacky::TmpVar { no: 1 }
            },
            InstructionTacky::Unary {
                op: UnaryOp::Negate,
                src: ValTacky::TmpVar { no: 1 },
                dst: ValTacky::TmpVar { no: 2 }
            },
            InstructionTacky::Ret {
                v: ValTacky::TmpVar { no: 2 }
            }
        ]
    );
}

/// ## TESTS THE FOLLOWING TRANSLATION
/// ## C (AST input):
/// ```c
/// return 1 + 1;
/// ```
/// ### TACKY (output):
/// ```text
/// Binary(Add, Constant(1), Constant(1), Var("tmp.0"))
/// Return(Var("tmp.0"))
/// ```
#[test]
fn translate_one_plus_one() {
    let ret_statement = StatementC::Return {
        exp: Box::new(Exp::Binary {
            op: BinaryOp::Add,
            l_exp: Box::new(Exp::Const { c: 1 }),
            r_exp: Box::new(Exp::Const { c: 2 }),
        }),
    };
    assert_eq!(
        TackyEmitter::new().translate_statement(ret_statement),
        vec![
            InstructionTacky::Binary {
                op: BinaryOp::Add,
                src1: ValTacky::Const { int: 1 },
                src2: ValTacky::Const { int: 2 },
                dst: ValTacky::TmpVar { no: 0 }
            },
            InstructionTacky::Ret {
                v: ValTacky::TmpVar { no: 0 }
            }
        ]
    );
}
