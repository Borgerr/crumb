use std::{fmt::Display, iter::Peekable};
use thiserror::Error;

use super::lexer::{Token, Type};

#[derive(Error, Debug, Clone, PartialEq)]
pub enum ParseError {
    FundefError { reason: String },
    SeverredStream { location: String },
    InvalidIdentifier { wrong_id: Token },
    InvalidSyntax { got: Token, expected: Token },
}

type ParseResult<T> = Result<T, ParseError>;

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FundefError { reason } => {
                write!(f, "(!) Error parsing function definition: {}", reason)
            }
            Self::SeverredStream { location } => write!(
                f,
                "(!) Error parsing interrupted stream of tokens in {}",
                location
            ),
            Self::InvalidIdentifier { wrong_id } => {
                write!(f, "(!) Error parsing on invalid identifier: {}", wrong_id)
            }
            Self::InvalidSyntax { got, expected } => write!(
                f,
                "(!) Error parsing, invalid syntax. Got a {} when I expected a {}.",
                got, expected
            ),
        }
    }
}

/// Abstract C program
/// ### Abstract grammar as of v0.1.0
/// ```text
/// program = Program(function_definition)
/// ```
/// ### Concrete grammar as of v0.1.0
/// ```text
/// <program> ::= <function>
/// ```
#[derive(PartialEq, Debug)]
pub struct ProgramC {
    pub function: Box<FunDefC>,
}

impl Display for ProgramC {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ProgramC with inner FunDefC : {}", self.function)
    }
}

/// Abstract C function definition
/// ### Abstract grammar as of v0.1.0
/// ```text
/// function_definition = Function(identifier name, statement)
/// ```
/// ### Concrete grammar as of v0.1.0
/// ```text
/// <function> ::= "int" <identifier> "(" "void" ")" "{" <statement> "}"
/// ```
#[derive(PartialEq, Debug)]
pub struct FunDefC {
    pub identifier: String,
    pub statement: Box<StatementC>,
}

impl Display for FunDefC {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "FunDefC with identifier ({}) and inner statement : {}",
            self.identifier, self.statement
        )
    }
}

/// Abstract C statement
/// ### Abstract grammar as of v0.1.0
/// ```text
/// statement = Return(exp)
/// ```
/// ### Concrete grammar as of v0.1.0
/// ```text
/// <statement> ::= "return" <exp> ";"
/// ```
#[derive(PartialEq, Debug)]
pub enum StatementC {
    Return { exp: Box<Exp> },
}

impl Display for StatementC {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Return { exp } => write!(f, "return expression with inner exp : {}", exp),
        }
    }
}

/// Resolved C expression unifying ExpC and FactorC symbols.
#[derive(PartialEq, Debug)]
pub enum Exp {
    Binary {
        op: BinaryOp,
        l_exp: Box<Exp>,
        r_exp: Box<Exp>,
    },
    Const {
        c: i32,
    },
    Unary {
        op: UnaryOp,
        exp: Box<Exp>,
    },
}

impl Display for Exp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Exp::Binary { op, l_exp, r_exp } => write!(
                f,
                "Binary expression with op = {}, l_exp = {}, r_exp = {}",
                op, *l_exp, *r_exp
            ),
            Exp::Const { c } => write!(f, "Constant expression with c = {}", c),
            Exp::Unary { op, exp } => {
                write!(f, "Unary expression with op = {}, exp = {}", op, *exp)
            }
        }
    }
}

impl Exp {
    fn from_expc(expc: ExpC) -> Self {
        match expc {
            ExpC::Factor { fac } => Self::from_factc(*fac),
            ExpC::Binary { op, l_exp, r_exp } => Self::Binary {
                op,
                l_exp: Box::new(Self::from_expc(*l_exp)),
                r_exp: Box::new(Self::from_expc(*r_exp)),
            },
        }
    }
    fn from_factc(factc: FactorC) -> Self {
        match factc {
            FactorC::Const { c } => Self::Const { c },
            FactorC::Unary { op, fac } => Self::Unary {
                op,
                exp: Box::new(Self::from_factc(*fac)),
            },
            FactorC::Exp { exp } => Self::from_expc(*exp),
        }
    }
}

/// Abstract C expression
/// ### Abstract grammar as of v0.1.2
/// ```text
/// exp = Factor(factor) | Binary(binary_operator, l_exp, r_exp)
/// ```
/// ### Concrete grammar as of v0.1.2
/// ```text
/// <exp> ::= <factor> | <exp> <binop> <exp>
/// ```
#[derive(PartialEq, Debug)]
enum ExpC {
    Factor {
        fac: Box<FactorC>,
    },
    Binary {
        op: BinaryOp,
        l_exp: Box<ExpC>,
        r_exp: Box<ExpC>,
    },
}

impl Display for ExpC {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Factor { fac } => write!(f, "Factor expression with inner fac = {}", *fac),
            Self::Binary { op, l_exp, r_exp } => write!(
                f,
                "Binary expression with binop = {}, l_exp = {}, r_exp = {}",
                op, *l_exp, *r_exp
            ),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    ShiftRight,
    ShiftLeft,
}

impl Display for BinaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add => write!(f, "Add"),
            Self::Subtract => write!(f, "Subtract"),
            Self::Multiply => write!(f, "Multiply"),
            Self::Divide => write!(f, "Divide"),
            Self::Remainder => write!(f, "Remainder"),
            Self::BitwiseAnd => write!(f, "Bitwise 'and'"),
            Self::BitwiseOr => write!(f, "Bitwise 'or'"),
            Self::BitwiseXor => write!(f, "Bitwise 'xor'"),
            Self::ShiftRight => write!(f, "Shift right"),
            Self::ShiftLeft => write!(f, "Shift left"),
        }
    }
}

impl BinaryOp {
    fn from(token: Token) -> ParseResult<Self> {
        match token {
            Token::Plus => Ok(Self::Add),
            Token::Minus => Ok(Self::Subtract),
            Token::Asterisk => Ok(Self::Multiply),
            Token::FSlash => Ok(Self::Divide),
            Token::Percent => Ok(Self::Remainder),
            Token::Ampersand => Ok(Self::BitwiseAnd),
            Token::Pipe => Ok(Self::BitwiseOr),
            Token::Caret => Ok(Self::BitwiseXor),
            Token::GtGt => Ok(Self::ShiftRight),
            Token::LtLt => Ok(Self::ShiftLeft),
            _ => Err(ParseError::InvalidSyntax {
                got: token,
                expected: Token::Plus,
            }),
        }
    }
    fn token_prec(token: &Token) -> u8 {
        match token {
            Token::Pipe => 0,
            Token::Caret => 1,
            Token::Ampersand => 2,
            Token::GtGt | Token::LtLt => 3,
            Token::Plus | Token::Minus => 4,
            Token::Asterisk | Token::FSlash | Token::Percent => 5,
            _ => 255,
        }
    }
}

/// Factor. Same ADT type as an expression, but allows for mutual recursion and precedence climbing.
/// ### Formal Grammar as of v0.1.2
/// ```text
/// <factor> ::= <int> | <unop> <factor> | "(" <exp> ")"
/// ```
#[derive(PartialEq, Debug)]
enum FactorC {
    Const { c: i32 },
    Unary { op: UnaryOp, fac: Box<FactorC> },
    Exp { exp: Box<ExpC> },
}

impl Display for FactorC {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Const { c } => write!(f, "constant factor with c = {}", c),
            Self::Unary { op, fac } => write!(f, "unary factor with unop = {}, fac = {}", op, *fac),
            Self::Exp { exp } => write!(f, "expression factor with exp = {}", *exp),
        }
    }
}

/// Abstract C unary operation.
/// - `~`: bitwise complement
/// - `-`: integer negation
#[derive(PartialEq, Debug, Clone)]
pub enum UnaryOp {
    Negate,
    BitwiseComplement,
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Negate => write!(f, "UnaryOp::Negate"),
            Self::BitwiseComplement => write!(f, "UnaryOp::BitwiseComplement"),
        }
    }
}

/// Big scary parse function.
/// As of v0.1.0, a thin wrapper over parse_fundef.
pub fn parse(tokens: Vec<Token>) -> ParseResult<ProgramC> {
    Ok(ProgramC {
        function: Box::new(parse_fundef(&mut tokens.into_iter())?),
    })
}

/// Expects a function definition.
/// If this isn't found, returns an error.
fn parse_fundef(tokens: &mut impl Iterator<Item = Token>) -> ParseResult<FunDefC> {
    if expect_token(tokens, String::from("parse_fundef (1)"))?
        != (Token::TyKeyword { ty: Type::Int })
    {
        return Err(ParseError::FundefError {
            reason: String::from(
                "expected a function definition but first token was not a valid return type",
            ),
        });
    }

    let id_attempt = expect_token(tokens, String::from("parse_fundef (2)"))?;
    let id_string = if let Token::Identifier { val } = id_attempt {
        val
    } else {
        return Err(ParseError::InvalidIdentifier {
            wrong_id: id_attempt,
        });
    };

    expect_variant(tokens, Token::OpenParens)?;

    if expect_token(tokens, String::from("parse_fundef (3)"))?
        != (Token::TyKeyword { ty: Type::Void })
    {
        return Err(ParseError::FundefError {
            reason: String::from("crumb v0.1.0 only accepts the `void` parameter"),
        });
    }

    expect_variant(tokens, Token::CloseParens)?;
    expect_variant(tokens, Token::OpenBrace)?;
    let function = FunDefC {
        identifier: id_string,
        statement: Box::new(parse_statement(tokens)?),
    };
    expect_variant(tokens, Token::CloseBrace)?;

    Ok(function)
}

/// Expects a statement.
/// If this isn't found, returns an error.
fn parse_statement(tokens: &mut impl Iterator<Item = Token>) -> ParseResult<StatementC> {
    let tokens = &mut tokens.peekable();
    expect_variant(tokens, Token::RetKeyword)?;
    let expc = parse_exp(tokens, 0)?;
    let exp = Exp::from_expc(expc);
    let ret = Ok(StatementC::Return { exp: Box::new(exp) });
    expect_variant(tokens, Token::Semicolon)?;
    ret
}

/// Expects an expression.
/// If this isn't found, returns an error.
fn parse_exp(
    tokens: &mut Peekable<&mut impl Iterator<Item = Token>>,
    min_prec: u8,
) -> ParseResult<ExpC> {
    let mut left = ExpC::Factor {
        fac: Box::new(parse_factor(tokens)?),
    };

    while let Some(next_token) = tokens.next_if(|t| {
        matches!(
            t,
            Token::Plus
                | Token::Minus
                | Token::Asterisk
                | Token::FSlash
                | Token::Percent
                | Token::Ampersand
                | Token::Pipe
                | Token::Caret
                | Token::GtGt
                | Token::LtLt
        ) && BinaryOp::token_prec(&t) >= min_prec
    }) {
        let prec = BinaryOp::token_prec(&next_token) + 1;
        left = ExpC::Binary {
            op: BinaryOp::from(next_token)?,
            l_exp: Box::new(left),
            r_exp: Box::new(parse_exp(tokens, prec)?),
        }
    }

    Ok(left)
}

fn parse_factor(tokens: &mut Peekable<&mut impl Iterator<Item = Token>>) -> ParseResult<FactorC> {
    let got = expect_token(tokens, String::from("parse_factor"))?;
    match got {
        Token::Constant { val } => Ok(FactorC::Const { c: val }),
        Token::Tilde => Ok(FactorC::Unary {
            op: UnaryOp::BitwiseComplement,
            fac: Box::new(parse_factor(tokens)?),
        }),
        Token::Minus => Ok(FactorC::Unary {
            op: UnaryOp::Negate,
            fac: Box::new(parse_factor(tokens)?),
        }),
        Token::OpenParens => {
            let inner = parse_exp(tokens, 0)?;
            expect_variant(tokens, Token::CloseParens)?;
            Ok(FactorC::Exp {
                exp: Box::new(inner),
            })
        }
        _ => Err(ParseError::InvalidSyntax {
            got,
            expected: Token::Constant { val: 42 },
        }),
    }
}

fn expect_token(tokens: &mut impl Iterator<Item = Token>, location: String) -> ParseResult<Token> {
    match tokens.next() {
        Some(token) => Ok(token),
        None => Err(ParseError::SeverredStream { location }),
    }
}

fn expect_variant(tokens: &mut impl Iterator<Item = Token>, expected: Token) -> ParseResult<()> {
    let token = expect_token(
        tokens,
        format!("expect_variant with expected token = {}", expected),
    )?;

    if token == expected {
        Ok(())
    } else {
        Err(ParseError::InvalidSyntax {
            got: token,
            expected,
        })
    }
}

#[test]
fn test_variant_error() {
    let mut tokens = vec![Token::OpenBrace].into_iter();
    let res = expect_variant(&mut tokens, Token::CloseBrace);

    match res {
        Ok(_) => assert!(false),
        Err(e) => assert_eq!(
            e,
            ParseError::InvalidSyntax {
                got: Token::OpenBrace,
                expected: Token::CloseBrace
            }
        ),
    }
}

#[test]
fn test_variant_success() {
    let mut tokens = vec![Token::OpenBrace].into_iter();
    let res = expect_variant(&mut tokens, Token::OpenBrace);
    assert!(res.is_ok());
}

/// tests the parsing of `2`
#[test]
fn test_constant_exp() {
    let tokens = &mut vec![Token::Constant { val: 2 }].into_iter();
    let tokens = &mut tokens.peekable();
    let res = parse_exp(tokens, 0);
    let res = res.unwrap();
    assert_eq!(Exp::from_expc(res), Exp::Const { c: 2 });
}

/// tests the parsing of `~(~(~2))`
#[test]
fn test_nested_cmp_parens() {
    let tokens = &mut vec![
        Token::Tilde,
        Token::OpenParens,
        Token::Tilde,
        Token::OpenParens,
        Token::Tilde,
        Token::Constant { val: 2 },
        Token::CloseParens,
        Token::CloseParens,
    ]
    .into_iter();
    let tokens = &mut tokens.peekable();
    let res = parse_exp(tokens, 0);
    let res = res.unwrap();
    assert_eq!(
        Exp::from_expc(res),
        Exp::Unary {
            op: UnaryOp::BitwiseComplement,
            exp: Box::new(Exp::Unary {
                op: UnaryOp::BitwiseComplement,
                exp: Box::new(Exp::Unary {
                    op: UnaryOp::BitwiseComplement,
                    exp: Box::new(Exp::Const { c: 2 })
                })
            })
        }
    )
}

/// tests the parsing of `(((2)))`
#[test]
fn test_nested_parens() {
    let tokens = &mut vec![
        Token::OpenParens,
        Token::OpenParens,
        Token::OpenParens,
        Token::Constant { val: 2 },
        Token::CloseParens,
        Token::CloseParens,
        Token::CloseParens,
    ]
    .into_iter();
    let tokens = &mut tokens.peekable();
    let res = parse_exp(tokens, 0);
    let res = res.unwrap();
    assert_eq!(Exp::from_expc(res), Exp::Const { c: 2 });
}

/// tests the parsing of `return ~(~(~2));`
#[test]
fn test_return_nested_parens() {
    let mut tokens = vec![
        Token::RetKeyword,
        Token::Tilde,
        Token::OpenParens,
        Token::Tilde,
        Token::OpenParens,
        Token::Tilde,
        Token::Constant { val: 2 },
        Token::CloseParens,
        Token::CloseParens,
        Token::Semicolon,
    ]
    .into_iter();
    let res = parse_statement(&mut tokens);
    assert!(res.is_ok());
}

/// tests the parsing of `1 + 1`
#[test]
fn test_one_plus_one() {
    let tokens = &mut vec![
        Token::Constant { val: 1 },
        Token::Plus,
        Token::Constant { val: 1 },
    ]
    .into_iter();
    let res = parse_exp(&mut tokens.peekable(), 0);
    let res = res.unwrap();
    let expected = ExpC::Binary {
        op: BinaryOp::Add,
        l_exp: Box::new(ExpC::Factor {
            fac: Box::new(FactorC::Const { c: 1 }),
        }),
        r_exp: Box::new(ExpC::Factor {
            fac: Box::new(FactorC::Const { c: 1 }),
        }),
    };
    assert_eq!(res, expected);
}

/// tests the parsing of `1 + 2 - 3`
#[test]
fn test_one_plus_two_minus_three() {
    let tokens = &mut vec![
        Token::Constant { val: 1 },
        Token::Plus,
        Token::Constant { val: 2 },
        Token::Minus,
        Token::Constant { val: 3 },
    ]
    .into_iter();
    let res = parse_exp(&mut tokens.peekable(), 0);
    let res = Exp::from_expc(res.unwrap());
    let expected = Exp::Binary {
        op: BinaryOp::Subtract,
        l_exp: Box::new(Exp::Binary {
            op: BinaryOp::Add,
            l_exp: Box::new(Exp::Const { c: 1 }),
            r_exp: Box::new(Exp::Const { c: 2 }),
        }),
        r_exp: Box::new(Exp::Const { c: 3 }),
    };
    assert_eq!(res, expected);
}

/// tests the parsing of `1 + (2 - 3)`
#[test]
fn test_one_plus_parens_two_minus_three() {
    let tokens = &mut vec![
        Token::Constant { val: 1 },
        Token::Plus,
        Token::OpenParens,
        Token::Constant { val: 2 },
        Token::Minus,
        Token::Constant { val: 3 },
        Token::CloseParens,
    ]
    .into_iter();
    let res = parse_exp(&mut tokens.peekable(), 0);
    let res = Exp::from_expc(res.unwrap());
    let expected = Exp::Binary {
        op: BinaryOp::Add,
        l_exp: Box::new(Exp::Const { c: 1 }),
        r_exp: Box::new(Exp::Binary {
            op: BinaryOp::Subtract,
            l_exp: Box::new(Exp::Const { c: 2 }),
            r_exp: Box::new(Exp::Const { c: 3 }),
        }),
    };
    assert_eq!(res, expected);
}

/// tests the parsing of `1 + 2 * 3`
#[test]
fn test_one_plus_two_times_three() {
    let tokens = &mut vec![
        Token::Constant { val: 1 },
        Token::Plus,
        Token::Constant { val: 2 },
        Token::Asterisk,
        Token::Constant { val: 3 },
    ]
    .into_iter();
    let res = parse_exp(&mut tokens.peekable(), 0);
    let res = Exp::from_expc(res.unwrap());
    let expected = Exp::Binary {
        op: BinaryOp::Add,
        l_exp: Box::new(Exp::Const { c: 1 }),
        r_exp: Box::new(Exp::Binary {
            op: BinaryOp::Multiply,
            l_exp: Box::new(Exp::Const { c: 2 }),
            r_exp: Box::new(Exp::Const { c: 3 }),
        }),
    };
    assert_eq!(res, expected);
}

/// tests the parsing of `1 * 2 - 3 * (4 + 5)`
#[test]
fn test_one_times_two_minus_three_times_parens_four_plus_five() {
    let tokens = &mut vec![
        Token::Constant { val: 1 },
        Token::Asterisk,
        Token::Constant { val: 2 },
        Token::Minus,
        Token::Constant { val: 3 },
        Token::Asterisk,
        Token::OpenParens,
        Token::Constant { val: 4 },
        Token::Plus,
        Token::Constant { val: 5 },
        Token::CloseParens,
    ]
    .into_iter();
    let res = parse_exp(&mut tokens.peekable(), 0);
    let res = Exp::from_expc(res.unwrap());
    let expected = Exp::Binary {
        op: BinaryOp::Subtract,
        l_exp: Box::new(Exp::Binary {
            op: BinaryOp::Multiply,
            l_exp: Box::new(Exp::Const { c: 1 }),
            r_exp: Box::new(Exp::Const { c: 2 }),
        }),
        r_exp: Box::new(Exp::Binary {
            op: BinaryOp::Multiply,
            l_exp: Box::new(Exp::Const { c: 3 }),
            r_exp: Box::new(Exp::Binary {
                op: BinaryOp::Add,
                l_exp: Box::new(Exp::Const { c: 4 }),
                r_exp: Box::new(Exp::Const { c: 5 }),
            }),
        }),
    };
    assert_eq!(res, expected);
}

/// tests the parsing of `-(1 + 1)`
#[test]
fn test_negate_one_plus_one() {
    let tokens = &mut vec![
        Token::Minus,
        Token::OpenParens,
        Token::Constant { val: 1 },
        Token::Plus,
        Token::Constant { val: 1 },
        Token::CloseParens,
    ]
    .into_iter();
    let res = parse_exp(&mut tokens.peekable(), 0);
    let res = Exp::from_expc(res.unwrap());
    let expected = Exp::Unary {
        op: UnaryOp::Negate,
        exp: Box::new(Exp::Binary {
            op: BinaryOp::Add,
            l_exp: Box::new(Exp::Const { c: 1 }),
            r_exp: Box::new(Exp::Const { c: 1 }),
        }),
    };
    assert_eq!(res, expected);
}
