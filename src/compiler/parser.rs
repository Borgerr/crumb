use std::{fmt::Display, vec::IntoIter};
use thiserror::Error;

use super::lexer::{Token, Type};

#[derive(Error, Debug, Clone, PartialEq)]
pub enum ParseError {
    FundefError { reason: String },
    SeverredStream,
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
            Self::SeverredStream => write!(f, "(!) Error parsing interrupted stream of tokens"),
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
    Return { exp: Box<ExpC> },
}

impl Display for StatementC {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Return { exp } => write!(f, "return expression with inner exp : {}", exp),
        }
    }
}

/// Abstract C expression
/// ### Abstract grammar as of v0.1.1
/// ```text
/// exp = Constant(int) | Unary(unary_operator, exp)
/// ```
/// ### Concrete grammar as of v0.1.1
/// ```text
/// <exp> ::= <int> | <unop> <exp> | "(" <exp> ")"
/// ```
#[derive(PartialEq, Debug)]
pub enum ExpC {
    Const { c: i32 },
    Unary { op: UnaryOp, exp: Box<ExpC> },
}

impl Display for ExpC {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Const { c } => write!(f, "ExpC::Const with c = {}", c),
            Self::Unary { op, exp } => write!(f, "ExpC::Unary with op = {}, exp = {}", op, *exp),
        }
    }
}

/// Factor. Same ADT type as an expression, but allows for mutual recursion and precedence climbing.
/// ### Formal Grammar as of v0.1.2
/// ```text
/// <factor> ::= <int> | <unop> <factor> | "(" <exp> ")"
/// ```
#[derive(PartialEq, Debug)]
pub enum FactorC {
    Const { c: i32 },
    Unary { op: UnaryOp, fac: Box<FactorC> },
    Exp { exp: Box<ExpC> },
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
    if expect_token(tokens)? != (Token::TyKeyword { ty: Type::Int }) {
        return Err(ParseError::FundefError {
            reason: String::from(
                "expected a function definition but first token was not a valid return type",
            ),
        });
    }

    let id_attempt = expect_token(tokens)?;
    let id_string = if let Token::Identifier { val } = id_attempt {
        val
    } else {
        return Err(ParseError::InvalidIdentifier {
            wrong_id: id_attempt,
        });
    };

    expect_variant(tokens, Token::OpenParens)?;

    if expect_token(tokens)? != (Token::TyKeyword { ty: Type::Void }) {
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
    expect_variant(tokens, Token::RetKeyword)?;
    let ret = Ok(StatementC::Return {
        exp: Box::new(parse_exp(tokens)?),
    });
    expect_variant(tokens, Token::Semicolon)?;
    ret
}

/// Expects an expression.
/// If this isn't found, returns an error.
fn parse_exp(tokens: &mut impl Iterator<Item = Token>) -> ParseResult<ExpC> {
    let got = expect_token(tokens)?;
    match got {
        Token::Constant { val } => Ok(ExpC::Const { c: val }),
        Token::Tilde => Ok(ExpC::Unary {
            op: UnaryOp::BitwiseComplement,
            exp: Box::new(parse_exp(tokens)?),
        }),
        Token::Minus => Ok(ExpC::Unary {
            op: UnaryOp::Negate,
            exp: Box::new(parse_exp(tokens)?),
        }),
        Token::OpenParens => {
            let inner_exp = parse_exp(tokens)?;
            let got = expect_token(tokens)?;
            if let Token::CloseParens = got {
                Ok(inner_exp)
            } else {
                Err(ParseError::InvalidSyntax {
                    got,
                    expected: Token::CloseParens,
                })
            }
        }
        _ => Err(ParseError::InvalidSyntax {
            got,
            expected: Token::Constant { val: 42 },
        }),
    }
}

fn expect_token(tokens: &mut impl Iterator<Item = Token>) -> ParseResult<Token> {
    match tokens.next() {
        Some(token) => Ok(token),
        None => Err(ParseError::SeverredStream),
    }
}

fn expect_variant(tokens: &mut impl Iterator<Item = Token>, expected: Token) -> ParseResult<()> {
    let token = expect_token(tokens)?;

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

/// tests the parsing of ~(~(~2))
#[test]
fn test_nested_cmp_parens() {
    let mut tokens = vec![
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
    let res = parse_exp(&mut tokens);
    assert!(res.is_ok());
}

#[test]
fn test_nested_parens() {
    let mut tokens = vec![
        Token::OpenParens,
        Token::OpenParens,
        Token::OpenParens,
        Token::Constant { val: 2 },
        Token::CloseParens,
        Token::CloseParens,
        Token::CloseParens,
    ]
    .into_iter();
    let res = parse_exp(&mut tokens);
    assert!(res.is_ok());
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
