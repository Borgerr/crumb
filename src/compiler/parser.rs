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

/* ABSTRACT GRAMMAR: (as of v0.1.0)
 * program = Program(function_definition)
 * function_definition = Function(identifier name, statement)
 * statement = Return(exp)
 * exp = Constant(int)
 */

/* FORMAL GRAMMAR: (as of v0.1.0)
 * <program> ::= <function>
 * <function> ::= "int" <identifier> "(" "void" ")" "{" <statement> "}"
 * <statement> ::= "return" <exp> ";"
 * <exp> ::= <int>
 * <identifier> ? An identifier token ?
 * <int> ? A constant token ?
 */

pub enum AST {
    Program {
        function: Box<AST>,
    },
    FunDef {
        identifier: String,
        statement: Box<AST>,
    },
    Statement {
        exp: Box<AST>,
    },
    Expression {
        c: i32,
    },
}

impl Display for AST {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Program { function } => write!(f, "program with inner function : {}", function),
            Self::FunDef {
                identifier,
                statement,
            } => write!(f, "function {} with definition : {}", identifier, statement),
            Self::Statement { exp } => write!(f, "statement with inner expression : {}", exp),
            Self::Expression { c } => write!(f, "expression with c = {}", c),
        }
    }
}

/// Big scary parse function.
/// As of v0.1.0, a thin wrapper over parse_fundef.
pub fn parse(tokens: Vec<Token>) -> Result<AST, ParseError> {
    Ok(AST::Program {
        function: Box::new(parse_fundef(&mut tokens.into_iter())?),
    })
}

/// Expects a function definition.
/// If this isn't found, returns an error.
/// ### v0.1.0 function definition grammar
/// `<function> ::= "int" <identifier> "(" "void" ")" "{" <statement> "}"`
fn parse_fundef(tokens: &mut IntoIter<Token>) -> Result<AST, ParseError> {
    if expect_token(tokens)? != (Token::TyKeyword { ty: Type::Int }) {
        return Err(ParseError::FundefError {
            reason: "expected a function definition but first token was not a valid return type"
                .to_string(),
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
            reason: "expected a function definition but first token was not a valid return type"
                .to_string(),
        });
    }

    expect_variant(tokens, Token::CloseParens)?;
    expect_variant(tokens, Token::OpenBrace)?;
    let function = AST::FunDef {
        identifier: id_string,
        statement: Box::new(parse_statement(tokens)?),
    };
    expect_variant(tokens, Token::CloseBrace)?;

    Ok(function)
}

/// Expects a statement.
/// If this isn't found, returns an error.
/// ### v0.1.0 statement grammar
/// `<statement> ::= "return" <exp> ";"`
fn parse_statement(tokens: &mut IntoIter<Token>) -> Result<AST, ParseError> {
    expect_variant(tokens, Token::RetKeyword)?;
    let ret = Ok(AST::Statement {
        exp: Box::new(parse_exp(tokens)?),
    });
    expect_variant(tokens, Token::Semicolon)?;
    ret
}

/// Expects an expression.
/// If this isn't found, returns an error.
/// ### v0.1.0 exp grammar
/// `<exp> ::= <int>`
fn parse_exp(tokens: &mut IntoIter<Token>) -> Result<AST, ParseError> {
    let got = expect_token(tokens)?;
    if let Token::Constant { val } = got {
        Ok(AST::Expression { c: val })
    } else {
        Err(ParseError::InvalidSyntax {
            got,
            expected: Token::Constant { val: 42 },
        })
    }
}

fn expect_token(tokens: &mut IntoIter<Token>) -> Result<Token, ParseError> {
    match tokens.next() {
        Some(token) => Ok(token),
        None => Err(ParseError::SeverredStream),
    }
}

fn expect_variant(tokens: &mut IntoIter<Token>, expected: Token) -> Result<(), ParseError> {
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
    assert!(if let Ok(_) = res { true } else { false });
}
