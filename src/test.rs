use crate::compiler::{
    lexer::{self, Token, Type},
    parser::{parse, AST},
};

static BASIC_RETURN_FROM_MAIN: &str = "int main(void) { return 2; }";
static WHITESPACELESS_RETURN_FROM_MAIN: &str = "int main(void){return 2;}";

#[test]
fn basic_return_from_main_tokenize() {
    let source = BASIC_RETURN_FROM_MAIN.to_owned();
    let stream = vec![
        Token::TyKeyword { ty: Type::Int },
        Token::Identifier {
            val: String::from("main"),
        },
        Token::OpenParens,
        Token::TyKeyword { ty: Type::Void },
        Token::CloseParens,
        Token::OpenBrace,
        Token::RetKeyword,
        Token::Constant { val: 2 },
        Token::Semicolon,
        Token::CloseBrace,
    ];

    if let Ok(tokens) = lexer::tokenize(source) {
        assert_eq!(stream, tokens)
    } else {
        assert!(false)
    }
}

#[test]
fn basic_return_from_main_parse() {
    let source = BASIC_RETURN_FROM_MAIN.to_owned();

    if let Ok(tokens) = lexer::tokenize(source) {
        assert_eq!(
            parse(tokens).unwrap(),
            AST::Program {
                function: Box::new(AST::FunDef {
                    identifier: String::from("main"),
                    statement: Box::new(AST::Statement {
                        exp: Box::new(AST::Expression { c: 2 })
                    })
                })
            }
        )
    } else {
        assert!(false)
    }
}

#[test]
fn whitespaceless_return_from_main_tokenize() {
    let source = WHITESPACELESS_RETURN_FROM_MAIN.to_owned();
    let stream = vec![
        Token::TyKeyword { ty: Type::Int },
        Token::Identifier {
            val: String::from("main"),
        },
        Token::OpenParens,
        Token::TyKeyword { ty: Type::Void },
        Token::CloseParens,
        Token::OpenBrace,
        Token::RetKeyword,
        Token::Constant { val: 2 },
        Token::Semicolon,
        Token::CloseBrace,
    ];

    if let Ok(tokens) = lexer::tokenize(source) {
        assert_eq!(stream, tokens)
    } else {
        assert!(false)
    }
}

#[test]
fn whitespaceless_return_from_main_parse() {
    let source = WHITESPACELESS_RETURN_FROM_MAIN.to_owned();

    if let Ok(tokens) = lexer::tokenize(source) {
        assert_eq!(
            parse(tokens).unwrap(),
            AST::Program {
                function: Box::new(AST::FunDef {
                    identifier: String::from("main"),
                    statement: Box::new(AST::Statement {
                        exp: Box::new(AST::Expression { c: 2 })
                    })
                })
            }
        )
    } else {
        assert!(false)
    }
}
