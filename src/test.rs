use crate::compiler::{lexer, parser};

static BASIC_RETURN_FROM_MAIN: &str = "int main(void) { return 2; }";
static WHITESPACELESS_RETURN_FROM_MAIN: &str = "int main(void){return 2;}";

#[test]
fn basic_return_from_main_tokenize() {
    let source = BASIC_RETURN_FROM_MAIN.to_owned();
    let stream = vec![
        lexer::Token::TyKeyword {
            ty: lexer::Type::Int,
        },
        lexer::Token::Identifier {
            val: String::from("main"),
        },
        lexer::Token::OpenParens,
        lexer::Token::TyKeyword {
            ty: lexer::Type::Void,
        },
        lexer::Token::CloseParens,
        lexer::Token::OpenBrace,
        lexer::Token::RetKeyword,
        lexer::Token::Constant { val: 2 },
        lexer::Token::Semicolon,
        lexer::Token::CloseBrace,
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
            parser::parse(tokens).unwrap(),
            parser::ProgramC {
                function: Box::new(parser::FunDefC {
                    identifier: String::from("main"),
                    statement: Box::new(parser::StatementC {
                        exp: Box::new(parser::ExpC { c: 2 })
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
        lexer::Token::TyKeyword {
            ty: lexer::Type::Int,
        },
        lexer::Token::Identifier {
            val: String::from("main"),
        },
        lexer::Token::OpenParens,
        lexer::Token::TyKeyword {
            ty: lexer::Type::Void,
        },
        lexer::Token::CloseParens,
        lexer::Token::OpenBrace,
        lexer::Token::RetKeyword,
        lexer::Token::Constant { val: 2 },
        lexer::Token::Semicolon,
        lexer::Token::CloseBrace,
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
            parser::parse(tokens).unwrap(),
            parser::ProgramC {
                function: Box::new(parser::FunDefC {
                    identifier: String::from("main"),
                    statement: Box::new(parser::StatementC {
                        exp: Box::new(parser::ExpC { c: 2 })
                    })
                })
            }
        )
    } else {
        assert!(false)
    }
}
