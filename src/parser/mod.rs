use nom::character::complete::{multispace0, multispace1};
use nom::error::{ErrorKind, ParseError};
use nom::{alt, char, complete, do_parse, many0, named, separated_list0, tag, terminated};

#[macro_use]
mod macros;
mod expr;
mod type_;

use crate::ast::{Arg, Decl, Fun, Ident};
pub use expr::expr;
pub use type_::type_;

pub type Error = nom::Err<nom::error::Error<String>>;

pub(crate) fn is_reserved(s: &str) -> bool {
    matches!(
        s,
        "if" | "then"
            | "else"
            | "let"
            | "in"
            | "fn"
            | "int"
            | "float"
            | "bool"
            | "true"
            | "false"
            | "cstring"
    )
}

pub(crate) fn ident<'a, E>(i: &'a str) -> nom::IResult<&'a str, Ident, E>
where
    E: ParseError<&'a str>,
{
    let mut chars = i.chars();
    if let Some(f) = chars.next() {
        if f.is_alphabetic() || f == '_' {
            let mut idx = 1;
            for c in chars {
                if !(c.is_alphanumeric() || c == '_') {
                    break;
                }
                idx += 1;
            }
            let id = &i[..idx];
            if is_reserved(id) {
                Err(nom::Err::Error(E::from_error_kind(i, ErrorKind::Satisfy)))
            } else {
                Ok((&i[idx..], Ident::from_str_unchecked(id)))
            }
        } else {
            Err(nom::Err::Error(E::from_error_kind(i, ErrorKind::Satisfy)))
        }
    } else {
        Err(nom::Err::Error(E::from_error_kind(i, ErrorKind::Eof)))
    }
}

named!(ascripted_arg(&str) -> Arg, do_parse!(
    complete!(char!('(')) >>
        multispace0 >>
        ident: ident >>
        multispace0 >>
        complete!(char!(':')) >>
        multispace0 >>
        type_: type_ >>
        multispace0 >>
        complete!(char!(')')) >>
        (Arg {
            ident,
            type_: Some(type_)
        })
));

named!(arg(&str) -> Arg, alt!(
    ident => { |ident| Arg {ident, type_: None}} |
    ascripted_arg
));

named!(fun_decl(&str) -> Decl, do_parse!(
    complete!(tag!("fn"))
        >> multispace0
        >> name: ident
        >> multispace1
        >> args: separated_list0!(multispace1, arg)
        >> multispace0
        >> char!('=')
        >> multispace0
        >> body: expr
        >> (Decl::Fun {
            name,
            body: Fun {
                args,
                body
            }
        })
));

named!(ascription_decl(&str) -> Decl, do_parse!(
    name: ident
        >> multispace0
        >> complete!(char!(':'))
        >> multispace0
        >> type_: type_
        >> (Decl::Ascription {
            name,
            type_
        })
));

named!(pub decl(&str) -> Decl, alt!(
    ascription_decl |
    fun_decl
));

named!(pub toplevel(&str) -> Vec<Decl>, terminated!(many0!(decl), multispace0));

#[cfg(test)]
mod tests {
    use std::convert::TryInto;

    use crate::ast::{BinaryOperator, Expr, FunctionType, Literal, Type};

    use super::*;
    use expr::tests::ident_expr;

    #[test]
    fn fn_decl() {
        let res = test_parse!(decl, "fn id x = x");
        assert_eq!(
            res,
            Decl::Fun {
                name: "id".try_into().unwrap(),
                body: Fun {
                    args: vec!["x".try_into().unwrap()],
                    body: *ident_expr("x"),
                }
            }
        )
    }

    #[test]
    fn ascripted_fn_args() {
        test_parse!(ascripted_arg, "(x : int)");
        let res = test_parse!(decl, "fn plus1 (x : int) = x + 1");
        assert_eq!(
            res,
            Decl::Fun {
                name: "plus1".try_into().unwrap(),
                body: Fun {
                    args: vec![Arg {
                        ident: "x".try_into().unwrap(),
                        type_: Some(Type::Int),
                    }],
                    body: Expr::BinaryOp {
                        lhs: ident_expr("x"),
                        op: BinaryOperator::Add,
                        rhs: Box::new(Expr::Literal(Literal::Int(1))),
                    }
                }
            }
        );
    }

    #[test]
    fn multiple_decls() {
        let res = test_parse!(
            toplevel,
            "fn id x = x
             fn plus x y = x + y
             fn main = plus (id 2) 7"
        );
        assert_eq!(res.len(), 3);
        let res = test_parse!(
            toplevel,
            "fn id x = x\nfn plus x y = x + y\nfn main = plus (id 2) 7\n"
        );
        assert_eq!(res.len(), 3);
    }

    #[test]
    fn top_level_ascription() {
        let res = test_parse!(toplevel, "id : fn a -> a");
        assert_eq!(
            res,
            vec![Decl::Ascription {
                name: "id".try_into().unwrap(),
                type_: Type::Function(FunctionType {
                    args: vec![Type::Var("a".try_into().unwrap())],
                    ret: Box::new(Type::Var("a".try_into().unwrap()))
                })
            }]
        )
    }
}
