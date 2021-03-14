use nom::character::complete::{multispace0, multispace1};
use nom::error::{ErrorKind, ParseError};
use nom::{alt, char, complete, do_parse, many0, named, separated_list0, tag};

#[macro_use]
mod macros;
mod expr;
mod type_;

use crate::ast::{Decl, Fun, Ident};
pub use expr::expr;
pub use type_::type_;

pub type Error = nom::Err<nom::error::Error<String>>;

pub(crate) fn is_reserved(s: &str) -> bool {
    matches!(
        s,
        "if" | "then" | "else" | "let" | "in" | "fn" | "int" | "float" | "bool" | "true" | "false"
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

named!(fun_decl(&str) -> Decl, do_parse!(
    complete!(tag!("fn"))
        >> multispace0
        >> name: ident
        >> multispace1
        >> args: separated_list0!(multispace1, ident)
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

named!(pub decl(&str) -> Decl, alt!(
    fun_decl
));

named!(pub toplevel(&str) -> Vec<Decl>, many0!(decl));

#[cfg(test)]
mod tests {
    use std::convert::TryInto;

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
    fn multiple_decls() {
        let res = test_parse!(
            toplevel,
            "fn id x = x
             fn plus x y = x + y
             fn main = plus (id 2) 7"
        );
        assert_eq!(res.len(), 3);
    }
}
