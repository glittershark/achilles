use std::borrow::Cow;

use nom::alt;
use nom::character::complete::{digit1, multispace0, multispace1};
use nom::{
    call, char, complete, delimited, do_parse, flat_map, many0, map, named, opt, parse_to,
    preceded, separated_list0, separated_list1, tag, tuple,
};
use pratt::{Affix, Associativity, PrattParser, Precedence};

use crate::ast::{BinaryOperator, Binding, Expr, Fun, Literal, UnaryOperator};
use crate::parser::{arg, ident, type_};

#[derive(Debug)]
enum TokenTree<'a> {
    Prefix(UnaryOperator),
    // Postfix(char),
    Infix(BinaryOperator),
    Primary(Expr<'a>),
    Group(Vec<TokenTree<'a>>),
}

named!(prefix(&str) -> TokenTree, map!(alt!(
    complete!(char!('-')) => { |_| UnaryOperator::Neg } |
    complete!(char!('!')) => { |_| UnaryOperator::Not }
), TokenTree::Prefix));

named!(infix(&str) -> TokenTree, map!(alt!(
    complete!(tag!("==")) => { |_| BinaryOperator::Equ } |
    complete!(tag!("!=")) => { |_| BinaryOperator::Neq } |
    complete!(char!('+')) => { |_| BinaryOperator::Add } |
    complete!(char!('-')) => { |_| BinaryOperator::Sub } |
    complete!(char!('*')) => { |_| BinaryOperator::Mul } |
    complete!(char!('/')) => { |_| BinaryOperator::Div } |
    complete!(char!('^')) => { |_| BinaryOperator::Pow }
), TokenTree::Infix));

named!(primary(&str) -> TokenTree, alt!(
    do_parse!(
        multispace0 >>
        char!('(') >>
        multispace0 >>
        group: group >>
        multispace0 >>
        char!(')') >>
        multispace0 >>
            (TokenTree::Group(group))
    ) |
    delimited!(multispace0, simple_expr, multispace0) => { |s| TokenTree::Primary(s) }
));

named!(
    rest(&str) -> Vec<(TokenTree, Vec<TokenTree>, TokenTree)>,
    many0!(tuple!(
        infix,
        delimited!(multispace0, many0!(prefix), multispace0),
        primary
        // many0!(postfix)
    ))
);

named!(group(&str) -> Vec<TokenTree>, do_parse!(
    prefix: many0!(prefix)
        >> primary: primary
        // >> postfix: many0!(postfix)
        >> rest: rest
        >> ({
            let mut res = prefix;
            res.push(primary);
            // res.append(&mut postfix);
            for (infix, mut prefix, primary/*, mut postfix*/) in rest {
                res.push(infix);
                res.append(&mut prefix);
                res.push(primary);
                // res.append(&mut postfix);
            }
            res
        })
));

fn token_tree(i: &str) -> nom::IResult<&str, Vec<TokenTree>> {
    group(i)
}

struct ExprParser;

impl<'a, I> PrattParser<I> for ExprParser
where
    I: Iterator<Item = TokenTree<'a>>,
{
    type Error = pratt::NoError;
    type Input = TokenTree<'a>;
    type Output = Expr<'a>;

    fn query(&mut self, input: &Self::Input) -> Result<Affix, Self::Error> {
        use BinaryOperator::*;
        use UnaryOperator::*;

        Ok(match input {
            TokenTree::Infix(Add) => Affix::Infix(Precedence(6), Associativity::Left),
            TokenTree::Infix(Sub) => Affix::Infix(Precedence(6), Associativity::Left),
            TokenTree::Infix(Mul) => Affix::Infix(Precedence(7), Associativity::Left),
            TokenTree::Infix(Div) => Affix::Infix(Precedence(7), Associativity::Left),
            TokenTree::Infix(Pow) => Affix::Infix(Precedence(8), Associativity::Right),
            TokenTree::Infix(Equ) => Affix::Infix(Precedence(4), Associativity::Right),
            TokenTree::Infix(Neq) => Affix::Infix(Precedence(4), Associativity::Right),
            TokenTree::Prefix(Neg) => Affix::Prefix(Precedence(6)),
            TokenTree::Prefix(Not) => Affix::Prefix(Precedence(6)),
            TokenTree::Primary(_) => Affix::Nilfix,
            TokenTree::Group(_) => Affix::Nilfix,
        })
    }

    fn primary(&mut self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        Ok(match input {
            TokenTree::Primary(expr) => expr,
            TokenTree::Group(group) => self.parse(&mut group.into_iter()).unwrap(),
            _ => unreachable!(),
        })
    }

    fn infix(
        &mut self,
        lhs: Self::Output,
        op: Self::Input,
        rhs: Self::Output,
    ) -> Result<Self::Output, Self::Error> {
        let op = match op {
            TokenTree::Infix(op) => op,
            _ => unreachable!(),
        };
        Ok(Expr::BinaryOp {
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
        })
    }

    fn prefix(&mut self, op: Self::Input, rhs: Self::Output) -> Result<Self::Output, Self::Error> {
        let op = match op {
            TokenTree::Prefix(op) => op,
            _ => unreachable!(),
        };

        Ok(Expr::UnaryOp {
            op,
            rhs: Box::new(rhs),
        })
    }

    fn postfix(
        &mut self,
        _lhs: Self::Output,
        _op: Self::Input,
    ) -> Result<Self::Output, Self::Error> {
        unreachable!()
    }
}

named!(int(&str) -> Literal, map!(flat_map!(digit1, parse_to!(u64)), Literal::Int));

named!(bool_(&str) -> Literal, alt!(
    complete!(tag!("true")) => { |_| Literal::Bool(true) } |
    complete!(tag!("false")) => { |_| Literal::Bool(false) }
));

fn string_internal(i: &str) -> nom::IResult<&str, Cow<'_, str>, nom::error::Error<&str>> {
    let (s, rem) = i
        .split_once('"')
        .ok_or_else(|| nom::Err::Error(nom::error::Error::new(i, nom::error::ErrorKind::Tag)))?;
    Ok((rem, Cow::Borrowed(s)))
}

named!(string(&str) -> Literal, preceded!(
    complete!(char!('"')),
    map!(
        string_internal,
        |s| Literal::String(s)
    )
));

named!(literal(&str) -> Literal, alt!(int | bool_ | string));

named!(literal_expr(&str) -> Expr, map!(literal, Expr::Literal));

named!(binding(&str) -> Binding, do_parse!(
    multispace0
        >> ident: ident
        >> multispace0
        >> type_: opt!(preceded!(tuple!(tag!(":"), multispace0), type_))
        >> multispace0
        >> char!('=')
        >> multispace0
        >> body: expr
        >> (Binding {
            ident,
            type_,
            body
        })
));

named!(let_(&str) -> Expr, do_parse!(
    tag!("let")
        >> multispace0
        >> bindings: separated_list1!(alt!(char!(';') | char!('\n')), binding)
        >> multispace0
        >> tag!("in")
        >> multispace0
        >> body: expr
        >> (Expr::Let {
            bindings,
            body: Box::new(body)
        })
));

named!(if_(&str) -> Expr, do_parse! (
    tag!("if")
        >> multispace0
        >> condition: expr
        >> multispace0
        >> tag!("then")
        >> multispace0
        >> then: expr
        >> multispace0
        >> tag!("else")
        >> multispace0
        >> else_: expr
        >> (Expr::If {
            condition: Box::new(condition),
            then: Box::new(then),
            else_: Box::new(else_)
        })
));

named!(ident_expr(&str) -> Expr, map!(ident, Expr::Ident));

fn ascripted<'a>(
    p: impl Fn(&'a str) -> nom::IResult<&'a str, Expr, nom::error::Error<&'a str>> + 'a,
) -> impl Fn(&'a str) -> nom::IResult<&str, Expr, nom::error::Error<&'a str>> {
    move |i| {
        do_parse!(
            i,
            expr: p
                >> multispace0
                >> complete!(tag!(":"))
                >> multispace0
                >> type_: type_
                >> (Expr::Ascription {
                    expr: Box::new(expr),
                    type_
                })
        )
    }
}

named!(paren_expr(&str) -> Expr,
       delimited!(complete!(tag!("(")), expr, complete!(tag!(")"))));

named!(funcref(&str) -> Expr, alt!(
    ident_expr |
    paren_expr
));

named!(no_arg_call(&str) -> Expr, do_parse!(
    fun: funcref
        >> multispace0
        >> complete!(tag!("()"))
        >> (Expr::Call {
            fun: Box::new(fun),
            args: vec![],
        })
));

named!(fun_expr(&str) -> Expr, do_parse!(
    tag!("fn")
        >> multispace1
        >> args: separated_list0!(multispace1, arg)
        >> multispace0
        >> char!('=')
        >> multispace0
        >> body: expr
        >> (Expr::Fun(Box::new(Fun {
            args,
            body
        })))
));

named!(fn_arg(&str) -> Expr, alt!(
    ident_expr |
    literal_expr |
    paren_expr
));

named!(call_with_args(&str) -> Expr, do_parse!(
    fun: funcref
        >> multispace1
        >> args: separated_list1!(multispace1, fn_arg)
        >> (Expr::Call {
            fun: Box::new(fun),
            args
        })
));

named!(simple_expr_unascripted(&str) -> Expr, alt!(
    let_ |
    if_ |
    fun_expr |
    literal_expr |
    ident_expr
));

named!(simple_expr(&str) -> Expr, alt!(
    call!(ascripted(simple_expr_unascripted)) |
    simple_expr_unascripted
));

named!(pub expr(&str) -> Expr, alt!(
    no_arg_call |
    call_with_args |
    map!(token_tree, |tt| {
        ExprParser.parse(&mut tt.into_iter()).unwrap()
    }) |
    simple_expr
));

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::ast::{Arg, Ident, Type};
    use std::convert::TryFrom;
    use BinaryOperator::*;
    use Expr::{BinaryOp, If, Let, UnaryOp};
    use UnaryOperator::*;

    pub(crate) fn ident_expr(s: &str) -> Box<Expr> {
        Box::new(Expr::Ident(Ident::try_from(s).unwrap()))
    }

    mod operators {
        use super::*;

        #[test]
        fn mul_plus() {
            let (rem, res) = expr("x*y+z").unwrap();
            assert!(rem.is_empty());
            assert_eq!(
                res,
                BinaryOp {
                    lhs: Box::new(BinaryOp {
                        lhs: ident_expr("x"),
                        op: Mul,
                        rhs: ident_expr("y")
                    }),
                    op: Add,
                    rhs: ident_expr("z")
                }
            )
        }

        #[test]
        fn mul_plus_ws() {
            let (rem, res) = expr("x * y    +    z").unwrap();
            assert!(rem.is_empty(), "non-empty remainder: \"{}\"", rem);
            assert_eq!(
                res,
                BinaryOp {
                    lhs: Box::new(BinaryOp {
                        lhs: ident_expr("x"),
                        op: Mul,
                        rhs: ident_expr("y")
                    }),
                    op: Add,
                    rhs: ident_expr("z")
                }
            )
        }

        #[test]
        fn unary() {
            let (rem, res) = expr("x * -z").unwrap();
            assert!(rem.is_empty(), "non-empty remainder: \"{}\"", rem);
            assert_eq!(
                res,
                BinaryOp {
                    lhs: ident_expr("x"),
                    op: Mul,
                    rhs: Box::new(UnaryOp {
                        op: Neg,
                        rhs: ident_expr("z"),
                    })
                }
            )
        }

        #[test]
        fn mul_literal() {
            let (rem, res) = expr("x * 3").unwrap();
            assert!(rem.is_empty());
            assert_eq!(
                res,
                BinaryOp {
                    lhs: ident_expr("x"),
                    op: Mul,
                    rhs: Box::new(Expr::Literal(Literal::Int(3))),
                }
            )
        }

        #[test]
        fn equ() {
            let res = test_parse!(expr, "x * 7 == 7");
            assert_eq!(
                res,
                BinaryOp {
                    lhs: Box::new(BinaryOp {
                        lhs: ident_expr("x"),
                        op: Mul,
                        rhs: Box::new(Expr::Literal(Literal::Int(7)))
                    }),
                    op: Equ,
                    rhs: Box::new(Expr::Literal(Literal::Int(7)))
                }
            )
        }
    }

    #[test]
    fn bools() {
        assert_eq!(
            test_parse!(expr, "true"),
            Expr::Literal(Literal::Bool(true))
        );
        assert_eq!(
            test_parse!(expr, "false"),
            Expr::Literal(Literal::Bool(false))
        );
    }

    #[test]
    fn simple_string_lit() {
        assert_eq!(
            test_parse!(expr, "\"foobar\""),
            Expr::Literal(Literal::String(Cow::Borrowed("foobar")))
        )
    }

    #[test]
    fn let_complex() {
        let res = test_parse!(expr, "let x = 1; y = x * 7 in (x + y) * 4");
        assert_eq!(
            res,
            Let {
                bindings: vec![
                    Binding {
                        ident: Ident::try_from("x").unwrap(),
                        type_: None,
                        body: Expr::Literal(Literal::Int(1))
                    },
                    Binding {
                        ident: Ident::try_from("y").unwrap(),
                        type_: None,
                        body: Expr::BinaryOp {
                            lhs: ident_expr("x"),
                            op: Mul,
                            rhs: Box::new(Expr::Literal(Literal::Int(7)))
                        }
                    }
                ],
                body: Box::new(Expr::BinaryOp {
                    lhs: Box::new(Expr::BinaryOp {
                        lhs: ident_expr("x"),
                        op: Add,
                        rhs: ident_expr("y"),
                    }),
                    op: Mul,
                    rhs: Box::new(Expr::Literal(Literal::Int(4))),
                })
            }
        )
    }

    #[test]
    fn if_simple() {
        let res = test_parse!(expr, "if x == 8 then 9 else 20");
        assert_eq!(
            res,
            If {
                condition: Box::new(BinaryOp {
                    lhs: ident_expr("x"),
                    op: Equ,
                    rhs: Box::new(Expr::Literal(Literal::Int(8))),
                }),
                then: Box::new(Expr::Literal(Literal::Int(9))),
                else_: Box::new(Expr::Literal(Literal::Int(20)))
            }
        )
    }

    #[test]
    fn no_arg_call() {
        let res = test_parse!(expr, "f()");
        assert_eq!(
            res,
            Expr::Call {
                fun: ident_expr("f"),
                args: vec![]
            }
        );
    }

    #[test]
    fn call_with_args() {
        let res = test_parse!(expr, "f x 1");
        assert_eq!(
            res,
            Expr::Call {
                fun: ident_expr("f"),
                args: vec![*ident_expr("x"), Expr::Literal(Literal::Int(1))]
            }
        )
    }

    #[test]
    fn call_funcref() {
        let res = test_parse!(expr, "(let x = 1 in x) 2");
        assert_eq!(
            res,
            Expr::Call {
                fun: Box::new(Expr::Let {
                    bindings: vec![Binding {
                        ident: Ident::try_from("x").unwrap(),
                        type_: None,
                        body: Expr::Literal(Literal::Int(1))
                    }],
                    body: ident_expr("x")
                }),
                args: vec![Expr::Literal(Literal::Int(2))]
            }
        )
    }

    #[test]
    fn anon_function() {
        let res = test_parse!(expr, "let id = fn x = x in id 1");
        assert_eq!(
            res,
            Expr::Let {
                bindings: vec![Binding {
                    ident: Ident::try_from("id").unwrap(),
                    type_: None,
                    body: Expr::Fun(Box::new(Fun {
                        args: vec![Arg::try_from("x").unwrap()],
                        body: *ident_expr("x")
                    }))
                }],
                body: Box::new(Expr::Call {
                    fun: ident_expr("id"),
                    args: vec![Expr::Literal(Literal::Int(1))],
                })
            }
        );
    }

    mod ascriptions {
        use super::*;

        #[test]
        fn bare_ascription() {
            let res = test_parse!(expr, "1: float");
            assert_eq!(
                res,
                Expr::Ascription {
                    expr: Box::new(Expr::Literal(Literal::Int(1))),
                    type_: Type::Float
                }
            )
        }

        #[test]
        fn fn_body_ascription() {
            let res = test_parse!(expr, "let const_1 = fn x = 1: int in const_1 2");
            assert_eq!(
                res,
                Expr::Let {
                    bindings: vec![Binding {
                        ident: Ident::try_from("const_1").unwrap(),
                        type_: None,
                        body: Expr::Fun(Box::new(Fun {
                            args: vec![Arg::try_from("x").unwrap()],
                            body: Expr::Ascription {
                                expr: Box::new(Expr::Literal(Literal::Int(1))),
                                type_: Type::Int,
                            }
                        }))
                    }],
                    body: Box::new(Expr::Call {
                        fun: ident_expr("const_1"),
                        args: vec![Expr::Literal(Literal::Int(2))]
                    })
                }
            )
        }

        #[test]
        fn let_binding_ascripted() {
            let res = test_parse!(expr, "let x: int = 1 in x");
            assert_eq!(
                res,
                Expr::Let {
                    bindings: vec![Binding {
                        ident: Ident::try_from("x").unwrap(),
                        type_: Some(Type::Int),
                        body: Expr::Literal(Literal::Int(1))
                    }],
                    body: ident_expr("x")
                }
            )
        }
    }
}
