use nom::character::complete::{digit1, multispace0, multispace1};
use nom::error::{ErrorKind, ParseError};
use nom::{
    alt, char, complete, delimited, do_parse, flat_map, many0, map, named, parse_to,
    separated_list0, separated_list1, tag, tuple,
};
use pratt::{Affix, Associativity, PrattParser, Precedence};

use crate::ast::{BinaryOperator, Decl, Expr, Fun, Ident, Literal, UnaryOperator};

pub type Error = nom::Err<nom::error::Error<String>>;

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

fn ident<'a, E>(i: &'a str) -> nom::IResult<&'a str, Ident, E>
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
            Ok((&i[idx..], Ident::from_str_unchecked(&i[..idx])))
        } else {
            Err(nom::Err::Error(E::from_error_kind(i, ErrorKind::Satisfy)))
        }
    } else {
        Err(nom::Err::Error(E::from_error_kind(i, ErrorKind::Eof)))
    }
}

named!(int(&str) -> Literal, map!(flat_map!(digit1, parse_to!(u64)), Literal::Int));

named!(literal(&str) -> Expr, map!(alt!(int), Expr::Literal));

named!(binding(&str) -> (Ident, Expr), do_parse!(
    multispace0
        >> ident: ident
        >> multispace0
        >> char!('=')
        >> multispace0
        >> expr: expr
        >> (ident, expr)
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

named!(simple_expr(&str) -> Expr, alt!(
    let_ |
    if_ |
    literal |
    ident_expr
));

named!(pub expr(&str) -> Expr, alt!(
    map!(token_tree, |tt| {
        ExprParser.parse(&mut tt.into_iter()).unwrap()
    }) |
    simple_expr));

//////

named!(fun(&str) -> Fun, do_parse!(
    tag!("fn")
        >> multispace0
        >> name: ident
        >> multispace1
        >> args: separated_list0!(multispace1, ident)
        >> multispace0
        >> char!('=')
        >> multispace0
        >> body: expr
        >> (Fun {
            name,
            args,
            body
        })
));

named!(pub decl(&str) -> Decl, alt!(
    fun => { |f| Decl::Fun(f) }
));

named!(pub toplevel(&str) -> Vec<Decl>, separated_list0!(multispace1, decl));

#[cfg(test)]
mod tests {
    use std::convert::{TryFrom, TryInto};

    use super::*;
    use BinaryOperator::*;
    use Expr::{BinaryOp, If, Let, UnaryOp};
    use UnaryOperator::*;

    fn ident_expr(s: &str) -> Box<Expr> {
        Box::new(Expr::Ident(Ident::try_from(s).unwrap()))
    }

    macro_rules! test_parse {
        ($parser: ident, $src: expr) => {{
            let (rem, res) = $parser($src).unwrap();
            assert!(
                rem.is_empty(),
                "non-empty remainder: \"{}\", parsed: {:?}",
                rem,
                res
            );
            res
        }};
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
    fn let_complex() {
        let res = test_parse!(expr, "let x = 1; y = x * 7 in (x + y) * 4");
        assert_eq!(
            res,
            Let {
                bindings: vec![
                    (
                        Ident::try_from("x").unwrap(),
                        Expr::Literal(Literal::Int(1))
                    ),
                    (
                        Ident::try_from("y").unwrap(),
                        Expr::BinaryOp {
                            lhs: ident_expr("x"),
                            op: Mul,
                            rhs: Box::new(Expr::Literal(Literal::Int(7)))
                        }
                    )
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
    fn fn_decl() {
        let res = test_parse!(decl, "fn id x = x");
        assert_eq!(
            res,
            Decl::Fun(Fun {
                name: "id".try_into().unwrap(),
                args: vec!["x".try_into().unwrap()],
                body: *ident_expr("x"),
            })
        )
    }
}
