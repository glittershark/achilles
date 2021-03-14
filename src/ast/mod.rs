pub(crate) mod hir;

use std::borrow::Cow;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt::{self, Display, Formatter};

use itertools::Itertools;

#[derive(Debug, PartialEq, Eq)]
pub struct InvalidIdentifier<'a>(Cow<'a, str>);

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Ident<'a>(pub Cow<'a, str>);

impl<'a> From<&'a Ident<'a>> for &'a str {
    fn from(id: &'a Ident<'a>) -> Self {
        id.0.as_ref()
    }
}

impl<'a> Display for Ident<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'a> Ident<'a> {
    pub fn to_owned(&self) -> Ident<'static> {
        Ident(Cow::Owned(self.0.clone().into_owned()))
    }

    pub fn from_str_unchecked(s: &'a str) -> Self {
        debug_assert!(is_valid_identifier(s));
        Self(Cow::Borrowed(s))
    }

    pub fn from_string_unchecked(s: String) -> Self {
        debug_assert!(is_valid_identifier(&s));
        Self(Cow::Owned(s))
    }
}

pub fn is_valid_identifier<S>(s: &S) -> bool
where
    S: AsRef<str> + ?Sized,
{
    s.as_ref()
        .chars()
        .any(|c| !c.is_alphanumeric() || !"_".contains(c))
}

impl<'a> TryFrom<&'a str> for Ident<'a> {
    type Error = InvalidIdentifier<'a>;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        if is_valid_identifier(s) {
            Ok(Ident(Cow::Borrowed(s)))
        } else {
            Err(InvalidIdentifier(Cow::Borrowed(s)))
        }
    }
}

impl<'a> TryFrom<String> for Ident<'a> {
    type Error = InvalidIdentifier<'static>;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        if is_valid_identifier(&s) {
            Ok(Ident(Cow::Owned(s)))
        } else {
            Err(InvalidIdentifier(Cow::Owned(s)))
        }
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum BinaryOperator {
    /// `+`
    Add,

    /// `-`
    Sub,

    /// `*`
    Mul,

    /// `/`
    Div,

    /// `^`
    Pow,

    /// `==`
    Equ,

    /// `!=`
    Neq,
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum UnaryOperator {
    /// !
    Not,

    /// -
    Neg,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Literal<'a> {
    Int(u64),
    Bool(bool),
    String(Cow<'a, str>),
}

impl<'a> Literal<'a> {
    pub fn to_owned(&self) -> Literal<'static> {
        match self {
            Literal::Int(i) => Literal::Int(*i),
            Literal::Bool(b) => Literal::Bool(*b),
            Literal::String(s) => Literal::String(Cow::Owned(s.clone().into_owned())),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Binding<'a> {
    pub ident: Ident<'a>,
    pub type_: Option<Type<'a>>,
    pub body: Expr<'a>,
}

impl<'a> Binding<'a> {
    fn to_owned(&self) -> Binding<'static> {
        Binding {
            ident: self.ident.to_owned(),
            type_: self.type_.as_ref().map(|t| t.to_owned()),
            body: self.body.to_owned(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr<'a> {
    Ident(Ident<'a>),

    Literal(Literal<'a>),

    UnaryOp {
        op: UnaryOperator,
        rhs: Box<Expr<'a>>,
    },

    BinaryOp {
        lhs: Box<Expr<'a>>,
        op: BinaryOperator,
        rhs: Box<Expr<'a>>,
    },

    Let {
        bindings: Vec<Binding<'a>>,
        body: Box<Expr<'a>>,
    },

    If {
        condition: Box<Expr<'a>>,
        then: Box<Expr<'a>>,
        else_: Box<Expr<'a>>,
    },

    Fun(Box<Fun<'a>>),

    Call {
        fun: Box<Expr<'a>>,
        args: Vec<Expr<'a>>,
    },

    Ascription {
        expr: Box<Expr<'a>>,
        type_: Type<'a>,
    },
}

impl<'a> Expr<'a> {
    pub fn to_owned(&self) -> Expr<'static> {
        match self {
            Expr::Ident(ref id) => Expr::Ident(id.to_owned()),
            Expr::Literal(ref lit) => Expr::Literal(lit.to_owned()),
            Expr::UnaryOp { op, rhs } => Expr::UnaryOp {
                op: *op,
                rhs: Box::new((**rhs).to_owned()),
            },
            Expr::BinaryOp { lhs, op, rhs } => Expr::BinaryOp {
                lhs: Box::new((**lhs).to_owned()),
                op: *op,
                rhs: Box::new((**rhs).to_owned()),
            },
            Expr::Let { bindings, body } => Expr::Let {
                bindings: bindings.iter().map(|binding| binding.to_owned()).collect(),
                body: Box::new((**body).to_owned()),
            },
            Expr::If {
                condition,
                then,
                else_,
            } => Expr::If {
                condition: Box::new((**condition).to_owned()),
                then: Box::new((**then).to_owned()),
                else_: Box::new((**else_).to_owned()),
            },
            Expr::Fun(fun) => Expr::Fun(Box::new((**fun).to_owned())),
            Expr::Call { fun, args } => Expr::Call {
                fun: Box::new((**fun).to_owned()),
                args: args.iter().map(|arg| arg.to_owned()).collect(),
            },
            Expr::Ascription { expr, type_ } => Expr::Ascription {
                expr: Box::new((**expr).to_owned()),
                type_: type_.to_owned(),
            },
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Arg<'a> {
    pub ident: Ident<'a>,
    pub type_: Option<Type<'a>>,
}

impl<'a> Arg<'a> {
    pub fn to_owned(&self) -> Arg<'static> {
        Arg {
            ident: self.ident.to_owned(),
            type_: self.type_.as_ref().map(Type::to_owned),
        }
    }
}

impl<'a> TryFrom<&'a str> for Arg<'a> {
    type Error = <Ident<'a> as TryFrom<&'a str>>::Error;

    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        Ok(Arg {
            ident: Ident::try_from(value)?,
            type_: None,
        })
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Fun<'a> {
    pub args: Vec<Arg<'a>>,
    pub body: Expr<'a>,
}

impl<'a> Fun<'a> {
    pub fn to_owned(&self) -> Fun<'static> {
        Fun {
            args: self.args.iter().map(|arg| arg.to_owned()).collect(),
            body: self.body.to_owned(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Decl<'a> {
    Fun { name: Ident<'a>, body: Fun<'a> },
    Ascription { name: Ident<'a>, type_: Type<'a> },
}

////

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FunctionType<'a> {
    pub args: Vec<Type<'a>>,
    pub ret: Box<Type<'a>>,
}

impl<'a> FunctionType<'a> {
    pub fn to_owned(&self) -> FunctionType<'static> {
        FunctionType {
            args: self.args.iter().map(|a| a.to_owned()).collect(),
            ret: Box::new((*self.ret).to_owned()),
        }
    }
}

impl<'a> Display for FunctionType<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "fn {} -> {}", self.args.iter().join(", "), self.ret)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Type<'a> {
    Int,
    Float,
    Bool,
    CString,
    Var(Ident<'a>),
    Function(FunctionType<'a>),
}

impl<'a> Type<'a> {
    pub fn to_owned(&self) -> Type<'static> {
        match self {
            Type::Int => Type::Int,
            Type::Float => Type::Float,
            Type::Bool => Type::Bool,
            Type::CString => Type::CString,
            Type::Var(v) => Type::Var(v.to_owned()),
            Type::Function(f) => Type::Function(f.to_owned()),
        }
    }

    pub fn alpha_equiv(&self, other: &Self) -> bool {
        fn do_alpha_equiv<'a>(
            substs: &mut HashMap<&'a Ident<'a>, &'a Ident<'a>>,
            lhs: &'a Type,
            rhs: &'a Type,
        ) -> bool {
            match (lhs, rhs) {
                (Type::Var(v1), Type::Var(v2)) => substs.entry(v1).or_insert(v2) == &v2,
                (
                    Type::Function(FunctionType {
                        args: args1,
                        ret: ret1,
                    }),
                    Type::Function(FunctionType {
                        args: args2,
                        ret: ret2,
                    }),
                ) => {
                    args1.len() == args2.len()
                        && args1
                            .iter()
                            .zip(args2)
                            .all(|(a1, a2)| do_alpha_equiv(substs, a1, a2))
                        && do_alpha_equiv(substs, ret1, ret2)
                }
                _ => lhs == rhs,
            }
        }

        let mut substs = HashMap::new();
        do_alpha_equiv(&mut substs, self, other)
    }
}

impl<'a> Display for Type<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => f.write_str("int"),
            Type::Float => f.write_str("float"),
            Type::Bool => f.write_str("bool"),
            Type::CString => f.write_str("cstring"),
            Type::Var(v) => v.fmt(f),
            Type::Function(ft) => ft.fmt(f),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn type_var(n: &str) -> Type<'static> {
        Type::Var(Ident::try_from(n.to_owned()).unwrap())
    }

    mod alpha_equiv {
        use super::*;

        #[test]
        fn trivial() {
            assert!(Type::Int.alpha_equiv(&Type::Int));
            assert!(!Type::Int.alpha_equiv(&Type::Bool));
        }

        #[test]
        fn simple_type_var() {
            assert!(type_var("a").alpha_equiv(&type_var("b")));
        }

        #[test]
        fn function_with_type_vars_equiv() {
            assert!(Type::Function(FunctionType {
                args: vec![type_var("a")],
                ret: Box::new(type_var("b")),
            })
            .alpha_equiv(&Type::Function(FunctionType {
                args: vec![type_var("b")],
                ret: Box::new(type_var("a")),
            })))
        }

        #[test]
        fn function_with_type_vars_non_equiv() {
            assert!(!Type::Function(FunctionType {
                args: vec![type_var("a")],
                ret: Box::new(type_var("a")),
            })
            .alpha_equiv(&Type::Function(FunctionType {
                args: vec![type_var("b")],
                ret: Box::new(type_var("a")),
            })))
        }
    }
}
