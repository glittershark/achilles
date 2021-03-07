use std::borrow::Cow;
use std::convert::TryFrom;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, PartialEq, Eq)]
pub struct InvalidIdentifier<'a>(Cow<'a, str>);

#[derive(Debug, PartialEq, Eq, Hash)]
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

#[derive(Debug, PartialEq, Eq)]
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

#[derive(Debug, PartialEq, Eq)]
pub enum UnaryOperator {
    /// !
    Not,

    /// -
    Neg,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Literal {
    Int(u64),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Expr<'a> {
    Ident(Ident<'a>),

    Literal(Literal),

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
        bindings: Vec<(Ident<'a>, Expr<'a>)>,
        body: Box<Expr<'a>>,
    },

    If {
        condition: Box<Expr<'a>>,
        then: Box<Expr<'a>>,
        else_: Box<Expr<'a>>,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub struct Fun<'a> {
    pub name: Ident<'a>,
    pub args: Vec<Ident<'a>>,
    pub body: Expr<'a>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Decl<'a> {
    Fun(Fun<'a>),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Type {
    Int,
    Float,
    Bool,
}

impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int => f.write_str("int"),
            Self::Float => f.write_str("float"),
            Self::Bool => f.write_str("bool"),
        }
    }
}
