use std::borrow::Cow;
use std::convert::TryFrom;
use std::fmt::{self, Display};
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::rc::Rc;
use std::result;

use derive_more::{Deref, From, TryInto};

use super::{Error, Result};
use crate::ast::hir::Expr;
use crate::ast::{FunctionType, Ident, Type};

#[derive(Debug, Clone)]
pub struct Function<'a> {
    pub type_: FunctionType<'a>,
    pub args: Vec<Ident<'a>>,
    pub body: Expr<'a, Type<'a>>,
}

#[derive(From, TryInto)]
#[try_into(owned, ref)]
pub enum Val<'a> {
    Int(i64),
    Float(f64),
    Bool(bool),
    String(Cow<'a, str>),
    Function(Function<'a>),
}

impl<'a> TryFrom<Val<'a>> for String {
    type Error = ();

    fn try_from(value: Val<'a>) -> result::Result<Self, Self::Error> {
        match value {
            Val::String(s) => Ok(s.into_owned()),
            _ => Err(()),
        }
    }
}

impl<'a> fmt::Debug for Val<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Val::Int(x) => f.debug_tuple("Int").field(x).finish(),
            Val::Float(x) => f.debug_tuple("Float").field(x).finish(),
            Val::Bool(x) => f.debug_tuple("Bool").field(x).finish(),
            Val::String(s) => f.debug_tuple("String").field(s).finish(),
            Val::Function(Function { type_, .. }) => {
                f.debug_struct("Function").field("type_", type_).finish()
            }
        }
    }
}

impl<'a> PartialEq for Val<'a> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Val::Int(x), Val::Int(y)) => x == y,
            (Val::Float(x), Val::Float(y)) => x == y,
            (Val::Bool(x), Val::Bool(y)) => x == y,
            (Val::Function(_), Val::Function(_)) => false,
            (_, _) => false,
        }
    }
}

impl<'a> From<u64> for Val<'a> {
    fn from(i: u64) -> Self {
        Self::from(i as i64)
    }
}

impl<'a> Display for Val<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Val::Int(x) => x.fmt(f),
            Val::Float(x) => x.fmt(f),
            Val::Bool(x) => x.fmt(f),
            Val::String(s) => write!(f, "{:?}", s),
            Val::Function(Function { type_, .. }) => write!(f, "<{}>", type_),
        }
    }
}

impl<'a> Val<'a> {
    pub fn type_(&self) -> Type {
        match self {
            Val::Int(_) => Type::Int,
            Val::Float(_) => Type::Float,
            Val::Bool(_) => Type::Bool,
            Val::String(_) => Type::CString,
            Val::Function(Function { type_, .. }) => Type::Function(type_.clone()),
        }
    }

    pub fn as_type<'b, T>(&'b self) -> Result<&'b T>
    where
        T: TypeOf + 'b + Clone,
        &'b T: TryFrom<&'b Self>,
    {
        <&T>::try_from(self).map_err(|_| Error::InvalidType {
            actual: self.type_().to_owned(),
            expected: <T as TypeOf>::type_of(),
        })
    }

    pub fn as_function<'b>(&'b self, function_type: FunctionType) -> Result<&'b Function<'a>> {
        match self {
            Val::Function(f) if f.type_ == function_type => Ok(&f),
            _ => Err(Error::InvalidType {
                actual: self.type_().to_owned(),
                expected: Type::Function(function_type.to_owned()),
            }),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Deref)]
pub struct Value<'a>(Rc<Val<'a>>);

impl<'a> Display for Value<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a, T> From<T> for Value<'a>
where
    Val<'a>: From<T>,
{
    fn from(x: T) -> Self {
        Self(Rc::new(x.into()))
    }
}

impl<'a> Neg for Value<'a> {
    type Output = Result<Value<'a>>;

    fn neg(self) -> Self::Output {
        Ok((-self.as_type::<i64>()?).into())
    }
}

impl<'a> Add for Value<'a> {
    type Output = Result<Value<'a>>;

    fn add(self, rhs: Self) -> Self::Output {
        Ok((self.as_type::<i64>()? + rhs.as_type::<i64>()?).into())
    }
}

impl<'a> Sub for Value<'a> {
    type Output = Result<Value<'a>>;

    fn sub(self, rhs: Self) -> Self::Output {
        Ok((self.as_type::<i64>()? - rhs.as_type::<i64>()?).into())
    }
}

impl<'a> Mul for Value<'a> {
    type Output = Result<Value<'a>>;

    fn mul(self, rhs: Self) -> Self::Output {
        Ok((self.as_type::<i64>()? * rhs.as_type::<i64>()?).into())
    }
}

impl<'a> Div for Value<'a> {
    type Output = Result<Value<'a>>;

    fn div(self, rhs: Self) -> Self::Output {
        Ok((self.as_type::<f64>()? / rhs.as_type::<f64>()?).into())
    }
}

pub trait TypeOf {
    fn type_of() -> Type<'static>;
}

impl TypeOf for i64 {
    fn type_of() -> Type<'static> {
        Type::Int
    }
}

impl TypeOf for bool {
    fn type_of() -> Type<'static> {
        Type::Bool
    }
}

impl TypeOf for f64 {
    fn type_of() -> Type<'static> {
        Type::Float
    }
}

impl TypeOf for String {
    fn type_of() -> Type<'static> {
        Type::CString
    }
}
