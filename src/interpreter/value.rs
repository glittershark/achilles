use std::convert::TryFrom;
use std::fmt::{self, Display};
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::rc::Rc;

use derive_more::{Deref, From, TryInto};

use super::{Error, Result};
use crate::ast::Type;

#[derive(Debug, PartialEq, From, TryInto)]
#[try_into(owned, ref)]
pub enum Val {
    Int(i64),
    Float(f64),
    Bool(bool),
}

impl From<u64> for Val {
    fn from(i: u64) -> Self {
        Self::from(i as i64)
    }
}

impl Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Val::Int(x) => x.fmt(f),
            Val::Float(x) => x.fmt(f),
            Val::Bool(x) => x.fmt(f),
        }
    }
}

impl Val {
    pub fn type_(&self) -> Type {
        match self {
            Val::Int(_) => Type::Int,
            Val::Float(_) => Type::Float,
            Val::Bool(_) => Type::Bool,
        }
    }

    pub fn into_type<'a, T>(&'a self) -> Result<&'a T>
    where
        T: TypeOf + 'a + Clone,
        &'a T: TryFrom<&'a Self>,
    {
        <&T>::try_from(self).map_err(|_| Error::InvalidType {
            actual: self.type_(),
            expected: <T as TypeOf>::type_of(),
        })
    }
}

#[derive(Debug, PartialEq, Clone, Deref)]
pub struct Value(Rc<Val>);

impl Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T> From<T> for Value
where
    Val: From<T>,
{
    fn from(x: T) -> Self {
        Self(Rc::new(x.into()))
    }
}

impl Neg for Value {
    type Output = Result<Value>;

    fn neg(self) -> Self::Output {
        Ok((-self.into_type::<i64>()?).into())
    }
}

impl Add for Value {
    type Output = Result<Value>;

    fn add(self, rhs: Self) -> Self::Output {
        Ok((self.into_type::<i64>()? + rhs.into_type::<i64>()?).into())
    }
}

impl Sub for Value {
    type Output = Result<Value>;

    fn sub(self, rhs: Self) -> Self::Output {
        Ok((self.into_type::<i64>()? - rhs.into_type::<i64>()?).into())
    }
}

impl Mul for Value {
    type Output = Result<Value>;

    fn mul(self, rhs: Self) -> Self::Output {
        Ok((self.into_type::<i64>()? * rhs.into_type::<i64>()?).into())
    }
}

impl Div for Value {
    type Output = Result<Value>;

    fn div(self, rhs: Self) -> Self::Output {
        Ok((self.into_type::<f64>()? / rhs.into_type::<f64>()?).into())
    }
}

pub trait TypeOf {
    fn type_of() -> Type;
}

impl TypeOf for i64 {
    fn type_of() -> Type {
        Type::Int
    }
}

impl TypeOf for bool {
    fn type_of() -> Type {
        Type::Bool
    }
}

impl TypeOf for f64 {
    fn type_of() -> Type {
        Type::Float
    }
}
