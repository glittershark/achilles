use std::result;

use thiserror::Error;

use crate::ast::{Ident, Type};

#[derive(Debug, PartialEq, Eq, Error)]
pub enum Error {
    #[error("Undefined variable {0}")]
    UndefinedVariable(Ident<'static>),

    #[error("Unexpected type {actual}, expected type {expected}")]
    InvalidType {
        actual: Type<'static>,
        expected: Type<'static>,
    },
}

pub type Result<T> = result::Result<T, Error>;
