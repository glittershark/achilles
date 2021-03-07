use std::{io, result};

use thiserror::Error;

use crate::{codegen, interpreter, parser};

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    IOError(#[from] io::Error),

    #[error("Error parsing input: {0}")]
    ParseError(#[from] parser::Error),

    #[error("Error evaluating expression: {0}")]
    EvalError(#[from] interpreter::Error),

    #[error("Compile error: {0}")]
    CodegenError(#[from] codegen::Error),

    #[error("{0}")]
    Message(String),
}

impl From<String> for Error {
    fn from(s: String) -> Self {
        Self::Message(s)
    }
}

impl<'a> From<nom::Err<nom::error::Error<&'a str>>> for Error {
    fn from(e: nom::Err<nom::error::Error<&'a str>>) -> Self {
        use nom::error::Error as NomError;
        use nom::Err::*;

        Self::ParseError(match e {
            Incomplete(i) => Incomplete(i),
            Error(NomError { input, code }) => Error(NomError {
                input: input.to_owned(),
                code,
            }),
            Failure(NomError { input, code }) => Failure(NomError {
                input: input.to_owned(),
                code,
            }),
        })
    }
}

pub type Result<T> = result::Result<T, Error>;
