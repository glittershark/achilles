use clap::Clap;

use crate::codegen;
use crate::interpreter;
use crate::parser;
use crate::Result;

/// Evaluate an expression and print its result
#[derive(Clap)]
pub struct Eval {
    /// JIT-compile with LLVM instead of interpreting
    #[clap(long)]
    jit: bool,

    /// Expression to evaluate
    expr: String,
}

impl Eval {
    pub fn run(self) -> Result<()> {
        let (_, parsed) = parser::expr(&self.expr)?;
        let result = if self.jit {
            codegen::jit_eval::<i64>(&parsed)?.into()
        } else {
            interpreter::eval(&parsed)?
        };
        println!("{}", result);
        Ok(())
    }
}
