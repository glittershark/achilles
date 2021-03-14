use clap::Clap;

pub mod ast;
pub mod codegen;
pub(crate) mod commands;
pub(crate) mod common;
pub mod compiler;
pub mod interpreter;
#[macro_use]
pub mod parser;
pub mod tc;

pub use common::{Error, Result};

#[derive(Clap)]
struct Opts {
    #[clap(subcommand)]
    subcommand: Command,
}

#[derive(Clap)]
enum Command {
    Eval(commands::Eval),
    Compile(commands::Compile),
    Check(commands::Check),
}

fn main() -> anyhow::Result<()> {
    let opts = Opts::parse();
    match opts.subcommand {
        Command::Eval(eval) => Ok(eval.run()?),
        Command::Compile(compile) => Ok(compile.run()?),
        Command::Check(check) => Ok(check.run()?),
    }
}
