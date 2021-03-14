use std::fmt::{self, Display};
use std::path::Path;
use std::str::FromStr;
use std::{fs, result};

use clap::Clap;
use test_strategy::Arbitrary;

use crate::codegen::{self, Codegen};
use crate::common::Result;
use crate::{parser, tc};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Arbitrary)]
pub enum OutputFormat {
    LLVM,
    Bitcode,
}

impl Default for OutputFormat {
    fn default() -> Self {
        Self::Bitcode
    }
}

impl FromStr for OutputFormat {
    type Err = String;

    fn from_str(s: &str) -> result::Result<Self, Self::Err> {
        match s {
            "llvm" => Ok(Self::LLVM),
            "binary" => Ok(Self::Bitcode),
            _ => Err(format!(
                "Invalid output format {}, expected one of {{llvm, binary}}",
                s
            )),
        }
    }
}

impl Display for OutputFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OutputFormat::LLVM => f.write_str("llvm"),
            OutputFormat::Bitcode => f.write_str("binary"),
        }
    }
}

#[derive(Clap, Debug, PartialEq, Eq, Default)]
pub struct CompilerOptions {
    #[clap(long, short = 'f', default_value)]
    format: OutputFormat,
}

pub fn compile_file(input: &Path, output: &Path, options: &CompilerOptions) -> Result<()> {
    let src = fs::read_to_string(input)?;
    let (_, decls) = parser::toplevel(&src)?; // TODO: statements
    let decls = tc::typecheck_toplevel(decls)?;

    let context = codegen::Context::create();
    let mut codegen = Codegen::new(
        &context,
        &input
            .file_stem()
            .map_or("UNKNOWN".to_owned(), |s| s.to_string_lossy().into_owned()),
    );
    for decl in &decls {
        codegen.codegen_decl(decl)?;
    }
    match options.format {
        OutputFormat::LLVM => codegen.print_to_file(output)?,
        OutputFormat::Bitcode => codegen.binary_to_file(output)?,
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_strategy::proptest;

    #[proptest]
    fn output_format_display_from_str_round_trip(of: OutputFormat) {
        assert_eq!(OutputFormat::from_str(&of.to_string()), Ok(of));
    }
}
