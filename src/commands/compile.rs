use std::path::PathBuf;

use clap::Clap;

use crate::common::Result;
use crate::compiler::{self, CompilerOptions};

/// Compile a source file
#[derive(Clap)]
pub struct Compile {
    /// File to compile
    file: PathBuf,

    /// Output file
    #[clap(short = 'o')]
    out_file: PathBuf,

    #[clap(flatten)]
    options: CompilerOptions,
}

impl Compile {
    pub fn run(self) -> Result<()> {
        eprintln!(
            ">>> {} -> {}",
            &self.file.to_string_lossy(),
            self.out_file.to_string_lossy()
        );
        compiler::compile_file(&self.file, &self.out_file, &self.options)
    }
}
