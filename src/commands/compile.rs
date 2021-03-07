use std::path::PathBuf;

use clap::Clap;

use crate::common::Result;
use crate::compiler::{self, CompilerOptions};

#[derive(Clap)]
pub struct Compile {
    file: PathBuf,

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
