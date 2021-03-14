use clap::Clap;
use std::path::PathBuf;

use crate::ast::Type;
use crate::{parser, tc, Result};

/// Typecheck a file or expression
#[derive(Clap)]
pub struct Check {
    /// File to check
    path: Option<PathBuf>,

    /// Expression to check
    #[clap(long, short = 'e')]
    expr: Option<String>,
}

fn run_expr(expr: String) -> Result<Type<'static>> {
    let (_, parsed) = parser::expr(&expr)?;
    let hir_expr = tc::typecheck_expr(parsed)?;
    Ok(hir_expr.type_().to_owned())
}

fn run_path(path: PathBuf) -> Result<Type<'static>> {
    todo!()
}

impl Check {
    pub fn run(self) -> Result<()> {
        let type_ = match (self.path, self.expr) {
            (None, None) => Err("Must specify either a file or expression to check".into()),
            (Some(_), Some(_)) => Err("Cannot specify both a file and expression to check".into()),
            (None, Some(expr)) => run_expr(expr),
            (Some(path), None) => run_path(path),
        }?;
        println!("type: {}", type_);
        Ok(())
    }
}
