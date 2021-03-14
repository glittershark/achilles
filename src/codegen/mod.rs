pub mod llvm;

use inkwell::execution_engine::JitFunction;
use inkwell::OptimizationLevel;
pub use llvm::*;

use crate::ast::hir::Expr;
use crate::ast::Type;
use crate::common::Result;

pub fn jit_eval<T>(expr: &Expr<Type>) -> Result<T> {
    let context = Context::create();
    let mut codegen = Codegen::new(&context, "eval");
    let execution_engine = codegen
        .module
        .create_jit_execution_engine(OptimizationLevel::None)
        .map_err(Error::from)?;
    codegen.codegen_function("test", &[], &expr)?;

    unsafe {
        let fun: JitFunction<unsafe extern "C" fn() -> T> =
            execution_engine.get_function("eval").unwrap();
        Ok(fun.call())
    }
}
