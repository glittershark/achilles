pub mod llvm;

use inkwell::execution_engine::JitFunction;
use inkwell::OptimizationLevel;
pub use llvm::*;

use crate::ast::Expr;
use crate::common::Result;

pub fn jit_eval<T>(expr: &Expr) -> Result<T> {
    let context = Context::create();
    let mut codegen = Codegen::new(&context, "eval");
    let execution_engine = codegen
        .module
        .create_jit_execution_engine(OptimizationLevel::None)
        .map_err(Error::from)?;
    codegen.new_function("eval", context.i64_type().fn_type(&[], false));
    let res = codegen.codegen_expr(&expr)?;
    codegen.finish_function(&res);

    unsafe {
        let fun: JitFunction<unsafe extern "C" fn() -> T> =
            execution_engine.get_function("eval").unwrap();
        Ok(fun.call())
    }
}
