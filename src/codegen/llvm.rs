use std::path::Path;
use std::result;

use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
pub use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::support::LLVMString;
use inkwell::types::FunctionType;
use inkwell::values::{BasicValueEnum, FunctionValue};
use inkwell::IntPredicate;
use thiserror::Error;

use crate::ast::{BinaryOperator, Decl, Expr, Fun, Ident, Literal, UnaryOperator};
use crate::common::env::Env;

#[derive(Debug, PartialEq, Eq, Error)]
pub enum Error {
    #[error("Undefined variable {0}")]
    UndefinedVariable(Ident<'static>),

    #[error("LLVM Error: {0}")]
    LLVMError(String),
}

impl From<LLVMString> for Error {
    fn from(s: LLVMString) -> Self {
        Self::LLVMError(s.to_string())
    }
}

pub type Result<T> = result::Result<T, Error>;

pub struct Codegen<'ctx, 'ast> {
    context: &'ctx Context,
    pub module: Module<'ctx>,
    builder: Builder<'ctx>,
    env: Env<'ast, BasicValueEnum<'ctx>>,
    function: Option<FunctionValue<'ctx>>,
}

impl<'ctx, 'ast> Codegen<'ctx, 'ast> {
    pub fn new(context: &'ctx Context, module_name: &str) -> Self {
        let module = context.create_module(module_name);
        let builder = context.create_builder();
        Self {
            context,
            module,
            builder,
            env: Default::default(),
            function: None,
        }
    }

    pub fn new_function<'a>(
        &'a mut self,
        name: &str,
        ty: FunctionType<'ctx>,
    ) -> &'a FunctionValue<'ctx> {
        self.function = Some(self.module.add_function(name, ty, None));
        let basic_block = self.append_basic_block("entry");
        self.builder.position_at_end(basic_block);
        self.function.as_ref().unwrap()
    }

    pub fn finish_function(&self, res: &BasicValueEnum<'ctx>) {
        self.builder.build_return(Some(res));
    }

    pub fn append_basic_block(&self, name: &str) -> BasicBlock<'ctx> {
        self.context
            .append_basic_block(self.function.unwrap(), name)
    }

    pub fn codegen_expr(&mut self, expr: &'ast Expr<'ast>) -> Result<BasicValueEnum<'ctx>> {
        match expr {
            Expr::Ident(id) => self
                .env
                .resolve(id)
                .cloned()
                .ok_or_else(|| Error::UndefinedVariable(id.to_owned())),
            Expr::Literal(Literal::Int(i)) => {
                let ty = self.context.i64_type();
                Ok(BasicValueEnum::IntValue(ty.const_int(*i, false)))
            }
            Expr::UnaryOp { op, rhs } => {
                let rhs = self.codegen_expr(rhs)?;
                match op {
                    UnaryOperator::Not => unimplemented!(),
                    UnaryOperator::Neg => Ok(BasicValueEnum::IntValue(
                        self.builder.build_int_neg(rhs.into_int_value(), "neg"),
                    )),
                }
            }
            Expr::BinaryOp { lhs, op, rhs } => {
                let lhs = self.codegen_expr(lhs)?;
                let rhs = self.codegen_expr(rhs)?;
                match op {
                    BinaryOperator::Add => {
                        Ok(BasicValueEnum::IntValue(self.builder.build_int_add(
                            lhs.into_int_value(),
                            rhs.into_int_value(),
                            "add",
                        )))
                    }
                    BinaryOperator::Sub => {
                        Ok(BasicValueEnum::IntValue(self.builder.build_int_sub(
                            lhs.into_int_value(),
                            rhs.into_int_value(),
                            "add",
                        )))
                    }
                    BinaryOperator::Mul => {
                        Ok(BasicValueEnum::IntValue(self.builder.build_int_sub(
                            lhs.into_int_value(),
                            rhs.into_int_value(),
                            "add",
                        )))
                    }
                    BinaryOperator::Div => {
                        Ok(BasicValueEnum::IntValue(self.builder.build_int_signed_div(
                            lhs.into_int_value(),
                            rhs.into_int_value(),
                            "add",
                        )))
                    }
                    BinaryOperator::Pow => unimplemented!(),
                    BinaryOperator::Equ => {
                        Ok(BasicValueEnum::IntValue(self.builder.build_int_compare(
                            IntPredicate::EQ,
                            lhs.into_int_value(),
                            rhs.into_int_value(),
                            "eq",
                        )))
                    }
                    BinaryOperator::Neq => todo!(),
                }
            }
            Expr::Let { bindings, body } => {
                self.env.push();
                for (id, val) in bindings {
                    let val = self.codegen_expr(val)?;
                    self.env.set(id, val);
                }
                let res = self.codegen_expr(body);
                self.env.pop();
                res
            }
            Expr::If {
                condition,
                then,
                else_,
            } => {
                let then_block = self.append_basic_block("then");
                let else_block = self.append_basic_block("else");
                let join_block = self.append_basic_block("join");
                let condition = self.codegen_expr(condition)?;
                self.builder.build_conditional_branch(
                    condition.into_int_value(),
                    then_block,
                    else_block,
                );
                self.builder.position_at_end(then_block);
                let then_res = self.codegen_expr(then)?;
                self.builder.build_unconditional_branch(join_block);

                self.builder.position_at_end(else_block);
                let else_res = self.codegen_expr(else_)?;
                self.builder.build_unconditional_branch(join_block);

                self.builder.position_at_end(join_block);
                let phi = self.builder.build_phi(self.context.i64_type(), "join");
                phi.add_incoming(&[(&then_res, then_block), (&else_res, else_block)]);
                Ok(phi.as_basic_value())
            }
        }
    }

    pub fn codegen_decl(&mut self, decl: &'ast Decl<'ast>) -> Result<()> {
        match decl {
            Decl::Fun(Fun { name, args, body }) => {
                let i64_type = self.context.i64_type();
                self.new_function(
                    name.into(),
                    i64_type.fn_type(
                        args.iter()
                            .map(|_| i64_type.into())
                            .collect::<Vec<_>>()
                            .as_slice(),
                        false,
                    ),
                );
                self.env.push();
                for (i, arg) in args.iter().enumerate() {
                    self.env
                        .set(arg, self.function.unwrap().get_nth_param(i as u32).unwrap());
                }
                let res = self.codegen_expr(body)?;
                self.env.pop();
                self.finish_function(&res);
                Ok(())
            }
        }
    }

    pub fn codegen_main(&mut self, expr: &'ast Expr<'ast>) -> Result<()> {
        self.new_function("main", self.context.i64_type().fn_type(&[], false));
        let res = self.codegen_expr(expr)?;
        self.finish_function(&res);
        Ok(())
    }

    pub fn print_to_file<P>(&self, path: P) -> Result<()>
    where
        P: AsRef<Path>,
    {
        Ok(self.module.print_to_file(path)?)
    }

    pub fn binary_to_file<P>(&self, path: P) -> Result<()>
    where
        P: AsRef<Path>,
    {
        if self.module.write_bitcode_to_path(path.as_ref()) {
            Ok(())
        } else {
            Err(Error::LLVMError(
                "Error writing bitcode to output path".to_owned(),
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use inkwell::execution_engine::JitFunction;
    use inkwell::OptimizationLevel;

    use super::*;

    fn jit_eval<T>(expr: &str) -> anyhow::Result<T> {
        let expr = crate::parser::expr(expr).unwrap().1;

        let context = Context::create();
        let mut codegen = Codegen::new(&context, "test");
        let execution_engine = codegen
            .module
            .create_jit_execution_engine(OptimizationLevel::None)
            .unwrap();

        codegen.new_function("test", context.i64_type().fn_type(&[], false));
        let res = codegen.codegen_expr(&expr)?;
        codegen.finish_function(&res);

        unsafe {
            let fun: JitFunction<unsafe extern "C" fn() -> T> =
                execution_engine.get_function("test")?;
            Ok(fun.call())
        }
    }

    #[test]
    fn add_literals() {
        assert_eq!(jit_eval::<i64>("1 + 2").unwrap(), 3);
    }

    #[test]
    fn variable_shadowing() {
        assert_eq!(
            jit_eval::<i64>("let x = 1 in (let x = 2 in x) + x").unwrap(),
            3
        );
    }

    #[test]
    fn eq() {
        assert_eq!(
            jit_eval::<i64>("let x = 1 in if x == 1 then 2 else 4").unwrap(),
            2
        );
    }
}
