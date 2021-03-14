use std::convert::{TryFrom, TryInto};
use std::path::Path;
use std::result;

use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
pub use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::support::LLVMString;
use inkwell::types::{BasicType, BasicTypeEnum, FunctionType, IntType};
use inkwell::values::{AnyValueEnum, BasicValueEnum, FunctionValue};
use inkwell::IntPredicate;
use thiserror::Error;

use crate::ast::hir::{Binding, Decl, Expr};
use crate::ast::{BinaryOperator, Ident, Literal, Type, UnaryOperator};
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
    env: Env<&'ast Ident<'ast>, AnyValueEnum<'ctx>>,
    function_stack: Vec<FunctionValue<'ctx>>,
    identifier_counter: u32,
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
            function_stack: Default::default(),
            identifier_counter: 0,
        }
    }

    pub fn new_function<'a>(
        &'a mut self,
        name: &str,
        ty: FunctionType<'ctx>,
    ) -> &'a FunctionValue<'ctx> {
        self.function_stack
            .push(self.module.add_function(name, ty, None));
        let basic_block = self.append_basic_block("entry");
        self.builder.position_at_end(basic_block);
        self.function_stack.last().unwrap()
    }

    pub fn finish_function(&mut self, res: &BasicValueEnum<'ctx>) -> FunctionValue<'ctx> {
        self.builder.build_return(Some(res));
        self.function_stack.pop().unwrap()
    }

    pub fn append_basic_block(&self, name: &str) -> BasicBlock<'ctx> {
        self.context
            .append_basic_block(*self.function_stack.last().unwrap(), name)
    }

    pub fn codegen_expr(&mut self, expr: &'ast Expr<'ast, Type>) -> Result<AnyValueEnum<'ctx>> {
        match expr {
            Expr::Ident(id, _) => self
                .env
                .resolve(id)
                .cloned()
                .ok_or_else(|| Error::UndefinedVariable(id.to_owned())),
            Expr::Literal(lit, ty) => {
                let ty = self.codegen_int_type(ty);
                match lit {
                    Literal::Int(i) => Ok(AnyValueEnum::IntValue(ty.const_int(*i, false))),
                    Literal::Bool(b) => Ok(AnyValueEnum::IntValue(
                        ty.const_int(if *b { 1 } else { 0 }, false),
                    )),
                    Literal::String(_) => todo!(),
                }
            }
            Expr::UnaryOp { op, rhs, .. } => {
                let rhs = self.codegen_expr(rhs)?;
                match op {
                    UnaryOperator::Not => unimplemented!(),
                    UnaryOperator::Neg => Ok(AnyValueEnum::IntValue(
                        self.builder.build_int_neg(rhs.into_int_value(), "neg"),
                    )),
                }
            }
            Expr::BinaryOp { lhs, op, rhs, .. } => {
                let lhs = self.codegen_expr(lhs)?;
                let rhs = self.codegen_expr(rhs)?;
                match op {
                    BinaryOperator::Add => Ok(AnyValueEnum::IntValue(self.builder.build_int_add(
                        lhs.into_int_value(),
                        rhs.into_int_value(),
                        "add",
                    ))),
                    BinaryOperator::Sub => Ok(AnyValueEnum::IntValue(self.builder.build_int_sub(
                        lhs.into_int_value(),
                        rhs.into_int_value(),
                        "add",
                    ))),
                    BinaryOperator::Mul => Ok(AnyValueEnum::IntValue(self.builder.build_int_sub(
                        lhs.into_int_value(),
                        rhs.into_int_value(),
                        "add",
                    ))),
                    BinaryOperator::Div => {
                        Ok(AnyValueEnum::IntValue(self.builder.build_int_signed_div(
                            lhs.into_int_value(),
                            rhs.into_int_value(),
                            "add",
                        )))
                    }
                    BinaryOperator::Pow => unimplemented!(),
                    BinaryOperator::Equ => {
                        Ok(AnyValueEnum::IntValue(self.builder.build_int_compare(
                            IntPredicate::EQ,
                            lhs.into_int_value(),
                            rhs.into_int_value(),
                            "eq",
                        )))
                    }
                    BinaryOperator::Neq => todo!(),
                }
            }
            Expr::Let { bindings, body, .. } => {
                self.env.push();
                for Binding { ident, body, .. } in bindings {
                    let val = self.codegen_expr(body)?;
                    self.env.set(ident, val);
                }
                let res = self.codegen_expr(body);
                self.env.pop();
                res
            }
            Expr::If {
                condition,
                then,
                else_,
                type_,
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
                let phi = self.builder.build_phi(self.codegen_type(type_), "join");
                phi.add_incoming(&[
                    (&BasicValueEnum::try_from(then_res).unwrap(), then_block),
                    (&BasicValueEnum::try_from(else_res).unwrap(), else_block),
                ]);
                Ok(phi.as_basic_value().into())
            }
            Expr::Call { fun, args, .. } => {
                if let Expr::Ident(id, _) = &**fun {
                    let function = self
                        .module
                        .get_function(id.into())
                        .or_else(|| self.env.resolve(id)?.clone().try_into().ok())
                        .ok_or_else(|| Error::UndefinedVariable(id.to_owned()))?;
                    let args = args
                        .iter()
                        .map(|arg| Ok(self.codegen_expr(arg)?.try_into().unwrap()))
                        .collect::<Result<Vec<_>>>()?;
                    Ok(self
                        .builder
                        .build_call(function, &args, "call")
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                        .into())
                } else {
                    todo!()
                }
            }
            Expr::Fun { args, body, .. } => {
                let fname = self.fresh_ident("f");
                let cur_block = self.builder.get_insert_block().unwrap();
                let env = self.env.save(); // TODO: closures
                let function = self.codegen_function(&fname, args, body)?;
                self.builder.position_at_end(cur_block);
                self.env.restore(env);
                Ok(function.into())
            }
        }
    }

    pub fn codegen_function(
        &mut self,
        name: &str,
        args: &'ast [(Ident<'ast>, Type)],
        body: &'ast Expr<'ast, Type>,
    ) -> Result<FunctionValue<'ctx>> {
        self.new_function(
            name,
            self.codegen_type(body.type_()).fn_type(
                args.iter()
                    .map(|(_, at)| self.codegen_type(at))
                    .collect::<Vec<_>>()
                    .as_slice(),
                false,
            ),
        );
        self.env.push();
        for (i, (arg, _)) in args.iter().enumerate() {
            self.env.set(
                arg,
                self.cur_function().get_nth_param(i as u32).unwrap().into(),
            );
        }
        let res = self.codegen_expr(body)?.try_into().unwrap();
        self.env.pop();
        Ok(self.finish_function(&res))
    }

    pub fn codegen_decl(&mut self, decl: &'ast Decl<'ast, Type>) -> Result<()> {
        match decl {
            Decl::Fun {
                name, args, body, ..
            } => {
                self.codegen_function(name.into(), args, body)?;
                Ok(())
            }
        }
    }

    pub fn codegen_main(&mut self, expr: &'ast Expr<'ast, Type>) -> Result<()> {
        self.new_function("main", self.context.i64_type().fn_type(&[], false));
        let res = self.codegen_expr(expr)?.try_into().unwrap();
        if *expr.type_() != Type::Int {
            self.builder
                .build_return(Some(&self.context.i64_type().const_int(0, false)));
        } else {
            self.finish_function(&res);
        }
        Ok(())
    }

    fn codegen_type(&self, type_: &'ast Type) -> BasicTypeEnum<'ctx> {
        // TODO
        self.context.i64_type().into()
    }

    fn codegen_int_type(&self, type_: &'ast Type) -> IntType<'ctx> {
        // TODO
        self.context.i64_type()
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

    fn fresh_ident(&mut self, prefix: &str) -> String {
        self.identifier_counter += 1;
        format!("{}{}", prefix, self.identifier_counter)
    }

    fn cur_function(&self) -> &FunctionValue<'ctx> {
        self.function_stack.last().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use inkwell::execution_engine::JitFunction;
    use inkwell::OptimizationLevel;

    use super::*;

    fn jit_eval<T>(expr: &str) -> anyhow::Result<T> {
        let expr = crate::parser::expr(expr).unwrap().1;

        let expr = crate::tc::typecheck_expr(expr).unwrap();

        let context = Context::create();
        let mut codegen = Codegen::new(&context, "test");
        let execution_engine = codegen
            .module
            .create_jit_execution_engine(OptimizationLevel::None)
            .unwrap();

        codegen.codegen_function("test", &[], &expr)?;

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

    #[test]
    fn function_call() {
        let res = jit_eval::<i64>("let id = fn x = x in id 1").unwrap();
        assert_eq!(res, 1);
    }
}
