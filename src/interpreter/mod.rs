mod error;
mod value;

pub use self::error::{Error, Result};
pub use self::value::{Function, Value};
use crate::ast::hir::{Binding, Expr};
use crate::ast::{BinaryOperator, FunctionType, Ident, Literal, Type, UnaryOperator};
use crate::common::env::Env;

#[derive(Debug, Default)]
pub struct Interpreter<'a> {
    env: Env<&'a Ident<'a>, Value<'a>>,
}

impl<'a> Interpreter<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    fn resolve(&self, var: &'a Ident<'a>) -> Result<Value<'a>> {
        self.env
            .resolve(var)
            .cloned()
            .ok_or_else(|| Error::UndefinedVariable(var.to_owned()))
    }

    pub fn eval(&mut self, expr: &'a Expr<'a, Type>) -> Result<Value<'a>> {
        let res = match expr {
            Expr::Ident(id, _) => self.resolve(id),
            Expr::Literal(Literal::Int(i), _) => Ok((*i).into()),
            Expr::Literal(Literal::Bool(b), _) => Ok((*b).into()),
            Expr::Literal(Literal::String(s), _) => Ok(s.clone().into()),
            Expr::UnaryOp { op, rhs, .. } => {
                let rhs = self.eval(rhs)?;
                match op {
                    UnaryOperator::Neg => -rhs,
                    _ => unimplemented!(),
                }
            }
            Expr::BinaryOp { lhs, op, rhs, .. } => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;
                match op {
                    BinaryOperator::Add => lhs + rhs,
                    BinaryOperator::Sub => lhs - rhs,
                    BinaryOperator::Mul => lhs * rhs,
                    BinaryOperator::Div => lhs / rhs,
                    BinaryOperator::Pow => todo!(),
                    BinaryOperator::Equ => Ok(lhs.eq(&rhs).into()),
                    BinaryOperator::Neq => todo!(),
                }
            }
            Expr::Let { bindings, body, .. } => {
                self.env.push();
                for Binding { ident, body, .. } in bindings {
                    let val = self.eval(body)?;
                    self.env.set(ident, val);
                }
                let res = self.eval(body)?;
                self.env.pop();
                Ok(res)
            }
            Expr::If {
                condition,
                then,
                else_,
                ..
            } => {
                let condition = self.eval(condition)?;
                if *(condition.as_type::<bool>()?) {
                    self.eval(then)
                } else {
                    self.eval(else_)
                }
            }
            Expr::Call { ref fun, args, .. } => {
                let fun = self.eval(fun)?;
                let expected_type = FunctionType {
                    args: args.iter().map(|_| Type::Int).collect(),
                    ret: Box::new(Type::Int),
                };

                let Function {
                    args: function_args,
                    body,
                    ..
                } = fun.as_function(expected_type)?;
                let arg_values = function_args.iter().zip(
                    args.iter()
                        .map(|v| self.eval(v))
                        .collect::<Result<Vec<_>>>()?,
                );
                let mut interpreter = Interpreter::new();
                for (arg_name, arg_value) in arg_values {
                    interpreter.env.set(arg_name, arg_value);
                }
                Ok(Value::from(*interpreter.eval(body)?.as_type::<i64>()?))
            }
            Expr::Fun { args, body, type_ } => {
                let type_ = match type_ {
                    Type::Function(ft) => ft.clone(),
                    _ => unreachable!("Function expression without function type"),
                };

                Ok(Value::from(value::Function {
                    // TODO
                    type_,
                    args: args.iter().map(|(arg, _)| arg.to_owned()).collect(),
                    body: (**body).to_owned(),
                }))
            }
        }?;
        debug_assert_eq!(&res.type_(), expr.type_());
        Ok(res)
    }
}

pub fn eval<'a>(expr: &'a Expr<'a, Type>) -> Result<Value<'a>> {
    let mut interpreter = Interpreter::new();
    interpreter.eval(expr)
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use super::value::{TypeOf, Val};
    use super::*;
    use BinaryOperator::*;

    fn int_lit(i: u64) -> Box<Expr<'static, Type<'static>>> {
        Box::new(Expr::Literal(Literal::Int(i), Type::Int))
    }

    fn do_eval<T>(src: &str) -> T
    where
        for<'a> &'a T: TryFrom<&'a Val<'a>>,
        T: Clone + TypeOf,
    {
        let expr = crate::parser::expr(src).unwrap().1;
        let hir = crate::tc::typecheck_expr(expr).unwrap();
        let res = eval(&hir).unwrap();
        res.as_type::<T>().unwrap().clone()
    }

    #[test]
    fn simple_addition() {
        let expr = Expr::BinaryOp {
            lhs: int_lit(1),
            op: Mul,
            rhs: int_lit(2),
            type_: Type::Int,
        };
        let res = eval(&expr).unwrap();
        assert_eq!(*res.as_type::<i64>().unwrap(), 2);
    }

    #[test]
    fn variable_shadowing() {
        let res = do_eval::<i64>("let x = 1 in (let x = 2 in x) + x");
        assert_eq!(res, 3);
    }

    #[test]
    fn conditional_with_equals() {
        let res = do_eval::<i64>("let x = 1 in if x == 1 then 2 else 4");
        assert_eq!(res, 2);
    }

    #[test]
    #[ignore]
    fn function_call() {
        let res = do_eval::<i64>("let id = fn x = x in id 1");
        assert_eq!(res, 1);
    }
}
