mod error;
mod value;

pub use self::error::{Error, Result};
pub use self::value::{Function, Value};
use crate::ast::{BinaryOperator, Expr, FunctionType, Ident, Literal, Type, UnaryOperator};
use crate::common::env::Env;

#[derive(Debug, Default)]
pub struct Interpreter<'a> {
    env: Env<'a, Value<'a>>,
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

    pub fn eval(&mut self, expr: &'a Expr<'a>) -> Result<Value<'a>> {
        match expr {
            Expr::Ident(id) => self.resolve(id),
            Expr::Literal(Literal::Int(i)) => Ok((*i).into()),
            Expr::UnaryOp { op, rhs } => {
                let rhs = self.eval(rhs)?;
                match op {
                    UnaryOperator::Neg => -rhs,
                    _ => unimplemented!(),
                }
            }
            Expr::BinaryOp { lhs, op, rhs } => {
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
            Expr::Let { bindings, body } => {
                self.env.push();
                for (id, val) in bindings {
                    let val = self.eval(val)?;
                    self.env.set(id, val);
                }
                let res = self.eval(body)?;
                self.env.pop();
                Ok(res)
            }
            Expr::If {
                condition,
                then,
                else_,
            } => {
                let condition = self.eval(condition)?;
                if *(condition.as_type::<bool>()?) {
                    self.eval(then)
                } else {
                    self.eval(else_)
                }
            }
            Expr::Call { ref fun, args } => {
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
            Expr::Fun(fun) => Ok(Value::from(value::Function {
                // TODO
                type_: FunctionType {
                    args: fun.args.iter().map(|_| Type::Int).collect(),
                    ret: Box::new(Type::Int),
                },
                args: fun.args.iter().map(|arg| arg.to_owned()).collect(),
                body: fun.body.to_owned(),
            })),
        }
    }
}

pub fn eval<'a>(expr: &'a Expr<'a>) -> Result<Value> {
    let mut interpreter = Interpreter::new();
    interpreter.eval(expr)
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;

    use super::value::{TypeOf, Val};
    use super::*;
    use BinaryOperator::*;

    fn int_lit(i: u64) -> Box<Expr<'static>> {
        Box::new(Expr::Literal(Literal::Int(i)))
    }

    fn parse_eval<T>(src: &str) -> T
    where
        for<'a> &'a T: TryFrom<&'a Val<'a>>,
        T: Clone + TypeOf,
    {
        let expr = crate::parser::expr(src).unwrap().1;
        let res = eval(&expr).unwrap();
        res.as_type::<T>().unwrap().clone()
    }

    #[test]
    fn simple_addition() {
        let expr = Expr::BinaryOp {
            lhs: int_lit(1),
            op: Mul,
            rhs: int_lit(2),
        };
        let res = eval(&expr).unwrap();
        assert_eq!(*res.as_type::<i64>().unwrap(), 2);
    }

    #[test]
    fn variable_shadowing() {
        let res = parse_eval::<i64>("let x = 1 in (let x = 2 in x) + x");
        assert_eq!(res, 3);
    }

    #[test]
    fn conditional_with_equals() {
        let res = parse_eval::<i64>("let x = 1 in if x == 1 then 2 else 4");
        assert_eq!(res, 2);
    }

    #[test]
    fn function_call() {
        let res = parse_eval::<i64>("let id = fn x = x in id 1");
        assert_eq!(res, 1);
    }
}
