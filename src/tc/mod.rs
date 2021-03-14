use derive_more::From;
use itertools::Itertools;
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::fmt::{self, Display};
use std::result;
use thiserror::Error;

use crate::ast::{self, hir, BinaryOperator, Ident, Literal};
use crate::common::env::Env;

#[derive(Debug, Error)]
pub enum Error {
    #[error("Undefined variable {0}")]
    UndefinedVariable(Ident<'static>),

    #[error("Mismatched types: expected {expected}, but got {actual}")]
    TypeMismatch { expected: Type, actual: Type },

    #[error("Mismatched types, expected numeric type, but got {0}")]
    NonNumeric(Type),

    #[error("Ambiguous type {0}")]
    AmbiguousType(TyVar),
}

pub type Result<T> = result::Result<T, Error>;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct TyVar(u64);

impl Display for TyVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.0)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct NullaryType(String);

impl Display for NullaryType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum PrimType {
    Int,
    Float,
    Bool,
    CString,
}

impl From<PrimType> for ast::Type {
    fn from(pr: PrimType) -> Self {
        match pr {
            PrimType::Int => ast::Type::Int,
            PrimType::Float => ast::Type::Float,
            PrimType::Bool => ast::Type::Bool,
            PrimType::CString => ast::Type::CString,
        }
    }
}

impl Display for PrimType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrimType::Int => f.write_str("int"),
            PrimType::Float => f.write_str("float"),
            PrimType::Bool => f.write_str("bool"),
            PrimType::CString => f.write_str("cstring"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, From)]
pub enum Type {
    #[from(ignore)]
    Univ(TyVar),
    #[from(ignore)]
    Exist(TyVar),
    Nullary(NullaryType),
    Prim(PrimType),
    Fun {
        args: Vec<Type>,
        ret: Box<Type>,
    },
}

impl PartialEq<ast::Type> for Type {
    fn eq(&self, other: &ast::Type) -> bool {
        match (self, other) {
            (Type::Univ(_), _) => todo!(),
            (Type::Exist(_), _) => false,
            (Type::Nullary(_), _) => todo!(),
            (Type::Prim(pr), ty) => ast::Type::from(*pr) == *ty,
            (Type::Fun { args, ret }, ast::Type::Function(ft)) => {
                *args == ft.args && (**ret).eq(&*ft.ret)
            }
            (Type::Fun { .. }, _) => false,
        }
    }
}

impl TryFrom<Type> for ast::Type {
    type Error = Type;

    fn try_from(value: Type) -> result::Result<Self, Self::Error> {
        match value {
            Type::Univ(_) => todo!(),
            Type::Exist(_) => Err(value),
            Type::Nullary(_) => todo!(),
            Type::Prim(p) => Ok(p.into()),
            Type::Fun { ref args, ref ret } => Ok(ast::Type::Function(ast::FunctionType {
                args: args
                    .clone()
                    .into_iter()
                    .map(Self::try_from)
                    .try_collect()
                    .map_err(|_| value.clone())?,
                ret: Box::new((*ret.clone()).try_into().map_err(|_| value.clone())?),
            })),
        }
    }
}

const INT: Type = Type::Prim(PrimType::Int);
const FLOAT: Type = Type::Prim(PrimType::Float);
const BOOL: Type = Type::Prim(PrimType::Bool);
const CSTRING: Type = Type::Prim(PrimType::CString);

impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Nullary(nt) => nt.fmt(f),
            Type::Prim(p) => p.fmt(f),
            Type::Univ(TyVar(n)) => write!(f, "∀{}", n),
            Type::Exist(TyVar(n)) => write!(f, "∃{}", n),
            Type::Fun { args, ret } => write!(f, "fn {} -> {}", args.iter().join(", "), ret),
        }
    }
}

impl From<ast::Type> for Type {
    fn from(type_: ast::Type) -> Self {
        match type_ {
            ast::Type::Int => INT,
            ast::Type::Float => FLOAT,
            ast::Type::Bool => BOOL,
            ast::Type::CString => CSTRING,
            ast::Type::Function(ast::FunctionType { args, ret }) => Type::Fun {
                args: args.into_iter().map(Self::from).collect(),
                ret: Box::new(Self::from(*ret)),
            },
        }
    }
}

struct Typechecker<'ast> {
    ty_var_counter: u64,
    ctx: HashMap<TyVar, Type>,
    env: Env<Ident<'ast>, Type>,
}

impl<'ast> Typechecker<'ast> {
    fn new() -> Self {
        Self {
            ty_var_counter: 0,
            ctx: Default::default(),
            env: Default::default(),
        }
    }

    pub(crate) fn tc_expr(&mut self, expr: ast::Expr<'ast>) -> Result<hir::Expr<'ast, Type>> {
        match expr {
            ast::Expr::Ident(ident) => {
                let type_ = self
                    .env
                    .resolve(&ident)
                    .ok_or_else(|| Error::UndefinedVariable(ident.to_owned()))?
                    .clone();
                Ok(hir::Expr::Ident(ident, type_))
            }
            ast::Expr::Literal(lit) => {
                let type_ = match lit {
                    Literal::Int(_) => Type::Prim(PrimType::Int),
                    Literal::Bool(_) => Type::Prim(PrimType::Bool),
                    Literal::String(_) => Type::Prim(PrimType::CString),
                };
                Ok(hir::Expr::Literal(lit.to_owned(), type_))
            }
            ast::Expr::UnaryOp { op, rhs } => todo!(),
            ast::Expr::BinaryOp { lhs, op, rhs } => {
                let lhs = self.tc_expr(*lhs)?;
                let rhs = self.tc_expr(*rhs)?;
                let type_ = match op {
                    BinaryOperator::Equ | BinaryOperator::Neq => {
                        self.unify(lhs.type_(), rhs.type_())?;
                        Type::Prim(PrimType::Bool)
                    }
                    BinaryOperator::Add | BinaryOperator::Sub | BinaryOperator::Mul => {
                        let ty = self.unify(lhs.type_(), rhs.type_())?;
                        // if !matches!(ty, Type::Int | Type::Float) {
                        //     return Err(Error::NonNumeric(ty));
                        // }
                        ty
                    }
                    BinaryOperator::Div => todo!(),
                    BinaryOperator::Pow => todo!(),
                };
                Ok(hir::Expr::BinaryOp {
                    lhs: Box::new(lhs),
                    op,
                    rhs: Box::new(rhs),
                    type_,
                })
            }
            ast::Expr::Let { bindings, body } => {
                self.env.push();
                let bindings = bindings
                    .into_iter()
                    .map(
                        |ast::Binding { ident, type_, body }| -> Result<hir::Binding<Type>> {
                            let body = self.tc_expr(body)?;
                            if let Some(type_) = type_ {
                                self.unify(body.type_(), &type_.into())?;
                            }
                            self.env.set(ident.clone(), body.type_().clone());
                            Ok(hir::Binding {
                                ident,
                                type_: body.type_().clone(),
                                body,
                            })
                        },
                    )
                    .collect::<Result<Vec<hir::Binding<Type>>>>()?;
                let body = self.tc_expr(*body)?;
                self.env.pop();
                Ok(hir::Expr::Let {
                    bindings,
                    type_: body.type_().clone(),
                    body: Box::new(body),
                })
            }
            ast::Expr::If {
                condition,
                then,
                else_,
            } => {
                let condition = self.tc_expr(*condition)?;
                self.unify(&Type::Prim(PrimType::Bool), condition.type_())?;
                let then = self.tc_expr(*then)?;
                let else_ = self.tc_expr(*else_)?;
                let type_ = self.unify(then.type_(), else_.type_())?;
                Ok(hir::Expr::If {
                    condition: Box::new(condition),
                    then: Box::new(then),
                    else_: Box::new(else_),
                    type_,
                })
            }
            ast::Expr::Fun(f) => {
                let ast::Fun { args, body } = *f;
                self.env.push();
                let args: Vec<_> = args
                    .into_iter()
                    .map(|id| {
                        let ty = self.fresh_ex();
                        self.env.set(id.clone(), ty.clone());
                        (id, ty)
                    })
                    .collect();
                let body = self.tc_expr(body)?;
                self.env.pop();
                Ok(hir::Expr::Fun {
                    type_: Type::Fun {
                        args: args.iter().map(|(_, ty)| ty.clone()).collect(),
                        ret: Box::new(body.type_().clone()),
                    },
                    args,
                    body: Box::new(body),
                })
            }
            ast::Expr::Call { fun, args } => {
                let ret_ty = self.fresh_ex();
                let arg_tys = args.iter().map(|_| self.fresh_ex()).collect::<Vec<_>>();
                let ft = Type::Fun {
                    args: arg_tys.clone(),
                    ret: Box::new(ret_ty.clone()),
                };
                let fun = self.tc_expr(*fun)?;
                self.unify(&ft, fun.type_())?;
                let args = args
                    .into_iter()
                    .zip(arg_tys)
                    .map(|(arg, ty)| {
                        let arg = self.tc_expr(arg)?;
                        self.unify(&ty, arg.type_())?;
                        Ok(arg)
                    })
                    .try_collect()?;
                Ok(hir::Expr::Call {
                    fun: Box::new(fun),
                    args,
                    type_: ret_ty,
                })
            }
            ast::Expr::Ascription { expr, type_ } => {
                let expr = self.tc_expr(*expr)?;
                self.unify(expr.type_(), &type_.into())?;
                Ok(expr)
            }
        }
    }

    pub(crate) fn tc_decl(&mut self, decl: ast::Decl<'ast>) -> Result<hir::Decl<'ast, Type>> {
        match decl {
            ast::Decl::Fun { name, body } => {
                let body = self.tc_expr(ast::Expr::Fun(Box::new(body)))?;
                let type_ = body.type_().clone();
                self.env.set(name.clone(), type_);
                match body {
                    hir::Expr::Fun { args, body, type_ } => Ok(hir::Decl::Fun {
                        name,
                        args,
                        body,
                        type_,
                    }),
                    _ => unreachable!(),
                }
            }
        }
    }

    fn fresh_tv(&mut self) -> TyVar {
        self.ty_var_counter += 1;
        TyVar(self.ty_var_counter)
    }

    fn fresh_ex(&mut self) -> Type {
        Type::Exist(self.fresh_tv())
    }

    fn fresh_univ(&mut self) -> Type {
        Type::Exist(self.fresh_tv())
    }

    fn universalize<'a>(&mut self, expr: hir::Expr<'a, Type>) -> hir::Expr<'a, Type> {
        // TODO
        expr
    }

    fn unify(&mut self, ty1: &Type, ty2: &Type) -> Result<Type> {
        match (ty1, ty2) {
            (Type::Prim(p1), Type::Prim(p2)) if p1 == p2 => Ok(ty2.clone()),
            (Type::Exist(tv), ty) | (ty, Type::Exist(tv)) => match self.resolve_tv(*tv) {
                Some(existing_ty) if *ty == existing_ty => Ok(ty.clone()),
                Some(existing_ty) => Err(Error::TypeMismatch {
                    expected: ty.clone(),
                    actual: existing_ty.into(),
                }),
                None => match self.ctx.insert(*tv, ty.clone()) {
                    Some(existing) => self.unify(&existing, ty),
                    None => Ok(ty.clone()),
                },
            },
            (Type::Univ(u1), Type::Univ(u2)) if u1 == u2 => Ok(ty2.clone()),
            (
                Type::Fun {
                    args: args1,
                    ret: ret1,
                },
                Type::Fun {
                    args: args2,
                    ret: ret2,
                },
            ) => {
                let args = args1
                    .iter()
                    .zip(args2)
                    .map(|(t1, t2)| self.unify(t1, t2))
                    .try_collect()?;
                let ret = self.unify(ret1, ret2)?;
                Ok(Type::Fun {
                    args,
                    ret: Box::new(ret),
                })
            }
            (Type::Nullary(_), _) | (_, Type::Nullary(_)) => todo!(),
            _ => Err(Error::TypeMismatch {
                expected: ty1.clone(),
                actual: ty2.clone(),
            }),
        }
    }

    fn finalize_expr(&self, expr: hir::Expr<'ast, Type>) -> Result<hir::Expr<'ast, ast::Type>> {
        expr.traverse_type(|ty| self.finalize_type(ty))
    }

    fn finalize_decl(&self, decl: hir::Decl<'ast, Type>) -> Result<hir::Decl<'ast, ast::Type>> {
        decl.traverse_type(|ty| self.finalize_type(ty))
    }

    fn finalize_type(&self, ty: Type) -> Result<ast::Type> {
        match ty {
            Type::Exist(tv) => self.resolve_tv(tv).ok_or(Error::AmbiguousType(tv)),
            Type::Univ(tv) => todo!(),
            Type::Nullary(_) => todo!(),
            Type::Prim(pr) => Ok(pr.into()),
            Type::Fun { args, ret } => Ok(ast::Type::Function(ast::FunctionType {
                args: args
                    .into_iter()
                    .map(|ty| self.finalize_type(ty))
                    .try_collect()?,
                ret: Box::new(self.finalize_type(*ret)?),
            })),
        }
    }

    fn resolve_tv(&self, tv: TyVar) -> Option<ast::Type> {
        let mut res = &Type::Exist(tv);
        loop {
            match res {
                Type::Exist(tv) => {
                    res = self.ctx.get(tv)?;
                }
                Type::Univ(_) => todo!(),
                Type::Nullary(_) => todo!(),
                Type::Prim(pr) => break Some((*pr).into()),
                Type::Fun { args, ret } => todo!(),
            }
        }
    }
}

pub fn typecheck_expr(expr: ast::Expr) -> Result<hir::Expr<ast::Type>> {
    let mut typechecker = Typechecker::new();
    let typechecked = typechecker.tc_expr(expr)?;
    typechecker.finalize_expr(typechecked)
}

pub fn typecheck_toplevel(decls: Vec<ast::Decl>) -> Result<Vec<hir::Decl<ast::Type>>> {
    let mut typechecker = Typechecker::new();
    decls
        .into_iter()
        .map(|decl| {
            let decl = typechecker.tc_decl(decl)?;
            typechecker.finalize_decl(decl)
        })
        .try_collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_type {
        ($expr: expr, $type: expr) => {
            use crate::parser::{expr, type_};
            let parsed_expr = test_parse!(expr, $expr);
            let parsed_type = test_parse!(type_, $type);
            let res = typecheck_expr(parsed_expr).unwrap_or_else(|e| panic!("{}", e));
            assert_eq!(res.type_(), &parsed_type);
        };
    }

    macro_rules! assert_type_error {
        ($expr: expr) => {
            use crate::parser::expr;
            let parsed_expr = test_parse!(expr, $expr);
            let res = typecheck_expr(parsed_expr);
            assert!(
                res.is_err(),
                "Expected type error, but got type: {}",
                res.unwrap().type_()
            );
        };
    }

    #[test]
    fn literal_int() {
        assert_type!("1", "int");
    }

    #[test]
    fn conditional() {
        assert_type!("if 1 == 2 then 3 else 4", "int");
    }

    #[test]
    #[ignore]
    fn add_bools() {
        assert_type_error!("true + false");
    }

    #[test]
    fn call_generic_function() {
        assert_type!("(fn x = x) 1", "int");
    }

    #[test]
    #[ignore]
    fn generic_function() {
        assert_type!("fn x = x", "fn x, y -> x");
    }

    #[test]
    #[ignore]
    fn let_generalization() {
        assert_type!("let id = fn x = x in if id true then id 1 else 2", "int");
    }

    #[test]
    fn concrete_function() {
        assert_type!("fn x = x + 1", "fn int -> int");
    }

    #[test]
    fn call_concrete_function() {
        assert_type!("(fn x = x + 1) 2", "int");
    }

    #[test]
    fn conditional_non_bool() {
        assert_type_error!("if 3 then true else false");
    }

    #[test]
    fn let_int() {
        assert_type!("let x = 1 in x", "int");
    }
}
