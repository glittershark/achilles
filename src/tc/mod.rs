use bimap::BiMap;
use derive_more::From;
use itertools::Itertools;
use std::cell::RefCell;
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::fmt::{self, Display};
use std::{mem, result};
use thiserror::Error;

use crate::ast::{self, hir, Arg, BinaryOperator, Ident, Literal};
use crate::common::env::Env;
use crate::common::{Namer, NamerOf};

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

impl<'a> From<PrimType> for ast::Type<'a> {
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

impl<'a> TryFrom<Type> for ast::Type<'a> {
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

struct Typechecker<'ast> {
    ty_var_namer: NamerOf<TyVar>,
    ctx: HashMap<TyVar, Type>,
    env: Env<Ident<'ast>, Type>,

    /// AST type var -> type
    instantiations: Env<Ident<'ast>, Type>,

    /// AST type-var -> universal TyVar
    type_vars: RefCell<(BiMap<Ident<'ast>, TyVar>, NamerOf<Ident<'static>>)>,
}

impl<'ast> Typechecker<'ast> {
    fn new() -> Self {
        Self {
            ty_var_namer: Namer::new(TyVar).boxed(),
            type_vars: RefCell::new((
                Default::default(),
                Namer::alphabetic().map(|n| Ident::try_from(n).unwrap()),
            )),
            ctx: Default::default(),
            env: Default::default(),
            instantiations: Default::default(),
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
                                let type_ = self.type_from_ast_type(type_);
                                self.unify(body.type_(), &type_)?;
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
                    .map(|Arg { ident, type_ }| {
                        let ty = match type_ {
                            Some(t) => self.type_from_ast_type(t),
                            None => self.fresh_ex(),
                        };
                        self.env.set(ident.clone(), ty.clone());
                        (ident, ty)
                    })
                    .collect();
                let body = self.tc_expr(body)?;
                self.env.pop();
                Ok(hir::Expr::Fun {
                    type_: self.universalize(
                        args.iter().map(|(_, ty)| ty.clone()).collect(),
                        body.type_().clone(),
                    ),
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
                self.instantiations.push();
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
                self.commit_instantiations();
                Ok(hir::Expr::Call {
                    fun: Box::new(fun),
                    args,
                    type_: ret_ty,
                })
            }
            ast::Expr::Ascription { expr, type_ } => {
                let expr = self.tc_expr(*expr)?;
                let type_ = self.type_from_ast_type(type_);
                self.unify(expr.type_(), &type_)?;
                Ok(expr)
            }
        }
    }

    pub(crate) fn tc_decl(
        &mut self,
        decl: ast::Decl<'ast>,
    ) -> Result<Option<hir::Decl<'ast, Type>>> {
        match decl {
            ast::Decl::Fun { name, body } => {
                let mut expr = ast::Expr::Fun(Box::new(body));
                if let Some(type_) = self.env.resolve(&name) {
                    expr = ast::Expr::Ascription {
                        expr: Box::new(expr),
                        type_: self.finalize_type(type_.clone())?,
                    };
                }

                let body = self.tc_expr(expr)?;
                let type_ = body.type_().clone();
                self.env.set(name.clone(), type_);
                match body {
                    hir::Expr::Fun { args, body, type_ } => Ok(Some(hir::Decl::Fun {
                        name,
                        args,
                        body,
                        type_,
                    })),
                    _ => unreachable!(),
                }
            }
            ast::Decl::Ascription { name, type_ } => {
                let type_ = self.type_from_ast_type(type_);
                self.env.set(name.clone(), type_);
                Ok(None)
            }
        }
    }

    fn fresh_tv(&mut self) -> TyVar {
        self.ty_var_namer.make_name()
    }

    fn fresh_ex(&mut self) -> Type {
        Type::Exist(self.fresh_tv())
    }

    fn fresh_univ(&mut self) -> Type {
        Type::Univ(self.fresh_tv())
    }

    #[allow(clippy::redundant_closure)] // https://github.com/rust-lang/rust-clippy/issues/6903
    fn universalize(&mut self, args: Vec<Type>, ret: Type) -> Type {
        let mut vars = HashMap::new();
        let mut universalize_type = move |ty| match ty {
            Type::Exist(tv) if self.resolve_tv(tv).is_none() => vars
                .entry(tv)
                .or_insert_with_key(|tv| {
                    let ty = self.fresh_univ();
                    self.ctx.insert(*tv, ty.clone());
                    ty
                })
                .clone(),
            _ => ty,
        };

        Type::Fun {
            args: args.into_iter().map(|t| universalize_type(t)).collect(),
            ret: Box::new(universalize_type(ret)),
        }
    }

    fn unify(&mut self, ty1: &Type, ty2: &Type) -> Result<Type> {
        match (ty1, ty2) {
            (Type::Exist(tv), ty) | (ty, Type::Exist(tv)) => match self.resolve_tv(*tv) {
                Some(existing_ty) if self.types_match(ty, &existing_ty) => Ok(ty.clone()),
                Some(var @ ast::Type::Var(_)) => {
                    let var = self.type_from_ast_type(var);
                    self.unify(&var, ty)
                }
                Some(existing_ty) => match ty {
                    Type::Exist(_) => {
                        let rhs = self.type_from_ast_type(existing_ty);
                        self.unify(ty, &rhs)
                    }
                    _ => Err(Error::TypeMismatch {
                        expected: ty.clone(),
                        actual: self.type_from_ast_type(existing_ty),
                    }),
                },
                None => match self.ctx.insert(*tv, ty.clone()) {
                    Some(existing) => self.unify(&existing, ty),
                    None => Ok(ty.clone()),
                },
            },
            (Type::Univ(u1), Type::Univ(u2)) if u1 == u2 => Ok(ty2.clone()),
            (Type::Univ(u), ty) | (ty, Type::Univ(u)) => {
                let ident = self.name_univ(*u);
                match self.instantiations.resolve(&ident) {
                    Some(existing_ty) if ty == existing_ty => Ok(ty.clone()),
                    Some(existing_ty) => Err(Error::TypeMismatch {
                        expected: ty.clone(),
                        actual: existing_ty.clone(),
                    }),
                    None => {
                        self.instantiations.set(ident, ty.clone());
                        Ok(ty.clone())
                    }
                }
            }
            (Type::Prim(p1), Type::Prim(p2)) if p1 == p2 => Ok(ty2.clone()),
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

    fn finalize_expr(
        &self,
        expr: hir::Expr<'ast, Type>,
    ) -> Result<hir::Expr<'ast, ast::Type<'ast>>> {
        expr.traverse_type(|ty| self.finalize_type(ty))
    }

    fn finalize_decl(
        &self,
        decl: hir::Decl<'ast, Type>,
    ) -> Result<hir::Decl<'ast, ast::Type<'ast>>> {
        decl.traverse_type(|ty| self.finalize_type(ty))
    }

    fn finalize_type(&self, ty: Type) -> Result<ast::Type<'static>> {
        let ret = match ty {
            Type::Exist(tv) => self.resolve_tv(tv).ok_or(Error::AmbiguousType(tv)),
            Type::Univ(tv) => Ok(ast::Type::Var(self.name_univ(tv))),
            Type::Nullary(_) => todo!(),
            Type::Prim(pr) => Ok(pr.into()),
            Type::Fun { args, ret } => Ok(ast::Type::Function(ast::FunctionType {
                args: args
                    .into_iter()
                    .map(|ty| self.finalize_type(ty))
                    .try_collect()?,
                ret: Box::new(self.finalize_type(*ret)?),
            })),
        };
        ret
    }

    fn resolve_tv(&self, tv: TyVar) -> Option<ast::Type<'static>> {
        let mut res = &Type::Exist(tv);
        loop {
            match res {
                Type::Exist(tv) => {
                    res = self.ctx.get(tv)?;
                }
                Type::Univ(tv) => {
                    let ident = self.name_univ(*tv);
                    if let Some(r) = self.instantiations.resolve(&ident) {
                        res = r;
                    } else {
                        break Some(ast::Type::Var(ident));
                    }
                }
                Type::Nullary(_) => todo!(),
                Type::Prim(pr) => break Some((*pr).into()),
                Type::Fun { args, ret } => todo!(),
            }
        }
    }

    fn type_from_ast_type(&mut self, ast_type: ast::Type<'ast>) -> Type {
        match ast_type {
            ast::Type::Int => INT,
            ast::Type::Float => FLOAT,
            ast::Type::Bool => BOOL,
            ast::Type::CString => CSTRING,
            ast::Type::Function(ast::FunctionType { args, ret }) => Type::Fun {
                args: args
                    .into_iter()
                    .map(|t| self.type_from_ast_type(t))
                    .collect(),
                ret: Box::new(self.type_from_ast_type(*ret)),
            },
            ast::Type::Var(id) => Type::Univ({
                let opt_tv = { self.type_vars.borrow_mut().0.get_by_left(&id).copied() };
                opt_tv.unwrap_or_else(|| {
                    let tv = self.fresh_tv();
                    self.type_vars
                        .borrow_mut()
                        .0
                        .insert_no_overwrite(id, tv)
                        .unwrap();
                    tv
                })
            }),
        }
    }

    fn name_univ(&self, tv: TyVar) -> Ident<'static> {
        let mut vars = self.type_vars.borrow_mut();
        vars.0
            .get_by_right(&tv)
            .map(Ident::to_owned)
            .unwrap_or_else(|| {
                let name = vars.1.make_name();
                vars.0.insert_no_overwrite(name.clone(), tv).unwrap();
                name
            })
    }

    fn commit_instantiations(&mut self) {
        let mut ctx = mem::take(&mut self.ctx);
        for (_, v) in ctx.iter_mut() {
            if let Type::Univ(tv) = v {
                if let Some(concrete) = self.instantiations.resolve(&self.name_univ(*tv)) {
                    *v = concrete.clone();
                }
            }
        }
        self.ctx = ctx;
        self.instantiations.pop();
    }

    fn types_match(&self, type_: &Type, ast_type: &ast::Type<'ast>) -> bool {
        match (type_, ast_type) {
            (Type::Univ(u), ast::Type::Var(v)) => {
                Some(u) == self.type_vars.borrow().0.get_by_left(v)
            }
            (Type::Univ(_), _) => false,
            (Type::Exist(_), _) => false,
            (Type::Nullary(_), _) => todo!(),
            (Type::Prim(pr), ty) => ast::Type::from(*pr) == *ty,
            (Type::Fun { args, ret }, ast::Type::Function(ft)) => {
                args.len() == ft.args.len()
                    && args
                        .iter()
                        .zip(&ft.args)
                        .all(|(a1, a2)| self.types_match(a1, &a2))
                    && self.types_match(&*ret, &*ft.ret)
            }
            (Type::Fun { .. }, _) => false,
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
    let mut res = Vec::with_capacity(decls.len());
    for decl in decls {
        if let Some(hir_decl) = typechecker.tc_decl(decl)? {
            let hir_decl = typechecker.finalize_decl(hir_decl)?;
            res.push(hir_decl);
        }
        typechecker.ctx.clear();
    }
    Ok(res)
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
            assert!(
                res.type_().alpha_equiv(&parsed_type),
                "{} inferred type {}, but expected {}",
                $expr,
                res.type_(),
                $type
            );
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
    fn generic_function() {
        assert_type!("fn x = x", "fn x -> x");
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
    fn arg_ascriptions() {
        assert_type!("fn (x: int) = x", "fn int -> int");
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
