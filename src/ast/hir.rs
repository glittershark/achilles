use itertools::Itertools;

use super::{BinaryOperator, Ident, Literal, UnaryOperator};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Binding<'a, T> {
    pub ident: Ident<'a>,
    pub type_: T,
    pub body: Expr<'a, T>,
}

impl<'a, T> Binding<'a, T> {
    fn to_owned(&self) -> Binding<'static, T>
    where
        T: Clone,
    {
        Binding {
            ident: self.ident.to_owned(),
            type_: self.type_.clone(),
            body: self.body.to_owned(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr<'a, T> {
    Ident(Ident<'a>, T),

    Literal(Literal<'a>, T),

    UnaryOp {
        op: UnaryOperator,
        rhs: Box<Expr<'a, T>>,
        type_: T,
    },

    BinaryOp {
        lhs: Box<Expr<'a, T>>,
        op: BinaryOperator,
        rhs: Box<Expr<'a, T>>,
        type_: T,
    },

    Let {
        bindings: Vec<Binding<'a, T>>,
        body: Box<Expr<'a, T>>,
        type_: T,
    },

    If {
        condition: Box<Expr<'a, T>>,
        then: Box<Expr<'a, T>>,
        else_: Box<Expr<'a, T>>,
        type_: T,
    },

    Fun {
        args: Vec<(Ident<'a>, T)>,
        body: Box<Expr<'a, T>>,
        type_: T,
    },

    Call {
        fun: Box<Expr<'a, T>>,
        args: Vec<Expr<'a, T>>,
        type_: T,
    },
}

impl<'a, T> Expr<'a, T> {
    pub fn type_(&self) -> &T {
        match self {
            Expr::Ident(_, t) => t,
            Expr::Literal(_, t) => t,
            Expr::UnaryOp { type_, .. } => type_,
            Expr::BinaryOp { type_, .. } => type_,
            Expr::Let { type_, .. } => type_,
            Expr::If { type_, .. } => type_,
            Expr::Fun { type_, .. } => type_,
            Expr::Call { type_, .. } => type_,
        }
    }

    pub fn traverse_type<F, U, E>(self, f: F) -> Result<Expr<'a, U>, E>
    where
        F: Fn(T) -> Result<U, E> + Clone,
    {
        match self {
            Expr::Ident(id, t) => Ok(Expr::Ident(id, f(t)?)),
            Expr::Literal(lit, t) => Ok(Expr::Literal(lit, f(t)?)),
            Expr::UnaryOp { op, rhs, type_ } => Ok(Expr::UnaryOp {
                op,
                rhs: Box::new(rhs.traverse_type(f.clone())?),
                type_: f(type_)?,
            }),
            Expr::BinaryOp {
                lhs,
                op,
                rhs,
                type_,
            } => Ok(Expr::BinaryOp {
                lhs: Box::new(lhs.traverse_type(f.clone())?),
                op,
                rhs: Box::new(rhs.traverse_type(f.clone())?),
                type_: f(type_)?,
            }),
            Expr::Let {
                bindings,
                body,
                type_,
            } => Ok(Expr::Let {
                bindings: bindings
                    .into_iter()
                    .map(|Binding { ident, type_, body }| {
                        Ok(Binding {
                            ident,
                            type_: f(type_)?,
                            body: body.traverse_type(f.clone())?,
                        })
                    })
                    .collect::<Result<Vec<_>, E>>()?,
                body: Box::new(body.traverse_type(f.clone())?),
                type_: f(type_)?,
            }),
            Expr::If {
                condition,
                then,
                else_,
                type_,
            } => Ok(Expr::If {
                condition: Box::new(condition.traverse_type(f.clone())?),
                then: Box::new(then.traverse_type(f.clone())?),
                else_: Box::new(else_.traverse_type(f.clone())?),
                type_: f(type_)?,
            }),
            Expr::Fun { args, body, type_ } => Ok(Expr::Fun {
                args: args
                    .into_iter()
                    .map(|(id, t)| Ok((id, f.clone()(t)?)))
                    .collect::<Result<Vec<_>, E>>()?,
                body: Box::new(body.traverse_type(f.clone())?),
                type_: f(type_)?,
            }),
            Expr::Call { fun, args, type_ } => Ok(Expr::Call {
                fun: Box::new(fun.traverse_type(f.clone())?),
                args: args
                    .into_iter()
                    .map(|e| e.traverse_type(f.clone()))
                    .collect::<Result<Vec<_>, E>>()?,
                type_: f(type_)?,
            }),
        }
    }

    pub fn to_owned(&self) -> Expr<'static, T>
    where
        T: Clone,
    {
        match self {
            Expr::Ident(id, t) => Expr::Ident(id.to_owned(), t.clone()),
            Expr::Literal(lit, t) => Expr::Literal(lit.to_owned(), t.clone()),
            Expr::UnaryOp { op, rhs, type_ } => Expr::UnaryOp {
                op: *op,
                rhs: Box::new((**rhs).to_owned()),
                type_: type_.clone(),
            },
            Expr::BinaryOp {
                lhs,
                op,
                rhs,
                type_,
            } => Expr::BinaryOp {
                lhs: Box::new((**lhs).to_owned()),
                op: *op,
                rhs: Box::new((**rhs).to_owned()),
                type_: type_.clone(),
            },
            Expr::Let {
                bindings,
                body,
                type_,
            } => Expr::Let {
                bindings: bindings.into_iter().map(|b| b.to_owned()).collect(),
                body: Box::new((**body).to_owned()),
                type_: type_.clone(),
            },
            Expr::If {
                condition,
                then,
                else_,
                type_,
            } => Expr::If {
                condition: Box::new((**condition).to_owned()),
                then: Box::new((**then).to_owned()),
                else_: Box::new((**else_).to_owned()),
                type_: type_.clone(),
            },
            Expr::Fun { args, body, type_ } => Expr::Fun {
                args: args
                    .into_iter()
                    .map(|(id, t)| (id.to_owned(), t.clone()))
                    .collect(),
                body: Box::new((**body).to_owned()),
                type_: type_.clone(),
            },
            Expr::Call { fun, args, type_ } => Expr::Call {
                fun: Box::new((**fun).to_owned()),
                args: args.into_iter().map(|e| e.to_owned()).collect(),
                type_: type_.clone(),
            },
        }
    }
}

pub enum Decl<'a, T> {
    Fun {
        name: Ident<'a>,
        args: Vec<(Ident<'a>, T)>,
        body: Box<Expr<'a, T>>,
        type_: T,
    },
}

impl<'a, T> Decl<'a, T> {
    pub fn type_(&self) -> &T {
        match self {
            Decl::Fun { type_, .. } => type_,
        }
    }

    pub fn traverse_type<F, U, E>(self, f: F) -> Result<Decl<'a, U>, E>
    where
        F: Fn(T) -> Result<U, E> + Clone,
    {
        match self {
            Decl::Fun {
                name,
                args,
                body,
                type_,
            } => Ok(Decl::Fun {
                name,
                args: args
                    .into_iter()
                    .map(|(id, t)| Ok((id, f(t)?)))
                    .try_collect()?,
                body: Box::new(body.traverse_type(f.clone())?),
                type_: f(type_)?,
            }),
        }
    }
}
