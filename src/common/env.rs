use std::collections::HashMap;
use std::mem;

use crate::ast::Ident;

/// A lexical environment
#[derive(Debug, PartialEq, Eq)]
pub struct Env<'ast, V>(Vec<HashMap<&'ast Ident<'ast>, V>>);

impl<'ast, V> Default for Env<'ast, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'ast, V> Env<'ast, V> {
    pub fn new() -> Self {
        Self(vec![Default::default()])
    }

    pub fn push(&mut self) {
        self.0.push(Default::default());
    }

    pub fn pop(&mut self) {
        self.0.pop();
    }

    pub fn save(&mut self) -> Self {
        mem::take(self)
    }

    pub fn restore(&mut self, saved: Self) {
        *self = saved;
    }

    pub fn set(&mut self, k: &'ast Ident<'ast>, v: V) {
        self.0.last_mut().unwrap().insert(k, v);
    }

    pub fn resolve<'a>(&'a self, k: &'ast Ident<'ast>) -> Option<&'a V> {
        for ctx in self.0.iter().rev() {
            if let Some(res) = ctx.get(k) {
                return Some(res);
            }
        }
        None
    }
}
