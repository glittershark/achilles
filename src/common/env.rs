use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::Hash;
use std::mem;

/// A lexical environment
#[derive(Debug, PartialEq, Eq)]
pub struct Env<K: Eq + Hash, V>(Vec<HashMap<K, V>>);

impl<K, V> Default for Env<K, V>
where
    K: Eq + Hash,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Env<K, V>
where
    K: Eq + Hash,
{
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

    pub fn set(&mut self, k: K, v: V) {
        self.0.last_mut().unwrap().insert(k, v);
    }

    pub fn resolve<'a, Q>(&'a self, k: &Q) -> Option<&'a V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        for ctx in self.0.iter().rev() {
            if let Some(res) = ctx.get(k) {
                return Some(res);
            }
        }
        None
    }
}
