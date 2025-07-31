use std::{
    fmt::Debug,
    ops::{Deref, DerefMut},
};

use crate::{ast::Spanned, ctx::Symbol, type_checker::hm_type::MonoType};

#[derive(Clone, Debug)]
pub struct TypedAst {
    pub functions: Vec<Spanned<TypedFunction>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedFunction {
    pub name: Symbol,
    pub params: Vec<Symbol>,
    pub expr: Box<Typed<Spanned<TypedExpr>>>,
}

pub struct Typed<T>(T, MonoType);

impl<T> Typed<T> {
    pub fn with_type(value: T, span: MonoType) -> Self {
        Typed(value, span)
    }
    pub fn ty(&self) -> &MonoType {
        &self.1
    }
    pub fn value(&self) -> &T {
        &self.0
    }
    pub fn into_value(self) -> T {
        self.0
    }
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Typed<U> {
        Typed(f(self.0), self.1)
    }
    pub fn as_ref(&self) -> Typed<&T> {
        Typed(&self.0, self.1.clone())
    }
    pub fn map_ref<U>(&self, f: impl FnOnce(&T) -> U) -> Typed<U> {
        Typed(f(&self.0), self.1.clone())
    }
}

impl<T: PartialEq> PartialEq for Typed<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}
impl<T: PartialEq + Eq> Eq for Typed<T> {}

impl<T> Deref for Typed<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Typed<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: Clone> Clone for Typed<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1.clone())
    }
}

impl<T: Debug> Debug for Typed<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({:#?} : {:?})", self.0, self.1)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypedExpr {
    String(Symbol),
    Ident(Symbol),
    Number(u32),

    Application(Box<Typed<Spanned<Self>>>, Box<Typed<Spanned<Self>>>),
    Lambda {
        params: Vec<Typed<Spanned<Symbol>>>,
        body: Box<Typed<Spanned<Self>>>,
    },
    Let {
        name: Spanned<Symbol>,
        value: Box<Typed<Spanned<Self>>>,
        body: Box<Typed<Spanned<Self>>>,
    },
}
