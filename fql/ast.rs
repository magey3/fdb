use std::{
    collections::HashMap,
    fmt::Debug,
    hash::Hash,
    ops::{Deref, DerefMut},
};

use chumsky::span::SimpleSpan;

use crate::ctx::Symbol;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ast {
    pub top_level: Vec<Spanned<TopLevel>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InfixOp {
    Addition,
    Subtraction,
    Multiplication,
    Division,
    FieldAccess,
    Pipe,
    Equality,
    NotEquality,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    And,
    Or,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrefixOp {
    Not,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    // atom
    String(Symbol),
    Ident(Symbol),
    Number(u32),

    Infix {
        op: InfixOp,
        left: Box<Spanned<Self>>,
        right: Box<Spanned<Self>>,
    },
    Prefix {
        op: PrefixOp,
        expr: Box<Spanned<Self>>,
    },
    Application(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Lambda(Vec<Spanned<Symbol>>, Box<Spanned<Self>>),
    Let {
        ident: Spanned<Symbol>,
        value: Box<Spanned<Self>>,
        expr: Box<Spanned<Self>>,
    },
}

impl Expr {
    /// Depth-first mutable visitor.
    /// Calls `f` on every node and allows mutation of the node in-place.
    pub fn walk_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Expr),
    {
        // Visit the current node first.
        f(self);

        // Recurse into children.
        match self {
            Expr::String(_) | Expr::Ident(_) | Expr::Number(_) => {
                // leaf – nothing to do
            }
            Expr::Infix { left, right, .. } => {
                left.walk_mut(f);
                right.walk_mut(f);
            }
            Expr::Prefix { expr, .. } => {
                expr.walk_mut(f);
            }
            Expr::Application(left, right) => {
                left.walk_mut(f);
                right.walk_mut(f);
            }
            Expr::Lambda(_params, body) => {
                body.walk_mut(f);
            }
            Expr::Let {
                ident: _,
                value,
                expr,
            } => {
                value.walk_mut(f);
                expr.walk_mut(f);
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Private,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    pub name: Symbol,
    pub params: Vec<Symbol>,
    pub expr: Box<Spanned<Expr>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Application(Spanned<Symbol>, Vec<Spanned<Self>>),
    Function(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Struct(HashMap<Spanned<Symbol>, Spanned<Self>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeAnnotation {
    pub name: Symbol,
    pub ty: Spanned<Type>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleExport {
    pub names: Vec<Symbol>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeDefinition {
    pub name: Symbol,
    pub ty: Box<Spanned<Type>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TopLevel {
    ModuleExport(ModuleExport),
    TypeAnnotation(TypeAnnotation),
    Function(Function),
    TypeDefinition(TypeDefinition),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    String(Symbol),
    Ident(Symbol),
    Number(u32),

    LeftParen,
    RightParen,
    LeftCurlyBrace,
    RightCurlyBrace,

    Period,
    Comma,
    Semicolon,
    Pipe,
    Equals,

    Arrow,
    Colon,

    Multiplication,
    Division,
    Addition,
    Subtraction,

    Equality,
    NotEquality,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    And,
    Or,
    Not,

    Public,
    Fn,
    Let,
    In,
    Type,
}

pub type Span = SimpleSpan;
pub struct Spanned<T>(pub T, pub Span);

impl<T> Spanned<T> {
    pub fn with_span(value: T, span: Span) -> Self {
        Spanned(value, span)
    }
    pub fn span(&self) -> Span {
        self.1
    }
    pub fn value(&self) -> &T {
        &self.0
    }
    pub fn into_value(self) -> T {
        self.0
    }
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Spanned<U> {
        Spanned(f(self.0), self.1)
    }
    pub fn as_ref(&self) -> Spanned<&T> {
        Spanned(&self.0, self.1)
    }
    pub fn map_ref<U>(&self, f: impl FnOnce(&T) -> U) -> Spanned<U> {
        Spanned(f(&self.0), self.1)
    }
}

impl<T: PartialEq> PartialEq for Spanned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}
impl<T: PartialEq + Eq> Eq for Spanned<T> {}

impl<T> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: Clone> Clone for Spanned<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1)
    }
}

impl<T: Debug> Debug for Spanned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({:#?}, {:?})", self.0, self.1)
    }
}

impl<T: Hash> Hash for Spanned<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
