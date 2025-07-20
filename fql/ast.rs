use std::ops::{Deref, DerefMut};

use chumsky::span::SimpleSpan;

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'src> {
    // atom
    String(&'src str),
    Ident(&'src str),
    Number(u32),

    // binary operators
    Addition(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Subtraction(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Multiplication(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Division(Box<Spanned<Self>>, Box<Spanned<Self>>),
    FieldAccess(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Pipe(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Application(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Equality(Box<Spanned<Self>>, Box<Spanned<Self>>),
    NotEquality(Box<Spanned<Self>>, Box<Spanned<Self>>),
    LessThan(Box<Spanned<Self>>, Box<Spanned<Self>>),
    GreaterThan(Box<Spanned<Self>>, Box<Spanned<Self>>),
    LessThanOrEqual(Box<Spanned<Self>>, Box<Spanned<Self>>),
    GreaterThanOrEqual(Box<Spanned<Self>>, Box<Spanned<Self>>),
    And(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Or(Box<Spanned<Self>>, Box<Spanned<Self>>),

    // unary operators
    Not(Box<Spanned<Self>>),

    Lambda(Vec<Spanned<&'src str>>, Box<Spanned<Self>>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Visibility {
    Public,
    Private,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Function<'src> {
    pub name: &'src str,
    pub params: Vec<&'src str>,
    pub expr: Box<Spanned<Expr<'src>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Type<'src> {
    Named(&'src str),
    Function(Box<Spanned<Self>>, Box<Spanned<Self>>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypeAnnotation<'src> {
    pub name: &'src str,
    pub ty: Box<Spanned<Type<'src>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ModuleExport<'src> {
    pub names: Vec<&'src str>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TopLevel<'src> {
    ModuleExport(ModuleExport<'src>),
    TypeAnnotation(TypeAnnotation<'src>),
    Function(Function<'src>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Token<'src> {
    String(&'src str),
    Ident(&'src str),
    Number(u32),

    LeftParen,
    RightParen,
    Period,
    Comma,
    Semicolon,
    Colon,
    Pipe,
    Equals,

    Arrow,
    DoubleColon,

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
}

pub type Span = SimpleSpan;
#[derive(Clone, Debug)]
pub struct Spanned<T: Clone + PartialEq>(pub T, pub Span);

impl<T: Clone + PartialEq> PartialEq for Spanned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<T: Clone + PartialEq> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Clone + PartialEq> DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
