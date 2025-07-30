use std::ops::{Deref, DerefMut};

use chumsky::span::SimpleSpan;

use crate::ctx::Symbol;

#[derive(Clone, Debug, PartialEq)]
pub struct Ast {
    pub top_level: Vec<Spanned<TopLevel>>,
}

#[derive(Clone, Debug, PartialEq)]
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

#[derive(Clone, Debug, PartialEq)]
pub enum PrefixOp {
    Not,
}

#[derive(Clone, Debug, PartialEq)]
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

#[derive(Clone, Debug, PartialEq)]
pub enum Visibility {
    Public,
    Private,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Function {
    pub name: Symbol,
    pub params: Vec<Symbol>,
    pub expr: Box<Spanned<Expr>>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Named(Symbol),
    Function(Box<Spanned<Self>>, Box<Spanned<Self>>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypeAnnotation {
    pub name: Symbol,
    pub ty: Box<Spanned<Type>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ModuleExport {
    pub names: Vec<Symbol>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TopLevel {
    ModuleExport(ModuleExport),
    TypeAnnotation(TypeAnnotation),
    Function(Function),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    String(Symbol),
    Ident(Symbol),
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
    Let,
    In,
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

// impl<'src> fmt::Display for Ast<'src> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         for item in &self.top_level {
//             writeln!(f, "{}", item.0)?;
//         }
//         Ok(())
//     }
// }
//
// impl fmt::Display for TopLevel {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         match self {
//             TopLevel::ModuleExport(export) => write!(f, "{export}"),
//             TopLevel::TypeAnnotation(ann) => write!(f, "{ann}"),
//             TopLevel::Function(func) => write!(f, "{func}"),
//         }
//     }
// }
//
// impl<'src> fmt::Display for ModuleExport<'src> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         write!(f, "pub {};", self.names.join(", "))
//     }
// }
//
// impl<'src> fmt::Display for TypeAnnotation<'src> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         write!(f, "{} :: {};", self.name, self.ty.0)
//     }
// }
//
// impl<'src> fmt::Display for Function<'src> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         write!(
//             f,
//             "{} {} = {};",
//             self.name,
//             self.params.join(" "),
//             self.expr.0
//         )
//     }
// }
//
// impl<'src> fmt::Display for Expr<'src> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         match self {
//             Expr::String(s) => write!(f, "\"{s}\""),
//             Expr::Ident(i) => write!(f, "{i}"),
//             Expr::Number(n) => write!(f, "{n}"),
//             Expr::Infix { op, left, right } => {
//                 use InfixOp::*;
//                 match op {
//                     Addition => write!(f, "({} + {})", left.0, right.0),
//                     Subtraction => write!(f, "({} - {})", left.0, right.0),
//                     Multiplication => write!(f, "({} * {})", left.0, right.0),
//                     Division => write!(f, "({} / {})", left.0, right.0),
//                     FieldAccess => write!(f, "{}.{}", left.0, right.0),
//                     Pipe => write!(f, "({} |> {})", left.0, right.0),
//                     Equality => write!(f, "({} == {})", left.0, right.0),
//                     NotEquality => write!(f, "({} != {})", left.0, right.0),
//                     LessThan => write!(f, "({} < {})", left.0, right.0),
//                     GreaterThan => write!(f, "({} > {})", left.0, right.0),
//                     LessThanOrEqual => write!(f, "({} <= {})", left.0, right.0),
//                     GreaterThanOrEqual => write!(f, "({} >= {})", left.0, right.0),
//                     And => write!(f, "({} && {})", left.0, right.0),
//                     Or => write!(f, "({} || {})", left.0, right.0),
//                 }
//             }
//             Expr::Prefix { op, expr } => {
//                 use PrefixOp::*;
//                 match op {
//                     Not => write!(f, "!{}", expr.0),
//                 }
//             }
//             Expr::Application(a, b) => write!(f, "{} {}", a.0, b.0),
//             Expr::Lambda(params, body) => {
//                 let params: Vec<_> = params.iter().map(|p| p.0).collect();
//                 write!(f, "fn {} = {}", params.join(" "), body.0)
//             }
//             Expr::Let { ident, value, expr } => {
//                 write!(f, "(let {} = {} in {})", ident.0, value.0, expr.0)
//             }
//         }
//     }
// }
//
// impl<'src> fmt::Display for Type<'src> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         match self {
//             Type::Named(n) => write!(f, "{n}"),
//             Type::Function(a, b) => write!(f, "{} -> {}", a.0, b.0),
//         }
//     }
// }

// pub fn desugar<'src>(ast: &mut Ast) {
//     for toplevel in &mut ast.top_level {
//         if let TopLevel::Function(function) = &mut toplevel.0 {
//             desugar_operators(&mut function.expr)
//         }
//     }
// }
//
// pub fn desugar_operators<'src>(expr: &mut Expr) {
//     match expr {
//         Expr::Infix { op, left, right } => {
//             let op_name = match op {
//                 InfixOp::Addition => "+",
//                 InfixOp::Subtraction => "-",
//                 InfixOp::Multiplication => "*",
//                 InfixOp::Division => "/",
//                 InfixOp::Equality => "==",
//                 InfixOp::NotEquality => "!=",
//                 InfixOp::LessThan => "<",
//                 InfixOp::GreaterThan => ">",
//                 InfixOp::LessThanOrEqual => "<=",
//                 InfixOp::GreaterThanOrEqual => ">=",
//                 InfixOp::And => "&&",
//                 InfixOp::Or => "||",
//                 InfixOp::FieldAccess => ".",
//                 InfixOp::Pipe => "|>",
//             };
//             *expr = Expr::Application(
//                 Box::new(Spanned(Expr::Ident(op_name), left.1)),
//                 right.clone(),
//             );
//         }
//
//         Expr::Prefix { op, expr: inner } => {
//             let op_name = match op {
//                 PrefixOp::Not => "!",
//             };
//             *expr = Expr::Application(
//                 Box::new(Spanned(Expr::Ident(op_name), inner.1)),
//                 inner.clone(),
//             );
//         }
//
//         _ => {
//             // Recurse into sub-expressions
//             expr.walk_mut(&mut |e| desugar_operators(e));
//         }
//     }
// }
