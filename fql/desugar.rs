use std::collections::HashMap;

use crate::{
    ast::{Ast, Expr, Function, InfixOp, PrefixOp, Spanned, TopLevel, Type, TypeDefinition},
    ctx::{CompileContext, Symbol},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnnotatedFunction {
    pub ty: Option<Spanned<Type>>,
    pub function: Spanned<Function>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DesugaredAst {
    pub functions: Vec<AnnotatedFunction>,
    pub exports: Vec<Spanned<Symbol>>,
    pub type_defs: Vec<Spanned<TypeDefinition>>,
}

pub fn desugar(ctx: &CompileContext, mut ast: Ast) -> DesugaredAst {
    for tl in &mut ast.top_level {
        if let TopLevel::Function(func) = &mut tl.0 {
            // take ownership of the old Expr
            let mut expr = (*func.expr).clone();
            // wrap params in reverse order
            for &param in func.params.iter().rev() {
                let span = expr.span();
                let param_spanned = Spanned(param, span);
                expr = Spanned(Expr::Lambda(vec![param_spanned], Box::new(expr)), span);
            }
            func.params.clear(); // no more top‐level params
            func.expr = Box::new(expr); // install the new lambda‐expression
        }
    }

    // 2) Now desugar all infix/prefix operators inside those (now nullary)
    //    function bodies
    for tl in &mut ast.top_level {
        if let TopLevel::Function(function) = &mut tl.0 {
            desugar_operators(ctx, &mut function.expr.0);
        }
    }

    let mut type_annotations = HashMap::new();
    let mut functions = Vec::new();
    let mut type_defs = Vec::new();
    let mut exports = Vec::new();

    for tl in ast.top_level {
        match tl.0 {
            TopLevel::ModuleExport(module_export) => exports.extend(
                module_export
                    .names
                    .into_iter()
                    .map(|n| Spanned::with_span(n, tl.1)),
            ),
            TopLevel::TypeAnnotation(type_annotation) => {
                // we ignore the span here becasue we mostly care about the actual types span not
                // for the entire annotation
                type_annotations.insert(type_annotation.name, type_annotation.ty);
            }
            TopLevel::Function(function) => functions.push(Spanned::with_span(function, tl.1)),
            TopLevel::TypeDefinition(type_definition) => {
                type_defs.push(Spanned::with_span(type_definition, tl.1))
            }
        }
    }

    let annotated_functions = functions
        .into_iter()
        .map(|func| AnnotatedFunction {
            ty: type_annotations.get(&func.name).cloned(),
            function: func,
        })
        .collect();

    DesugaredAst {
        functions: annotated_functions,
        exports,
        type_defs,
    }
}

pub fn desugar_operators(ctx: &CompileContext, expr: &mut Expr) {
    match expr {
        Expr::Infix { op, left, right } => {
            // 1) Desugar sub‐expressions first
            desugar_operators(ctx, &mut *left);
            desugar_operators(ctx, &mut *right);

            // 2) Intern the operator name
            let sym = ctx.intern_static(match op {
                InfixOp::Addition => "+",
                InfixOp::Subtraction => "-",
                InfixOp::Multiplication => "*",
                InfixOp::Division => "/",
                InfixOp::Equality => "==",
                InfixOp::NotEquality => "!=",
                InfixOp::LessThan => "<",
                InfixOp::GreaterThan => ">",
                InfixOp::LessThanOrEqual => "<=",
                InfixOp::GreaterThanOrEqual => ">=",
                InfixOp::And => "&&",
                InfixOp::Or => "||",
                InfixOp::FieldAccess => ".",
                InfixOp::Pipe => "|>",
            });

            // 3) Clone the now‐desugared operands
            let lhs = left.clone();
            let rhs = right.clone();
            let lhs_span = lhs.span();

            // 4) Build `(op lhs)` then `((op lhs) rhs)`
            let op_ident = Spanned(Expr::Ident(sym), lhs.span());
            let first_app = Spanned(Expr::Application(Box::new(op_ident), lhs), lhs_span);
            *expr = Expr::Application(Box::new(first_app), rhs);
        }

        Expr::Prefix { op, expr: inner } => {
            // Desugar inside first
            desugar_operators(ctx, &mut *inner);

            let sym = ctx.intern_static(match op {
                PrefixOp::Not => "!",
            });

            let arg = inner.clone();
            let op_ident = Spanned(Expr::Ident(sym), arg.span());
            *expr = Expr::Application(Box::new(op_ident), arg);
        }

        Expr::Application(func, arg) => {
            desugar_operators(ctx, &mut *func);
            desugar_operators(ctx, &mut *arg);
        }

        Expr::Lambda(_params, body) => {
            desugar_operators(ctx, &mut *body);
        }

        Expr::Let {
            ident: _,
            value,
            expr,
        } => {
            desugar_operators(ctx, &mut *value);
            desugar_operators(ctx, &mut *expr);
        }

        // Leaf cases: nothing to do
        Expr::String(_) | Expr::Ident(_) | Expr::Number(_) => {}
    }
}
