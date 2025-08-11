use std::collections::HashMap;

use crate::{
    ast::{Expr, Spanned, Type},
    ctx::{
        CompileContext,
        registry::{TYPE_ID_INT, TYPE_ID_STRING, TypeKind, TypeRegistryError},
    },
    desugar::DesugaredAst,
    error::{SemanticError, span_to_miette},
    type_checker::{
        hm_type::{MonoType, PolyType, TypeVar},
        substitution::Substitution,
        type_env::TypeEnv,
        typed::{Typed, TypedAst, TypedExpr, TypedFunction},
    },
};

pub mod hm_type;
pub mod substitution;
pub mod type_env;
pub mod typed;

/// Core of Algorithm W
fn w(
    ctx: &CompileContext,
    env: &mut TypeEnv,
    expr: &Spanned<Expr>,
) -> (Typed<Spanned<TypedExpr>>, Substitution) {
    let span = expr.span();
    match &expr.0 {
        Expr::String(s) => (
            Typed::with_type(
                Spanned::with_span(TypedExpr::String(*s), span),
                MonoType::Application(TYPE_ID_STRING, vec![]),
            ),
            Substitution::default(),
        ),
        Expr::Number(n) => (
            Typed::with_type(
                Spanned::with_span(TypedExpr::Number(*n), span),
                MonoType::Application(TYPE_ID_INT, vec![]),
            ),
            Substitution::default(),
        ),
        Expr::Ident(name) => {
            let poly = env.lookup_ident(ctx, name);
            let mono = poly.instantiate(Substitution::default());
            (
                Typed::with_type(Spanned::with_span(TypedExpr::Ident(*name), span), mono),
                Substitution::default(),
            )
        }
        Expr::Application(e1, e2) => {
            let (t1, s1) = w(ctx, env, e1);
            let ty1 = t1.ty();
            let mut env1 = env.substitute(&s1);
            let (t2, s2) = w(ctx, &mut env1, e2);
            let ty2 = t2.ty();

            let beta = TypeVar::unique();
            let arrow = MonoType::Function(
                Box::new(ty2.substitute(&s2)),
                Box::new(MonoType::Variable(beta)),
            );

            let s = match ty1.substitute(&s2).unify(&arrow) {
                Ok(s3) => {
                    let s = s3.compose(&s2).compose(&s1);
                    env.apply_substitution(&s);
                    s
                }
                Err(err) => {
                    ctx.push_error(err.into_semantic(ctx, span));
                    s2.compose(&s1)
                }
            };

            env.apply_substitution(&s);
            (
                Typed::with_type(
                    Spanned::with_span(TypedExpr::Application(Box::new(t1), Box::new(t2)), span),
                    MonoType::Variable(beta).substitute(&s),
                ),
                s,
            )
        }
        Expr::Lambda(args, body) => {
            let mut env2 = env.clone();
            let mut arg_ts = Vec::new();
            for arg in args {
                let tv = MonoType::Variable(TypeVar::unique());
                env2.insert_in_current_scope(**arg, PolyType::MonoType(tv.clone()));
                arg_ts.push(tv);
            }
            let (t_body, s_body) = w(ctx, &mut env2, body);
            let mut result = t_body.ty().clone();
            for tv in arg_ts.iter().rev() {
                result = MonoType::Function(Box::new(tv.substitute(&s_body)), Box::new(result));
            }
            (
                Typed::with_type(
                    Spanned::with_span(
                        TypedExpr::Lambda {
                            params: args
                                .iter()
                                .zip(arg_ts)
                                .map(|(arg, ty)| Typed::with_type(*arg, ty))
                                .collect(),

                            body: Box::new(t_body),
                        },
                        span,
                    ),
                    result,
                ),
                s_body,
            )
        }
        Expr::Let { ident, value, expr } => {
            let (e1, s1) = w(ctx, env, value);
            let t1 = e1.ty();
            let mut env2 = env.clone();
            let qt = t1.generalize(&env2);
            env2.insert_in_current_scope(**ident, qt);
            env2.apply_substitution(&s1);
            let (e2, s2) = w(ctx, &mut env2, expr);
            let t2 = e2.ty().clone();
            (
                Typed::with_type(
                    Spanned::with_span(
                        TypedExpr::Let {
                            name: *ident,
                            value: Box::new(e1),
                            body: Box::new(e2),
                        },
                        span,
                    ),
                    t2,
                ),
                s2.compose(&s1),
            )
        }
        Expr::Constructor {
            name,
            fields: ctor_fields,
        } => {
            let type_id = ctx.type_registry.get_type_id(**name);
            let ty = ctx.type_registry.get_type(type_id);

            let mut new_fields = HashMap::new();
            let mut subst = Substitution::default();
            if let TypeKind::Struct(ty_fields) = &ty.kind {
                if ctor_fields.len() != ty_fields.len()
                    || !ctor_fields.keys().all(|k| ty_fields.contains_key(k))
                {
                    ctx.push_error(SemanticError::FieldMismatch {
                        expected: ty_fields
                            .keys()
                            .map(|k| ctx.resolve_string(k))
                            .collect::<Vec<_>>()
                            .join(", "),
                        received: ctor_fields
                            .keys()
                            .map(|k| ctx.resolve_string(k))
                            .collect::<Vec<_>>()
                            .join(", "),
                        span: span_to_miette(span),
                    });
                }

                for (field_name, field_expr, field_monotype) in ctor_fields
                    .iter()
                    .flat_map(|field| ty_fields.get(field.0).map(|ty| (field.0, field.1, ty)))
                {
                    env.apply_substitution(&subst);
                    let (e, s) = w(ctx, env, field_expr);
                    let ty = e.ty().substitute(&s);
                    let unified = ty.unify(field_monotype);

                    match unified {
                        Ok(s) => {
                            subst = subst.compose(&s);
                            new_fields.insert(
                                *field_name,
                                Typed::with_type(e.into_value(), field_monotype.clone()),
                            );
                        }
                        Err(err) => ctx.push_error(err.into_semantic(ctx, field_expr.span())),
                    }
                }
            } else {
                ctx.push_error(SemanticError::ConstructorForNonStruct {
                    type_name: ctx.resolve_string(&ty.name),
                    span: span_to_miette(span),
                });
            }

            (
                Typed::with_type(
                    Spanned::with_span(
                        TypedExpr::Constructor {
                            name: *name,
                            fields: new_fields,
                        },
                        span,
                    ),
                    MonoType::Application(type_id, Vec::new()),
                ),
                subst,
            )
        }
        Expr::Infix { .. } | Expr::Prefix { .. } => unreachable!(),
    }
}

pub fn type_check(ctx: &CompileContext, ast: DesugaredAst) -> TypedAst {
    register_types(ctx, &ast);

    let mut env = TypeEnv::new(ctx);
    let mut typed_functions = Vec::new();
    let mut global_subst = Substitution::default();

    for tl in ast.functions {
        let f = tl.function;
        env.apply_substitution(&global_subst);

        let (typed_body, s) = w(ctx, &mut env, &f.expr);
        let mono = typed_body.ty().clone().substitute(&s);

        let scheme = mono.generalize(&env);
        env.insert_in_current_scope(f.name, scheme);

        typed_functions.push(Spanned::with_span(
            TypedFunction {
                name: f.name,
                params: f.params.clone(),
                expr: Box::new(typed_body),
            },
            f.span(),
        ));

        global_subst = global_subst.compose(&s);
    }

    TypedAst {
        functions: typed_functions,
    }
}

fn ast_type_to_monotype(ctx: &CompileContext, ty: &Spanned<Type>) -> MonoType {
    match ty.value() {
        Type::Application(name, params) => {
            let mut params_mono = Vec::new();
            for param in params {
                params_mono.push(ast_type_to_monotype(ctx, param));
            }
            MonoType::Application(ctx.type_registry.get_type_id(**name), params_mono)
        }
        Type::Function(a, b) => MonoType::Function(
            Box::new(ast_type_to_monotype(ctx, a)),
            Box::new(ast_type_to_monotype(ctx, b)),
        ),
        Type::Struct(_) => unimplemented!(),
    }
}

fn register_types(ctx: &CompileContext, ast: &DesugaredAst) {
    for type_def in &ast.type_defs {
        let ty = &type_def.0.ty;
        let ty = match ty.value() {
            Type::Application(..) | Type::Function(..) => {
                ctx.push_error(SemanticError::UnimplementedTypeAliasing {
                    span: span_to_miette(ty.span()),
                });
                continue;
            }
            Type::Struct(type_struct) => {
                let mut new = HashMap::new();
                for (field, value) in type_struct {
                    let val = ast_type_to_monotype(ctx, value);

                    new.insert(field.0, val);
                }

                TypeKind::Struct(new)
            }
        };
        let id = ctx.type_registry.register_type(type_def.name, 0, ty);

        if let Err(err) = id {
            let err = match err {
                TypeRegistryError::TypeExists { name } => SemanticError::TypeExists {
                    name: ctx.resolve_string(&name),
                    span: span_to_miette(type_def.span()),
                },
            };
            ctx.push_error(err);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::{Expr, Span, Spanned},
        ctx::registry::TYPE_ID_BOOL,
        desugar::desugar,
        parser::parse,
    };
    use chumsky::span::Span as _;

    fn empty_span() -> Span {
        Span::new((), 0..0)
    }
    fn spanned<T: Clone + PartialEq>(v: T) -> Spanned<T> {
        Spanned(v, empty_span())
    }

    fn infer(ctx: &CompileContext, expr: &Expr) -> MonoType {
        let (t, s) = w(ctx, &mut TypeEnv::new(ctx), &spanned(expr.clone()));
        t.ty().substitute(&s)
    }

    #[test]
    fn test_unification() {
        // identical vars
        let v = TypeVar::unique();
        assert_eq!(
            MonoType::Variable(v).unify(&MonoType::Variable(v)).unwrap(),
            Substitution::default()
        );
        // var with concrete
        let v2 = TypeVar::unique();
        let int_t = MonoType::Application(TYPE_ID_INT, vec![]);
        assert_eq!(
            MonoType::Variable(v2).unify(&int_t).unwrap(),
            Substitution::singleton(v2, int_t.clone())
        );
    }

    #[test]
    #[should_panic(expected = "TypeMismatch")]
    fn test_unify_mismatch() {
        MonoType::Application(TYPE_ID_INT, vec![])
            .unify(&MonoType::Application(TYPE_ID_BOOL, vec![]))
            .unwrap();
    }

    #[test]
    fn test_number_literal() {
        let ctx = CompileContext::default();
        assert_eq!(
            infer(&ctx, &Expr::Number(42)),
            MonoType::Application(TYPE_ID_INT, vec![])
        );
    }

    #[test]
    fn test_string_literal() {
        let ctx = CompileContext::default();
        assert_eq!(
            infer(&ctx, &Expr::String(ctx.intern_static("hi"))),
            MonoType::Application(TYPE_ID_STRING, vec![])
        );
    }

    #[test]
    fn test_identity_function() {
        let ctx = CompileContext::default();
        let id = Expr::Lambda(
            vec![spanned(ctx.intern_static("x"))],
            Box::new(spanned(Expr::Ident(ctx.intern_static("x")))),
        );
        if let MonoType::Function(arg_ty, ret_ty) = infer(&ctx, &id) {
            match (&*arg_ty, &*ret_ty) {
                (MonoType::Variable(v1), MonoType::Variable(v2)) => assert_eq!(v1, v2),
                _ => panic!("expected two identical variables"),
            }
        } else {
            panic!("expected a function type");
        }
    }

    #[test]
    fn test_bool_literal() {
        let ctx = CompileContext::default();
        let ty_true = infer(&ctx, &Expr::Ident(ctx.intern_static("true")));
        assert_eq!(ty_true, MonoType::Application(TYPE_ID_BOOL, vec![]));
    }

    #[test]
    fn test_const_function() {
        let ctx = CompileContext::default();
        // \x y -> x
        let const_expr = Expr::Lambda(
            vec![
                spanned(ctx.intern_static("x")),
                spanned(ctx.intern_static("y")),
            ],
            Box::new(spanned(Expr::Ident(ctx.intern_static("x")))),
        );
        let ty = infer(&ctx, &const_expr);
        // top‐level arrow
        if let MonoType::Function(t1, rest) = ty {
            // nested arrow
            if let MonoType::Function(t2, t3) = *rest {
                // result must match first argument
                match (&*t1, &*t3) {
                    (MonoType::Variable(v1), MonoType::Variable(v2)) if v1 == v2 => { /* ok */ }
                    _ => panic!("const: result must match first argument"),
                }
                // second parameter is a fresh var
                if let MonoType::Variable(_) = *t2 {
                    /* ok */
                } else {
                    panic!("const: second arg must be a fresh var");
                }
            } else {
                panic!("const: expected nested function arrow");
            }
        } else {
            panic!("const: expected top-level function arrow");
        }
    }

    #[test]
    fn test_id_application() {
        let ctx = CompileContext::default();
        // ( \x -> x ) 5
        let id_expr = Expr::Lambda(
            vec![spanned(ctx.intern_static("x"))],
            Box::new(spanned(Expr::Ident(ctx.intern_static("x")))),
        );
        let app = Expr::Application(
            Box::new(spanned(id_expr)),
            Box::new(spanned(Expr::Number(5))),
        );
        let ty = infer(&ctx, &app);
        assert_eq!(ty, MonoType::Application(TYPE_ID_INT, vec![]));
    }

    #[test]
    fn test_simple_let_binding() {
        // let x = 5 in x
        let ctx = CompileContext::default();
        let expr = Expr::Let {
            ident: spanned(ctx.intern_static("x")),
            value: Box::new(spanned(Expr::Number(5))),
            expr: Box::new(spanned(Expr::Ident(ctx.intern_static("x")))),
        };
        let ty = infer(&ctx, &expr);
        assert_eq!(ty, MonoType::Application(TYPE_ID_INT, vec![]));
    }

    #[test]
    fn test_let_id_application() {
        // let id = \x -> x in id 10
        let ctx = CompileContext::default();
        let id_lambda = Expr::Lambda(
            vec![spanned(ctx.intern_static("x"))],
            Box::new(spanned(Expr::Ident(ctx.intern_static("x")))),
        );
        let expr = Expr::Let {
            ident: spanned(ctx.intern_static("id")),
            value: Box::new(spanned(id_lambda)),
            expr: Box::new(spanned(Expr::Application(
                Box::new(spanned(Expr::Ident(ctx.intern_static("id")))),
                Box::new(spanned(Expr::Number(10))),
            ))),
        };
        let ty = infer(&ctx, &expr);
        assert_eq!(ty, MonoType::Application(TYPE_ID_INT, vec![]));
    }

    #[test]
    fn test_let_polymorphism() {
        // let id = \x -> x in id true
        let ctx = CompileContext::default();
        let id_lambda = Expr::Lambda(
            vec![spanned(ctx.intern_static("x"))],
            Box::new(spanned(Expr::Ident(ctx.intern_static("x")))),
        );
        let expr = Expr::Let {
            ident: spanned(ctx.intern_static("id")),
            value: Box::new(spanned(id_lambda)),
            expr: Box::new(spanned(Expr::Application(
                Box::new(spanned(Expr::Ident(ctx.intern_static("id")))),
                Box::new(spanned(Expr::Ident(ctx.intern_static("true")))),
            ))),
        };
        let ty = infer(&ctx, &expr);
        assert_eq!(ty, MonoType::Application(TYPE_ID_BOOL, vec![]));
    }

    #[test]
    fn test_nested_let_shadowing() {
        // let x = 5 in let x = "hi" in x
        let ctx = CompileContext::default();
        let inner_let = Expr::Let {
            ident: spanned(ctx.intern_static("x")),
            value: Box::new(spanned(Expr::String(ctx.intern_static("hi")))),
            expr: Box::new(spanned(Expr::Ident(ctx.intern_static("x")))),
        };
        let expr = Expr::Let {
            ident: spanned(ctx.intern_static("x")),
            value: Box::new(spanned(Expr::Number(5))),
            expr: Box::new(spanned(inner_let)),
        };
        let ty = infer(&ctx, &expr);
        assert_eq!(ty, MonoType::Application(TYPE_ID_STRING, vec![]));
    }
    /// Parse, desugar and type‐check a little program, returning
    /// both the Context (for resolving symbols) and the TypedAst.
    fn parse_and_type(src: &str) -> (CompileContext, TypedAst) {
        let ctx = CompileContext::default();
        let ast = parse(&ctx, src);
        let desugared_ast = desugar(&ctx, ast);
        let ta = type_check(&ctx, desugared_ast);
        (ctx, ta)
    }

    #[test]
    fn polymorphic_id() {
        let (ctx, ta) = {
            let ctx = CompileContext::default();
            let ast = parse(&ctx, "id a = a;");
            let desugared_ast = desugar(&ctx, ast);
            let t = type_check(&ctx, desugared_ast);
            (ctx, t)
        };
        // exactly one function: `id`
        assert_eq!(ta.functions.len(), 1);
        let f = &ta.functions[0];
        assert_eq!(ctx.resolve_string(&f.name), "id");
        assert!(f.params.is_empty());
        // id : α -> α
        match f.expr.ty() {
            MonoType::Function(a, b) => {
                assert_eq!(*a, *b);
            }
            _ => panic!("`id` did not infer to a function type"),
        }
    }

    #[test]
    fn id_on_string_returns_string() {
        let src = r#"
            id a = a;
            test = id "hello";
        "#;
        let (ctx, ta) = parse_and_type(src);
        // two functions: id, then test
        assert_eq!(ta.functions.len(), 2);
        let test_f = &ta.functions[1];
        assert_eq!(ctx.resolve_string(&test_f.name), "test");
        // test : String
        let ty = test_f.expr.ty().clone();
        let expected = MonoType::Application(TYPE_ID_STRING, vec![]);
        assert_eq!(ty, expected);
    }

    #[test]
    fn id_on_number_returns_int() {
        let src = r#"
            id a = a;
            test = id 42;
        "#;
        let (_, ta) = parse_and_type(src);
        let test_f = &ta.functions[1];
        let ty = test_f.expr.ty().clone();
        let expected = MonoType::Application(TYPE_ID_INT, vec![]);
        assert_eq!(ty, expected);
    }

    #[test]
    fn multiple_instantiations_are_independent() {
        let src = r#"
            id a = a;
            test1 = id 42;
            test2 = id "world";
        "#;
        let (_, ta) = parse_and_type(src);
        let ty1 = ta.functions[1].expr.ty().clone();
        let ty2 = ta.functions[2].expr.ty().clone();
        let int_ty = MonoType::Application(TYPE_ID_INT, vec![]);
        let str_ty = MonoType::Application(TYPE_ID_STRING, vec![]);
        assert_eq!(ty1, int_ty);
        assert_eq!(ty2, str_ty);
    }
}
