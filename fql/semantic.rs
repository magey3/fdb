use std::{
    collections::{HashMap, HashSet},
    sync::atomic::{AtomicU32, Ordering},
};

use crate::{
    ast::Expr,
    ctx::{CompileContext, Symbol},
};

pub struct VarGen(AtomicU32);

impl VarGen {
    pub const fn new() -> Self {
        Self(AtomicU32::new(0))
    }

    pub fn unique(&self) -> TypeVar {
        let n = self.0.fetch_add(1, Ordering::Relaxed);
        TypeVar(n)
    }
}

impl Default for VarGen {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypeVar(pub u32);

static NEXT: VarGen = VarGen::new();

impl TypeVar {
    pub fn unique() -> Self {
        NEXT.unique()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Substitution(pub HashMap<TypeVar, MonoType>);

impl Substitution {
    pub fn new(vals: HashMap<TypeVar, MonoType>) -> Self {
        Self(vals)
    }

    /// Return other ∘ self (apply `self` first, then `other`)
    #[must_use]
    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut map = self
            .0
            .iter()
            .map(|(k, v)| (*k, v.substitute(other)))
            .collect::<HashMap<_, _>>();
        map.extend(other.0.clone());
        Substitution(map)
    }

    pub fn singleton(var: TypeVar, ty: MonoType) -> Self {
        let mut map = HashMap::new();
        map.insert(var, ty);
        Self(map)
    }
}

impl Default for Substitution {
    fn default() -> Self {
        Self::new(HashMap::new())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MonoType {
    Application(Symbol, Vec<Self>),
    Variable(TypeVar),
}

impl MonoType {
    pub fn substitute(&self, sub: &Substitution) -> Self {
        match self {
            MonoType::Application(name, args) => {
                MonoType::Application(*name, args.iter().map(|t| t.substitute(sub)).collect())
            }
            MonoType::Variable(tv) => sub.0.get(tv).cloned().unwrap_or_else(|| self.clone()),
        }
    }

    pub fn free_variables(&self) -> HashSet<TypeVar> {
        match self {
            MonoType::Application(_, args) => {
                args.iter().flat_map(|t| t.free_variables()).collect()
            }
            MonoType::Variable(v) => {
                let mut set = HashSet::new();
                set.insert(*v);
                set
            }
        }
    }

    pub fn contains(&self, var: TypeVar) -> bool {
        match self {
            MonoType::Application(_, ts) => ts.iter().any(|t| t.contains(var)),
            MonoType::Variable(tv) => *tv == var,
        }
    }

    pub fn generalize(&self, env: &TypeEnv) -> PolyType {
        let fvars = env.free_variables();
        let other = self.free_variables();
        let to_add = other.difference(&fvars);

        let mut out = PolyType::MonoType(self.clone());
        for &tv in to_add {
            out = PolyType::TypeQuantifier(tv, Box::new(out));
        }
        out
    }

    pub fn unify(&self, ctx: &CompileContext, other: &Self) -> Substitution {
        match (self, other) {
            (Self::Variable(a), Self::Variable(b)) if a == b => Substitution::default(),

            (Self::Variable(a), t) => {
                if t.contains(*a) {
                    panic!("infinite type");
                }
                Substitution::singleton(*a, t.clone())
            }

            (_, Self::Variable(_)) => other.unify(ctx, self),

            (Self::Application(f, f_args), Self::Application(g, g_args)) => {
                if f != g {
                    let f = ctx.resolve_string(f);
                    let g = ctx.resolve_string(g);
                    panic!("type mismatch: expected {f}, found {g}");
                }
                if f_args.len() != g_args.len() {
                    let f = ctx.resolve_string(f);
                    panic!(
                        "arity mismatch: {f} expects {} args, got {}",
                        f_args.len(),
                        g_args.len()
                    );
                }
                f_args
                    .iter()
                    .zip(g_args)
                    .fold(Substitution::default(), |acc, (a, b)| {
                        let s = a.substitute(&acc).unify(ctx, &b.substitute(&acc));
                        acc.compose(&s)
                    })
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PolyType {
    MonoType(MonoType),
    TypeQuantifier(TypeVar, Box<Self>),
}

impl PolyType {
    pub fn substitute(&self, sub: &Substitution) -> Self {
        match self {
            PolyType::MonoType(t) => PolyType::MonoType(t.substitute(sub)),
            PolyType::TypeQuantifier(binder, body) => {
                let fresh = TypeVar::unique();
                let mut inner = Substitution::default();
                for (tv, ty) in &sub.0 {
                    if tv != binder {
                        inner.0.insert(*tv, ty.clone());
                    }
                }
                inner.0.insert(*binder, MonoType::Variable(fresh));
                PolyType::TypeQuantifier(fresh, Box::new(body.substitute(&inner)))
            }
        }
    }

    pub fn free_variables(&self) -> HashSet<TypeVar> {
        match self {
            PolyType::MonoType(t) => t.free_variables(),
            PolyType::TypeQuantifier(binder, body) => {
                let mut fvs = body.free_variables();
                fvs.remove(binder);
                fvs
            }
        }
    }

    pub fn instantiate(&self, mut subs: Substitution) -> MonoType {
        match self {
            PolyType::MonoType(t) => t.substitute(&subs),
            PolyType::TypeQuantifier(tv, body) => {
                let fresh = TypeVar::unique();
                subs.0.insert(*tv, MonoType::Variable(fresh));
                body.instantiate(subs)
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct TypeEnv {
    scopes: HashMap<Symbol, PolyType>,
}

impl TypeEnv {
    pub fn new(ctx: &CompileContext) -> Self {
        Self {
            scopes: Self::prelude(ctx),
        }
    }

    pub fn prelude(ctx: &CompileContext) -> HashMap<Symbol, PolyType> {
        use MonoType::*;

        let int = || Application(ctx.intern_static("Int"), vec![]);
        let bool = || Application(ctx.intern_static("Bool"), vec![]);
        let string = || Application(ctx.intern_static("String"), vec![]);

        let arrow = |a: MonoType, b: MonoType| Application(ctx.intern_static("->"), vec![a, b]);
        let binop = |t: MonoType| arrow(t.clone(), arrow(t.clone(), t));
        let cmp = |t: MonoType| arrow(t.clone(), arrow(t.clone(), bool()));

        HashMap::from([
            (ctx.intern_static("true"), PolyType::MonoType(bool())),
            (ctx.intern_static("false"), PolyType::MonoType(bool())),
            (ctx.intern_static("+"), PolyType::MonoType(binop(int()))),
            (ctx.intern_static("-"), PolyType::MonoType(binop(int()))),
            (ctx.intern_static("*"), PolyType::MonoType(binop(int()))),
            (ctx.intern_static("/"), PolyType::MonoType(binop(int()))),
            (ctx.intern_static("=="), PolyType::MonoType(cmp(int()))),
            (ctx.intern_static("!="), PolyType::MonoType(cmp(int()))),
            (ctx.intern_static("<"), PolyType::MonoType(cmp(int()))),
            (ctx.intern_static(">"), PolyType::MonoType(cmp(int()))),
            (ctx.intern_static("<="), PolyType::MonoType(cmp(int()))),
            (ctx.intern_static(">="), PolyType::MonoType(cmp(int()))),
            (ctx.intern_static("&&"), PolyType::MonoType(binop(bool()))),
            (ctx.intern_static("||"), PolyType::MonoType(binop(bool()))),
            (
                ctx.intern_static("!"),
                PolyType::MonoType(arrow(bool(), bool())),
            ),
            (ctx.intern_static("++"), PolyType::MonoType(binop(string()))),
        ])
    }

    pub fn insert_in_current_scope(&mut self, ident: Symbol, ty: PolyType) {
        self.scopes.insert(ident, ty);
    }

    pub fn lookup_ident(&self, ctx: &CompileContext, ident: &Symbol) -> PolyType {
        self.scopes.get(ident).cloned().unwrap_or_else(|| {
            let ident = ctx.resolve_string(ident);
            panic!("unbound variable {ident}");
        })
    }

    pub fn substitute(&self, sub: &Substitution) -> Self {
        let scopes = self
            .scopes
            .iter()
            .map(|(k, v)| (*k, v.substitute(sub)))
            .collect();
        TypeEnv { scopes }
    }

    pub fn apply_substitution(&mut self, sub: &Substitution) {
        *self = self.substitute(sub);
    }

    pub fn free_variables(&self) -> HashSet<TypeVar> {
        let mut fvs = HashSet::new();
        for ty in self.scopes.values() {
            fvs.extend(ty.free_variables());
        }
        fvs
    }
}

/// Public entry point for type inference
pub fn infer(ctx: &CompileContext, expr: &Expr) -> MonoType {
    let (t, s) = w(ctx, &mut TypeEnv::new(ctx), expr);
    t.substitute(&s)
}

/// Core of Algorithm W
fn w(ctx: &CompileContext, env: &mut TypeEnv, expr: &Expr) -> (MonoType, Substitution) {
    match expr {
        Expr::String(_) => (
            MonoType::Application(ctx.intern_static("String"), vec![]),
            Substitution::default(),
        ),
        Expr::Number(_) => (
            MonoType::Application(ctx.intern_static("Int"), vec![]),
            Substitution::default(),
        ),
        Expr::Ident(name) => {
            let poly = env.lookup_ident(ctx, name);
            let mono = poly.instantiate(Substitution::default());
            (mono, Substitution::default())
        }
        Expr::Application(e1, e2) => {
            let (t1, s1) = w(ctx, env, e1);
            let mut env1 = env.substitute(&s1);
            let (t2, s2) = w(ctx, &mut env1, e2);

            let beta = TypeVar::unique();
            let arrow = MonoType::Application(
                ctx.intern_static("->"),
                vec![t2.substitute(&s2), MonoType::Variable(beta)],
            );
            let s3 = t1.substitute(&s2).unify(ctx, &arrow);

            let s = s3.compose(&s2).compose(&s1);
            env.apply_substitution(&s);
            (MonoType::Variable(beta).substitute(&s), s)
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
            let mut result = t_body;
            for tv in arg_ts.into_iter().rev() {
                result = MonoType::Application(
                    ctx.intern_static("->"),
                    vec![tv.substitute(&s_body), result],
                );
            }
            (result, s_body)
        }
        Expr::Let { ident, value, expr } => {
            let (t1, s1) = w(ctx, env, value);
            let mut env2 = env.clone();
            let qt = t1.generalize(&env2);
            env2.insert_in_current_scope(**ident, qt);
            env2.apply_substitution(&s1);
            let (t2, s2) = w(ctx, &mut env2, expr);
            (t2, s2.compose(&s1))
        }
        Expr::Infix { .. } | Expr::Prefix { .. } => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Expr, Span, Spanned};
    use chumsky::span::Span as _;

    fn empty_span() -> Span {
        Span::new((), 0..0)
    }
    fn spanned<T: Clone + PartialEq>(v: T) -> Spanned<T> {
        Spanned(v, empty_span())
    }

    #[test]
    fn test_unification() {
        let ctx = CompileContext::default();
        // identical vars
        let v = TypeVar::unique();
        assert_eq!(
            MonoType::Variable(v).unify(&ctx, &MonoType::Variable(v)),
            Substitution::default()
        );
        // var with concrete
        let v2 = TypeVar::unique();
        let int_t = MonoType::Application(ctx.intern_static("Int"), vec![]);
        assert_eq!(
            MonoType::Variable(v2).unify(&ctx, &int_t),
            Substitution::singleton(v2, int_t.clone())
        );
    }

    #[test]
    #[should_panic(expected = "type mismatch")]
    fn test_unify_mismatch() {
        let ctx = CompileContext::default();
        MonoType::Application(ctx.intern_static("Int"), vec![]).unify(
            &ctx,
            &MonoType::Application(ctx.intern_static("Bool"), vec![]),
        );
    }

    #[test]
    fn test_number_literal() {
        let ctx = CompileContext::default();
        assert_eq!(
            infer(&ctx, &Expr::Number(42)),
            MonoType::Application(ctx.intern_static("Int"), vec![])
        );
    }

    #[test]
    fn test_string_literal() {
        let ctx = CompileContext::default();
        assert_eq!(
            infer(&ctx, &Expr::String(ctx.intern_static("hi"))),
            MonoType::Application(ctx.intern_static("String"), vec![])
        );
    }

    #[test]
    fn test_identity_function() {
        let ctx = CompileContext::default();
        let id = Expr::Lambda(
            vec![spanned(ctx.intern_static("x"))],
            Box::new(spanned(Expr::Ident(ctx.intern_static("x")))),
        );
        if let MonoType::Application(arr, args) = infer(&ctx, &id) {
            assert_eq!(arr, ctx.intern_static("->"));
            assert_eq!(args.len(), 2);
            match (&args[0], &args[1]) {
                (MonoType::Variable(v1), MonoType::Variable(v2)) => assert_eq!(v1, v2),
                _ => panic!("expected two identical vars"),
            }
        } else {
            panic!("expected arrow");
        }
    }

    #[test]
    #[should_panic(expected = "arity mismatch")]
    fn test_unify_arity_mismatch() {
        let ctx = CompileContext::default();
        let t1 = MonoType::Application(
            ctx.intern_static("->"),
            vec![
                MonoType::Application(ctx.intern_static("Int"), vec![]),
                MonoType::Application(ctx.intern_static("String"), vec![]),
            ],
        );
        let t2 = MonoType::Application(
            ctx.intern_static("->"),
            vec![
                MonoType::Application(ctx.intern_static("Int"), vec![]),
                MonoType::Application(ctx.intern_static("String"), vec![]),
                MonoType::Application(ctx.intern_static("Bool"), vec![]),
            ],
        );
        t1.unify(&ctx, &t2);
    }

    #[test]
    fn test_bool_literal() {
        let ctx = CompileContext::default();
        let ty_true = infer(&ctx, &Expr::Ident(ctx.intern_static("true")));
        assert_eq!(
            ty_true,
            MonoType::Application(ctx.intern_static("Bool"), vec![])
        );
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
        if let MonoType::Application(arr1, top_args) = ty {
            assert_eq!(arr1, ctx.intern_static("->"));
            assert_eq!(top_args.len(), 2);
            let t1 = &top_args[0];
            if let MonoType::Application(arr2, inner_args) = &top_args[1] {
                assert_eq!(*arr2, ctx.intern_static("->"));
                assert_eq!(inner_args.len(), 2);
                // result must match first arg
                assert!(
                    matches!((t1, &inner_args[1]),
                             (MonoType::Variable(v1),
                              MonoType::Variable(v2)) if v1 == v2),
                    "const: result must match first argument"
                );
                // second arg is a fresh var
                assert!(
                    matches!(inner_args[0], MonoType::Variable(_)),
                    "const: second arg must be a fresh var"
                );
            } else {
                panic!("const: expected nested arrow");
            }
        } else {
            panic!("const: expected arrow type");
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
        assert_eq!(ty, MonoType::Application(ctx.intern_static("Int"), vec![]));
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
        assert_eq!(ty, MonoType::Application(ctx.intern_static("Int"), vec![]));
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
        assert_eq!(ty, MonoType::Application(ctx.intern_static("Int"), vec![]));
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
        assert_eq!(ty, MonoType::Application(ctx.intern_static("Bool"), vec![]));
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
        assert_eq!(
            ty,
            MonoType::Application(ctx.intern_static("String"), vec![])
        );
    }
}
