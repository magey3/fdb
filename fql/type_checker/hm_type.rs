use std::{
    collections::HashSet,
    sync::atomic::{AtomicU32, Ordering},
};

use crate::{
    ctx::{CompileContext, Symbol},
    type_checker::{substitution::Substitution, type_env::TypeEnv},
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
