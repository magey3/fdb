use std::{
    collections::HashSet,
    sync::atomic::{AtomicU32, Ordering},
};

use miette::Diagnostic;
use thiserror::Error;

use crate::{
    ast::Span,
    ctx::{CompileContext, registry::TypeId},
    error::{SemanticError, span_to_miette},
    type_checker::{substitution::Substitution, type_env::TypeEnv},
};

#[derive(Clone, Debug, Error, Diagnostic)]
pub enum UnificationError {
    #[error("found type recursion, remove the infinite type")]
    InfiniteType,
    #[error("type mismatch: expected {0:?}, got {1:?}")]
    TypeMismatch(TypeId, TypeId),
    #[error("arity mismatch: type constructor {0:?} expected {1} args but received {2} args")]
    ArityMismatch(TypeId, usize, usize),
}

impl UnificationError {
    pub fn into_semantic(self, ctx: &CompileContext, span: Span) -> SemanticError {
        match self {
            UnificationError::InfiniteType => SemanticError::InfiniteType {
                span: span_to_miette(span),
            },
            UnificationError::TypeMismatch(a, b) => SemanticError::TypeMismatch {
                a: ctx.resolve_string(&ctx.type_registry.get_type(a).name),
                b: ctx.resolve_string(&ctx.type_registry.get_type(b).name),
                span: span_to_miette(span),
            },
            UnificationError::ArityMismatch(_type_id, _, _) => {
                unreachable!("this shouldn't happen anymore")
            }
        }
    }
}

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
    Application(TypeId, Vec<Self>),
    Function(Box<Self>, Box<Self>),
    Variable(TypeVar),
}

impl MonoType {
    pub fn substitute(&self, sub: &Substitution) -> Self {
        match self {
            MonoType::Application(name, args) => {
                MonoType::Application(*name, args.iter().map(|t| t.substitute(sub)).collect())
            }
            MonoType::Variable(tv) => sub.0.get(tv).cloned().unwrap_or_else(|| self.clone()),
            MonoType::Function(a, b) => {
                let a = a.substitute(sub);
                let b = b.substitute(sub);
                MonoType::Function(Box::new(a), Box::new(b))
            }
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
            MonoType::Function(a, b) => {
                let mut a = a.free_variables();
                a.extend(b.free_variables());
                a
            }
        }
    }

    pub fn contains(&self, var: TypeVar) -> bool {
        match self {
            MonoType::Application(_, ts) => ts.iter().any(|t| t.contains(var)),
            MonoType::Variable(tv) => *tv == var,
            MonoType::Function(a, b) => a.contains(var) || b.contains(var),
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

    pub fn unify(&self, other: &Self) -> Result<Substitution, UnificationError> {
        Ok(match (self, other) {
            (Self::Variable(a), Self::Variable(b)) if a == b => Substitution::default(),

            (Self::Variable(a), t) => {
                if t.contains(*a) {
                    panic!("infinite type");
                }
                Substitution::singleton(*a, t.clone())
            }

            (_, Self::Variable(_)) => other.unify(self)?,

            (Self::Function(a, b), Self::Function(c, d)) => {
                let s1 = a.unify(c)?;
                let s2 = b.substitute(&s1).unify(&d.substitute(&s1))?;
                s1.compose(&s2)
            }

            (Self::Application(f, f_args), Self::Application(g, g_args)) => {
                if f != g {
                    return Err(UnificationError::TypeMismatch(*f, *g));
                }
                if f_args.len() != g_args.len() {
                    return Err(UnificationError::ArityMismatch(
                        *f,
                        f_args.len(),
                        g_args.len(),
                    ));
                }
                f_args.iter().zip(g_args).try_fold(
                    Substitution::default(),
                    |acc, (a, b)| -> Result<Substitution, UnificationError> {
                        let s = a.substitute(&acc).unify(&b.substitute(&acc))?;
                        Ok(acc.compose(&s))
                    },
                )?
            }
            (lhs, rhs) => panic!("type mismatch {lhs:?} != {rhs:?}"),
        })
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
