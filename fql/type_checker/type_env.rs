use std::collections::{HashMap, HashSet};

use crate::{
    ctx::{
        CompileContext, Symbol,
        registry::{TYPE_ID_BOOL, TYPE_ID_INT, TYPE_ID_STRING},
    },
    type_checker::{
        hm_type::{MonoType, PolyType, TypeVar},
        substitution::Substitution,
    },
};

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

        let int = || Application(TYPE_ID_INT, vec![]);
        let bool = || Application(TYPE_ID_BOOL, vec![]);
        let string = || Application(TYPE_ID_STRING, vec![]);

        let arrow = |a: MonoType, b: MonoType| Function(Box::new(a), Box::new(b));
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
