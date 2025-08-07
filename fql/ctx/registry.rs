use std::{cell::RefCell, collections::HashMap, num::NonZeroU32};

use lasso::Rodeo;
use thiserror::Error;

use crate::{ctx::Symbol, type_checker::hm_type::MonoType};

pub const TYPE_ID_INT: TypeId = TypeId::new(1);
pub const TYPE_ID_BOOL: TypeId = TypeId::new(2);
pub const TYPE_ID_STRING: TypeId = TypeId::new(3);
pub const TYPE_ID_UUID: TypeId = TypeId::new(4);

pub const BUILTINS: &[(TypeId, &str, TypeKind, u32)] = &[
    (TYPE_ID_INT, "Int", TypeKind::Builtin, 0),
    (TYPE_ID_BOOL, "Bool", TypeKind::Builtin, 0),
    (TYPE_ID_STRING, "String", TypeKind::Builtin, 0),
    (TYPE_ID_UUID, "Uuid", TypeKind::Builtin, 0),
];

#[derive(Clone, Debug, Error)]
pub enum TypeRegistryError {
    #[error(
        "Attempted to create type {name:?} within the TypeRegistry, but the type already exists"
    )]
    TypeExists { name: Symbol },
}

pub struct TypeRegistry(RefCell<TypeRegistryInner>);

#[derive(Clone, Debug)]
struct TypeRegistryInner {
    by_name: HashMap<Symbol, TypeId>,
    by_id: Vec<TypeConstructor>,
    next_type_id: TypeId,
}

impl TypeRegistryInner {
    fn next_type_id(&mut self) -> TypeId {
        let id = self.next_type_id;

        self.next_type_id.0 = self.next_type_id.0.checked_add(1).unwrap();

        id
    }
}

impl TypeRegistry {
    /// Creates a new `TypeRegistry` and initializes it with the `BUILTINS`
    /// There should only ever exist one `TypeRegistry`, and that is within the `CompileContext`
    pub fn new(interner: &mut Rodeo) -> Self {
        let mut by_name = HashMap::new();
        let mut by_id = Vec::new();
        let next_type_id = TypeId::new(BUILTINS.len() as u32 + 1);

        for (id, name, kind, arity) in BUILTINS {
            let name = interner.get_or_intern_static(name);
            by_id.push(TypeConstructor {
                type_id: *id,
                name,
                kind: kind.clone(),
                arity: *arity,
            });
            by_name.insert(name, *id);
        }

        TypeRegistry(RefCell::new(TypeRegistryInner {
            by_name,
            by_id,
            next_type_id,
        }))
    }

    /// Returns the `TypeConstructor` for a particular `TypeId`
    ///
    /// This operation should be infallible as `TypeId` can only be created by
    /// the `TypeRegistry`, so long as the registry is a singleton within the `CompileContext`
    pub fn get_type(&self, id: TypeId) -> TypeConstructor {
        // we must subtract by 1 since TypeId uses NonZeroU32 under the hood
        self.0.borrow().by_id[id.0.get() as usize - 1].clone()
    }

    pub fn get_type_id(&self, name: Symbol) -> TypeId {
        let mut inner = self.0.borrow_mut();
        if let Some(id) = inner.by_name.get(&name) {
            *id
        } else {
            let id = inner.next_type_id();
            inner.by_name.insert(name, id);
            inner.by_id.push(TypeConstructor {
                arity: 0,
                type_id: id,
                name,
                kind: TypeKind::Undefined,
            });
            id
        }
    }

    /// Registers a new type within the `TypeRegistry`
    ///
    /// Fails if the type is alr
    pub fn register_type(
        &self,
        name: Symbol,
        arity: u32,
        kind: TypeKind,
    ) -> Result<TypeId, TypeRegistryError> {
        let id = self.get_type_id(name);
        let mut inner = self.0.borrow_mut();

        let tc = &mut inner.by_id[id.0.get() as usize - 1];
        if tc.kind != TypeKind::Undefined {
            return Err(TypeRegistryError::TypeExists { name });
        }

        *tc = TypeConstructor {
            type_id: id,
            name,
            kind,
            arity,
        };

        Ok(id)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypeId(NonZeroU32);

impl TypeId {
    const fn new(id: u32) -> Self {
        Self(NonZeroU32::new(id).unwrap())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub enum TypeKind {
    #[default]
    Undefined,
    Builtin,
    Struct(HashMap<Symbol, MonoType>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeConstructor {
    pub arity: u32,
    pub type_id: TypeId,
    pub name: Symbol,
    pub kind: TypeKind,
}
