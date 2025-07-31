use std::collections::HashMap;

use crate::type_checker::hm_type::{MonoType, TypeVar};

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
