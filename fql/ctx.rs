use std::cell::RefCell;

use lasso::{Rodeo, Spur};

use crate::error::CompileError;

pub type Symbol = Spur;

pub struct CompileContext {
    pub interner: RefCell<Rodeo>,
    pub errors: RefCell<Vec<CompileError>>,
}

impl CompileContext {
    pub fn new() -> Self {
        Self {
            errors: RefCell::new(Vec::new()),
            interner: RefCell::new(Rodeo::new()),
        }
    }

    pub fn push_error(&self, error: impl Into<CompileError>) {
        self.errors.borrow_mut().push(error.into());
    }

    pub fn extend_errors(&self, errors: impl IntoIterator<Item = CompileError>) {
        self.errors.borrow_mut().extend(errors);
    }

    pub fn resolve_string(&self, sym: &Symbol) -> String {
        self.interner.borrow().resolve(sym).to_string()
    }

    pub fn intern(&self, x: impl AsRef<str>) -> Symbol {
        self.interner.borrow_mut().get_or_intern(x)
    }

    pub fn intern_static(&self, x: &'static str) -> Symbol {
        self.interner.borrow_mut().get_or_intern_static(x)
    }
}

impl Default for CompileContext {
    fn default() -> Self {
        Self::new()
    }
}
