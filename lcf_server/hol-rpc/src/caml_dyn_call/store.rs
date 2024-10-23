use std::{
    cell::RefCell,
    fmt::{self, Display, Formatter},
    rc::Rc,
};

use ocaml_interop::BoxRoot;
use slotmap::{DefaultKey, Key as SlotMapKey, SlotMap};

pub type Obj = Rc<BoxRoot<String>>;

/// A token to an opaque OCaml value.
pub struct Token {
    key: DefaultKey,
    store: Rc<RefCell<SlotMap<DefaultKey, Obj>>>,
}

impl Display for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Token({})", self.key.data().as_ffi())
    }
}

impl Token {
    /// Get the value of the token.
    pub(crate) fn get(&self) -> Option<Obj> {
        Some(self.store.borrow().get(self.key)?.clone())
    }
}

impl Drop for Token {
    fn drop(&mut self) {
        self.store.borrow_mut().remove(self.key);
    }
}

/// A global store for OCaml values.
#[derive(Clone)]
pub struct Session {
    store: Rc<RefCell<SlotMap<DefaultKey, Obj>>>,
}

impl Session {
    /// Create a new global store.
    pub fn new() -> Self {
        Self {
            store: Rc::new(RefCell::new(SlotMap::new())),
        }
    }

    /// Store a value in the global store.
    pub(crate) fn store(&self, value: Obj) -> Token {
        Token {
            key: self.store.borrow_mut().insert(value),
            store: self.store.clone(),
        }
    }

    /// Get a value from the global store.
    pub(crate) fn get(&self, token: &Token) -> Option<Obj> {
        Some(self.store.borrow().get(token.key)?.clone())
    }
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}
