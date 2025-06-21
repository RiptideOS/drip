use std::sync::{Arc, RwLock};

use once_cell::sync::Lazy;

#[derive(Debug, Default)]
pub struct InterningTable {
    strings: RwLock<Vec<&'static str>>,
}

pub static INTERNING_TABLE: Lazy<Arc<InterningTable>> = Lazy::new(Default::default);

impl InterningTable {
    pub fn get(&self, index: u32) -> Option<&str> {
        let strings = self.strings.read().unwrap();

        strings.get(index as usize).copied()
    }

    pub fn insert_if_absent(&self, string: &str) -> u32 {
        if let Some(index) = self.index_of(string) {
            return index;
        }

        let mut strings = self.strings.write().unwrap();

        strings.push(Box::leak(Box::new(string.to_owned())));
        (strings.len() - 1) as _
    }

    pub fn index_of(&self, string: &str) -> Option<u32> {
        let strings = self.strings.read().unwrap();

        strings.iter().position(|s| *s == string).map(|i| i as _)
    }
}

/// An index into the string interning table
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InternedSymbol(u32);

impl InternedSymbol {
    pub fn new(value: &str) -> Self {
        let index = INTERNING_TABLE.insert_if_absent(value);

        Self(index)
    }

    pub fn as_u32(self) -> u32 {
        self.0
    }

    pub fn value(&self) -> &'static str {
        INTERNING_TABLE.get(self.0).expect("Once an interned symbol is created, the string it references should never be removed from the table")
    }
}

impl core::fmt::Debug for InternedSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("InternedSymbol")
            .field(&self.0)
            .field(&self.value())
            .finish()
    }
}
