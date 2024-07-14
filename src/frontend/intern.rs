use std::sync::{Arc, RwLock};

use once_cell::sync::Lazy;

#[derive(Debug, Default)]
pub struct InterningTable {
    strings: RwLock<Vec<&'static str>>,
}

pub static INTERNING_TABLE: Lazy<Arc<InterningTable>> = Lazy::new(Default::default);

impl InterningTable {
    pub fn get(&self, index: usize) -> Option<&str> {
        let strings = self.strings.read().unwrap();

        strings.get(index).copied()
    }

    pub fn insert_if_absent(&self, string: &str) -> usize {
        if let Some(index) = self.index_of(string) {
            return index;
        }

        let mut strings = self.strings.write().unwrap();

        strings.push(Box::leak(Box::new(string.to_owned())));
        strings.len() - 1
    }

    pub fn index_of(&self, string: &str) -> Option<usize> {
        let strings = self.strings.read().unwrap();

        strings.iter().position(|s| *s == string)
    }
}
