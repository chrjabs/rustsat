//! # Satisfiability and Optimization Instance Representations
//!
//! Types representing general satisfiability and optimization instances with
//! functionality to convert them to SAT or MaxSAT instances.

use std::{
    any::{Any, TypeId},
    hash::{Hash, Hasher},
};

use crate::{
    types::{Lit, RsHashMap, RsHasher, Var},
    var,
};

mod sat;
pub use sat::{Cnf, Instance as SatInstance};

#[cfg(feature = "optimization")]
mod opt;
#[cfg(feature = "optimization")]
pub use opt::{Instance as OptInstance, Objective};

#[cfg(feature = "multiopt")]
mod multiopt;
#[cfg(feature = "multiopt")]
pub use multiopt::MultiOptInstance;

pub mod fio;

/// Trait for variable managers keeping track of used variables
pub trait ManageVars {
    /// Uses up the next free variable
    fn new_var(&mut self) -> Var;
    /// Uses up the next free variable and returns its positive literal.
    fn new_lit(&mut self) -> Lit {
        self.new_var().pos_lit()
    }
    /// Gets the used variable with the highest index
    fn max_var(&self) -> Option<Var>;
    /// Increases the next free variable index if the provided variable has a
    /// higher index than the next variable in the manager.
    /// Returns true if the next free index has been increased and false otherwise.
    fn increase_next_free(&mut self, v: Var) -> bool;
    /// Marks variables up to the given one as used. Returns true if the next
    /// free index has been increased and false otherwise.
    fn mark_used(&mut self, v: Var) -> bool {
        self.increase_next_free(v + 1)
    }
    /// Combines two variable managers.
    /// In case an object is in both object maps, the one of `other` has precedence.
    fn combine(&mut self, other: Self)
    where
        Self: Sized;
    /// Gets the number of used variables. Typically this is just the index of
    /// the next free variable.
    fn n_used(&self) -> u32;
    /// Forget variables `>= min_var`
    fn forget_from(&mut self, min_var: Var);
}

/// Trait for variable managers re-indexing an existing instance
pub trait ReindexVars: ManageVars {
    /// Gets a remapped variable for an input variable or crates a new mapping
    fn reindex(&mut self, in_var: Var) -> Var;
    /// Gets a remapped literal for an input literal
    fn reindex_lit(&mut self, in_lit: Lit) -> Lit {
        let v = self.reindex(in_lit.var());
        if in_lit.is_pos() {
            v.pos_lit()
        } else {
            v.neg_lit()
        }
    }
    /// Reverses the re-indexing of a variable
    fn reverse(&self, out_var: Var) -> Option<Var>;
    /// Reverses the re-indexing of a literal
    fn reverse_lit(&self, out_lit: Lit) -> Option<Lit> {
        self.reverse(out_lit.var()).map(|v| {
            if out_lit.is_pos() {
                v.pos_lit()
            } else {
                v.neg_lit()
            }
        })
    }
}

/// Simple counting variable manager
#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BasicVarManager {
    next_var: Var,
}

impl BasicVarManager {
    /// Creates a new variable manager from a next free variable
    #[must_use]
    pub fn from_next_free(next_var: Var) -> BasicVarManager {
        BasicVarManager { next_var }
    }
}

impl ManageVars for BasicVarManager {
    fn new_var(&mut self) -> Var {
        let v = self.next_var;
        self.next_var += 1;
        v
    }

    fn max_var(&self) -> Option<Var> {
        if self.next_var == var![0] {
            None
        } else {
            Some(self.next_var - 1)
        }
    }

    fn increase_next_free(&mut self, v: Var) -> bool {
        if v > self.next_var {
            self.next_var = v;
            return true;
        };
        false
    }

    fn combine(&mut self, other: Self) {
        if other.next_var > self.next_var {
            self.next_var = other.next_var;
        };
    }

    fn n_used(&self) -> u32 {
        self.next_var.idx32()
    }

    fn forget_from(&mut self, min_var: Var) {
        self.next_var = std::cmp::min(self.next_var, min_var);
    }
}

impl Default for BasicVarManager {
    fn default() -> Self {
        Self {
            next_var: Var::new(0),
        }
    }
}

/// Manager for re-indexing an existing instance
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ReindexingVarManager {
    next_var: Var,
    in_map: RsHashMap<Var, Var>,
    out_map: RsHashMap<Var, Var>,
}

impl ReindexingVarManager {
    /// Creates a new variable manager from a next free variable
    #[must_use]
    pub fn from_next_free(next_var: Var) -> Self {
        Self {
            next_var,
            in_map: RsHashMap::default(),
            out_map: RsHashMap::default(),
        }
    }
}

impl ReindexVars for ReindexingVarManager {
    fn reindex(&mut self, in_var: Var) -> Var {
        if let Some(v) = self.in_map.get(&in_var) {
            *v
        } else {
            let v = self.new_var();
            self.in_map.insert(in_var, v);
            self.out_map.insert(v, in_var);
            v
        }
    }

    fn reverse(&self, out_var: Var) -> Option<Var> {
        self.out_map.get(&out_var).copied()
    }
}

impl Default for ReindexingVarManager {
    fn default() -> Self {
        Self {
            next_var: Var::new(0),
            in_map: RsHashMap::default(),
            out_map: RsHashMap::default(),
        }
    }
}

impl ManageVars for ReindexingVarManager {
    fn new_var(&mut self) -> Var {
        let v = self.next_var;
        self.next_var = v + 1;
        v
    }

    fn max_var(&self) -> Option<Var> {
        if self.next_var == var![0] {
            None
        } else {
            Some(self.next_var - 1)
        }
    }

    fn increase_next_free(&mut self, v: Var) -> bool {
        if v > self.next_var {
            self.next_var = v;
            return true;
        };
        false
    }

    fn combine(&mut self, other: Self) {
        if other.next_var > self.next_var {
            self.next_var = other.next_var;
        };
        self.in_map.extend(other.in_map);
    }

    fn n_used(&self) -> u32 {
        self.next_var.idx32()
    }

    fn forget_from(&mut self, min_var: Var) {
        self.in_map.retain(|_, v| *v < min_var);
        self.out_map.retain(|v, _| *v < min_var);
        self.next_var = std::cmp::min(self.next_var, min_var);
    }
}

/// Manager keeping track of used variables and variables associated with objects
#[derive(PartialEq, Eq)]
pub struct ObjectVarManager {
    next_var: Var,
    object_map: RsHashMap<Box<dyn VarKey>, Var>,
}

impl ObjectVarManager {
    /// Creates a new variable manager from a next free variable
    #[must_use]
    pub fn from_next_free(next_var: Var) -> Self {
        Self {
            next_var,
            object_map: RsHashMap::default(),
        }
    }

    /// Gets a variable associated with an object
    /// A new variable is used up if the object is seen for the first time
    pub fn object_var<T>(&mut self, obj: T) -> Var
    where
        T: Eq + Hash + 'static,
    {
        let key: Box<dyn VarKey> = Box::new(obj);
        if let Some(v) = self.object_map.get(&key) {
            *v
        } else {
            let v = self.new_var();
            self.object_map.insert(key, v);
            v
        }
    }
}

impl Default for ObjectVarManager {
    fn default() -> Self {
        Self {
            next_var: Var::new(0),
            object_map: RsHashMap::default(),
        }
    }
}

impl ManageVars for ObjectVarManager {
    fn new_var(&mut self) -> Var {
        let v = self.next_var;
        self.next_var = v + 1;
        v
    }

    fn max_var(&self) -> Option<Var> {
        if self.next_var == var![0] {
            None
        } else {
            Some(self.next_var - 1)
        }
    }

    fn increase_next_free(&mut self, v: Var) -> bool {
        if v > self.next_var {
            self.next_var = v;
            return true;
        };
        false
    }

    fn combine(&mut self, other: Self) {
        if other.next_var > self.next_var {
            self.next_var = other.next_var;
        };
        self.object_map.extend(other.object_map);
    }

    fn n_used(&self) -> u32 {
        self.next_var.idx32()
    }

    fn forget_from(&mut self, min_var: Var) {
        self.object_map.retain(|_, v| *v < min_var);
        self.next_var = std::cmp::min(self.next_var, min_var);
    }
}

#[cfg(feature = "rand")]
/// Manager for randomly re-indexing an instance
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RandReindVarManager {
    next_var: Var,
    in_map: Vec<Var>,
    out_map: Vec<Var>,
}

#[cfg(feature = "rand")]
impl RandReindVarManager {
    /// Creates a new variable manager from a next free variable
    pub fn init(n_vars: u32) -> Self {
        use rand::seq::SliceRandom;
        let mut in_map: Vec<Var> = (0..n_vars).map(Var::new).collect();
        let mut rng = rand::rng();
        // Build randomly shuffled input map
        in_map[..].shuffle(&mut rng);
        // Build reverse map
        let mut out_map = vec![Var::new(0); n_vars as usize];
        in_map.iter().enumerate().for_each(|(idx, v)| {
            out_map[v.idx()] = Var::new(crate::utils::unreachable_err!(u32::try_from(idx)));
        });
        Self {
            next_var: Var::new(n_vars),
            in_map,
            out_map,
        }
    }
}

#[cfg(feature = "rand")]
impl ReindexVars for RandReindVarManager {
    fn reindex(&mut self, in_var: Var) -> Var {
        match self.in_map.get(in_var.idx()) {
            Some(v) => *v,
            None => {
                // Don't reindex vars that are out of initialized range
                in_var
            }
        }
    }

    fn reverse(&self, out_var: Var) -> Option<Var> {
        match self.out_map.get(out_var.idx()) {
            Some(v) => Some(*v),
            None => {
                // Vars out of the initialized range are not reindexed
                Some(out_var)
            }
        }
    }
}

#[cfg(feature = "rand")]
impl ManageVars for RandReindVarManager {
    fn new_var(&mut self) -> Var {
        let v = self.next_var;
        self.next_var = v + 1;
        v
    }

    fn max_var(&self) -> Option<Var> {
        if self.next_var == var![0] {
            None
        } else {
            Some(self.next_var - 1)
        }
    }

    fn increase_next_free(&mut self, v: Var) -> bool {
        if v > self.next_var {
            self.next_var = v;
            return true;
        };
        false
    }

    fn combine(&mut self, other: Self) {
        if other.next_var > self.next_var {
            self.next_var = other.next_var;
        };
        self.in_map.extend(other.in_map);
    }

    fn n_used(&self) -> u32 {
        self.next_var.idx32()
    }

    fn forget_from(&mut self, min_var: Var) {
        self.next_var = std::cmp::min(self.next_var, min_var);
    }
}

/// Allows for a hash map with arbitrary key type:
/// <https://stackoverflow.com/a/64840069>
trait VarKey {
    fn eq(&self, other: &dyn VarKey) -> bool;
    fn hash(&self) -> u64;
    fn as_any(&self) -> &dyn Any;
}

impl<T: Eq + Hash + 'static> VarKey for T {
    fn eq(&self, other: &dyn VarKey) -> bool {
        if let Some(other) = other.as_any().downcast_ref::<T>() {
            return self == other;
        }
        false
    }

    fn hash(&self) -> u64 {
        let mut h = RsHasher::default();
        // mix the typeid of T into the hash to make distinct types
        // provide distinct hashes
        Hash::hash(&(TypeId::of::<T>(), self), &mut h);
        h.finish()
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl PartialEq for Box<dyn VarKey> {
    fn eq(&self, other: &Self) -> bool {
        VarKey::eq(self.as_ref(), other.as_ref())
    }
}

impl Eq for Box<dyn VarKey> {}

impl Hash for Box<dyn VarKey> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let key_hash = VarKey::hash(self.as_ref());
        state.write_u64(key_hash);
    }
}

#[cfg(test)]
mod tests {
    use super::{ManageVars, ObjectVarManager};

    #[test]
    fn var_manager_sequence() {
        let mut man = ObjectVarManager::default();
        let v1 = man.new_var();
        let v2 = man.new_var();
        let v3 = man.new_var();
        let v4 = man.new_var();
        assert_eq!(v1.idx(), 0);
        assert_eq!(v2.idx(), 1);
        assert_eq!(v3.idx(), 2);
        assert_eq!(v4.idx(), 3);
    }

    #[test]
    fn var_manager_objects() {
        let mut man = ObjectVarManager::default();
        let obj1 = ("Test", 5);
        let obj2 = vec![3, 1, 6];
        let v1 = man.object_var(obj1);
        let v2 = man.object_var(obj2);
        let v3 = man.object_var(obj1);
        assert_ne!(v1, v2);
        assert_eq!(v1, v3);
    }
}
