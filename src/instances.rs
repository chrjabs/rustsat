//! # Satisfiability and Optimization Instance Representations
//!
//! Types representing general satisfiability and optimization instances with
//! functionality to convert them to SAT or MaxSAT instances.

use std::{
    any::{Any, TypeId},
    collections::{hash_map::DefaultHasher, HashMap},
    fs::File,
    hash::{Hash, Hasher},
    io,
    io::Read,
    path::Path,
};

use crate::{
    clause,
    solvers::Solve,
    types::{Clause, Error, Lit, Var},
};

#[cfg(feature = "compression")]
use bzip2::read::BzDecoder;
#[cfg(feature = "compression")]
use flate2::read::GzDecoder;
#[cfg(feature = "compression")]
use std::ffi::OsStr;

mod dimacs;
pub use dimacs::DimacsError;

/// Opens a buffered reader for the file at Path.
/// With feature `compression` supports bzip2 and gzip compression.
fn open_compressed_uncompressed(path: &Path) -> Result<Box<dyn Read>, io::Error> {
    let raw_reader = File::open(path)?;
    #[cfg(feature = "compression")]
    match path.extension() {
        Some(ext) => {
            if ext.eq_ignore_ascii_case(OsStr::new("bz2")) {
                return Ok(Box::new(BzDecoder::new(raw_reader)));
            }
            if ext.eq_ignore_ascii_case(OsStr::new("gz")) {
                return Ok(Box::new(GzDecoder::new(raw_reader)));
            }
        }
        None => (),
    };
    Ok(Box::new(raw_reader))
}

/// Simple type representing a CNF formula. Other than [`SatInstance<VM>`], this
/// type only supports clauses and does have an internal variable manager.
#[derive(Clone, Debug, PartialEq)]
pub struct CNF {
    clauses: Vec<Clause>,
}

impl CNF {
    /// Creates a new CNF
    pub fn new() -> CNF {
        CNF { clauses: vec![] }
    }

    /// Creates a CNF from a vector of clauses
    pub fn from_clauses(clauses: Vec<Clause>) -> CNF {
        CNF { clauses }
    }

    /// Adds a clause to the CNF
    pub fn add_clause(&mut self, clause: Clause) {
        self.clauses.push(clause);
    }

    /// Returns the number of clauses in the instance
    pub fn n_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Adds an implication of form (a -> b) to the instance
    pub fn add_lit_impl_lit(&mut self, a: Lit, b: Lit) {
        self.add_clause(clause![!a, b])
    }

    /// Adds an implication of form a -> (b1 | b2 | ... | bm)
    pub fn add_lit_impl_clause(&mut self, a: Lit, b: Vec<Lit>) {
        let mut cl = clause![!a];
        b.into_iter().for_each(|bi| cl.add(bi));
        self.add_clause(cl)
    }

    /// Adds an implication of form a -> (b1 & b2 & ... & bm)
    pub fn add_lit_impl_cube(&mut self, a: Lit, b: Vec<Lit>) {
        b.into_iter()
            .for_each(|bi| self.add_clause(clause![!a, bi]));
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> b
    pub fn add_cube_impl_lit(&mut self, a: Vec<Lit>, b: Lit) {
        let mut cl = clause![b];
        a.into_iter().for_each(|ai| cl.add(!ai));
        self.add_clause(cl)
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> b
    pub fn add_clause_impl_lit(&mut self, a: Vec<Lit>, b: Lit) {
        for ai in &a {
            self.add_clause(clause![!*ai, b]);
        }
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> (b1 | b2 | ... | bm)
    pub fn add_cube_impl_clause(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        let mut cl = Clause::new();
        a.into_iter().for_each(|ai| cl.add(!ai));
        b.into_iter().for_each(|bi| cl.add(bi));
        self.add_clause(cl)
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> (b1 | b2 | ... | bm)
    pub fn add_clause_impl_clause(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        for ai in a {
            let mut cl = clause![!ai];
            b.iter().for_each(|bi| cl.add(*bi));
            self.add_clause(cl)
        }
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> (b1 & b2 & ... & bm)
    pub fn add_clause_impl_cube(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        for ai in &a {
            b.iter().for_each(|bi| self.add_clause(clause![!*ai, *bi]));
        }
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> (b1 & b2 & ... & bm)
    pub fn add_cube_impl_cube(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        for bi in b {
            let mut cl = clause![bi];
            a.iter().for_each(|ai| cl.add(!*ai));
            self.add_clause(cl)
        }
    }

    /// Extends the CNF by another CNF
    pub fn extend(&mut self, mut other: CNF) {
        self.clauses.append(&mut other.clauses);
    }

    /// Adds the CNF to a solver
    pub fn add_to_solver<S>(self, solver: &mut S)
    where
        S: Solve,
    {
        self.clauses
            .into_iter()
            .for_each(|cl| solver.add_clause(cl))
    }
}

/// Type representing a satisfiability instance.
/// For now this only supports clausal constraints, but more will be added.
#[derive(Clone, Debug, PartialEq)]
pub struct SatInstance<VM: ManageVars = BasicVarManager> {
    cnf: CNF,
    var_manager: VM,
}

impl<VM: ManageVars> SatInstance<VM> {
    /// Creates a new satisfiability instance
    pub fn new() -> SatInstance<VM> {
        SatInstance {
            cnf: CNF::new(),
            var_manager: VM::new(),
        }
    }

    /// Creates a new satisfiability instance with a specific var manager
    pub fn new_with_manager(var_manager: VM) -> SatInstance<VM> {
        SatInstance {
            cnf: CNF::new(),
            var_manager,
        }
    }

    /// Parse a DIMACS instance from a reader object with a specific variable manager
    pub fn from_dimacs_reader<R: Read>(reader: R) -> Result<SatInstance<VM>, Error> {
        match dimacs::parse_cnf(reader) {
            Err(dimacs_error) => Err(Error::Dimacs(dimacs_error)),
            Ok(inst) => {
                let inst = inst.change_var_manager(|mut vm| {
                    let nfv = vm.next_free();
                    let mut vm2 = VM::new();
                    vm2.increase_next_free(nfv);
                    vm2
                });
                Ok(inst)
            }
        }
    }

    /// Parse a DIMACS instance from a file path with a specific variable manager
    pub fn from_dimacs_path(path: &Path) -> Result<SatInstance<VM>, Error> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(Error::IO(why)),
            Ok(reader) => SatInstance::from_dimacs_reader(reader),
        }
    }

    /// Returns the number of clauses in the instance
    pub fn n_clauses(&self) -> usize {
        self.cnf.n_clauses()
    }

    /// Adds a clause to the instance
    pub fn add_clause(&mut self, cl: Clause) {
        cl.iter().for_each(|l| {
            self.var_manager.increase_next_free(*l.var());
        });
        self.cnf.add_clause(cl);
    }

    /// Adds an implication of form (a -> b) to the instance
    pub fn add_lit_impl_lit(&mut self, a: Lit, b: Lit) {
        self.cnf.add_lit_impl_lit(a, b);
    }

    /// Adds an implication of form a -> (b1 | b2 | ... | bm)
    pub fn add_lit_impl_clause(&mut self, a: Lit, b: Vec<Lit>) {
        self.cnf.add_lit_impl_clause(a, b);
    }

    /// Adds an implication of form a -> (b1 & b2 & ... & bm)
    pub fn add_lit_impl_cube(&mut self, a: Lit, b: Vec<Lit>) {
        self.cnf.add_lit_impl_cube(a, b);
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> b
    pub fn add_cube_impl_lit(&mut self, a: Vec<Lit>, b: Lit) {
        self.cnf.add_cube_impl_lit(a, b);
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> b
    pub fn add_clause_impl_lit(&mut self, a: Vec<Lit>, b: Lit) {
        self.cnf.add_clause_impl_lit(a, b);
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> (b1 | b2 | ... | bm)
    pub fn add_cube_impl_clause(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        self.cnf.add_cube_impl_clause(a, b);
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> (b1 | b2 | ... | bm)
    pub fn add_clause_impl_clause(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        self.cnf.add_clause_impl_clause(a, b);
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> (b1 & b2 & ... & bm)
    pub fn add_clause_impl_cube(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        self.cnf.add_clause_impl_cube(a, b);
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> (b1 & b2 & ... & bm)
    pub fn add_cube_impl_cube(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        self.cnf.add_cube_impl_cube(a, b);
    }

    /// Get a reference to the variable manager
    pub fn var_manager(&mut self) -> &mut VM {
        &mut self.var_manager
    }

    /// Converts the included variable manager to a different type
    pub fn change_var_manager<VM2, VMC>(self, vm_converter: VMC) -> SatInstance<VM2>
    where
        VM2: ManageVars,
        VMC: Fn(VM) -> VM2,
    {
        SatInstance {
            cnf: self.cnf,
            var_manager: vm_converter(self.var_manager),
        }
    }

    /// Converts the instance to a set of clauses
    pub fn as_cnf(self) -> (CNF, VM) {
        (self.cnf, self.var_manager)
    }

    /// Adds the instance to a solver
    pub fn add_to_solver<S>(self, solver: &mut S)
    where
        S: Solve,
    {
        self.cnf.add_to_solver(solver);
    }

    /// Extends the instance by another instance
    pub fn extend(&mut self, other: SatInstance<VM>) {
        self.cnf.extend(other.cnf);
        self.var_manager.combine(other.var_manager);
    }
}

#[cfg(feature = "optimization")]
/// Type representing an optimization instance.
/// The constraints are represented as a [`SatInstance`] struct.
/// For the objective, this currently supports soft clauses and soft literals.
#[derive(Clone, Debug, PartialEq)]
pub struct OptInstance<VM: ManageVars = BasicVarManager> {
    constraints: SatInstance<VM>,
    soft_lits: HashMap<Lit, usize>,
    soft_clauses: HashMap<Clause, usize>,
}

impl<VM: ManageVars> OptInstance<VM> {
    /// Creates a new optimization instance
    pub fn new() -> OptInstance<VM> {
        OptInstance {
            constraints: SatInstance::new(),
            soft_lits: HashMap::new(),
            soft_clauses: HashMap::new(),
        }
    }

    /// Creates a new optimization instance with a specific var manager
    pub fn new_with_manager(var_manager: VM) -> OptInstance<VM> {
        OptInstance {
            constraints: SatInstance::new_with_manager(var_manager),
            soft_lits: HashMap::new(),
            soft_clauses: HashMap::new(),
        }
    }

    /// Parse a DIMACS instance from a reader object
    pub fn from_dimacs_reader<R: Read>(reader: R) -> Result<OptInstance<VM>, Error> {
        match dimacs::parse_wcnf(reader) {
            Err(dimacs_error) => Err(Error::Dimacs(dimacs_error)),
            Ok(inst) => {
                let inst = inst.change_var_manager(|mut vm| {
                    let nfv = vm.next_free();
                    let mut vm2 = VM::new();
                    vm2.increase_next_free(nfv);
                    vm2
                });
                Ok(inst)
            }
        }
    }

    /// Parse a DIMACS instance from a file path
    pub fn from_dimacs_path(path: &Path) -> Result<OptInstance<VM>, Error> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(Error::IO(why)),
            Ok(reader) => OptInstance::from_dimacs_reader(reader),
        }
    }

    /// Gets a mutable reference to the hard constraints for modifying them
    pub fn get_constraints(&mut self) -> &mut SatInstance<VM> {
        &mut self.constraints
    }

    /// Adds a soft literal or updates its weight
    pub fn add_soft_lit(&mut self, w: usize, l: Lit) {
        self.constraints.var_manager.increase_next_free(*l.var());
        self.soft_lits.insert(l, w);
    }

    /// Adds a soft clause or updates its weight
    pub fn add_soft_clause(&mut self, w: usize, cl: Clause) {
        cl.iter().for_each(|l| {
            self.constraints.var_manager.increase_next_free(*l.var());
        });
        self.soft_clauses.insert(cl, w);
    }

    /// Converts the instance to a set of hard and soft clauses
    pub fn as_hard_cl_soft_cl(mut self) -> (CNF, HashMap<Clause, usize>, VM) {
        self.soft_clauses.reserve(self.soft_lits.len());
        for (l, w) in self.soft_lits {
            self.soft_clauses.insert(clause![!l], w);
        }
        let (cnf, vm) = self.constraints.as_cnf();
        (cnf, self.soft_clauses, vm)
    }

    /// Converts the instance to a set of hard clauses and soft literals
    pub fn as_hard_cl_soft_lit(mut self) -> (CNF, HashMap<Lit, usize>, VM) {
        self.soft_lits.reserve(self.soft_clauses.len());
        self.constraints
            .cnf
            .clauses
            .reserve(self.soft_clauses.len());
        for (mut cl, w) in self.soft_clauses {
            let relax_lit = self.constraints.var_manager.next_free().pos_lit();
            cl.add(relax_lit);
            self.constraints.add_clause(cl);
            self.soft_lits.insert(relax_lit, w);
        }
        let (cnf, vm) = self.constraints.as_cnf();
        (cnf, self.soft_lits, vm)
    }

    /// Converts the included variable manager to a different type
    pub fn change_var_manager<VM2, VMC>(self, vm_converter: VMC) -> OptInstance<VM2>
    where
        VM2: ManageVars,
        VMC: Fn(VM) -> VM2,
    {
        OptInstance {
            constraints: self.constraints.change_var_manager(vm_converter),
            soft_lits: self.soft_lits,
            soft_clauses: self.soft_clauses,
        }
    }
}

/// Trait for variable managers keeping track of used variables
pub trait ManageVars {
    /// Creates a new variable manager
    fn new() -> Self
    where
        Self: Sized;

    /// Uses up the next free variable
    fn next_free(&mut self) -> Var;

    /// Increases the next free variable index if the provided variable has a
    /// higher index than the next variable in the manager.
    /// Returns true if the next free index has been increased and false otherwise.
    fn increase_next_free(&mut self, v: Var) -> bool;

    /// Combines two variable managers.
    /// In case an object is in both object maps, the one of `other` has precedence.
    fn combine(&mut self, other: Self)
    where
        Self: Sized;

    /// Gets the number of used variables. Typically this is just the index of
    /// the next free variable.
    fn n_used(&self) -> usize;
}

/// Simple counter variable manager
#[derive(Debug, PartialEq, Clone)]
pub struct BasicVarManager {
    next_var: Var,
}

impl BasicVarManager {
    /// Creates a new variable manager from a next free variable
    pub fn from_next_free(next_var: Var) -> BasicVarManager {
        BasicVarManager { next_var }
    }
}

impl ManageVars for BasicVarManager {
    fn new() -> Self {
        BasicVarManager {
            next_var: Var::new(0),
        }
    }

    fn next_free(&mut self) -> Var {
        let v = self.next_var;
        self.next_var = Var::new(v.index() + 1);
        v
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

    fn n_used(&self) -> usize {
        self.next_var.index()
    }
}

/// Manager keeping track of used variables and variables associated with objects
#[derive(PartialEq)]
pub struct ObjectVarManager {
    next_var: Var,
    object_map: HashMap<Box<dyn VarKey>, Var>,
}

impl ObjectVarManager {
    /// Creates a new variable manager from a next free variable
    pub fn from_next_free(next_var: Var) -> Self {
        Self {
            next_var,
            object_map: HashMap::new(),
        }
    }

    /// Gets a variable associated with an object
    /// A new variabe is used up if the object is seen for the first time
    pub fn object_var<T>(&mut self, obj: T) -> Var
    where
        T: Eq + Hash + 'static,
    {
        let key: Box<dyn VarKey> = Box::new(obj);
        match self.object_map.get(&key) {
            Some(v) => *v,
            None => {
                let v = self.next_free();
                self.object_map.insert(key, v);
                v
            }
        }
    }
}

impl ManageVars for ObjectVarManager {
    fn new() -> Self {
        Self {
            next_var: Var::new(0),
            object_map: HashMap::new(),
        }
    }

    fn next_free(&mut self) -> Var {
        let v = self.next_var;
        self.next_var = Var::new(v.index() + 1);
        v
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

    fn n_used(&self) -> usize {
        self.next_var.index()
    }
}

/// Allows for a hash map with arbitrary key type
/// https://stackoverflow.com/a/64840069
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
        let mut h = DefaultHasher::new();
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
        let mut man = ObjectVarManager::new();
        let v1 = man.next_free();
        let v2 = man.next_free();
        let v3 = man.next_free();
        let v4 = man.next_free();
        assert_eq!(v1.index(), 0);
        assert_eq!(v2.index(), 1);
        assert_eq!(v3.index(), 2);
        assert_eq!(v4.index(), 3);
    }

    #[test]
    fn var_manager_objects() {
        let mut man = ObjectVarManager::new();
        let obj1 = ("Test", 5);
        let obj2 = vec![3, 1, 6];
        let v1 = man.object_var(obj1);
        let v2 = man.object_var(obj2);
        let v3 = man.object_var(obj1);
        assert_ne!(v1, v2);
        assert_eq!(v1, v3);
    }
}
