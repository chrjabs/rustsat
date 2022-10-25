//! # Satisfiability and Optimization Instance Representations
//!
//! Types representing general satisfiability and optimization instances with
//! functionality to convert them to SAT or MaxSAT instances.

use std::{
    any::{Any, TypeId},
    collections::{hash_map::DefaultHasher, HashMap},
    fmt,
    fs::File,
    hash::{Hash, Hasher},
    io,
    io::Read,
    path::Path,
    slice::{Iter, IterMut},
    vec::IntoIter,
};

use crate::{
    clause,
    types::{Clause, Lit, Var},
};

#[cfg(feature = "compression")]
use bzip2::read::BzDecoder;
#[cfg(feature = "compression")]
use flate2::read::GzDecoder;
#[cfg(feature = "compression")]
use std::ffi::OsStr;

mod dimacs;
pub use dimacs::DimacsError;

/// Combined Parsing Errors
#[derive(Debug)]
pub enum ParsingError {
    /// IO Errors
    IO(std::io::Error),
    /// Dimacs Parsing Error
    Dimacs(DimacsError),
}

impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParsingError::IO(ioe) => write!(f, "IO error: {}", ioe),
            ParsingError::Dimacs(de) => write!(f, "Dimacs error: {}", de),
        }
    }
}

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

    /// Returns an iterator over references to the clauses
    pub fn iter(&self) -> Iter<'_, Clause> {
        self.clauses.iter()
    }

    /// Returns an iterator over mutable references to the clauses
    pub fn iter_mut(&mut self) -> IterMut<'_, Clause> {
        self.clauses.iter_mut()
    }
}

impl IntoIterator for CNF {
    type Item = Clause;

    type IntoIter = IntoIter<Clause>;

    fn into_iter(self) -> Self::IntoIter {
        self.clauses.into_iter()
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
    pub fn new_with_manager(var_manager: VM) -> Self {
        SatInstance {
            cnf: CNF::new(),
            var_manager,
        }
    }

    /// Parse a DIMACS instance from a reader object with a specific variable
    /// manager.
    ///
    /// # File Format
    ///
    /// The file format expected by this parser is the DIMACS CNF format used in
    /// the SAT competition since 2011. For details on the file format see
    /// [here](http://www.satcompetition.org/2011/format-benchmarks2011.html).
    pub fn from_dimacs_reader<R: Read>(reader: R) -> Result<Self, ParsingError> {
        match dimacs::parse_cnf(reader) {
            Err(dimacs_error) => Err(ParsingError::Dimacs(dimacs_error)),
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

    /// Parse a DIMACS instance from a file path with a specific variable
    /// manager. For more details see [`SatInstance::from_dimacs_reader`].
    pub fn from_dimacs_path(path: &Path) -> Result<Self, ParsingError> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(ParsingError::IO(why)),
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
            self.var_manager.increase_next_free(l.var());
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

    /// Extends the instance by another instance
    pub fn extend(&mut self, other: SatInstance<VM>) {
        self.cnf.extend(other.cnf);
        self.var_manager.combine(other.var_manager);
    }
}

#[cfg(feature = "optimization")]
/// Type representing an optimization objective.
/// This type currently supports soft clauses and soft literals.
#[derive(Clone, Debug, PartialEq)]
pub struct Objective {
    soft_lits: HashMap<Lit, usize>,
    soft_clauses: HashMap<Clause, usize>,
}

#[cfg(feature = "optimization")]
impl Objective {
    /// Creates a new empty objective
    pub fn new() -> Self {
        Objective {
            soft_lits: HashMap::new(),
            soft_clauses: HashMap::new(),
        }
    }

    /// Adds a soft literal or updates its weight
    pub fn add_soft_lit(&mut self, w: usize, l: Lit) {
        self.soft_lits.insert(l, w);
    }

    /// Adds a soft clause or updates its weight
    pub fn add_soft_clause(&mut self, w: usize, cl: Clause) {
        if cl.len() == 1 {
            return self.add_soft_lit(w, !cl[0]);
        }
        self.soft_clauses.insert(cl, w);
    }

    /// Converts the objective to a set of soft clauses
    pub fn as_soft_cls(mut self) -> HashMap<Clause, usize> {
        self.soft_clauses.reserve(self.soft_lits.len());
        for (l, w) in self.soft_lits {
            self.soft_clauses.insert(clause![!l], w);
        }
        self.soft_clauses
    }

    /// Converts the objective to a set of hard clauses and soft literals
    pub fn as_soft_lits<VM>(mut self, var_manager: &mut VM) -> (CNF, HashMap<Lit, usize>)
    where
        VM: ManageVars,
    {
        let mut cnf = CNF::new();
        cnf.clauses.reserve(self.soft_clauses.len());
        self.soft_lits.reserve(self.soft_clauses.len());
        for (mut cl, w) in self.soft_clauses {
            if cl.len() > 1 {
                let relax_lit = var_manager.next_free().pos_lit();
                cl.add(relax_lit);
                cnf.add_clause(cl);
                self.soft_lits.insert(relax_lit, w);
            } else {
                assert!(cl.len() == 1);
                self.soft_lits.insert(!cl[0], w);
            }
        }
        (cnf, self.soft_lits)
    }
}

#[cfg(feature = "optimization")]
/// Type representing an optimization instance.
/// The constraints are represented as a [`SatInstance`] struct.
#[derive(Clone, Debug, PartialEq)]
pub struct OptInstance<VM: ManageVars = BasicVarManager> {
    constr: SatInstance<VM>,
    obj: Objective,
}

#[cfg(feature = "optimization")]
impl<VM: ManageVars> OptInstance<VM> {
    /// Creates a new optimization instance
    pub fn new() -> Self {
        OptInstance {
            constr: SatInstance::new(),
            obj: Objective::new(),
        }
    }

    /// Creates a new optimization instance with a specific var manager
    pub fn new_with_manager(var_manager: VM) -> Self {
        OptInstance {
            constr: SatInstance::new_with_manager(var_manager),
            obj: Objective::new(),
        }
    }

    /// Creates a new optimization instance from constraints and an objective
    pub fn compose(constraints: SatInstance<VM>, objective: Objective) -> Self {
        OptInstance {
            constr: constraints,
            obj: objective,
        }
    }

    /// Decomposes the optimization instance to a [`SatInstance`] and an [`Objective`]
    pub fn decompose(self) -> (SatInstance<VM>, Objective) {
        (self.constr, self.obj)
    }

    /// Parse a DIMACS instance from a reader object.
    ///
    /// # File Format
    ///
    /// The file format expected by this reader is either the [old DIMACS
    /// WCNF](https://maxsat-evaluations.github.io/2017/rules.html#input) format
    /// used in the MaxSAT evaluation before 2022 or the [new
    /// format](https://maxsat-evaluations.github.io/2022/rules.html#input) used
    /// since 2022.
    pub fn from_dimacs_reader<R: Read>(reader: R) -> Result<Self, ParsingError> {
        match dimacs::parse_wcnf(reader) {
            Err(dimacs_error) => Err(ParsingError::Dimacs(dimacs_error)),
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

    /// Parse a DIMACS instance from a file path. For more details see
    /// [`OptInstance::from_dimacs_reader`].
    pub fn from_dimacs_path(path: &Path) -> Result<Self, ParsingError> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(ParsingError::IO(why)),
            Ok(reader) => OptInstance::from_dimacs_reader(reader),
        }
    }

    /// Gets a mutable reference to the hard constraints for modifying them
    pub fn get_constraints(&mut self) -> &mut SatInstance<VM> {
        &mut self.constr
    }

    /// Gets a mutable reference to the objective for modifying it
    pub fn get_objective(&mut self) -> &mut Objective {
        &mut self.obj
    }

    /// Converts the instance to a set of hard and soft clauses
    pub fn as_hard_cls_soft_cls(self) -> (CNF, HashMap<Clause, usize>, VM) {
        let (cnf, vm) = self.constr.as_cnf();
        (cnf, self.obj.as_soft_cls(), vm)
    }

    /// Converts the instance to a set of hard clauses and soft literals
    pub fn as_hard_cls_soft_lits(self) -> (CNF, HashMap<Lit, usize>, VM) {
        let (mut cnf, mut vm) = self.constr.as_cnf();
        let (hard_softs, soft_lits) = self.obj.as_soft_lits(&mut vm);
        cnf.extend(hard_softs);
        (cnf, soft_lits, vm)
    }

    /// Converts the included variable manager to a different type
    pub fn change_var_manager<VM2, VMC>(self, vm_converter: VMC) -> OptInstance<VM2>
    where
        VM2: ManageVars,
        VMC: Fn(VM) -> VM2,
    {
        OptInstance {
            constr: self.constr.change_var_manager(vm_converter),
            obj: self.obj,
        }
    }
}

#[cfg(feature = "multiopt")]
/// Type representing a bi-objective optimization instance.
/// The constraints are represented as a [`SatInstance`] struct.
#[derive(Clone, Debug, PartialEq)]
pub struct BiOptInstance<VM: ManageVars = BasicVarManager> {
    constr: SatInstance<VM>,
    obj_1: Objective,
    obj_2: Objective,
}

#[cfg(feature = "multiopt")]
/// Type representing a bi-objective optimization instance.
impl<VM: ManageVars> BiOptInstance<VM> {
    /// Creates a new optimization instance
    pub fn new() -> Self {
        BiOptInstance {
            constr: SatInstance::new(),
            obj_1: Objective::new(),
            obj_2: Objective::new(),
        }
    }

    /// Creates a new optimization instance with a specific var manager
    pub fn new_with_manager(var_manager: VM) -> Self {
        BiOptInstance {
            constr: SatInstance::new_with_manager(var_manager),
            obj_1: Objective::new(),
            obj_2: Objective::new(),
        }
    }

    /// Creates a new optimization instance from constraints and two objectives
    pub fn compose(
        constraints: SatInstance<VM>,
        objective_1: Objective,
        objective_2: Objective,
    ) -> Self {
        BiOptInstance {
            constr: constraints,
            obj_1: objective_1,
            obj_2: objective_2,
        }
    }

    /// Decomposes the optimization instance to a [`SatInstance`] and two [`Objective`]s
    pub fn decompose(self) -> (SatInstance<VM>, Objective, Objective) {
        (self.constr, self.obj_1, self.obj_2)
    }

    /// Gets a mutable reference to the hard constraints for modifying them
    pub fn get_constraints(&mut self) -> &mut SatInstance<VM> {
        &mut self.constr
    }

    /// Gets a mutable reference to the first objective for modifying it
    pub fn get_objective_1(&mut self) -> &mut Objective {
        &mut self.obj_1
    }

    /// Gets a mutable reference to the second objective for modifying it
    pub fn get_objective_2(&mut self) -> &mut Objective {
        &mut self.obj_2
    }

    /// Converts the instance to a set of hard and soft clauses
    pub fn as_hard_cls_soft_cls(self) -> (CNF, HashMap<Clause, usize>, HashMap<Clause, usize>, VM) {
        let (cnf, vm) = self.constr.as_cnf();
        (cnf, self.obj_1.as_soft_cls(), self.obj_2.as_soft_cls(), vm)
    }

    /// Converts the instance to a set of hard clauses and soft literals
    pub fn as_hard_cls_soft_lits(self) -> (CNF, HashMap<Lit, usize>, HashMap<Lit, usize>, VM) {
        let (mut cnf, mut vm) = self.constr.as_cnf();
        let (hard_softs, soft_lits_1) = self.obj_1.as_soft_lits(&mut vm);
        cnf.extend(hard_softs);
        let (hard_softs, soft_lits_2) = self.obj_2.as_soft_lits(&mut vm);
        cnf.extend(hard_softs);
        (cnf, soft_lits_1, soft_lits_2, vm)
    }

    /// Converts the included variable manager to a different type
    pub fn change_var_manager<VM2, VMC>(self, vm_converter: VMC) -> BiOptInstance<VM2>
    where
        VM2: ManageVars,
        VMC: Fn(VM) -> VM2,
    {
        BiOptInstance {
            constr: self.constr.change_var_manager(vm_converter),
            obj_1: self.obj_1,
            obj_2: self.obj_2,
        }
    }
}

#[cfg(feature = "multiopt")]
/// Type representing a multi-objective optimization instance.
/// The constraints are represented as a [`SatInstance`] struct.
#[derive(Clone, Debug, PartialEq)]
pub struct MultiOptInstance<VM: ManageVars = BasicVarManager> {
    constr: SatInstance<VM>,
    objs: Vec<Objective>,
}

#[cfg(feature = "multiopt")]
impl<VM: ManageVars> MultiOptInstance<VM> {
    /// Creates a new optimization instance
    pub fn new(n_objs: usize) -> Self {
        MultiOptInstance {
            constr: SatInstance::new(),
            objs: {
                let mut tmp = Vec::with_capacity(n_objs);
                tmp.resize(n_objs, Objective::new());
                tmp
            },
        }
    }

    /// Creates a new optimization instance with a specific var manager
    pub fn new_with_manager(n_objs: usize, var_manager: VM) -> Self {
        MultiOptInstance {
            constr: SatInstance::new_with_manager(var_manager),
            objs: {
                let mut tmp = Vec::with_capacity(n_objs);
                tmp.resize(n_objs, Objective::new());
                tmp
            },
        }
    }

    /// Creates a new optimization instance from constraints and objectives
    pub fn compose(constraints: SatInstance<VM>, objectives: Vec<Objective>) -> Self {
        MultiOptInstance {
            constr: constraints,
            objs: objectives,
        }
    }

    /// Decomposes the optimization instance to a [`SatInstance`] and [`Objective`]s
    pub fn decompose(self) -> (SatInstance<VM>, Vec<Objective>) {
        (self.constr, self.objs)
    }

    /// Gets a mutable reference to the hard constraints for modifying them
    /// Parse a DIMACS instance from a reader object.
    ///
    /// # File Format
    ///
    /// The file format expected by this reader is an extension of the [new
    /// DIMACS WCNF
    /// format](https://maxsat-evaluations.github.io/2022/rules.html#input) to
    /// multiple objectives, which we call DIMACS MCNF. An example of this file
    /// format is the following:
    ///
    /// ```text
    /// c <comment>
    /// p mcnf
    /// h 1 2 3 0
    /// 1 5 1 0
    /// 2 7 2 3 0
    /// ```
    ///
    /// Comments start with `c`, as in other DIMACS formats. The first line that
    /// is not a comment needs to be a `p`-line indicating that this a MCNF
    /// file. After that, hard clauses start with an `h`, as in WCNF files. Soft
    /// clauses are of the following form `<obj idx> <weight> <lit 1> ... <lit
    /// n> 0`. The first token must be a positive number indicating what
    /// objective this soft clause belongs to. After that, the format is
    /// identical to a soft clause in a WCNF file.
    pub fn from_dimacs_reader<R: Read>(reader: R) -> Result<Self, ParsingError> {
        match dimacs::parse_mcnf(reader) {
            Err(dimacs_error) => Err(ParsingError::Dimacs(dimacs_error)),
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

    /// Parse a DIMACS instance from a file path. For more details see
    /// [`OptInstance::from_dimacs_reader`].
    pub fn from_dimacs_path(path: &Path) -> Result<Self, ParsingError> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(ParsingError::IO(why)),
            Ok(reader) => MultiOptInstance::from_dimacs_reader(reader),
        }
    }

    pub fn get_constraints(&mut self) -> &mut SatInstance<VM> {
        &mut self.constr
    }

    /// Gets a mutable reference to the first objective for modifying it.
    /// Make sure `obj_idx` does not exceed the number of objectives in the instance.
    pub fn get_objective(&mut self, obj_idx: usize) -> &mut Objective {
        assert!(obj_idx < self.objs.len());
        &mut self.objs[obj_idx]
    }

    /// Converts the instance to a set of hard and soft clauses
    pub fn as_hard_cls_soft_cls(self) -> (CNF, Vec<HashMap<Clause, usize>>, VM) {
        let (cnf, vm) = self.constr.as_cnf();
        let soft_cls = self.objs.into_iter().map(|o| o.as_soft_cls()).collect();
        (cnf, soft_cls, vm)
    }

    /// Converts the instance to a set of hard clauses and soft literals
    pub fn as_hard_cls_soft_lits(self) -> (CNF, Vec<HashMap<Lit, usize>>, VM) {
        let (mut cnf, mut vm) = self.constr.as_cnf();
        let soft_lits = self
            .objs
            .into_iter()
            .map(|o| {
                let (hards, softs) = o.as_soft_lits(&mut vm);
                cnf.extend(hards);
                softs
            })
            .collect();
        (cnf, soft_lits, vm)
    }

    /// Converts the included variable manager to a different type
    pub fn change_var_manager<VM2, VMC>(self, vm_converter: VMC) -> MultiOptInstance<VM2>
    where
        VM2: ManageVars,
        VMC: Fn(VM) -> VM2,
    {
        MultiOptInstance {
            constr: self.constr.change_var_manager(vm_converter),
            objs: self.objs,
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
        self.next_var = Var::new(v.idx() + 1);
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
        self.next_var.idx()
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
        self.next_var = Var::new(v.idx() + 1);
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
        self.next_var.idx()
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
        assert_eq!(v1.idx(), 0);
        assert_eq!(v2.idx(), 1);
        assert_eq!(v3.idx(), 2);
        assert_eq!(v4.idx(), 3);
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
