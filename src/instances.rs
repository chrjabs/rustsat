//! # Satisfiability and Optimization Instance Representations
//!
//! Types representing general satisfiability and optimization instances with
//! functionality to convert them to SAT or MaxSAT instances.

use std::{
    any::{Any, TypeId},
    fmt,
    fs::File,
    hash::{Hash, Hasher},
    io::Read,
    io::{self, Write},
    path::Path,
    slice::{Iter, IterMut},
    vec::IntoIter,
};

use crate::{
    clause,
    encodings::{card, pb},
    types::{
        constraints::{CardConstraint, PBConstraint},
        Clause, Lit, RsHashMap, RsHasher, Var,
    },
    var,
};

#[cfg(feature = "compression")]
use bzip2::read::BzDecoder;
#[cfg(feature = "compression")]
use flate2::read::GzDecoder;
#[cfg(feature = "compression")]
use std::ffi::OsStr;

/// DIMACS parsing module
mod dimacs;
pub use dimacs::DimacsError;

/// OPB parsing module
mod opb;
pub use opb::OpbError;

#[cfg(feature = "optimization")]
/// An objective expressed as soft literals with an offset
pub type SoftLitsOffset = (RsHashMap<Lit, usize>, isize);
#[cfg(feature = "optimization")]
/// An objective expressed as soft clauses with an offset
pub type SoftClsOffset = (RsHashMap<Clause, usize>, isize);

/// Combined Parsing Errors
#[derive(Debug)]
pub enum ParsingError {
    /// IO Errors
    IO(std::io::Error),
    /// Dimacs Parsing Error
    Dimacs(DimacsError),
    /// OPB Parsing Error
    Opb(OpbError),
}

impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParsingError::IO(ioe) => write!(f, "IO error: {}", ioe),
            ParsingError::Dimacs(de) => write!(f, "Dimacs error: {}", de),
            ParsingError::Opb(oe) => write!(f, "OPB error: {}", oe),
        }
    }
}

/// Opens a buffered reader for the file at Path.
/// With feature `compression` supports bzip2 and gzip compression.
fn open_compressed_uncompressed<P: AsRef<Path>>(path: P) -> Result<Box<dyn Read>, io::Error> {
    let path = path.as_ref();
    let raw_reader = File::open(path)?;
    #[cfg(feature = "compression")]
    if let Some(ext) = path.extension() {
        if ext.eq_ignore_ascii_case(OsStr::new("bz2")) {
            return Ok(Box::new(BzDecoder::new(raw_reader)));
        }
        if ext.eq_ignore_ascii_case(OsStr::new("gz")) {
            return Ok(Box::new(GzDecoder::new(raw_reader)));
        }
    }
    Ok(Box::new(raw_reader))
}

/// Simple type representing a CNF formula. Other than [`SatInstance<VM>`], this
/// type only supports clauses and does have an internal variable manager.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct CNF {
    clauses: Vec<Clause>,
}

impl CNF {
    /// Creates a new CNF
    pub fn new() -> CNF {
        CNF::default()
    }

    /// Creates a CNF from a vector of clauses
    pub fn from_clauses(clauses: Vec<Clause>) -> CNF {
        CNF { clauses }
    }

    /// Adds a clause to the CNF
    pub fn add_clause(&mut self, clause: Clause) {
        self.clauses.push(clause);
    }

    /// Adds a unit clause to the CNF
    pub fn add_unit(&mut self, unit: Lit) {
        self.add_clause(clause![unit])
    }

    /// Adds a binary clause to the CNF
    pub fn add_binary(&mut self, lit1: Lit, lit2: Lit) {
        self.add_clause(clause![lit1, lit2])
    }

    /// Adds a ternary clause to the CNF
    pub fn add_ternary(&mut self, lit1: Lit, lit2: Lit, lit3: Lit) {
        self.add_clause(clause![lit1, lit2, lit3])
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

    /// Normalizes the CNF. This includes normalizing and sorting the clauses,
    /// removing duplicates and tautologies. Comparing two normalized CNFs
    /// is equal to comparing sets of sets of literals.
    pub fn normalize(self) -> Self {
        let mut norm_clauses: Vec<Clause> =
            self.into_iter().filter_map(|cl| cl.normalize()).collect();
        // Sort and filter duplicates
        norm_clauses.sort_unstable();
        norm_clauses.dedup();
        Self {
            clauses: norm_clauses,
        }
    }
}

impl IntoIterator for CNF {
    type Item = Clause;

    type IntoIter = IntoIter<Clause>;

    fn into_iter(self) -> Self::IntoIter {
        self.clauses.into_iter()
    }
}

/// Type representing a satisfiability instance. Supported constraints are
/// clauses, cardinality constraints and pseudo-boolean constraints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SatInstance<VM: ManageVars = BasicVarManager> {
    cnf: CNF,
    cards: Vec<CardConstraint>,
    pbs: Vec<PBConstraint>,
    var_manager: VM,
}

impl<VM: ManageVars> SatInstance<VM> {
    /// Creates a new satisfiability instance
    pub fn new() -> SatInstance<VM> {
        SatInstance::default()
    }

    /// Creates a new satisfiability instance with a specific var manager
    pub fn new_with_manager(var_manager: VM) -> Self {
        SatInstance {
            cnf: CNF::new(),
            cards: vec![],
            pbs: vec![],
            var_manager,
        }
    }

    /// Parses a DIMACS instance from a reader object.
    ///
    /// # File Format
    ///
    /// The file format expected by this parser is the DIMACS CNF format used in
    /// the SAT competition since 2011. For details on the file format see
    /// [here](http://www.satcompetition.org/2011/format-benchmarks2011.html).
    ///
    /// If a DIMACS WCNF or MCNF file is parsed with this method, the objectives
    /// are ignored and only the constraints returned.
    pub fn from_dimacs_reader<R: Read>(reader: R) -> Result<Self, ParsingError> {
        match dimacs::parse_cnf(reader) {
            Err(dimacs_error) => Err(ParsingError::Dimacs(dimacs_error)),
            Ok(inst) => {
                let inst = inst.change_var_manager(|mut vm| {
                    let nfv = vm.new_var();
                    let mut vm2 = VM::new();
                    vm2.increase_next_free(nfv);
                    vm2
                });
                Ok(inst)
            }
        }
    }

    /// Parses a DIMACS instance from a file path. For more details see
    /// [`SatInstance::from_dimacs_reader`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    pub fn from_dimacs_path<P: AsRef<Path>>(path: P) -> Result<Self, ParsingError> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(ParsingError::IO(why)),
            Ok(reader) => SatInstance::from_dimacs_reader(reader),
        }
    }

    /// Parses an OPB instance from a reader object.
    ///
    /// # File Format
    ///
    /// The file format expected by this parser is the OPB format for
    /// pseudo-boolean satisfaction instances. For details on the file format
    /// see [here](https://www.cril.univ-artois.fr/PB12/format.pdf).
    pub fn from_opb_reader<R: Read>(reader: R) -> Result<Self, ParsingError> {
        match opb::parse_sat(reader) {
            Err(opb_error) => Err(ParsingError::Opb(opb_error)),
            Ok(inst) => {
                let inst = inst.change_var_manager(|mut vm| {
                    let nfv = vm.new_var();
                    let mut vm2 = VM::new();
                    vm2.increase_next_free(nfv);
                    vm2
                });
                Ok(inst)
            }
        }
    }

    /// Parses an OPB instance from a file path. For more details see
    /// [`SatInstance::from_opb_reader`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    pub fn from_opb_path<P: AsRef<Path>>(path: P) -> Result<Self, ParsingError> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(ParsingError::IO(why)),
            Ok(reader) => SatInstance::from_opb_reader(reader),
        }
    }

    /// Returns the number of clauses in the instance
    pub fn n_clauses(&self) -> usize {
        self.cnf.n_clauses()
    }

    /// Adds a clause to the instance
    pub fn add_clause(&mut self, cl: Clause) {
        cl.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.cnf.add_clause(cl);
    }

    /// Adds a unit clause to the instance
    pub fn add_unit(&mut self, unit: Lit) {
        self.add_clause(clause![unit])
    }

    /// Adds a binary clause to the instance
    pub fn add_binary(&mut self, lit1: Lit, lit2: Lit) {
        self.add_clause(clause![lit1, lit2])
    }

    /// Adds a ternary clause to the instance
    pub fn add_ternary(&mut self, lit1: Lit, lit2: Lit, lit3: Lit) {
        self.add_clause(clause![lit1, lit2, lit3])
    }

    /// Adds an implication of form (a -> b) to the instance
    pub fn add_lit_impl_lit(&mut self, a: Lit, b: Lit) {
        self.var_manager.mark_used(a.var());
        self.var_manager.mark_used(b.var());
        self.cnf.add_lit_impl_lit(a, b);
    }

    /// Adds an implication of form a -> (b1 | b2 | ... | bm)
    pub fn add_lit_impl_clause(&mut self, a: Lit, b: Vec<Lit>) {
        self.var_manager.mark_used(a.var());
        b.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.cnf.add_lit_impl_clause(a, b);
    }

    /// Adds an implication of form a -> (b1 & b2 & ... & bm)
    pub fn add_lit_impl_cube(&mut self, a: Lit, b: Vec<Lit>) {
        self.var_manager.mark_used(a.var());
        b.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.cnf.add_lit_impl_cube(a, b);
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> b
    pub fn add_cube_impl_lit(&mut self, a: Vec<Lit>, b: Lit) {
        a.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.var_manager.mark_used(b.var());
        self.cnf.add_cube_impl_lit(a, b);
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> b
    pub fn add_clause_impl_lit(&mut self, a: Vec<Lit>, b: Lit) {
        a.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.var_manager.mark_used(b.var());
        self.cnf.add_clause_impl_lit(a, b);
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> (b1 | b2 | ... | bm)
    pub fn add_cube_impl_clause(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        a.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        b.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.cnf.add_cube_impl_clause(a, b);
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> (b1 | b2 | ... | bm)
    pub fn add_clause_impl_clause(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        a.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        b.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.cnf.add_clause_impl_clause(a, b);
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> (b1 & b2 & ... & bm)
    pub fn add_clause_impl_cube(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        a.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        b.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.cnf.add_clause_impl_cube(a, b);
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> (b1 & b2 & ... & bm)
    pub fn add_cube_impl_cube(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        a.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        b.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.cnf.add_cube_impl_cube(a, b);
    }

    /// Adds a cardinality constraint
    pub fn add_card_constr(&mut self, card: CardConstraint) {
        card.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.cards.push(card)
    }

    /// Adds a cardinality constraint
    pub fn add_pb_constr(&mut self, pb: PBConstraint) {
        pb.iter().for_each(|(l, _)| {
            self.var_manager.mark_used(l.var());
        });
        self.pbs.push(pb)
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
            cards: self.cards,
            pbs: self.pbs,
            var_manager: vm_converter(self.var_manager),
        }
    }

    /// Converts the instance to a set of clauses.
    /// Uses the default encoders from the `encodings` module.
    pub fn as_cnf(self) -> (CNF, VM) {
        self.as_cnf_with_encoders(
            card::default_encode_cardinality_constraint,
            pb::default_encode_pb_constraint,
        )
    }

    /// Converts the instance to a set of clauses with explicitly specified
    /// converters for non-clausal constraints.
    pub fn as_cnf_with_encoders<CardEnc, PBEnc>(
        mut self,
        mut card_encoder: CardEnc,
        mut pb_encoder: PBEnc,
    ) -> (CNF, VM)
    where
        CardEnc: FnMut(CardConstraint, &mut dyn ManageVars) -> CNF,
        PBEnc: FnMut(PBConstraint, &mut dyn ManageVars) -> CNF,
    {
        self.cards
            .into_iter()
            .for_each(|constr| self.cnf.extend(card_encoder(constr, &mut self.var_manager)));
        self.pbs
            .into_iter()
            .for_each(|constr| self.cnf.extend(pb_encoder(constr, &mut self.var_manager)));
        (self.cnf, self.var_manager)
    }

    /// Extends the instance by another instance
    pub fn extend(&mut self, other: SatInstance<VM>) {
        self.cnf.extend(other.cnf);
        self.var_manager.combine(other.var_manager);
    }

    /// Writes the instance to DIMACS CNF
    pub fn to_dimacs<W: Write>(self, writer: &mut W) -> Result<(), io::Error> {
        self.to_dimacs_with_encoders(
            card::default_encode_cardinality_constraint,
            pb::default_encode_pb_constraint,
            writer,
        )
    }

    /// Writes the instance to DIMACS CNF converting non-clausal constraints
    /// with specific encoders.
    pub fn to_dimacs_with_encoders<W, CardEnc, PBEnc>(
        self,
        card_encoder: CardEnc,
        pb_encoder: PBEnc,
        writer: &mut W,
    ) -> Result<(), io::Error>
    where
        W: Write,
        CardEnc: FnMut(CardConstraint, &mut dyn ManageVars) -> CNF,
        PBEnc: FnMut(PBConstraint, &mut dyn ManageVars) -> CNF,
    {
        let (cnf, vm) = self.as_cnf_with_encoders(card_encoder, pb_encoder);
        dimacs::write_cnf(writer, cnf, vm.max_var())
    }

    /// Writes the instance to an OPB file
    pub fn to_opb<W: Write>(self, writer: &mut W) -> Result<(), io::Error> {
        opb::write_sat(writer, self)
    }
}

impl<VM: ManageVars> Default for SatInstance<VM> {
    fn default() -> Self {
        Self {
            cnf: Default::default(),
            cards: Default::default(),
            pbs: Default::default(),
            var_manager: VM::new(),
        }
    }
}

#[cfg(feature = "optimization")]
/// Type representing an optimization objective.
/// This type currently supports soft clauses and soft literals.
/// All objectives are considered minimization objectives.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Objective {
    Weighted {
        offset: isize,
        soft_lits: RsHashMap<Lit, usize>,
        soft_clauses: RsHashMap<Clause, usize>,
    },
    Unweighted {
        offset: isize,
        unit_weight: Option<usize>,
        soft_lits: Vec<Lit>,
        soft_clauses: Vec<Clause>,
    },
}

#[cfg(feature = "optimization")]
impl Default for Objective {
    fn default() -> Self {
        Self::Unweighted {
            offset: Default::default(),
            unit_weight: Default::default(),
            soft_lits: Default::default(),
            soft_clauses: Default::default(),
        }
    }
}

#[cfg(feature = "optimization")]
impl Objective {
    /// Creates a new empty objective
    pub fn new() -> Self {
        Default::default()
    }

    /// Checks if the objective is empty
    pub fn is_empty(&self) -> bool {
        match self {
            Objective::Weighted {
                offset,
                soft_lits,
                soft_clauses,
            } => soft_lits.is_empty() && soft_clauses.is_empty() && offset == &0,
            Objective::Unweighted {
                offset,
                soft_lits,
                soft_clauses,
                ..
            } => soft_lits.is_empty() && soft_clauses.is_empty() && offset == &0,
        }
    }

    /// Sets the value offset
    pub fn set_offset(&mut self, new_offset: isize) {
        match self {
            Objective::Weighted { offset, .. } => *offset = new_offset,
            Objective::Unweighted { offset, .. } => *offset = new_offset,
        }
    }

    /// Gets the global value offset
    pub fn offset(&self) -> isize {
        match self {
            Objective::Weighted { offset, .. } => *offset,
            Objective::Unweighted { offset, .. } => *offset,
        }
    }

    /// Increases the value offset
    pub fn increase_offset(&mut self, offset_incr: isize) {
        match self {
            Objective::Weighted { offset, .. } => *offset += offset_incr,
            Objective::Unweighted { offset, .. } => *offset += offset_incr,
        }
    }

    /// Checks if the objective is weighted
    pub fn weighted(&self) -> bool {
        match self {
            Objective::Weighted { .. } => true,
            Objective::Unweighted { .. } => false,
        }
    }

    /// Converts an objective from unweighted to weighted
    fn unweighted_2_weighted(&mut self) {
        match self {
            Objective::Weighted { .. } => (),
            Objective::Unweighted {
                offset,
                unit_weight,
                soft_lits,
                soft_clauses,
            } => {
                if let Some(unit_weight) = unit_weight {
                    *self = Objective::Weighted {
                        offset: *offset,
                        soft_lits: soft_lits.iter_mut().map(|l| (*l, *unit_weight)).collect(),
                        soft_clauses: soft_clauses
                            .iter_mut()
                            .map(|cl| (cl.clone(), *unit_weight))
                            .collect(),
                    }
                } else {
                    *self = Objective::Weighted {
                        offset: *offset,
                        soft_lits: RsHashMap::default(),
                        soft_clauses: RsHashMap::default(),
                    }
                }
            }
        }
    }

    /// Converts an objective from weighted to unweighted
    fn weighted_2_unweighted(&mut self) {
        match self {
            Objective::Unweighted { .. } => (),
            Objective::Weighted {
                offset,
                soft_lits,
                soft_clauses,
            } => {
                let mut soft_unit_lits = vec![];
                soft_lits
                    .iter_mut()
                    .for_each(|(l, w)| soft_unit_lits.resize(soft_unit_lits.len() + *w, *l));
                let mut soft_unit_clauses = vec![];
                soft_clauses.iter_mut().for_each(|(cl, w)| {
                    soft_unit_clauses.resize(soft_unit_clauses.len() + *w, cl.clone())
                });
                *self = Objective::Unweighted {
                    offset: *offset,
                    unit_weight: Some(1),
                    soft_lits: soft_unit_lits,
                    soft_clauses: soft_unit_clauses,
                }
            }
        }
    }

    /// Adds a soft literal or updates its weight. Returns the old weight, if
    /// the literal was already in the objective.
    pub fn add_soft_lit(&mut self, w: usize, l: Lit) -> Option<usize> {
        match self {
            Objective::Weighted { soft_lits, .. } => {
                if w == 0 {
                    return soft_lits.remove(&l);
                }
                soft_lits.insert(l, w)
            }
            Objective::Unweighted {
                unit_weight,
                soft_lits,
                ..
            } => {
                if w == 0 {
                    if let Some(idx) = soft_lits.iter().position(|l2| l2 == &l) {
                        soft_lits.swap_remove(idx);
                        return Some(unit_weight.unwrap());
                    }
                    None
                } else {
                    match unit_weight {
                        Some(unit_weight) => {
                            if w == *unit_weight {
                                if let Some(_) = soft_lits.iter().position(|l2| l2 == &l) {
                                    return Some(*unit_weight);
                                }
                                soft_lits.push(l);
                                None
                            } else {
                                // Type changes from unweighted to weighted
                                self.unweighted_2_weighted();
                                // Add literal to new weighted objective
                                self.add_soft_lit(w, l)
                            }
                        }
                        None => {
                            soft_lits.push(l);
                            *unit_weight = Some(w);
                            None
                        }
                    }
                }
            }
        }
    }

    /// Increases the weight of a soft literal. Returns the old weight, if the
    /// literal was already in the objective.
    pub fn increase_soft_lit(&mut self, add_w: usize, l: Lit) -> Option<usize> {
        self.unweighted_2_weighted();
        match self {
            Objective::Weighted { soft_lits, .. } => match soft_lits.get_mut(&l) {
                Some(old_w) => {
                    *old_w += add_w;
                    Some(*old_w - add_w)
                }
                None => soft_lits.insert(l, add_w),
            },
            Objective::Unweighted { .. } => panic!(),
        }
    }

    /// Increases a soft literal with possibly negative weight. Internally all
    /// weights are positive, negative weights are represented by a global value
    /// offset and negated literals.
    /// This does _not_ update weights but increases them, since otherwise,
    /// adding literal l with a positive weight and afterwards -l with a
    /// negative weight would mess up the state.
    pub fn increase_soft_lit_int(&mut self, add_w: isize, l: Lit) {
        if add_w < 0 {
            self.increase_offset(add_w);
            self.increase_soft_lit(-add_w as usize, !l);
        } else {
            self.increase_soft_lit(add_w as usize, l);
        }
    }

    /// Adds a soft clause or updates its weight. Returns the old weight, if
    /// the clause was already in the objective.
    pub fn add_soft_clause(&mut self, w: usize, cl: Clause) -> Option<usize> {
        if cl.len() == 1 {
            return self.add_soft_lit(w, !cl[0]);
        }
        match self {
            Objective::Weighted { soft_clauses, .. } => {
                if w == 0 {
                    return soft_clauses.remove(&cl);
                }
                soft_clauses.insert(cl, w)
            }
            Objective::Unweighted {
                unit_weight,
                soft_clauses,
                ..
            } => {
                if w == 0 {
                    if let Some(idx) = soft_clauses.iter().position(|cl2| cl2 == &cl) {
                        soft_clauses.swap_remove(idx);
                        return Some(unit_weight.unwrap());
                    }
                    None
                } else {
                    match unit_weight {
                        Some(unit_weight) => {
                            if w == *unit_weight {
                                if let Some(_) = soft_clauses.iter().position(|cl2| cl2 == &cl) {
                                    return Some(*unit_weight);
                                }
                                soft_clauses.push(cl);
                                None
                            } else {
                                // Type changes from unweighted to weighted
                                self.unweighted_2_weighted();
                                // Add literal to new weighted objective
                                self.add_soft_clause(w, cl)
                            }
                        }
                        None => {
                            soft_clauses.push(cl);
                            *unit_weight = Some(w);
                            None
                        }
                    }
                }
            }
        }
    }

    /// Converts the objective to a set of soft clauses and an offset
    pub fn as_soft_cls(mut self) -> SoftClsOffset {
        self.unweighted_2_weighted();
        match self {
            Objective::Unweighted { .. } => panic!(),
            Objective::Weighted {
                mut soft_clauses,
                soft_lits,
                offset,
            } => {
                soft_clauses.reserve(soft_lits.len());
                for (l, w) in soft_lits {
                    soft_clauses.insert(clause![!l], w);
                }
                (soft_clauses, offset)
            }
        }
    }

    /// Converts the objective to unweighted soft clauses, a unit weight and an offset. If the
    /// objective is weighted, the soft clause will appear as often as its
    /// weight in the output vector.
    pub fn as_unweighted_soft_cls(mut self) -> (Vec<Clause>, usize, isize) {
        self.weighted_2_unweighted();
        match self {
            Objective::Weighted { .. } => panic!(),
            Objective::Unweighted {
                offset,
                unit_weight,
                soft_lits,
                mut soft_clauses,
            } => {
                if let Some(unit_weight) = unit_weight {
                    soft_clauses.reserve(soft_lits.len());
                    for l in soft_lits {
                        soft_clauses.push(clause![!l]);
                    }
                    (soft_clauses, unit_weight, offset)
                } else {
                    (vec![], 1, offset)
                }
            }
        }
    }

    /// Converts the objective to a set of hard clauses, soft literals and an offset
    pub fn as_soft_lits<VM>(mut self, var_manager: &mut VM) -> (CNF, SoftLitsOffset)
    where
        VM: ManageVars,
    {
        self.unweighted_2_weighted();
        match self {
            Objective::Unweighted { .. } => panic!(),
            Objective::Weighted {
                mut soft_lits,
                soft_clauses,
                offset,
            } => {
                let mut cnf = CNF::new();
                cnf.clauses.reserve(soft_clauses.len());
                soft_lits.reserve(soft_clauses.len());
                for (mut cl, w) in soft_clauses {
                    if cl.len() > 1 {
                        let relax_lit = var_manager.new_var().pos_lit();
                        cl.add(relax_lit);
                        cnf.add_clause(cl);
                        soft_lits.insert(relax_lit, w);
                    } else {
                        assert!(cl.len() == 1);
                        soft_lits.insert(!cl[0], w);
                    }
                }
                (cnf, (soft_lits, offset))
            }
        }
    }

    /// Converts the objective to hard clauses, unweighted soft literals, a unit
    /// weight and an offset. If the objective is weighted, the soft literals
    /// will appear as often as its weight in the output vector.
    pub fn as_unweighted_soft_lits<VM>(self, var_manager: &mut VM) -> (CNF, Vec<Lit>, usize, isize)
    where
        VM: ManageVars,
    {
        match self {
            Objective::Weighted { .. } => {
                let (cnf, softs) = self.as_soft_lits(var_manager);
                let mut soft_unit_lits = vec![];
                softs
                    .0
                    .into_iter()
                    .for_each(|(l, w)| soft_unit_lits.resize(soft_unit_lits.len() + w, l));
                (cnf, soft_unit_lits, 1, softs.1)
            }
            Objective::Unweighted {
                offset,
                unit_weight,
                mut soft_lits,
                soft_clauses,
            } => {
                if let Some(unit_weight) = unit_weight {
                    let mut cnf = CNF::new();
                    cnf.clauses.reserve(soft_clauses.len());
                    soft_lits.reserve(soft_clauses.len());
                    for mut cl in soft_clauses {
                        if cl.len() > 1 {
                            let relax_lit = var_manager.new_var().pos_lit();
                            cl.add(relax_lit);
                            cnf.add_clause(cl);
                            soft_lits.push(relax_lit);
                        } else {
                            assert!(cl.len() == 1);
                            soft_lits.push(!cl[0]);
                        }
                    }
                    (cnf, soft_lits, unit_weight, offset)
                } else {
                    (CNF::new(), vec![], 1, offset)
                }
            }
        }
    }
}

#[cfg(feature = "optimization")]
/// Type representing an optimization instance.
/// The constraints are represented as a [`SatInstance`] struct.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct OptInstance<VM: ManageVars = BasicVarManager> {
    constrs: SatInstance<VM>,
    obj: Objective,
}

#[cfg(feature = "optimization")]
impl<VM: ManageVars> OptInstance<VM> {
    /// Creates a new optimization instance
    pub fn new() -> Self {
        OptInstance {
            constrs: SatInstance::new(),
            obj: Objective::new(),
        }
    }

    /// Creates a new optimization instance with a specific var manager
    pub fn new_with_manager(var_manager: VM) -> Self {
        OptInstance {
            constrs: SatInstance::new_with_manager(var_manager),
            obj: Objective::new(),
        }
    }

    /// Creates a new optimization instance from constraints and an objective
    pub fn compose(constraints: SatInstance<VM>, objective: Objective) -> Self {
        OptInstance {
            constrs: constraints,
            obj: objective,
        }
    }

    /// Decomposes the optimization instance to a [`SatInstance`] and an [`Objective`]
    pub fn decompose(self) -> (SatInstance<VM>, Objective) {
        (self.constrs, self.obj)
    }

    /// Parses a DIMACS instance from a reader object.
    ///
    /// # File Format
    ///
    /// The file format expected by this reader is either the [old DIMACS
    /// WCNF](https://maxsat-evaluations.github.io/2017/rules.html#input) format
    /// used in the MaxSAT evaluation before 2022 or the [new
    /// format](https://maxsat-evaluations.github.io/2022/rules.html#input) used
    /// since 2022.
    ///
    /// If a DIMACS MCNF file is passed to this function, all objectives but the
    /// first are ignored.
    pub fn from_dimacs_reader<R: Read>(reader: R) -> Result<Self, ParsingError> {
        Self::from_dimacs_reader_with_idx(reader, 0)
    }

    /// Parses a DIMACS instance from a reader object, selecting the objective
    /// with index `obj_idx` if multiple are available. The index starts at 0.
    /// For more details see [`OptInstance::from_dimacs_reader`].
    pub fn from_dimacs_reader_with_idx<R: Read>(
        reader: R,
        obj_idx: usize,
    ) -> Result<Self, ParsingError> {
        match dimacs::parse_wcnf_with_idx(reader, obj_idx) {
            Err(dimacs_error) => Err(ParsingError::Dimacs(dimacs_error)),
            Ok(inst) => {
                let inst = inst.change_var_manager(|mut vm| {
                    let nfv = vm.new_var();
                    let mut vm2 = VM::new();
                    vm2.increase_next_free(nfv);
                    vm2
                });
                Ok(inst)
            }
        }
    }

    /// Parses a DIMACS instance from a file path. For more details see
    /// [`OptInstance::from_dimacs_reader`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    pub fn from_dimacs_path<P: AsRef<Path>>(path: P) -> Result<Self, ParsingError> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(ParsingError::IO(why)),
            Ok(reader) => OptInstance::from_dimacs_reader(reader),
        }
    }

    /// Parses a DIMACS instance from a file path. For more details see
    /// [`OptInstance::from_dimacs_reader_with_idx`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    pub fn from_dimacs_path_with_idx<P: AsRef<Path>>(
        path: P,
        obj_idx: usize,
    ) -> Result<Self, ParsingError> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(ParsingError::IO(why)),
            Ok(reader) => OptInstance::from_dimacs_reader_with_idx(reader, obj_idx),
        }
    }

    /// Parses an OPB instance from a reader object.
    ///
    /// # File Format
    ///
    /// The file format expected by this parser is the OPB format for
    /// pseudo-boolean optimization instances. For details on the file format
    /// see [here](https://www.cril.univ-artois.fr/PB12/format.pdf).
    pub fn from_opb_reader<R: Read>(reader: R) -> Result<Self, ParsingError> {
        OptInstance::from_opb_reader_with_idx(reader, 0)
    }

    /// Parses an OPB instance from a reader object, selecting the objective
    /// with index `obj_idx` if multiple are available. The index starts at 0.
    /// For more details see [`OptInstance::from_opb_reader`].
    pub fn from_opb_reader_with_idx<R: Read>(
        reader: R,
        obj_idx: usize,
    ) -> Result<Self, ParsingError> {
        match opb::parse_opt_with_idx(reader, obj_idx) {
            Err(opb_error) => Err(ParsingError::Opb(opb_error)),
            Ok(inst) => {
                let inst = inst.change_var_manager(|mut vm| {
                    let nfv = vm.new_var();
                    let mut vm2 = VM::new();
                    vm2.increase_next_free(nfv);
                    vm2
                });
                Ok(inst)
            }
        }
    }

    /// Parses an OPB instance from a file path. For more details see
    /// [`OptInstance::from_opb_reader`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    pub fn from_opb_path<P: AsRef<Path>>(path: P) -> Result<Self, ParsingError> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(ParsingError::IO(why)),
            Ok(reader) => OptInstance::from_opb_reader(reader),
        }
    }

    /// Parses an OPB instance from a file path, selecting the objective with
    /// index `obj_idx` if multiple are available. The index starts at 0. For
    /// more details see [`OptInstance::from_opb_reader`]. With feature
    /// `compression` supports bzip2 and gzip compression, detected by the file
    /// extension.
    pub fn from_opb_path_with_idx<P: AsRef<Path>>(
        path: P,
        obj_idx: usize,
    ) -> Result<Self, ParsingError> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(ParsingError::IO(why)),
            Ok(reader) => OptInstance::from_opb_reader_with_idx(reader, obj_idx),
        }
    }

    /// Gets a mutable reference to the hard constraints for modifying them
    pub fn get_constraints(&mut self) -> &mut SatInstance<VM> {
        &mut self.constrs
    }

    /// Gets a mutable reference to the objective for modifying it
    pub fn get_objective(&mut self) -> &mut Objective {
        &mut self.obj
    }

    /// Converts the instance to a set of hard and soft clauses, an objective
    /// offset and a variable manager
    pub fn as_hard_cls_soft_cls(self) -> (CNF, SoftClsOffset, VM) {
        let (cnf, vm) = self.constrs.as_cnf();
        (cnf, self.obj.as_soft_cls(), vm)
    }

    /// Converts the instance to a set of hard clauses and soft literals, an
    /// objective offset and a variable manager
    pub fn as_hard_cls_soft_lits(self) -> (CNF, SoftLitsOffset, VM) {
        let (mut cnf, mut vm) = self.constrs.as_cnf();
        let (hard_softs, softs) = self.obj.as_soft_lits(&mut vm);
        cnf.extend(hard_softs);
        (cnf, softs, vm)
    }

    /// Converts the included variable manager to a different type
    pub fn change_var_manager<VM2, VMC>(self, vm_converter: VMC) -> OptInstance<VM2>
    where
        VM2: ManageVars,
        VMC: Fn(VM) -> VM2,
    {
        OptInstance {
            constrs: self.constrs.change_var_manager(vm_converter),
            obj: self.obj,
        }
    }

    /// Write to DIMACS WCNF (post 22)
    pub fn to_dimacs<W: Write>(self, writer: &mut W) -> Result<(), io::Error> {
        self.to_dimacs_with_encoders(
            card::default_encode_cardinality_constraint,
            pb::default_encode_pb_constraint,
            writer,
        )
    }

    /// Writes the instance to DIMACS WCNF (post 22) converting non-clausal
    /// constraints with specific encoders.
    pub fn to_dimacs_with_encoders<W, CardEnc, PBEnc>(
        self,
        card_encoder: CardEnc,
        pb_encoder: PBEnc,
        writer: &mut W,
    ) -> Result<(), io::Error>
    where
        W: Write,
        CardEnc: FnMut(CardConstraint, &mut dyn ManageVars) -> CNF,
        PBEnc: FnMut(PBConstraint, &mut dyn ManageVars) -> CNF,
    {
        let (cnf, vm) = self.constrs.as_cnf_with_encoders(card_encoder, pb_encoder);
        let soft_cls = self.obj.as_soft_cls();
        dimacs::write_wcnf(writer, cnf, soft_cls, vm.max_var())
    }

    /// Writes the instance to an OPB file
    pub fn to_opb<W: Write>(self, writer: &mut W) -> Result<(), io::Error> {
        opb::write_opt(writer, self)
    }
}

#[cfg(feature = "multiopt")]
/// Type representing a bi-objective optimization instance.
/// The constraints are represented as a [`SatInstance`] struct.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
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

    /// Converts the instance to a set of hard and soft clauses with objective offsets
    pub fn as_hard_cls_soft_cls(self) -> (CNF, SoftClsOffset, SoftClsOffset, VM) {
        let (cnf, vm) = self.constr.as_cnf();
        (cnf, self.obj_1.as_soft_cls(), self.obj_2.as_soft_cls(), vm)
    }

    /// Converts the instance to a set of hard clauses and soft literals
    pub fn as_hard_cls_soft_lits(self) -> (CNF, SoftLitsOffset, SoftLitsOffset, VM) {
        let (mut cnf, mut vm) = self.constr.as_cnf();
        let (hard_softs, softs_1) = self.obj_1.as_soft_lits(&mut vm);
        cnf.extend(hard_softs);
        let (hard_softs, softs_2) = self.obj_2.as_soft_lits(&mut vm);
        cnf.extend(hard_softs);
        (cnf, softs_1, softs_2, vm)
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
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct MultiOptInstance<VM: ManageVars = BasicVarManager> {
    constrs: SatInstance<VM>,
    objs: Vec<Objective>,
}

#[cfg(feature = "multiopt")]
impl<VM: ManageVars> MultiOptInstance<VM> {
    /// Creates a new optimization instance
    pub fn new(n_objs: usize) -> Self {
        MultiOptInstance {
            constrs: SatInstance::new(),
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
            constrs: SatInstance::new_with_manager(var_manager),
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
            constrs: constraints,
            objs: objectives,
        }
    }

    /// Decomposes the optimization instance to a [`SatInstance`] and [`Objective`]s
    pub fn decompose(self) -> (SatInstance<VM>, Vec<Objective>) {
        (self.constrs, self.objs)
    }

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
    /// h 1 2 3 0
    /// o1 5 1 0
    /// o2 7 2 3 0
    /// ```
    ///
    /// Comments start with `c`, as in other DIMACS formats. Hard clauses start
    /// with an `h`, as in WCNF files. Soft clauses are of the following form
    /// `o<obj idx> <weight> <lit 1> ... <lit n> 0`. The first token must be a
    /// positive number preceded by an 'o', indicating what objective this soft
    /// clause belongs to. After that, the format is identical to a soft clause
    /// in a WCNF file.
    pub fn from_dimacs_reader<R: Read>(reader: R) -> Result<Self, ParsingError> {
        match dimacs::parse_mcnf(reader) {
            Err(dimacs_error) => Err(ParsingError::Dimacs(dimacs_error)),
            Ok(inst) => {
                let inst = inst.change_var_manager(|mut vm| {
                    let nfv = vm.new_var();
                    let mut vm2 = VM::new();
                    vm2.increase_next_free(nfv);
                    vm2
                });
                Ok(inst)
            }
        }
    }

    /// Parses a DIMACS instance from a file path. For more details see
    /// [`OptInstance::from_dimacs_reader`].
    pub fn from_dimacs_path<P: AsRef<Path>>(path: P) -> Result<Self, ParsingError> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(ParsingError::IO(why)),
            Ok(reader) => MultiOptInstance::from_dimacs_reader(reader),
        }
    }

    /// Parses an OPB instance from a reader object.
    ///
    /// # File Format
    ///
    /// The file format expected by this parser is the OPB format for
    /// pseudo-boolean optimization instances with multiple objectives defined.
    /// For details on the file format see
    /// [here](https://www.cril.univ-artois.fr/PB12/format.pdf).
    pub fn from_opb_reader<R: Read>(reader: R) -> Result<Self, ParsingError> {
        match opb::parse_multi_opt(reader) {
            Err(opb_error) => Err(ParsingError::Opb(opb_error)),
            Ok(inst) => {
                let inst = inst.change_var_manager(|mut vm| {
                    let nfv = vm.new_var();
                    let mut vm2 = VM::new();
                    vm2.increase_next_free(nfv);
                    vm2
                });
                Ok(inst)
            }
        }
    }

    /// Parses an OPB instance from a file path. For more details see
    /// [`MultiOptInstance::from_opb_reader`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    pub fn from_opb_path<P: AsRef<Path>>(path: P) -> Result<Self, ParsingError> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(ParsingError::IO(why)),
            Ok(reader) => MultiOptInstance::from_opb_reader(reader),
        }
    }

    /// Gets a mutable reference to the hard constraints for modifying them
    pub fn get_constraints(&mut self) -> &mut SatInstance<VM> {
        &mut self.constrs
    }

    /// Gets a mutable reference to the first objective for modifying it.
    /// Make sure `obj_idx` does not exceed the number of objectives in the instance.
    pub fn get_objective(&mut self, obj_idx: usize) -> &mut Objective {
        assert!(obj_idx < self.objs.len());
        &mut self.objs[obj_idx]
    }

    /// Converts the instance to a set of hard and soft clauses
    pub fn as_hard_cls_soft_cls(self) -> (CNF, Vec<SoftClsOffset>, VM) {
        let (cnf, vm) = self.constrs.as_cnf();
        let soft_cls = self.objs.into_iter().map(|o| o.as_soft_cls()).collect();
        (cnf, soft_cls, vm)
    }

    /// Converts the instance to a set of hard clauses and soft literals
    pub fn as_hard_cls_soft_lits(self) -> (CNF, Vec<SoftLitsOffset>, VM) {
        let (mut cnf, mut vm) = self.constrs.as_cnf();
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
            constrs: self.constrs.change_var_manager(vm_converter),
            objs: self.objs,
        }
    }

    /// Write to DIMACS MCNF
    pub fn to_dimacs<W: Write>(self, writer: &mut W) -> Result<(), io::Error> {
        self.to_dimacs_with_encoders(
            card::default_encode_cardinality_constraint,
            pb::default_encode_pb_constraint,
            writer,
        )
    }

    /// Writes the instance to DIMACS MCNF converting non-clausal constraints
    /// with specific encoders.
    pub fn to_dimacs_with_encoders<W, CardEnc, PBEnc>(
        self,
        card_encoder: CardEnc,
        pb_encoder: PBEnc,
        writer: &mut W,
    ) -> Result<(), io::Error>
    where
        W: Write,
        CardEnc: FnMut(CardConstraint, &mut dyn ManageVars) -> CNF,
        PBEnc: FnMut(PBConstraint, &mut dyn ManageVars) -> CNF,
    {
        let (cnf, mut vm) = self.constrs.as_cnf_with_encoders(card_encoder, pb_encoder);
        let soft_cls = self.objs.into_iter().map(|o| o.as_soft_cls()).collect();
        dimacs::write_mcnf(writer, cnf, soft_cls, vm.max_var())
    }

    /// Writes the instance to an OPB file
    pub fn to_opb<W: Write>(self, writer: &mut W) -> Result<(), io::Error> {
        opb::write_multi_opt(writer, self)
    }
}

/// Trait for variable managers keeping track of used variables
pub trait ManageVars {
    /// Creates a new variable manager
    fn new() -> Self
    where
        Self: Sized;
    /// Uses up the next free variable
    fn new_var(&mut self) -> Var;
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
    fn n_used(&self) -> usize;
}

/// Simple counter variable manager
#[derive(Debug, PartialEq, Eq, Clone)]
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
        Self::default()
    }

    fn new_var(&mut self) -> Var {
        let v = self.next_var;
        self.next_var = Var::new(v.idx() + 1);
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

    fn n_used(&self) -> usize {
        self.next_var.idx()
    }
}

impl Default for BasicVarManager {
    fn default() -> Self {
        Self {
            next_var: Var::new(0),
        }
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
    pub fn from_next_free(next_var: Var) -> Self {
        Self {
            next_var,
            object_map: RsHashMap::default(),
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
                let v = self.new_var();
                self.object_map.insert(key, v);
                v
            }
        }
    }
}

impl Default for ObjectVarManager {
    fn default() -> Self {
        Self {
            next_var: Var::new(0),
            object_map: Default::default(),
        }
    }
}

impl ManageVars for ObjectVarManager {
    fn new() -> Self {
        Self::default()
    }

    fn new_var(&mut self) -> Var {
        let v = self.next_var;
        self.next_var = Var::new(v.idx() + 1);
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
        let mut man = ObjectVarManager::new();
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
