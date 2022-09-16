//! # Satisfiability and Optimization Instance Representations
//!
//! Types representing general satisfiability and optimization instances with
//! functionality to convert them to SAT or MaxSAT instances.

use std::{collections::HashMap, fs::File, io, io::Read, path::Path};

use crate::{
    clause, lit,
    solvers::Solver,
    types::{Clause, Error, Lit},
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

/// Type representing a satisfiability instance.
/// For now this only supports clausal constraints, but more will be added.
#[derive(Clone, Debug, PartialEq)]
pub struct SatInstance {
    clauses: Vec<Clause>,
    next_free_idx: usize,
}

impl SatInstance {
    /// Creates a new satisfiability instance
    pub fn new() -> SatInstance {
        SatInstance {
            clauses: vec![],
            next_free_idx: 0,
        }
    }

    /// Parse a DIMACS instance from a reader object
    pub fn from_dimacs_reader<R: Read>(reader: R) -> Result<SatInstance, Error> {
        match dimacs::parse_cnf(reader) {
            Err(dimacs_error) => Err(Error::Dimacs(dimacs_error)),
            Ok(inst) => Ok(inst),
        }
    }

    /// Parse a DIMACS instance from a file path
    pub fn from_dimacs_path(path: &Path) -> Result<SatInstance, Error> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(Error::IO(why)),
            Ok(reader) => SatInstance::from_dimacs_reader(reader),
        }
    }

    /// Adds a clause to the instance
    pub fn add_clause(&mut self, cl: Clause) {
        cl.iter().for_each(|l| {
            if l.var().index() >= self.next_free_idx {
                self.next_free_idx = l.var().index() + 1;
            }
        });
        self.clauses.push(cl)
    }

    /// Adds an implication of form (a -> b) to the instance
    pub fn add_lit_impl_lit(&mut self, a: Lit, b: Lit) {
        self.add_clause(clause![!a, b])
    }

    /// Adds an implication of form a -> (b1 | b2 | ... | bm)
    pub fn add_lit_impl_or(&mut self, a: Lit, b: Vec<Lit>) {
        let mut cl = clause![!a];
        b.into_iter().for_each(|bi| cl.add(bi));
        self.add_clause(cl)
    }

    /// Adds an implication of form a -> (b1 & b2 & ... & bm)
    pub fn add_lit_impl_and(&mut self, a: Lit, b: Vec<Lit>) {
        b.into_iter()
            .for_each(|bi| self.add_clause(clause![!a, bi]));
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> b
    pub fn add_and_impl_lit(&mut self, a: Vec<Lit>, b: Lit) {
        let mut cl = clause![b];
        a.into_iter().for_each(|ai| cl.add(!ai));
        self.add_clause(cl)
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> b
    pub fn add_or_impl_lit(&mut self, a: Vec<Lit>, b: Lit) {
        for ai in &a {
            self.add_clause(clause![!*ai, b]);
        }
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> (b1 | b2 | ... | bm)
    pub fn add_and_impl_or(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        let mut cl = Clause::new();
        a.into_iter().for_each(|ai| cl.add(!ai));
        b.into_iter().for_each(|bi| cl.add(bi));
        self.add_clause(cl)
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> (b1 | b2 | ... | bm)
    pub fn add_or_impl_or(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        for ai in a {
            let mut cl = clause![ai];
            b.iter().for_each(|bi| cl.add(*bi));
            self.add_clause(cl)
        }
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> (b1 & b2 & ... & bm)
    pub fn add_or_impl_and(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        for ai in &a {
            b.iter().for_each(|bi| self.add_clause(clause![!*ai, *bi]));
        }
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> (b1 & b2 & ... & bm)
    pub fn add_and_impl_and(&mut self, a: Vec<Lit>, b: Vec<Lit>) {
        for bi in b {
            let mut cl = clause![bi];
            a.iter().for_each(|ai| cl.add(!*ai));
            self.add_clause(cl)
        }
    }

    /// Converts the instance to a set of clauses
    pub fn as_clauses(self) -> Vec<Clause> {
        self.clauses
    }

    /// Adds the instance to a solver
    pub fn add_to_solver<S>(self, solver: &mut S)
    where
        S: Solver,
    {
        self.clauses
            .into_iter()
            .for_each(|cl| solver.add_clause(cl))
    }
}

#[cfg(feature = "optimization")]
/// Type representing an optimization instance.
/// The constraints are represented as a [`SatInstance`] struct.
/// For the objective, this currently supports soft clauses and soft literals.
#[derive(Clone, Debug, PartialEq)]
pub struct OptInstance {
    constraints: SatInstance,
    soft_lits: HashMap<Lit, u64>,
    soft_clauses: HashMap<Clause, u64>,
}

impl OptInstance {
    pub fn new() -> OptInstance {
        OptInstance {
            constraints: SatInstance::new(),
            soft_lits: HashMap::new(),
            soft_clauses: HashMap::new(),
        }
    }

    /// Parse a DIMACS instance from a reader object
    pub fn from_dimacs_reader<R: Read>(reader: R) -> Result<OptInstance, Error> {
        match dimacs::parse_wcnf(reader) {
            Err(dimacs_error) => Err(Error::Dimacs(dimacs_error)),
            Ok(inst) => Ok(inst),
        }
    }

    /// Parse a DIMACS instance from a file path
    pub fn from_dimacs_path(path: &Path) -> Result<OptInstance, Error> {
        match open_compressed_uncompressed(path) {
            Err(why) => Err(Error::IO(why)),
            Ok(reader) => OptInstance::from_dimacs_reader(reader),
        }
    }

    /// Gets a mutable reference to the hard constraints for modifying them
    pub fn get_constraints(&mut self) -> &mut SatInstance {
        &mut self.constraints
    }

    /// Adds a soft literal or updates its weight
    pub fn add_soft_lit(&mut self, w: u64, l: Lit) {
        if l.var().index() >= self.constraints.next_free_idx {
            self.constraints.next_free_idx = l.var().index() + 1;
        }
        self.soft_lits.insert(l, w);
    }

    /// Adds a soft clause or updates its weight
    pub fn add_soft_clause(&mut self, w: u64, cl: Clause) {
        cl.iter().for_each(|l| {
            if l.var().index() >= self.constraints.next_free_idx {
                self.constraints.next_free_idx = l.var().index() + 1;
            }
        });
        self.soft_clauses.insert(cl, w);
    }

    /// Converts the instance to a set of hard and soft clauses
    pub fn as_hard_cl_soft_cl(mut self) -> (Vec<Clause>, HashMap<Clause, u64>) {
        self.soft_clauses.reserve(self.soft_lits.len());
        for (l, w) in self.soft_lits {
            self.soft_clauses.insert(clause![!l], w);
        }
        (self.constraints.as_clauses(), self.soft_clauses)
    }

    /// Converts the instance to a set of hard clauses and soft literals
    pub fn as_hard_cl_soft_lit(mut self) -> (Vec<Clause>, HashMap<Lit, u64>) {
        self.soft_lits.reserve(self.soft_clauses.len());
        self.constraints.clauses.reserve(self.soft_clauses.len());
        for (mut cl, w) in self.soft_clauses {
            let relax_lit = lit![self.constraints.next_free_idx];
            self.constraints.next_free_idx += 1;
            cl.add(relax_lit);
            self.constraints.add_clause(cl);
            self.soft_lits.insert(relax_lit, w);
        }
        (self.constraints.as_clauses(), self.soft_lits)
    }
}
