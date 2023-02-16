//! # Satsifiability Instance Representations

use std::{io, path::Path};

use crate::{
    clause,
    encodings::{card, pb},
    types::{
        constraints::{CardConstraint, PBConstraint},
        Clause, Lit,
    },
};

use super::{fio, BasicVarManager, ManageVars, ReindexVars};

/// Simple type representing a CNF formula. Other than [`SatInstance<VM>`], this
/// type only supports clauses and does have an internal variable manager.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct CNF {
    pub(super) clauses: Vec<Clause>,
}

impl CNF {
    /// Creates a new CNF
    pub fn new() -> CNF {
        CNF::default()
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

    /// Checks if the CNF is empty
    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Returns the number of clauses in the instance
    pub fn len(&self) -> usize {
        self.clauses.len()
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

    /// Joins the current CNF with another one. Like [`CNF::extend`] but
    /// consumes the object and returns a new object.
    pub fn join(mut self, other: CNF) -> CNF {
        self.extend(other);
        self
    }

    /// Returns an iterator over references to the clauses
    pub fn iter(&self) -> std::slice::Iter<'_, Clause> {
        self.clauses.iter()
    }

    /// Returns an iterator over mutable references to the clauses
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, Clause> {
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

    #[cfg(feature = "rand")]
    /// Randomly shuffles the order of clauses in the CNF
    pub fn shuffle(mut self) -> Self {
        use rand::seq::SliceRandom;
        let mut rng = rand::thread_rng();
        self.clauses[..].shuffle(&mut rng);
        self
    }
}

impl IntoIterator for CNF {
    type Item = Clause;

    type IntoIter = std::vec::IntoIter<Clause>;

    fn into_iter(self) -> Self::IntoIter {
        self.clauses.into_iter()
    }
}

impl FromIterator<Clause> for CNF {
    fn from_iter<T: IntoIterator<Item = Clause>>(iter: T) -> Self {
        Self {
            clauses: iter.into_iter().collect(),
        }
    }
}

/// Type representing a satisfiability instance. Supported constraints are
/// clauses, cardinality constraints and pseudo-boolean constraints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SatInstance<VM: ManageVars = BasicVarManager> {
    pub(super) cnf: CNF,
    pub(super) cards: Vec<CardConstraint>,
    pub(super) pbs: Vec<PBConstraint>,
    pub(super) var_manager: VM,
}

impl<VM: ManageVars> SatInstance<VM> {
    /// Creates a new satisfiability instance with a specific var manager
    pub fn new_with_manager(var_manager: VM) -> Self {
        SatInstance {
            cnf: CNF::new(),
            cards: vec![],
            pbs: vec![],
            var_manager,
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
    pub fn change_var_manager<VM2, VMC>(self, vm_converter: VMC) -> (SatInstance<VM2>, VM)
    where
        VM2: ManageVars,
        VMC: Fn(&VM) -> VM2,
    {
        (
            SatInstance {
                cnf: self.cnf,
                cards: self.cards,
                pbs: self.pbs,
                var_manager: vm_converter(&self.var_manager),
            },
            self.var_manager,
        )
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

    /// Reindexes all variables in the instance with a reindexing variable manager
    pub fn reindex<R: ReindexVars>(mut self, mut reindexer: R) -> SatInstance<R> {
        self.cnf
            .iter_mut()
            .for_each(|cl| cl.iter_mut().for_each(|l| *l = reindexer.reindex_lit(*l)));
        self.cards
            .iter_mut()
            .for_each(|card| card.iter_mut().for_each(|l| *l = reindexer.reindex_lit(*l)));
        self.pbs.iter_mut().for_each(|pb| {
            pb.iter_mut()
                .for_each(|(l, _)| *l = reindexer.reindex_lit(*l))
        });
        SatInstance {
            cnf: self.cnf,
            cards: self.cards,
            pbs: self.pbs,
            var_manager: reindexer,
        }
    }

    #[cfg(feature = "rand")]
    /// Randomly shuffles the order of constraints.
    pub fn shuffle(mut self) -> Self {
        use rand::seq::SliceRandom;
        self.cnf = self.cnf.shuffle();
        let mut rng = rand::thread_rng();
        self.cards[..].shuffle(&mut rng);
        self.pbs[..].shuffle(&mut rng);
        self
    }

    /// Writes the instance to a DIMACS CNF file at a path
    pub fn to_dimacs_path<P: AsRef<Path>>(self, path: P) -> Result<(), io::Error> {
        let mut writer = fio::open_compressed_uncompressed_write(path)?;
        self.to_dimacs(&mut writer)
    }

    /// Writes the instance to DIMACS CNF
    pub fn to_dimacs<W: io::Write>(self, writer: &mut W) -> Result<(), io::Error> {
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
        W: io::Write,
        CardEnc: FnMut(CardConstraint, &mut dyn ManageVars) -> CNF,
        PBEnc: FnMut(PBConstraint, &mut dyn ManageVars) -> CNF,
    {
        let (cnf, vm) = self.as_cnf_with_encoders(card_encoder, pb_encoder);
        fio::dimacs::write_cnf(writer, cnf, vm.max_var())
    }

    /// Writes the instance to an OPB file at a path
    pub fn to_opb_path<P: AsRef<Path>>(
        self,
        path: P,
        opts: fio::opb::Options,
    ) -> Result<(), io::Error> {
        let mut writer = fio::open_compressed_uncompressed_write(path)?;
        self.to_opb(&mut writer, opts)
    }

    /// Writes the instance to an OPB file
    pub fn to_opb<W: io::Write>(
        self,
        writer: &mut W,
        opts: fio::opb::Options,
    ) -> Result<(), io::Error> {
        fio::opb::write_sat(writer, self, opts)
    }
}

impl<VM: ManageVars + Default> SatInstance<VM> {
    /// Creates a new satisfiability instance
    pub fn new() -> SatInstance<VM> {
        SatInstance::default()
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
    pub fn from_dimacs_reader<R: io::Read>(reader: R) -> Result<Self, fio::ParsingError> {
        Ok(fio::dimacs::parse_cnf(reader)?)
    }

    /// Parses a DIMACS instance from a file path. For more details see
    /// [`SatInstance::from_dimacs_reader`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    pub fn from_dimacs_path<P: AsRef<Path>>(path: P) -> Result<Self, fio::ParsingError> {
        match fio::open_compressed_uncompressed_read(path) {
            Err(why) => Err(fio::ParsingError::IO(why)),
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
    pub fn from_opb_reader<R: io::Read>(
        reader: R,
        opts: fio::opb::Options,
    ) -> Result<Self, fio::ParsingError> {
        Ok(fio::opb::parse_sat(reader, opts)?)
    }

    /// Parses an OPB instance from a file path. For more details see
    /// [`SatInstance::from_opb_reader`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    pub fn from_opb_path<P: AsRef<Path>>(
        path: P,
        opts: fio::opb::Options,
    ) -> Result<Self, fio::ParsingError> {
        match fio::open_compressed_uncompressed_read(path) {
            Err(why) => Err(fio::ParsingError::IO(why)),
            Ok(reader) => SatInstance::from_opb_reader(reader, opts),
        }
    }
}

impl<VM: ManageVars + Default> Default for SatInstance<VM> {
    fn default() -> Self {
        Self {
            cnf: Default::default(),
            cards: Default::default(),
            pbs: Default::default(),
            var_manager: VM::default(),
        }
    }
}

impl<VM: ManageVars + Default> FromIterator<Clause> for SatInstance<VM> {
    fn from_iter<T: IntoIterator<Item = Clause>>(iter: T) -> Self {
        let mut inst = Self::default();
        iter.into_iter().for_each(|cl| inst.add_clause(cl));
        inst
    }
}
