//! # Satsifiability Instance Representations

use std::{cmp, collections::TryReserveError, io, ops::Index, path::Path};

use crate::{
    clause,
    encodings::{atomics, card, pb, CollectClauses},
    lit,
    types::{
        constraints::{CardConstraint, PBConstraint},
        Assignment, Clause, Lit, Var,
    },
    utils::LimitedIter,
    RequiresClausal,
};

use anyhow::Context;

use super::{
    fio::{self, dimacs::CnfLine},
    BasicVarManager, ManageVars, ReindexVars,
};

/// Simple type representing a CNF formula. Other than [`SatInstance<VM>`], this
/// type only supports clauses and does have an internal variable manager.
#[derive(Clone, PartialEq, Eq, Default)]
pub struct Cnf {
    pub(super) clauses: Vec<Clause>,
}

impl std::fmt::Debug for Cnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Cnf")
            .field("clauses", &self.clauses)
            .finish()
    }
}

impl Cnf {
    /// Creates a new [`Cnf`]
    pub fn new() -> Cnf {
        Cnf::default()
    }

    /// Creates a new [`Cnf`] with a given capacity of clauses
    pub fn with_capacity(capacity: usize) -> Cnf {
        Cnf {
            clauses: Vec::with_capacity(capacity),
        }
    }

    /// Tries to reserve memory for at least `additional` new clauses
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.clauses.try_reserve(additional)
    }

    /// Shrinks the allocated memory of the [`Cnf`] to fit the number of clauses
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.clauses.shrink_to_fit()
    }

    /// Gets the capacity of the [`Cnf`]
    #[inline]
    pub fn capacity(&self) -> usize {
        self.clauses.capacity()
    }

    /// Checks if the CNF is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Returns the number of clauses in the instance
    #[inline]
    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    /// Adds a clause from a slice of literals
    pub fn add_nary(&mut self, lits: &[Lit]) {
        self.add_clause(lits.into())
    }

    /// See [`atomics::lit_impl_lit`]
    pub fn add_lit_impl_lit(&mut self, a: Lit, b: Lit) {
        self.add_clause(atomics::lit_impl_lit(a, b))
    }

    /// See [`atomics::lit_impl_clause`]
    pub fn add_lit_impl_clause(&mut self, a: Lit, b: &[Lit]) {
        self.add_clause(atomics::lit_impl_clause(a, b))
    }

    /// See [`atomics::lit_impl_cube`]
    pub fn add_lit_impl_cube(&mut self, a: Lit, b: &[Lit]) {
        self.extend(atomics::lit_impl_cube(a, b))
    }

    /// See [`atomics::cube_impl_lit`]
    pub fn add_cube_impl_lit(&mut self, a: &[Lit], b: Lit) {
        self.add_clause(atomics::cube_impl_lit(a, b))
    }

    /// See [`atomics::clause_impl_lit`]
    pub fn add_clause_impl_lit(&mut self, a: &[Lit], b: Lit) {
        self.extend(atomics::clause_impl_lit(a, b))
    }

    /// See [`atomics::cube_impl_clause`]
    pub fn add_cube_impl_clause(&mut self, a: &[Lit], b: &[Lit]) {
        self.add_clause(atomics::cube_impl_clause(a, b))
    }

    /// See [`atomics::clause_impl_clause`]
    pub fn add_clause_impl_clause(&mut self, a: &[Lit], b: &[Lit]) {
        self.extend(atomics::clause_impl_clause(a, b))
    }

    /// See [`atomics::clause_impl_cube`]
    pub fn add_clause_impl_cube(&mut self, a: &[Lit], b: &[Lit]) {
        self.extend(atomics::clause_impl_cube(a, b))
    }

    /// See [`atomics::cube_impl_cube`]
    pub fn add_cube_impl_cube(&mut self, a: &[Lit], b: &[Lit]) {
        self.extend(atomics::cube_impl_cube(a, b))
    }

    /// Joins the current CNF with another one. Like [`Cnf::extend`] but
    /// consumes the object and returns a new object.
    pub fn join(mut self, other: Cnf) -> Cnf {
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

    /// Sanitizes the CNF by removing tautologies, removing redundant literals,
    /// etc.
    pub fn sanitize(self) -> Self {
        Self {
            clauses: self.into_iter().filter_map(|cl| cl.sanitize()).collect(),
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

    /// Adds a clause to the CNF
    #[inline]
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

    /// Writes the CNF to a DIMACS CNF file at a path
    pub fn write_dimacs_path<P: AsRef<Path>>(&self, path: P, n_vars: u32) -> Result<(), io::Error> {
        let mut writer = fio::open_compressed_uncompressed_write(path)?;
        self.write_dimacs(&mut writer, n_vars)
    }

    /// Writes the CNF to DIMACS CNF
    ///
    /// # Performance
    ///
    /// For performance, consider using a [`std::io::BufWriter`] instance.
    pub fn write_dimacs<W: io::Write>(&self, writer: &mut W, n_vars: u32) -> Result<(), io::Error> {
        fio::dimacs::write_cnf_annotated(writer, self, n_vars)
    }
}

impl CollectClauses for Cnf {
    fn n_clauses(&self) -> usize {
        self.clauses.len()
    }

    fn extend_clauses<T>(&mut self, cl_iter: T) -> Result<(), crate::OutOfMemory>
    where
        T: IntoIterator<Item = Clause>,
    {
        let cl_iter = cl_iter.into_iter();
        if let Some(ub) = cl_iter.size_hint().1 {
            self.try_reserve(ub)?;
            self.extend(cl_iter);
        } else {
            // Extend by reserving in exponential chunks
            let mut cl_iter = cl_iter.peekable();
            while cl_iter.peek().is_some() {
                let additional = (self.len() + cmp::max(cl_iter.size_hint().0, 1))
                    .next_power_of_two()
                    - self.len();
                self.try_reserve(additional)?;
                self.extend(LimitedIter::new(&mut cl_iter, additional));
            }
        }
        Ok(())
    }
}

impl IntoIterator for Cnf {
    type Item = Clause;

    type IntoIter = std::vec::IntoIter<Clause>;

    fn into_iter(self) -> Self::IntoIter {
        self.clauses.into_iter()
    }
}

impl FromIterator<Clause> for Cnf {
    fn from_iter<T: IntoIterator<Item = Clause>>(iter: T) -> Self {
        Self {
            clauses: iter.into_iter().collect(),
        }
    }
}

impl FromIterator<CnfLine> for Cnf {
    fn from_iter<T: IntoIterator<Item = CnfLine>>(iter: T) -> Self {
        Self::from_iter(iter.into_iter().filter_map(|line| match line {
            CnfLine::Comment(_) => None,
            CnfLine::Clause(cl) => Some(cl),
        }))
    }
}

impl Extend<Clause> for Cnf {
    fn extend<Iter: IntoIterator<Item = Clause>>(&mut self, iter: Iter) {
        self.clauses.extend(iter)
    }
}

impl Index<usize> for Cnf {
    type Output = Clause;

    fn index(&self, index: usize) -> &Self::Output {
        &self.clauses[index]
    }
}

/// Type representing a satisfiability instance. Supported constraints are
/// clauses, cardinality constraints and pseudo-boolean constraints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SatInstance<VM: ManageVars = BasicVarManager> {
    pub(super) cnf: Cnf,
    pub(super) cards: Vec<CardConstraint>,
    pub(super) pbs: Vec<PBConstraint>,
    pub(super) var_manager: VM,
}

impl<VM: ManageVars> SatInstance<VM> {
    /// Creates a new satisfiability instance with a specific var manager
    pub fn new_with_manager(var_manager: VM) -> Self {
        SatInstance {
            cnf: Cnf::new(),
            cards: vec![],
            pbs: vec![],
            var_manager,
        }
    }

    /// Returns the number of clauses in the instance
    pub fn n_clauses(&self) -> usize {
        self.cnf.n_clauses()
    }

    /// Returns the number of cardinality constraints in the instance
    pub fn n_cards(&self) -> usize {
        self.cards.len()
    }

    /// Returns the number of PB constraints in the instance
    pub fn n_pbs(&self) -> usize {
        self.pbs.len()
    }

    /// Adds a clause to the instance
    pub fn add_clause(&mut self, cl: Clause) {
        cl.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.cnf.add_clause(cl);
    }

    /// Adds a clause from a slice of literals
    pub fn add_nary(&mut self, lits: &[Lit]) {
        self.add_clause(lits.into())
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
    pub fn add_lit_impl_clause(&mut self, a: Lit, b: &[Lit]) {
        self.var_manager.mark_used(a.var());
        b.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.cnf.add_lit_impl_clause(a, b);
    }

    /// Adds an implication of form a -> (b1 & b2 & ... & bm)
    pub fn add_lit_impl_cube(&mut self, a: Lit, b: &[Lit]) {
        self.var_manager.mark_used(a.var());
        b.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.cnf.add_lit_impl_cube(a, b);
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> b
    pub fn add_cube_impl_lit(&mut self, a: &[Lit], b: Lit) {
        a.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.var_manager.mark_used(b.var());
        self.cnf.add_cube_impl_lit(a, b);
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> b
    pub fn add_clause_impl_lit(&mut self, a: &[Lit], b: Lit) {
        a.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.var_manager.mark_used(b.var());
        self.cnf.add_clause_impl_lit(a, b);
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> (b1 | b2 | ... | bm)
    pub fn add_cube_impl_clause(&mut self, a: &[Lit], b: &[Lit]) {
        a.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        b.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.cnf.add_cube_impl_clause(a, b);
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> (b1 | b2 | ... | bm)
    pub fn add_clause_impl_clause(&mut self, a: &[Lit], b: &[Lit]) {
        a.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        b.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.cnf.add_clause_impl_clause(a, b);
    }

    /// Adds an implication of form (a1 | a2 | ... | an) -> (b1 & b2 & ... & bm)
    pub fn add_clause_impl_cube(&mut self, a: &[Lit], b: &[Lit]) {
        a.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        b.iter().for_each(|l| {
            self.var_manager.mark_used(l.var());
        });
        self.cnf.add_clause_impl_cube(a, b);
    }

    /// Adds an implication of form (a1 & a2 & ... & an) -> (b1 & b2 & ... & bm)
    pub fn add_cube_impl_cube(&mut self, a: &[Lit], b: &[Lit]) {
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

    /// Gets a reference to the internal CNF
    pub fn cnf(&self) -> &Cnf {
        &self.cnf
    }

    /// Gets a reference to the variable manager
    #[deprecated(
        since = "0.5.0",
        note = "var_manager has been renamed to var_manager_mut and will be removed in a future release"
    )]
    pub fn var_manager(&mut self) -> &mut VM {
        &mut self.var_manager
    }

    /// Gets a mutable reference to the variable manager
    pub fn var_manager_mut(&mut self) -> &mut VM {
        &mut self.var_manager
    }

    /// Gets a reference to the variable manager
    pub fn var_manager_ref(&self) -> &VM {
        &self.var_manager
    }

    /// Reserves a new variable in the internal variable manager. This is a
    /// shortcut for `inst.var_manager().new_var()`.
    pub fn new_var(&mut self) -> Var {
        self.var_manager_mut().new_var()
    }

    /// Reserves a new variable in the internal variable manager. This is a
    /// shortcut for `inst.var_manager().new_lit()`.
    pub fn new_lit(&mut self) -> Lit {
        self.var_manager_mut().new_lit()
    }

    /// Gets the used variable with the highest index. This is a shortcut
    /// for `inst.var_manager().max_var()`.
    pub fn max_var(&self) -> Option<Var> {
        self.var_manager_ref().max_var()
    }

    /// Returns the number of variables in the variable manager of the instance
    pub fn n_vars(&self) -> u32 {
        self.var_manager_ref().n_used()
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
    #[deprecated(
        since = "0.5.0",
        note = "as_cnf has been renamed to into_cnf and will be removed in a future release"
    )]
    pub fn as_cnf(self) -> (Cnf, VM) {
        self.into_cnf()
    }

    /// Converts the instance to a set of clauses.
    /// Uses the default encoders from the `encodings` module.
    ///
    /// See [`Self::convert_to_cnf`] for converting in place
    ///
    /// # Panic
    ///
    /// This might panic if the conversion to [`Cnf`] runs out of memory.
    pub fn into_cnf(self) -> (Cnf, VM) {
        self.into_cnf_with_encoders(
            |constr, cnf, vm| {
                card::default_encode_cardinality_constraint(constr, cnf, vm)
                    .expect("cardinality encoding ran out of memory")
            },
            |constr, cnf, vm| {
                pb::default_encode_pb_constraint(constr, cnf, vm)
                    .expect("pb encoding ran out of memory")
            },
        )
    }

    /// Converts the instance to a set of clauses inplace.
    /// Uses the default encoders from the `encodings` module.
    ///
    /// See [`Self::into_cnf`] if you don't need to convert in place
    ///
    /// # Panic
    ///
    /// This might panic if the conversion to [`Cnf`] runs out of memory.
    pub fn convert_to_cnf(&mut self) {
        self.convert_to_cnf_with_encoders(
            |constr, cnf, vm| {
                card::default_encode_cardinality_constraint(constr, cnf, vm)
                    .expect("cardinality encoding ran out of memory")
            },
            |constr, cnf, vm| {
                pb::default_encode_pb_constraint(constr, cnf, vm)
                    .expect("pb encoding ran out of memory")
            },
        )
    }

    /// Converts the instance to a set of clauses with explicitly specified
    /// converters for non-clausal constraints.
    #[deprecated(
        since = "0.5.0",
        note = "as_cnf_with_encoders has been renamed to into_cnf_with_encoders and will be removed in a future release"
    )]
    pub fn as_cnf_with_encoders<CardEnc, PBEnc>(
        self,
        card_encoder: CardEnc,
        pb_encoder: PBEnc,
    ) -> (Cnf, VM)
    where
        CardEnc: FnMut(CardConstraint, &mut Cnf, &mut dyn ManageVars),
        PBEnc: FnMut(PBConstraint, &mut Cnf, &mut dyn ManageVars),
    {
        self.into_cnf_with_encoders(card_encoder, pb_encoder)
    }

    /// Converts the instance to a set of clauses with explicitly specified
    /// converters for non-clausal constraints.
    ///
    /// See [`Self::into_cnf_with_encoders`] to convert in place
    ///
    /// # Panic
    ///
    /// The encoder functions might panic if the conversion runs out of memory.
    pub fn into_cnf_with_encoders<CardEnc, PBEnc>(
        mut self,
        card_encoder: CardEnc,
        pb_encoder: PBEnc,
    ) -> (Cnf, VM)
    where
        CardEnc: FnMut(CardConstraint, &mut Cnf, &mut dyn ManageVars),
        PBEnc: FnMut(PBConstraint, &mut Cnf, &mut dyn ManageVars),
    {
        self.convert_to_cnf_with_encoders(card_encoder, pb_encoder);
        (self.cnf, self.var_manager)
    }

    /// Converts the instance inplace to a set of clauses with explicitly specified
    /// converters for non-clausal constraints.
    ///
    /// See [`Self::into_cnf_with_encoders`] if you don't need to convert in place
    ///
    /// # Panic
    ///
    /// The encoder functions might panic if the conversion runs out of memory.
    pub fn convert_to_cnf_with_encoders<CardEnc, PBEnc>(
        &mut self,
        mut card_encoder: CardEnc,
        mut pb_encoder: PBEnc,
    ) where
        CardEnc: FnMut(CardConstraint, &mut Cnf, &mut dyn ManageVars),
        PBEnc: FnMut(PBConstraint, &mut Cnf, &mut dyn ManageVars),
    {
        self.cards
            .drain(..)
            .for_each(|constr| card_encoder(constr, &mut self.cnf, &mut self.var_manager));
        self.pbs
            .drain(..)
            .for_each(|constr| pb_encoder(constr, &mut self.cnf, &mut self.var_manager));
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
    ///
    /// # Performance
    ///
    /// For performance, consider using a [`std::io::BufWriter`] instance.
    #[deprecated(since = "0.5.0", note = "use write_dimacs_path instead")]
    pub fn to_dimacs_path<P: AsRef<Path>>(self, path: P) -> Result<(), io::Error> {
        let mut writer = fio::open_compressed_uncompressed_write(path)?;
        #[allow(deprecated)]
        self.to_dimacs(&mut writer)
    }

    /// Writes the instance to DIMACS CNF
    #[deprecated(since = "0.5.0", note = "use write_dimacs instead")]
    pub fn to_dimacs<W: io::Write>(self, writer: &mut W) -> Result<(), io::Error> {
        #[allow(deprecated)]
        self.to_dimacs_with_encoders(
            |constr, cnf, vm| {
                card::default_encode_cardinality_constraint(constr, cnf, vm)
                    .expect("cardinality encoding ran out of memory")
            },
            |constr, cnf, vm| {
                pb::default_encode_pb_constraint(constr, cnf, vm)
                    .expect("pb encoding ran out of memory")
            },
            writer,
        )
    }

    /// Writes the instance to DIMACS CNF converting non-clausal constraints
    /// with specific encoders.
    #[deprecated(
        since = "0.5.0",
        note = "use convert_to_cnf_with_encoders and write_dimacs instead"
    )]
    pub fn to_dimacs_with_encoders<W, CardEnc, PBEnc>(
        self,
        card_encoder: CardEnc,
        pb_encoder: PBEnc,
        writer: &mut W,
    ) -> Result<(), io::Error>
    where
        W: io::Write,
        CardEnc: FnMut(CardConstraint, &mut Cnf, &mut dyn ManageVars),
        PBEnc: FnMut(PBConstraint, &mut Cnf, &mut dyn ManageVars),
    {
        let (cnf, vm) = self.into_cnf_with_encoders(card_encoder, pb_encoder);
        fio::dimacs::write_cnf_annotated(writer, &cnf, vm.n_used())
    }

    /// Writes the instance to a DIMACS CNF file at a path
    ///
    /// This requires that the instance is clausal, i.e., does not contain any non-converted
    /// cardinality of pseudo-boolean constraints. If necessary, the instance can be converted by
    /// [`Self::convert_to_cnf`] or [`Self::convert_to_cnf_with_encoders`] first.
    ///
    /// # Errors
    ///
    /// - If the instance is not clausal, returns [`RequiresClausal`]
    /// - Returns [`io::Error`] on errors during writing
    pub fn write_dimacs_path<P: AsRef<Path>>(&self, path: P) -> anyhow::Result<()> {
        let mut writer = fio::open_compressed_uncompressed_write(path)?;
        self.write_dimacs(&mut writer)
    }

    /// Writes the instance to DIMACS CNF
    ///
    /// This requires that the instance is clausal, i.e., does not contain any non-converted
    /// cardinality of pseudo-boolean constraints. If necessary, the instance can be converted by
    /// [`Self::convert_to_cnf`] or [`Self::convert_to_cnf_with_encoders`] first.
    ///
    /// # Performance
    ///
    /// For performance, consider using a [`std::io::BufWriter`] instance.
    ///
    /// # Errors
    ///
    /// - If the instance is not clausal, returns [`RequiresClausal`]
    /// - Returns [`io::Error`] on errors during writing
    pub fn write_dimacs<W: io::Write>(&self, writer: &mut W) -> anyhow::Result<()> {
        if self.n_cards() > 0 || self.n_pbs() > 0 {
            return Err(RequiresClausal.into());
        }
        let n_vars = self.n_vars();
        Ok(fio::dimacs::write_cnf_annotated(writer, &self.cnf, n_vars)?)
    }

    /// Writes the instance to an OPB file at a path
    ///
    /// # Performance
    ///
    /// For performance, consider using a [`std::io::BufWriter`] instance.
    #[deprecated(since = "0.5.0", note = "use write_opb_path instead")]
    pub fn to_opb_path<P: AsRef<Path>>(
        self,
        path: P,
        opts: fio::opb::Options,
    ) -> Result<(), io::Error> {
        let mut writer = fio::open_compressed_uncompressed_write(path)?;
        #[allow(deprecated)]
        self.to_opb(&mut writer, opts)
    }

    /// Writes the instance to an OPB file
    #[deprecated(since = "0.5.0", note = "use write_opb instead")]
    pub fn to_opb<W: io::Write>(
        self,
        writer: &mut W,
        opts: fio::opb::Options,
    ) -> Result<(), io::Error> {
        fio::opb::write_sat(writer, &self, opts)
    }

    /// Writes the instance to an OPB file at a path
    pub fn write_opb_path<P: AsRef<Path>>(
        &self,
        path: P,
        opts: fio::opb::Options,
    ) -> Result<(), io::Error> {
        let mut writer = fio::open_compressed_uncompressed_write(path)?;
        self.write_opb(&mut writer, opts)
    }

    /// Writes the instance to an OPB file
    ///
    /// # Performance
    ///
    /// For performance, consider using a [`std::io::BufWriter`] instance.
    pub fn write_opb<W: io::Write>(
        &self,
        writer: &mut W,
        opts: fio::opb::Options,
    ) -> Result<(), io::Error> {
        fio::opb::write_sat(writer, self, opts)
    }

    /// Sanitizes the constraints, i.e., for example a cardinality
    /// constraint of form `x + y >= 1` will be converted to a clause and
    /// tautologies will be removed.
    pub fn sanitize(self) -> Self {
        let mut unsat = false;
        let mut cnf = self.cnf;
        let mut cards = self.cards;
        let pbs = self
            .pbs
            .into_iter()
            .filter_map(|pb| {
                if pb.is_tautology() {
                    return None;
                }
                if pb.is_unsat() {
                    unsat = true;
                    return None;
                }
                if pb.is_positive_assignment() {
                    // Add unit clauses
                    pb.into_lits()
                        .into_iter()
                        .for_each(|(l, _)| cnf.add_unit(l));
                    return None;
                }
                if pb.is_negative_assignment() {
                    // Add unit clauses
                    pb.into_lits()
                        .into_iter()
                        .for_each(|(l, _)| cnf.add_unit(!l));
                    return None;
                }
                if pb.is_clause() {
                    cnf.add_clause(pb.into_clause().unwrap());
                    return None;
                }
                if pb.is_card() {
                    cards.push(pb.into_card_constr().unwrap());
                    return None;
                }
                Some(pb)
            })
            .collect();
        let cards = cards
            .into_iter()
            .filter_map(|card| {
                if card.is_tautology() {
                    return None;
                }
                if card.is_unsat() {
                    unsat = true;
                    return None;
                }
                if card.is_positive_assignment() {
                    // Add unit clauses
                    card.into_lits().into_iter().for_each(|l| cnf.add_unit(l));
                    return None;
                }
                if card.is_negative_assignment() {
                    // Add unit clauses
                    card.into_lits().into_iter().for_each(|l| cnf.add_unit(!l));
                    return None;
                }
                if card.is_clause() {
                    cnf.add_clause(card.into_clause().unwrap());
                    return None;
                }
                Some(card)
            })
            .collect();
        if unsat {
            return Self {
                cnf: Cnf::from_iter(vec![clause![lit![0]], clause![!lit![0]]]),
                cards: vec![],
                pbs: vec![],
                var_manager: self.var_manager,
            };
        }
        Self {
            cnf: Cnf::from_iter(cnf.into_iter().filter_map(|cl| cl.sanitize())),
            cards,
            pbs,
            var_manager: self.var_manager,
        }
    }

    /// Checks whether the instance is satisfied by the given assignment
    pub fn is_sat(&self, assign: &Assignment) -> bool {
        for clause in self.cnf.iter() {
            if !clause.is_sat(assign) {
                return false;
            }
        }
        for card in &self.cards {
            if !card.is_sat(assign) {
                return false;
            }
        }
        for pb in &self.pbs {
            if !pb.is_sat(assign) {
                return false;
            }
        }
        true
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
    pub fn from_dimacs<R: io::BufRead>(reader: R) -> anyhow::Result<Self> {
        fio::dimacs::parse_cnf(reader)
    }

    /// Parses a DIMACS instance from a file path. For more details see
    /// [`SatInstance::from_dimacs`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    pub fn from_dimacs_path<P: AsRef<Path>>(path: P) -> anyhow::Result<Self> {
        let reader =
            fio::open_compressed_uncompressed_read(path).context("failed to open reader")?;
        SatInstance::from_dimacs(reader)
    }

    /// Parses an OPB instance from a reader object.
    ///
    /// # File Format
    ///
    /// The file format expected by this parser is the OPB format for
    /// pseudo-boolean satisfaction instances. For details on the file format
    /// see [here](https://www.cril.univ-artois.fr/PB12/format.pdf).
    pub fn from_opb<R: io::BufRead>(reader: R, opts: fio::opb::Options) -> anyhow::Result<Self> {
        fio::opb::parse_sat(reader, opts)
    }

    /// Parses an OPB instance from a file path. For more details see
    /// [`SatInstance::from_opb`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    pub fn from_opb_path<P: AsRef<Path>>(path: P, opts: fio::opb::Options) -> anyhow::Result<Self> {
        let reader =
            fio::open_compressed_uncompressed_read(path).context("failed to open reader")?;
        SatInstance::from_opb(reader, opts)
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

impl<VM: ManageVars + Default> FromIterator<CnfLine> for SatInstance<VM> {
    fn from_iter<T: IntoIterator<Item = CnfLine>>(iter: T) -> Self {
        Self::from_iter(iter.into_iter().filter_map(|line| match line {
            CnfLine::Comment(_) => None,
            CnfLine::Clause(cl) => Some(cl),
        }))
    }
}

impl<VM: ManageVars + Default> From<Cnf> for SatInstance<VM> {
    fn from(value: Cnf) -> Self {
        let mut inst = Self {
            cnf: value,
            ..Default::default()
        };
        inst.cnf.iter().for_each(|cl| {
            cl.iter().for_each(|l| {
                inst.var_manager.increase_next_free(l.var() + 1);
            })
        });
        inst
    }
}

impl CollectClauses for SatInstance {
    fn n_clauses(&self) -> usize {
        self.n_clauses()
    }

    fn extend_clauses<T>(&mut self, cl_iter: T) -> Result<(), crate::OutOfMemory>
    where
        T: IntoIterator<Item = Clause>,
    {
        self.cnf.extend_clauses(cl_iter)
    }
}
