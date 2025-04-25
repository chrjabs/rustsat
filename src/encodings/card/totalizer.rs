//! # Totalizer Encoding
//!
//! Implementation of the binary adder tree totalizer encoding \[1\].
//! The implementation is incremental as extended in \[2\].
//! The implementation is based on a node database.
//! For now, this implementation only supports upper bounding.
//!
//! # References
//!
//! - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality
//!   Constraints_, CP 2003.
//! - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental
//!   Cardinality Constraints for MaxSAT_, CP 2014.

use std::{cmp, ops::RangeBounds};

use crate::{
    encodings::{
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
        totdb, CollectClauses, EncodeStats, EnforceError, Monotone, NotEncoded,
    },
    instances::ManageVars,
    types::Lit,
};

use super::{
    BoundBoth, BoundBothIncremental, BoundLower, BoundLowerIncremental, BoundUpper,
    BoundUpperIncremental, Encode, EncodeIncremental,
};

/// Implementation of the binary adder tree totalizer encoding \[1\].
/// The implementation is incremental as extended in \[2\].
/// The implementation is based on a node database.
/// For now, this implementation only supports upper bounding.
///
/// # References
///
/// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality
///   Constraints_, CP 2003.
/// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental
///   Cardinality Constraints for MaxSAT_, CP 2014.
#[derive(Default, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Totalizer {
    /// Literals added but not yet in the encoding
    lit_buffer: Vec<Lit>,
    /// The root of the tree, if constructed
    root: Option<NodeId>,
    /// The number of variables in the totalizer
    n_vars: u32,
    /// The number of clauses in the totalizer
    n_clauses: usize,
    /// The node database of the totalizer
    db: totdb::Db,
    /// The offset of the totalizer
    offset: usize,
}

impl Totalizer {
    /// Creates a totalizer from its internal parts
    #[cfg(feature = "internals")]
    #[must_use]
    pub fn from_raw(root: NodeId, offset: usize, db: totdb::Db) -> Self {
        Self {
            root: Some(root),
            db,
            offset,
            ..Default::default()
        }
    }

    fn extend_tree(&mut self) {
        if self.lit_buffer.is_empty() {
            return;
        }
        let new_tree = self.db.lit_tree(&self.lit_buffer);
        self.root = Some(match self.root {
            Some(old_root) => {
                self.db
                    .merge(&[NodeCon::full(old_root), NodeCon::full(new_tree)])
                    .id
            }
            None => new_tree,
        });
        self.lit_buffer.clear();
    }

    /// Gets the maximum depth of the tree
    #[must_use]
    pub fn depth(&self) -> usize {
        self.root.map_or(0, |root| self.db[root].depth())
    }

    /// Gets the details of a totalizer output related to proof logging
    ///
    /// # Errors
    ///
    /// If the requested output is not encoded
    #[cfg(feature = "proof-logging")]
    pub fn output_proof_details(
        &self,
        value: usize,
    ) -> Result<(Lit, totdb::cert::SemDefs), NotEncoded> {
        match self.root {
            None => Err(NotEncoded),
            Some(root) => self
                .db
                .get_semantics(root, self.offset, value + self.offset)
                .map(|sem| (self.db[root][value + self.offset], sem))
                .ok_or(NotEncoded),
        }
    }

    /// Gets the number of output literals in the totalizer
    ///
    /// This will only differ from [`Self::n_lits`] if the encoding has an offset
    #[must_use]
    pub fn n_output_lits(&self) -> usize {
        match self.root {
            Some(root) => self.db[root].len() - self.offset,
            None => 0,
        }
    }

    /// From an assignment to the input literals, generates an assignment over the totalizer
    /// variables following strict semantics, i.e., `sum >= k <-> olit`
    ///
    /// # Panics
    ///
    /// If `assign` does not assign all input literals
    pub fn strictly_extend_assignment<'slf>(
        &'slf self,
        assign: &'slf crate::types::Assignment,
    ) -> std::iter::Flatten<std::option::IntoIter<totdb::AssignIter<'slf>>> {
        self.root
            .map(|root| self.db.strictly_extend_assignment(root, assign))
            .into_iter()
            .flatten()
    }
}

impl Encode for Totalizer {
    fn n_lits(&self) -> usize {
        self.lit_buffer.len()
            + match self.root {
                Some(id) => self.db[id].len(),
                None => 0,
            }
    }
}

impl EncodeIncremental for Totalizer {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.extend_tree();
        if let Some(root) = self.root {
            self.db.reserve_vars(root, var_manager);
        }
    }
}

impl BoundUpper for Totalizer {
    fn encode_ub<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        self.db.reset_encoded(totdb::Semantics::If);
        self.encode_ub_change(range, collector, var_manager)
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, NotEncoded> {
        if ub >= self.n_lits() - self.offset {
            return Ok(vec![]);
        }
        if !self.lit_buffer.is_empty() {
            return Err(NotEncoded);
        }
        if let Some(id) = self.root {
            match &self.db[id] {
                totdb::Node::Leaf(lit) => {
                    debug_assert_eq!(ub, self.offset);
                    return Ok(vec![!*lit]);
                }
                totdb::Node::Unit(node) => {
                    if let totdb::LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = node.lits[ub + self.offset]
                    {
                        if semantics.has_if() {
                            return Ok(vec![!lit]);
                        }
                    }
                }
                totdb::Node::General(_) | totdb::Node::Dummy => unreachable!(),
            }
        }
        Err(NotEncoded)
    }
}

impl BoundUpperIncremental for Totalizer {
    fn encode_ub_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        let range = super::prepare_ub_range(self, range);
        let range = range.start..cmp::min(range.end, self.n_lits() - self.offset);
        if range.is_empty() {
            return Ok(());
        }
        self.extend_tree();
        if let Some(id) = self.root {
            let n_vars_before = var_manager.n_used();
            let n_clauses_before = collector.n_clauses();
            for idx in range {
                self.db.define_unweighted(
                    id,
                    idx + self.offset,
                    totdb::Semantics::If,
                    collector,
                    var_manager,
                )?;
            }
            self.n_clauses += collector.n_clauses() - n_clauses_before;
            self.n_vars += var_manager.n_used() - n_vars_before;
        }
        Ok(())
    }
}

impl BoundLower for Totalizer {
    fn encode_lb<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        self.db.reset_encoded(totdb::Semantics::OnlyIf);
        self.encode_lb_change(range, collector, var_manager)
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EnforceError> {
        if lb <= self.offset {
            return Ok(vec![]);
        }
        if lb > self.n_lits() + self.offset {
            return Err(EnforceError::Unsat);
        }
        if !self.lit_buffer.is_empty() {
            return Err(EnforceError::NotEncoded);
        }
        if let Some(id) = self.root {
            match &self.db[id] {
                totdb::Node::Leaf(lit) => {
                    debug_assert_eq!(lb, 1);
                    return Ok(vec![*lit]);
                }
                totdb::Node::Unit(node) => {
                    if let totdb::LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = node.lits[lb - 1 + self.offset]
                    {
                        if semantics.has_only_if() {
                            return Ok(vec![lit]);
                        }
                    }
                }
                totdb::Node::General(_) | totdb::Node::Dummy => unreachable!(),
            }
        }
        Err(EnforceError::NotEncoded)
    }
}

impl BoundLowerIncremental for Totalizer {
    fn encode_lb_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        let range = super::prepare_lb_range(self, range);
        let range = range.start..cmp::min(range.end, self.n_lits() - self.offset + 1);
        if range.is_empty() {
            return Ok(());
        }
        self.extend_tree();
        if let Some(id) = self.root {
            let n_vars_before = var_manager.n_used();
            let n_clauses_before = collector.n_clauses();
            for idx in range {
                self.db.define_unweighted(
                    id,
                    idx - 1 + self.offset,
                    totdb::Semantics::OnlyIf,
                    collector,
                    var_manager,
                )?;
            }
            self.n_clauses += collector.n_clauses() - n_clauses_before;
            self.n_vars += var_manager.n_used() - n_vars_before;
        }
        Ok(())
    }
}

impl BoundBoth for Totalizer {
    fn encode_both<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize> + Clone,
    {
        self.encode_ub_change(range.clone(), collector, var_manager)?;
        self.encode_lb_change(range, collector, var_manager)?;
        Ok(())
    }
}

impl BoundBothIncremental for Totalizer {}

impl Monotone for Totalizer {}

impl EncodeStats for Totalizer {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        self.n_vars
    }
}

impl From<Vec<Lit>> for Totalizer {
    fn from(lits: Vec<Lit>) -> Self {
        Self {
            lit_buffer: lits,
            root: None,
            n_vars: 0,
            n_clauses: 0,
            db: totdb::Db::default(),
            offset: 0,
        }
    }
}

impl FromIterator<Lit> for Totalizer {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            lit_buffer: Vec::from_iter(iter),
            root: None,
            n_vars: 0,
            n_clauses: 0,
            db: totdb::Db::default(),
            offset: 0,
        }
    }
}

impl Extend<Lit> for Totalizer {
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        self.lit_buffer.extend(iter);
    }
}

#[cfg(feature = "proof-logging")]
impl super::cert::BoundUpper for Totalizer {
    fn encode_ub_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), crate::encodings::cert::EncodingError>
    where
        Col: crate::encodings::cert::CollectClauses,
        R: RangeBounds<usize>,
        W: std::io::Write,
    {
        use super::cert::BoundUpperIncremental;
        self.db.reset_encoded(totdb::Semantics::If);
        self.encode_ub_change_cert(range, collector, var_manager, proof)
    }

    fn encode_ub_constr_cert<Col, W>(
        constr: (
            crate::types::constraints::CardUbConstr,
            pigeons::AbsConstraintId,
        ),
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), crate::encodings::cert::EncodingError>
    where
        Col: crate::encodings::cert::CollectClauses,
        W: std::io::Write,
        Self: FromIterator<Lit> + Sized,
    {
        use pigeons::{OperationLike, OperationSequence};

        use crate::types::Var;

        // TODO: properly take care of constraints where no structure is built

        let (constr, id) = constr;
        let (lits, ub) = constr.decompose();
        if ub > lits.len() {
            return Ok(());
        }
        let mut enc = Self::from_iter(lits);
        enc.encode_ub_cert(ub..=ub, collector, var_manager, proof)?;
        let (olit, sem_defs) = enc
            .output_proof_details(ub + 1)
            .expect("encoded just before, so should be fine");
        let unit_id = proof.operations(
            &(OperationSequence::<Var>::from(id) + sem_defs.only_if_def.unwrap()).saturate(),
        )?;
        let unit_cl = crate::clause![!olit];
        #[cfg(feature = "verbose-proofs")]
        proof.equals(&unit_cl, Some(unit_id.into()))?;
        collector.add_cert_clause(unit_cl, unit_id)?;
        enc.db.delete_semantics(proof)?;
        Ok(())
    }
}

#[cfg(feature = "proof-logging")]
impl super::cert::BoundUpperIncremental for Totalizer {
    fn encode_ub_change_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), crate::encodings::cert::EncodingError>
    where
        Col: crate::encodings::cert::CollectClauses,
        R: RangeBounds<usize>,
        W: std::io::Write,
    {
        let range = super::prepare_ub_range(self, range);
        let range = range.start..cmp::min(range.end, self.n_lits() - self.offset);
        if range.is_empty() {
            return Ok(());
        }
        self.extend_tree();
        if let Some(id) = self.root {
            let mut leaves = vec![crate::lit![0]; self.db[id].n_leaves()];
            let mut leaves_init = false;
            let n_vars_before = var_manager.n_used();
            let n_clauses_before = collector.n_clauses();
            for idx in range {
                (_, leaves_init) = self.db.define_unweighted_cert(
                    id,
                    idx + self.offset,
                    totdb::Semantics::If,
                    collector,
                    var_manager,
                    proof,
                    (&mut leaves, leaves_init, false),
                )?;
            }
            self.n_clauses += collector.n_clauses() - n_clauses_before;
            self.n_vars += var_manager.n_used() - n_vars_before;
        }
        Ok(())
    }
}

#[cfg(feature = "proof-logging")]
impl super::cert::BoundLower for Totalizer {
    fn encode_lb_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), crate::encodings::cert::EncodingError>
    where
        Col: crate::encodings::cert::CollectClauses,
        R: RangeBounds<usize>,
        W: std::io::Write,
    {
        use super::cert::BoundLowerIncremental;
        self.db.reset_encoded(totdb::Semantics::OnlyIf);
        self.encode_lb_change_cert(range, collector, var_manager, proof)
    }

    fn encode_lb_constr_cert<Col, W>(
        constr: (
            crate::types::constraints::CardLbConstr,
            pigeons::AbsConstraintId,
        ),
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), crate::encodings::cert::ConstraintEncodingError>
    where
        Col: crate::encodings::cert::CollectClauses,
        W: std::io::Write,
        Self: FromIterator<Lit> + Sized,
    {
        use pigeons::{OperationLike, OperationSequence};

        use crate::types::Var;

        // TODO: properly take care of constraints where no structure is built

        let (constr, id) = constr;
        let (lits, lb) = constr.decompose();
        if lb > lits.len() {
            return Err(crate::encodings::cert::ConstraintEncodingError::Unsat);
        }
        let mut enc = Self::from_iter(lits);
        enc.encode_lb_cert(lb..=lb, collector, var_manager, proof)?;
        let (olit, sem_defs) = enc
            .output_proof_details(lb)
            .expect("encoded right before, so should be fine");
        let unit_id = proof.operations(
            &(OperationSequence::<Var>::from(id) + sem_defs.if_def.unwrap()).saturate(),
        )?;
        let unit_cl = crate::clause![olit];
        #[cfg(feature = "verbose-proofs")]
        proof.equals(&unit_cl, Some(unit_id.into()))?;
        collector.add_cert_clause(unit_cl, unit_id)?;
        enc.db.delete_semantics(proof)?;
        Ok(())
    }
}

#[cfg(feature = "proof-logging")]
impl super::cert::BoundLowerIncremental for Totalizer {
    fn encode_lb_change_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), crate::encodings::cert::EncodingError>
    where
        Col: crate::encodings::cert::CollectClauses,
        R: RangeBounds<usize>,
        W: std::io::Write,
    {
        let range = super::prepare_lb_range(self, range);
        let range = range.start..cmp::min(range.end, self.n_lits() - self.offset + 1);
        if range.is_empty() {
            return Ok(());
        }
        self.extend_tree();
        if let Some(id) = self.root {
            let mut leaves = vec![crate::lit![0]; self.db[id].n_leaves()];
            let mut leaves_init = false;
            let n_vars_before = var_manager.n_used();
            let n_clauses_before = collector.n_clauses();
            for idx in range {
                (_, leaves_init) = self.db.define_unweighted_cert(
                    id,
                    idx - 1 + self.offset,
                    totdb::Semantics::OnlyIf,
                    collector,
                    var_manager,
                    proof,
                    (&mut leaves, leaves_init, false),
                )?;
            }
            self.n_clauses += collector.n_clauses() - n_clauses_before;
            self.n_vars += var_manager.n_used() - n_vars_before;
        }
        Ok(())
    }
}

#[cfg(feature = "proof-logging")]
impl super::cert::BoundBoth for Totalizer {
    fn encode_both_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), crate::encodings::cert::EncodingError>
    where
        Col: crate::encodings::cert::CollectClauses,
        R: RangeBounds<usize> + Clone,
        W: std::io::Write,
    {
        use super::cert::{BoundLowerIncremental, BoundUpperIncremental};

        self.encode_ub_change_cert(range.clone(), collector, var_manager, proof)?;
        self.encode_lb_change_cert(range, collector, var_manager, proof)?;
        Ok(())
    }

    fn encode_eq_constr_cert<Col, W>(
        constr: (
            crate::types::constraints::CardEqConstr,
            pigeons::AbsConstraintId,
        ),
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), crate::encodings::cert::ConstraintEncodingError>
    where
        Col: crate::encodings::cert::CollectClauses,
        W: std::io::Write,
        Self: FromIterator<Lit> + Sized,
    {
        use pigeons::{OperationLike, OperationSequence};

        use crate::types::Var;

        // TODO: properly take care of constraints where no structure is built

        let (constr, id) = constr;
        let (lits, b) = constr.decompose();
        if b > lits.len() {
            return Err(crate::encodings::cert::ConstraintEncodingError::Unsat);
        }
        let mut enc = Self::from_iter(lits);
        enc.encode_both_cert(b..=b, collector, var_manager, proof)?;
        // UB
        let (olit, sem_defs) = enc
            .output_proof_details(b + 1)
            .expect("encoded just before, so should be fine");
        let unit_id = proof.operations(
            &(OperationSequence::<Var>::from(id + 1) + sem_defs.only_if_def.unwrap()).saturate(),
        )?;
        let unit_cl = crate::clause![!olit];
        #[cfg(feature = "verbose-proofs")]
        proof.equals(&unit_cl, Some(unit_id.into()))?;
        collector.add_cert_clause(unit_cl, unit_id)?;
        // LB
        let (olit, sem_defs) = enc
            .output_proof_details(b)
            .expect("encoded just before, so should be fine");
        let unit_id = proof.operations(
            &((OperationSequence::<Var>::from(id) + sem_defs.if_def.unwrap()).saturate()),
        )?;
        let unit_cl = crate::clause![olit];
        #[cfg(feature = "verbose-proofs")]
        proof.equals(&unit_cl, Some(unit_id.into()))?;
        collector.add_cert_clause(unit_cl, unit_id)?;
        enc.db.delete_semantics(proof)?;
        Ok(())
    }
}

#[cfg(feature = "proof-logging")]
impl super::cert::BoundBothIncremental for Totalizer {}

/// Totalizer encoding types that do not own but reference their [`totdb::Db`]
#[cfg(feature = "internals")]
pub mod referenced {
    use std::cell::RefCell;

    use crate::{
        encodings::{
            card::{
                BoundBoth, BoundBothIncremental, BoundLower, BoundLowerIncremental, BoundUpper,
                BoundUpperIncremental, Encode, EncodeIncremental,
            },
            nodedb::{NodeId, NodeLike},
            totdb, CollectClauses, EnforceError, NotEncoded,
        },
        instances::ManageVars,
        types::Lit,
    };

    /// Implementation of the binary adder tree totalizer encoding \[1\].
    /// The implementation is incremental as extended in \[2\].
    /// This uses a _mutable reference_ to a totalizer database.
    ///
    /// # References
    ///
    /// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
    /// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.
    #[derive(Debug)]
    pub struct Tot<'totdb> {
        /// The root of the tree, if constructed
        root: NodeId,
        /// The node database of the totalizer
        db: &'totdb mut totdb::Db,
    }

    /// Implementation of the binary adder tree totalizer encoding \[1\].
    /// The implementation is incremental as extended in \[2\].
    /// This uses a [`RefCell`] to a totalizer database.
    ///
    /// # References
    ///
    /// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
    /// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.
    #[derive(Debug)]
    pub struct TotCell<'totdb> {
        /// The root of the tree, if constructed
        root: NodeId,
        /// The node database of the totalizer
        db: &'totdb RefCell<&'totdb mut totdb::Db>,
    }

    impl<'totdb> Tot<'totdb> {
        /// Constructs a new Totalizer encoding referencing a totalizer database
        pub fn new(root: NodeId, db: &'totdb mut totdb::Db) -> Self {
            Self { root, db }
        }

        /// Gets the maximum depth of the tree
        #[must_use]
        pub fn depth(&self) -> usize {
            self.db[self.root].depth()
        }
    }

    impl<'totdb> TotCell<'totdb> {
        /// Constructs a new Totalizer encoding referencing a totalizer database
        pub fn new(root: NodeId, db: &'totdb RefCell<&'totdb mut totdb::Db>) -> Self {
            Self { root, db }
        }

        /// Gets the maximum depth of the tree
        #[must_use]
        pub fn depth(&self) -> usize {
            self.db.borrow()[self.root].depth()
        }
    }

    impl Encode for Tot<'_> {
        fn n_lits(&self) -> usize {
            self.db[self.root].len()
        }
    }

    impl Encode for TotCell<'_> {
        fn n_lits(&self) -> usize {
            self.db.borrow()[self.root].len()
        }
    }

    impl EncodeIncremental for Tot<'_> {
        fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
            self.db.reserve_vars(self.root, var_manager);
        }
    }

    impl EncodeIncremental for TotCell<'_> {
        fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
            self.db.borrow_mut().reserve_vars(self.root, var_manager);
        }
    }

    impl BoundUpper for Tot<'_> {
        fn encode_ub<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) -> Result<(), crate::OutOfMemory>
        where
            Col: CollectClauses,
            R: std::ops::RangeBounds<usize>,
        {
            self.db.reset_encoded(totdb::Semantics::If);
            self.encode_ub_change(range, collector, var_manager)
        }

        fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, NotEncoded> {
            if ub >= self.n_lits() {
                return Ok(vec![]);
            }
            match &self.db[self.root] {
                totdb::Node::Leaf(lit) => {
                    debug_assert_eq!(ub, 0);
                    return Ok(vec![!*lit]);
                }
                totdb::Node::Unit(node) => {
                    if let totdb::LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = node.lits[ub]
                    {
                        if semantics.has_if() {
                            return Ok(vec![!lit]);
                        }
                    }
                }
                totdb::Node::General(_) | totdb::Node::Dummy => unreachable!(),
            }
            Err(NotEncoded)
        }
    }

    impl BoundUpper for TotCell<'_> {
        fn encode_ub<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) -> Result<(), crate::OutOfMemory>
        where
            Col: CollectClauses,
            R: std::ops::RangeBounds<usize>,
        {
            self.db.borrow_mut().reset_encoded(totdb::Semantics::If);
            self.encode_ub_change(range, collector, var_manager)
        }

        fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, NotEncoded> {
            if ub >= self.n_lits() {
                return Ok(vec![]);
            }
            match &self.db.borrow()[self.root] {
                totdb::Node::Leaf(lit) => {
                    debug_assert_eq!(ub, 0);
                    return Ok(vec![!*lit]);
                }
                totdb::Node::Unit(node) => {
                    if let totdb::LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = node.lits[ub]
                    {
                        if semantics.has_if() {
                            return Ok(vec![!lit]);
                        }
                    }
                }
                totdb::Node::General(_) | totdb::Node::Dummy => unreachable!(),
            }
            Err(NotEncoded)
        }
    }

    impl BoundLower for Tot<'_> {
        fn encode_lb<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) -> Result<(), crate::OutOfMemory>
        where
            Col: CollectClauses,
            R: std::ops::RangeBounds<usize>,
        {
            self.db.reset_encoded(totdb::Semantics::If);
            self.encode_lb_change(range, collector, var_manager)
        }

        fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EnforceError> {
            if lb > self.n_lits() {
                return Err(EnforceError::Unsat);
            }
            match &self.db[self.root] {
                totdb::Node::Leaf(lit) => {
                    debug_assert_eq!(lb, 1);
                    return Ok(vec![*lit]);
                }
                totdb::Node::Unit(node) => {
                    if let totdb::LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = node.lits[lb - 1]
                    {
                        if semantics.has_only_if() {
                            return Ok(vec![lit]);
                        }
                    }
                }
                totdb::Node::General(_) | totdb::Node::Dummy => unreachable!(),
            }
            Err(EnforceError::NotEncoded)
        }
    }

    impl BoundLower for TotCell<'_> {
        fn encode_lb<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) -> Result<(), crate::OutOfMemory>
        where
            Col: CollectClauses,
            R: std::ops::RangeBounds<usize>,
        {
            self.db.borrow_mut().reset_encoded(totdb::Semantics::If);
            self.encode_lb_change(range, collector, var_manager)
        }

        fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EnforceError> {
            if lb > self.n_lits() {
                return Err(EnforceError::Unsat);
            }
            match &self.db.borrow()[self.root] {
                totdb::Node::Leaf(lit) => {
                    debug_assert_eq!(lb, 1);
                    return Ok(vec![*lit]);
                }
                totdb::Node::Unit(node) => {
                    if let totdb::LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = node.lits[lb - 1]
                    {
                        if semantics.has_only_if() {
                            return Ok(vec![lit]);
                        }
                    }
                }
                totdb::Node::General(_) | totdb::Node::Dummy => unreachable!(),
            }
            Err(EnforceError::NotEncoded)
        }
    }

    impl BoundUpperIncremental for Tot<'_> {
        fn encode_ub_change<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) -> Result<(), crate::OutOfMemory>
        where
            Col: CollectClauses,
            R: std::ops::RangeBounds<usize>,
        {
            let range = super::super::prepare_ub_range(self, range);
            if range.is_empty() {
                return Ok(());
            }
            for idx in range {
                self.db.define_unweighted(
                    self.root,
                    idx,
                    totdb::Semantics::If,
                    collector,
                    var_manager,
                )?;
            }
            Ok(())
        }
    }

    impl BoundUpperIncremental for TotCell<'_> {
        fn encode_ub_change<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) -> Result<(), crate::OutOfMemory>
        where
            Col: CollectClauses,
            R: std::ops::RangeBounds<usize>,
        {
            let range = super::super::prepare_ub_range(self, range);
            if range.is_empty() {
                return Ok(());
            }
            for idx in range {
                self.db.borrow_mut().define_unweighted(
                    self.root,
                    idx,
                    totdb::Semantics::If,
                    collector,
                    var_manager,
                )?;
            }
            Ok(())
        }
    }

    impl BoundLowerIncremental for Tot<'_> {
        fn encode_lb_change<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) -> Result<(), crate::OutOfMemory>
        where
            Col: CollectClauses,
            R: std::ops::RangeBounds<usize>,
        {
            let range = super::super::prepare_lb_range(self, range);
            if range.is_empty() {
                return Ok(());
            }
            for idx in range {
                self.db.define_unweighted(
                    self.root,
                    idx - 1,
                    totdb::Semantics::OnlyIf,
                    collector,
                    var_manager,
                )?;
            }
            Ok(())
        }
    }

    impl BoundLowerIncremental for TotCell<'_> {
        fn encode_lb_change<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) -> Result<(), crate::OutOfMemory>
        where
            Col: CollectClauses,
            R: std::ops::RangeBounds<usize>,
        {
            let range = super::super::prepare_lb_range(self, range);
            if range.is_empty() {
                return Ok(());
            }
            for idx in range {
                self.db.borrow_mut().define_unweighted(
                    self.root,
                    idx - 1,
                    totdb::Semantics::OnlyIf,
                    collector,
                    var_manager,
                )?;
            }
            Ok(())
        }
    }

    impl BoundBoth for Tot<'_> {
        fn encode_both<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) -> Result<(), crate::OutOfMemory>
        where
            Col: CollectClauses,
            R: std::ops::RangeBounds<usize> + Clone,
        {
            self.encode_ub_change(range.clone(), collector, var_manager)?;
            self.encode_lb_change(range, collector, var_manager)?;
            Ok(())
        }
    }

    impl BoundBoth for TotCell<'_> {
        fn encode_both<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) -> Result<(), crate::OutOfMemory>
        where
            Col: CollectClauses,
            R: std::ops::RangeBounds<usize> + Clone,
        {
            self.encode_ub_change(range.clone(), collector, var_manager)?;
            self.encode_lb_change(range, collector, var_manager)?;
            Ok(())
        }
    }

    impl BoundBothIncremental for Tot<'_> {}

    impl BoundBothIncremental for TotCell<'_> {}
}

#[cfg(test)]
mod tests {
    use super::Totalizer;
    use crate::{
        encodings::{
            card::{
                BoundLower, BoundLowerIncremental, BoundUpper, BoundUpperIncremental,
                EncodeIncremental,
            },
            EncodeStats, EnforceError, NotEncoded,
        },
        instances::{BasicVarManager, Cnf, ManageVars},
        lit, var,
    };

    #[test]
    fn functions() {
        let mut tot = Totalizer::default();
        tot.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        assert_eq!(tot.enforce_ub(2), Err(NotEncoded));
        assert_eq!(tot.enforce_lb(2), Err(EnforceError::NotEncoded));
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf = Cnf::new();
        tot.encode_ub(0..5, &mut cnf, &mut var_manager).unwrap();
        assert_eq!(tot.depth(), 3);
        println!("len: {}, {:?}", cnf.len(), cnf);
        assert_eq!(cnf.len(), 14);
        assert_eq!(tot.n_clauses(), 14);
        assert_eq!(tot.n_vars(), 8);
        assert_eq!(tot.enforce_ub(2).unwrap().len(), 1);
    }

    #[test]
    fn capi_basics() {
        let mut tot = Totalizer::default();
        tot.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf = Cnf::new();
        tot.encode_ub(0..=4, &mut cnf, &mut var_manager).unwrap();
        tot.encode_lb(0..=4, &mut cnf, &mut var_manager).unwrap();
        assert_eq!(var_manager.n_used(), 12);
        assert_eq!(cnf.len(), 28);
    }

    #[test]
    fn functions_min_rhs() {
        let mut tot = Totalizer::default();
        tot.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf = Cnf::new();
        tot.encode_ub(3..4, &mut cnf, &mut var_manager).unwrap();
        assert_eq!(tot.depth(), 3);
        assert_eq!(cnf.len(), 3);
        assert_eq!(cnf.len(), tot.n_clauses());
    }

    #[test]
    fn incremental_building_ub() {
        let mut tot1 = Totalizer::default();
        tot1.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf1 = Cnf::new();
        tot1.encode_ub(0..5, &mut cnf1, &mut var_manager).unwrap();
        let mut tot2 = Totalizer::default();
        tot2.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf2 = Cnf::new();
        tot2.encode_ub(0..3, &mut cnf2, &mut var_manager).unwrap();
        tot2.encode_ub_change(0..5, &mut cnf2, &mut var_manager)
            .unwrap();
        assert_eq!(cnf1.len(), cnf2.len());
        assert_eq!(cnf1.len(), tot1.n_clauses());
        assert_eq!(cnf2.len(), tot2.n_clauses());
    }

    #[test]
    fn incremental_building_lb() {
        let mut tot1 = Totalizer::default();
        tot1.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf1 = Cnf::new();
        tot1.encode_lb(0..5, &mut cnf1, &mut var_manager).unwrap();
        let mut tot2 = Totalizer::default();
        tot2.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf2 = Cnf::new();
        tot2.encode_lb(0..3, &mut cnf2, &mut var_manager).unwrap();
        tot2.encode_lb_change(0..5, &mut cnf2, &mut var_manager)
            .unwrap();
        assert_eq!(cnf1.len(), cnf2.len());
        assert_eq!(cnf1.len(), tot1.n_clauses());
        assert_eq!(cnf2.len(), tot2.n_clauses());
    }

    #[test]
    fn reserve() {
        let mut tot = Totalizer::default();
        tot.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::from_next_free(var![4]);
        tot.reserve(&mut var_manager);
        assert_eq!(var_manager.n_used(), 12);
        let mut cnf = Cnf::new();
        tot.encode_ub(0..3, &mut cnf, &mut var_manager).unwrap();
        assert_eq!(var_manager.n_used(), 12);
    }

    #[cfg(feature = "proof-logging")]
    mod proofs {
        use std::{
            fs::File,
            io::{BufRead, BufReader},
            path::Path,
            process::Command,
        };

        use crate::{
            encodings::card::cert::BoundBoth,
            instances::{Cnf, SatInstance},
            types::{constraints::CardConstraint, Var},
        };

        fn print_file<P: AsRef<Path>>(path: P) {
            println!();
            for line in BufReader::new(File::open(path).expect("could not open file")).lines() {
                println!("{}", line.unwrap());
            }
            println!();
        }

        fn verify_proof<P1: AsRef<Path>, P2: AsRef<Path>>(instance: P1, proof: P2) {
            if let Ok(veripb) = std::env::var("VERIPB_CHECKER") {
                println!("start checking proof");
                let out = Command::new(veripb)
                    .arg(instance.as_ref())
                    .arg(proof.as_ref())
                    .output()
                    .expect("failed to run veripb");
                print_file(proof);
                if out.status.success() {
                    return;
                }
                panic!("verification failed: {out:?}")
            } else {
                println!("`$VERIPB_CHECKER` not set, omitting proof checking");
            }
        }

        fn new_proof(
            num_constraints: usize,
            optimization: bool,
        ) -> pigeons::Proof<tempfile::NamedTempFile> {
            let file =
                tempfile::NamedTempFile::new().expect("failed to create temporary proof file");
            pigeons::Proof::new(file, num_constraints, optimization).expect("failed to start proof")
        }

        #[test]
        fn constraint() {
            let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
            let inst_path = format!("{manifest}/data/single-card-eq.opb");
            let constr: SatInstance = SatInstance::from_opb_path(
                &inst_path,
                crate::instances::fio::opb::Options::default(),
            )
            .unwrap();
            let (constr, mut vm) = constr.into_pbs();
            assert_eq!(constr.len(), 1);
            let constr = constr.into_iter().next().unwrap();
            let constr = constr.into_card_constr().unwrap();
            let CardConstraint::Eq(constr) = constr else {
                panic!()
            };
            let mut cnf = Cnf::new();
            let mut proof = new_proof(2, false);
            super::Totalizer::encode_eq_constr_cert(
                (constr, pigeons::AbsConstraintId::new(1)),
                &mut cnf,
                &mut vm,
                &mut proof,
            )
            .unwrap();
            let proof_file = proof
                .conclude::<Var>(pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
                .unwrap();
            verify_proof(&inst_path, proof_file.path());
        }
    }
}
