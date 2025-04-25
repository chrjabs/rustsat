//! # Generalized Totalizer Encoding
//!
//! Implementation of the binary adder tree generalized totalizer encoding
//! \[1\]. The implementation is incremental. The implementation is recursive.
//! This encoding only support upper bounding. Lower bounding can be achieved by
//! negating the input literals. This is implemented in
//! [`super::simulators::Inverted`].
//! The implementation is based on a node database.
//!
//! # References
//!
//! - \[1\] Saurabh Joshi and Ruben Martins and Vasco Manquinho: _Generalized
//!   Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.

use std::ops::RangeBounds;

use crate::{
    encodings::{
        nodedb::{NodeById, NodeCon, NodeLike},
        totdb, CollectClauses, EncodeStats, EnforceError, Monotone,
    },
    instances::ManageVars,
    types::{Lit, RsHashMap},
};

use super::{BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental};

/// Implementation of the binary adder tree generalized totalizer encoding
/// \[1\]. The implementation is incremental. The implementation is recursive.
/// This encoding only support upper bounding. Lower bounding can be achieved by
/// negating the input literals. This is implemented in
/// [`super::simulators::Inverted`].
/// The implementation is based on a node database.
///
/// # References
///
/// - \[1\] Saurabh Joshi and Ruben Martins and Vasco Manquinho: _Generalized
///   Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.
#[derive(Default, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GeneralizedTotalizer {
    /// Input literals and weights not yet in the tree
    lit_buffer: RsHashMap<Lit, usize>,
    /// The root of the tree, if constructed
    root: Option<NodeCon>,
    /// Maximum weight of a leaf, needed for computing how much more than
    /// `max_rhs` to encode
    max_leaf_weight: usize,
    /// The number of variables in the totalizer
    n_vars: u32,
    /// The number of clauses in the totalizer
    n_clauses: usize,
    /// The node database of the totalizer
    db: totdb::Db,
}

impl GeneralizedTotalizer {
    /// Creates a generalized totalizer from its internal parts
    #[cfg(feature = "internals")]
    #[must_use]
    pub fn from_raw(root: NodeCon, db: totdb::Db, max_leaf_weight: usize) -> Self {
        Self {
            root: Some(root),
            max_leaf_weight,
            db,
            ..Default::default()
        }
    }

    fn extend_tree(&mut self, max_weight: usize) {
        if !self.lit_buffer.is_empty() {
            let mut new_lits: Vec<(Lit, usize)> = self
                .lit_buffer
                .iter()
                .filter_map(|(&l, &w)| {
                    if w <= max_weight {
                        if w > self.max_leaf_weight {
                            self.max_leaf_weight = w;
                        }
                        Some((l, w))
                    } else {
                        None
                    }
                })
                .collect();
            if !new_lits.is_empty() {
                // add nodes in sorted fashion to minimize clauses
                new_lits.sort_by_key(|(_, w)| *w);
                // Detect sequences of literals of equal weight and merge them
                let mut seg_begin = 0;
                let mut seg_end = 0;
                let mut cons = vec![];
                loop {
                    seg_end += 1;
                    if seg_end < new_lits.len() && new_lits[seg_end].1 == new_lits[seg_begin].1 {
                        continue;
                    }
                    // merge lits of equal weight
                    let seg: Vec<_> = new_lits[seg_begin..seg_end]
                        .iter()
                        .map(|(lit, _)| *lit)
                        .collect();
                    let id = self.db.lit_tree(&seg);
                    cons.push(NodeCon::weighted(id, new_lits[seg_begin].1));
                    seg_begin = seg_end;
                    if seg_end >= new_lits.len() {
                        break;
                    }
                }
                if let Some(con) = self.root {
                    cons.push(con);
                }
                self.root = Some(self.db.merge_balanced(&cons));
                self.lit_buffer.retain(|_, w| *w > max_weight);
            }
        }
    }

    /// Gets the depth of the encoding, i.e., the longest path from the root to a leaf
    #[must_use]
    pub fn depth(&self) -> usize {
        self.root.map_or(0, |con| self.db[con.id].depth())
    }

    /// Gets the details of a generalized totalizer output related to proof logging
    ///
    /// # Errors
    ///
    /// If the requested output is not encoded
    #[cfg(feature = "proof-logging")]
    pub fn output_proof_details(
        &self,
        value: usize,
    ) -> Result<(Lit, totdb::cert::SemDefs), crate::encodings::NotEncoded> {
        match self.root {
            None => Err(crate::encodings::NotEncoded),
            Some(root) => {
                if !root.is_possible(value) {
                    return Err(crate::encodings::NotEncoded);
                }
                self.db
                    .get_semantics(root.id, root.offset, root.rev_map(value))
                    .map(|sem| (self.db[root.id][root.rev_map(value)], sem))
                    .ok_or(crate::encodings::NotEncoded)
            }
        }
    }

    /// Gets the number of output literals in the generalized totalizer
    #[must_use]
    pub fn n_output_lits(&self) -> usize {
        match self.root {
            Some(root) => self.db[root.id].len(),
            None => 0,
        }
    }

    /// Checks if the input literal buffer is empty, i.e., all input literals are included in the
    /// encoding.
    ///
    /// Even after encodings, this might not be the case, if an input literal has a higher weight
    /// than the bound encoded for
    #[must_use]
    pub fn is_buffer_empty(&self) -> bool {
        self.lit_buffer.is_empty()
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
            .map(|root| self.db.strictly_extend_assignment(root.id, assign))
            .into_iter()
            .flatten()
    }
}

impl Encode for GeneralizedTotalizer {
    fn weight_sum(&self) -> usize {
        self.lit_buffer.iter().fold(0, |sum, (_, w)| sum + w)
            + if let Some(root) = self.root {
                root.map(self.db[root.id].max_val())
            } else {
                0
            }
    }

    fn next_higher(&self, val: usize) -> usize {
        if let Some(con) = self.root {
            self.db[con.id]
                .vals(con.rev_map_round_up(val + 1)..)
                .next()
                .map_or(val + 1, |val| con.map(val))
        } else {
            val + 1
        }
    }

    fn next_lower(&self, val: usize) -> usize {
        if val == 0 {
            return 0;
        }
        if let Some(con) = self.root {
            return self.db[con.id]
                .vals(con.offset()..con.rev_map_round_up(val))
                .next_back()
                .map_or(0, |val| con.map(val));
        }
        val - 1
    }
}

impl EncodeIncremental for GeneralizedTotalizer {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.extend_tree(usize::MAX);
        if let Some(con) = self.root {
            self.db.reserve_vars(con.id, var_manager);
        }
    }
}

impl BoundUpper for GeneralizedTotalizer {
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

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EnforceError> {
        if ub >= self.weight_sum() {
            return Ok(vec![]);
        }

        let mut assumps = vec![];
        self.lit_buffer.iter().try_for_each(|(&l, &w)| {
            if w <= ub {
                Err(EnforceError::NotEncoded)
            } else {
                assumps.push(!l);
                Ok(())
            }
        })?;
        // Enforce bound on internal tree
        if let Some(con) = self.root {
            self.db[con.id]
                .vals(con.rev_map_round_up(ub + 1)..=con.rev_map(ub + self.max_leaf_weight))
                .try_for_each(|val| {
                    match &self.db[con.id] {
                        totdb::Node::Leaf(lit) => {
                            assumps.push(!*lit);
                            return Ok(());
                        }
                        totdb::Node::Unit(node) => {
                            if let totdb::LitData::Lit {
                                lit,
                                semantics: Some(semantics),
                            } = node.lits[val - 1]
                            {
                                if semantics.has_if() {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        totdb::Node::General(node) => {
                            if let Some(totdb::LitData::Lit {
                                lit,
                                semantics: Some(semantics),
                            }) = node.lit_data(val)
                            {
                                if semantics.has_if() {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        totdb::Node::Dummy => unreachable!(),
                    }
                    Err(EnforceError::NotEncoded)
                })?;
        }
        Ok(assumps)
    }
}

impl BoundUpperIncremental for GeneralizedTotalizer {
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
        if range.is_empty() {
            return Ok(());
        }
        let n_vars_before = var_manager.n_used();
        let n_clauses_before = collector.n_clauses();
        self.extend_tree(range.end - 1);
        if let Some(con) = self.root {
            self.db[con.id]
                .vals(
                    con.rev_map_round_up(range.start + 1)
                        ..=con.rev_map(range.end + self.max_leaf_weight),
                )
                .try_for_each(|val| {
                    self.db
                        .define_weighted(con.id, val, collector, var_manager)?
                        .unwrap();
                    Ok::<(), crate::OutOfMemory>(())
                })?;
        }
        self.n_clauses += collector.n_clauses() - n_clauses_before;
        self.n_vars += var_manager.n_used() - n_vars_before;
        Ok(())
    }
}

impl Monotone for GeneralizedTotalizer {}

impl EncodeStats for GeneralizedTotalizer {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        self.n_vars
    }
}

impl From<RsHashMap<Lit, usize>> for GeneralizedTotalizer {
    fn from(lits: RsHashMap<Lit, usize>) -> Self {
        Self {
            lit_buffer: lits,
            ..Default::default()
        }
    }
}

impl FromIterator<(Lit, usize)> for GeneralizedTotalizer {
    fn from_iter<T: IntoIterator<Item = (Lit, usize)>>(iter: T) -> Self {
        let lits: RsHashMap<Lit, usize> = RsHashMap::from_iter(iter);
        Self::from(lits)
    }
}

impl Extend<(Lit, usize)> for GeneralizedTotalizer {
    fn extend<T: IntoIterator<Item = (Lit, usize)>>(&mut self, iter: T) {
        iter.into_iter().for_each(|(l, w)| {
            // Insert into buffer to be added to tree
            match self.lit_buffer.get_mut(&l) {
                Some(old_w) => *old_w += w,
                None => {
                    self.lit_buffer.insert(l, w);
                }
            }
        });
    }
}

#[cfg(feature = "proof-logging")]
impl super::cert::BoundUpper for GeneralizedTotalizer {
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
            crate::types::constraints::PbUbConstr,
            pigeons::AbsConstraintId,
        ),
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), crate::encodings::cert::ConstraintEncodingError>
    where
        Col: crate::encodings::cert::CollectClauses,
        W: std::io::Write,
        Self: FromIterator<(Lit, usize)> + Sized,
    {
        use pigeons::{OperationSequence, VarLike};

        use crate::types::Var;

        // TODO: properly take care of constraints where no structure is built

        let (constr, mut id) = constr;
        let (lits, ub) = constr.decompose();
        if ub < 0 {
            return Err(crate::encodings::cert::ConstraintEncodingError::Unsat);
        }
        let ub = ub.unsigned_abs();
        if ub > lits.iter().fold(0, |sum, (_, w)| sum + *w) {
            return Ok(());
        }
        let mut enc = Self::from_iter(lits);
        enc.encode_ub_cert(ub..=ub, collector, var_manager, proof)?;
        let mut val = enc.next_higher(ub);
        for unit in enc
            .enforce_ub(ub)
            .expect("should have caught special case before here")
        {
            let (olit, sem_defs) = enc
                .output_proof_details(val)
                .expect("encoded just before, so should be fine");
            let unit_cl = crate::clause![unit];
            let unit_id = if unit.var() < olit.var() {
                // input literal with weight larger than bound
                let weight = *enc.lit_buffer.get(&!unit).unwrap();
                let unit_id = proof.reverse_unit_prop(&unit_cl, [id.into()])?;
                // simplify main constraint
                #[cfg(feature = "verbose-proofs")]
                proof.comment(&"rewritten main constraint")?;
                id = proof.operations(
                    &(OperationSequence::<Var>::from(unit.var().axiom(!unit.is_neg())) * weight
                        + id),
                )?;
                unit_id
            } else {
                // output literal
                // NOTE: by the time we're here, all buffered literals have been removed from `id`
                debug_assert_eq!(!unit, olit);
                let unit_id = proof.operations(
                    &((OperationSequence::<Var>::from(id) + sem_defs.only_if_def.unwrap()) / val),
                )?;
                #[cfg(feature = "verbose-proofs")]
                proof.equals(&unit_cl, Some(unit_id.into()))?;
                val = enc.next_higher(val);
                unit_id
            };
            collector.add_cert_clause(unit_cl, unit_id)?;
        }
        enc.db.delete_semantics(proof)?;
        Ok(())
    }
}

#[cfg(feature = "proof-logging")]
impl super::cert::BoundUpperIncremental for GeneralizedTotalizer {
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
        if range.is_empty() {
            return Ok(());
        }
        let n_vars_before = var_manager.n_used();
        let n_clauses_before = collector.n_clauses();
        self.extend_tree(range.end - 1);
        if let Some(con) = self.root {
            let mut leaves = vec![(crate::lit![0], 0); self.db[con.id].n_leaves()];
            let mut leaves_init = false;
            self.db[con.id]
                .vals(
                    con.rev_map_round_up(range.start + 1)
                        ..=con.rev_map(range.end + self.max_leaf_weight),
                )
                .try_for_each(|val| {
                    (_, leaves_init) = self
                        .db
                        .define_weighted_cert(
                            con.id,
                            val,
                            collector,
                            var_manager,
                            proof,
                            (&mut leaves, leaves_init, false),
                        )?
                        .unwrap();
                    Ok::<(), crate::encodings::cert::EncodingError>(())
                })?;
        }
        self.n_clauses += collector.n_clauses() - n_clauses_before;
        self.n_vars += var_manager.n_used() - n_vars_before;
        Ok(())
    }
}

/// Generalized totalizer encoding types that do not own but reference their [`totdb::Db`]
#[cfg(feature = "internals")]
pub mod referenced {
    use std::{cell::RefCell, ops::RangeBounds};

    use crate::{
        encodings::{
            nodedb::{NodeCon, NodeLike},
            pb::{BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental},
            totdb, CollectClauses, EnforceError,
        },
        instances::ManageVars,
        types::Lit,
    };

    /// Generalized totalizer encoding with a _mutable reference_ to a totalizer
    /// database rather than owning it.
    ///
    /// ## References
    ///
    /// - \[1\] Saurabh Joshi and Ruben Martins and Vasco Manquinho: _Generalized
    ///   Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.
    #[derive(Debug)]
    pub struct Gte<'totdb> {
        /// A node connection to the root
        root: NodeCon,
        /// The maximum weight of any leaf
        max_leaf_weight: usize,
        /// The node database of the totalizer
        db: &'totdb mut totdb::Db,
    }

    /// Generalized totalizer encoding with a [`RefCell`] to a totalizer
    /// database rather than owning it.
    ///
    /// ## References
    ///
    /// - \[1\] Saurabh Joshi and Ruben Martins and Vasco Manquinho: _Generalized
    ///   Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.
    #[derive(Debug)]
    pub struct GteCell<'totdb> {
        /// A node connection to the root
        root: NodeCon,
        /// The maximum weight of any leaf
        max_leaf_weight: usize,
        /// The node database of the totalizer
        db: &'totdb RefCell<&'totdb mut totdb::Db>,
    }

    impl<'totdb> Gte<'totdb> {
        /// Constructs a new GTE encoding referencing a totalizer database
        pub fn new(root: NodeCon, max_leaf_weight: usize, db: &'totdb mut totdb::Db) -> Self {
            Self {
                root,
                max_leaf_weight,
                db,
            }
        }

        /// Gets the maximum depth of the tree
        #[must_use]
        pub fn depth(&self) -> usize {
            self.db[self.root.id].depth()
        }
    }

    impl<'totdb> GteCell<'totdb> {
        /// Constructs a new GTE encoding referencing a totalizer database
        pub fn new(
            root: NodeCon,
            max_leaf_weight: usize,
            db: &'totdb RefCell<&'totdb mut totdb::Db>,
        ) -> Self {
            Self {
                root,
                max_leaf_weight,
                db,
            }
        }

        /// Gets the maximum depth of the tree
        #[must_use]
        pub fn depth(&self) -> usize {
            self.db.borrow()[self.root.id].depth()
        }
    }

    impl Encode for Gte<'_> {
        fn weight_sum(&self) -> usize {
            self.root.map(self.db[self.root.id].max_val())
        }

        fn next_higher(&self, val: usize) -> usize {
            self.db[self.root.id]
                .vals(self.root.rev_map_round_up(val + 1)..)
                .next()
                .map_or(val + 1, |val| self.root.map(val))
        }

        fn next_lower(&self, val: usize) -> usize {
            self.db[self.root.id]
                .vals(self.root.offset()..self.root.rev_map_round_up(val))
                .next_back()
                .map_or(val - 1, |val| self.root.map(val))
        }
    }

    impl Encode for GteCell<'_> {
        fn weight_sum(&self) -> usize {
            self.root.map(self.db.borrow()[self.root.id].max_val())
        }

        fn next_higher(&self, val: usize) -> usize {
            self.db.borrow()[self.root.id]
                .vals(self.root.rev_map_round_up(val + 1)..)
                .next()
                .map_or(val + 1, |val| self.root.map(val))
        }

        fn next_lower(&self, val: usize) -> usize {
            self.db.borrow()[self.root.id]
                .vals(self.root.offset()..self.root.rev_map_round_up(val))
                .next_back()
                .map_or(val - 1, |val| self.root.map(val))
        }
    }

    impl EncodeIncremental for Gte<'_> {
        fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
            self.db.reserve_vars(self.root.id, var_manager);
        }
    }

    impl EncodeIncremental for GteCell<'_> {
        fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
            self.db.borrow_mut().reserve_vars(self.root.id, var_manager);
        }
    }

    impl BoundUpper for Gte<'_> {
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

        fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EnforceError> {
            if ub >= self.weight_sum() {
                return Ok(vec![]);
            }

            let mut assumps = vec![];
            // Enforce bound on internal tree
            self.db[self.root.id]
                .vals(
                    self.root.rev_map_round_up(ub + 1)
                        ..=self.root.rev_map(ub + self.max_leaf_weight),
                )
                .try_for_each(|val| {
                    match &self.db[self.root.id] {
                        totdb::Node::Leaf(lit) => {
                            assumps.push(!*lit);
                            return Ok(());
                        }
                        totdb::Node::Unit(node) => {
                            if let totdb::LitData::Lit {
                                lit,
                                semantics: Some(semantics),
                            } = node.lits[val - 1]
                            {
                                if semantics.has_if() {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        totdb::Node::General(node) => {
                            if let Some(totdb::LitData::Lit {
                                lit,
                                semantics: Some(semantics),
                            }) = node.lit_data(val)
                            {
                                if semantics.has_if() {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        totdb::Node::Dummy => panic!(),
                    }
                    Err(EnforceError::NotEncoded)
                })?;
            Ok(assumps)
        }
    }

    impl BoundUpper for GteCell<'_> {
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
            self.db.borrow_mut().reset_encoded(totdb::Semantics::If);
            self.encode_ub_change(range, collector, var_manager)
        }

        fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EnforceError> {
            if ub >= self.weight_sum() {
                return Ok(vec![]);
            }

            let mut assumps = vec![];
            // Enforce bound on internal tree
            self.db.borrow()[self.root.id]
                .vals(
                    self.root.rev_map_round_up(ub + 1)
                        ..=self.root.rev_map(ub + self.max_leaf_weight),
                )
                .try_for_each(|val| {
                    match &self.db.borrow()[self.root.id] {
                        totdb::Node::Leaf(lit) => {
                            assumps.push(!*lit);
                            return Ok(());
                        }
                        totdb::Node::Unit(node) => {
                            if let totdb::LitData::Lit {
                                lit,
                                semantics: Some(semantics),
                            } = node.lits[val - 1]
                            {
                                if semantics.has_if() {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        totdb::Node::General(node) => {
                            if let Some(totdb::LitData::Lit {
                                lit,
                                semantics: Some(semantics),
                            }) = node.lit_data(val)
                            {
                                if semantics.has_if() {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        totdb::Node::Dummy => unreachable!(),
                    }
                    Err(EnforceError::NotEncoded)
                })?;
            Ok(assumps)
        }
    }

    impl BoundUpperIncremental for Gte<'_> {
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
            let range = super::super::prepare_ub_range(self, range);
            if range.is_empty() {
                return Ok(());
            }
            self.db[self.root.id]
                .vals(
                    self.root.rev_map_round_up(range.start + 1)
                        ..=self.root.rev_map(range.end + self.max_leaf_weight),
                )
                .try_for_each(|val| {
                    self.db
                        .define_weighted(self.root.id, val, collector, var_manager)?
                        .unwrap();
                    Ok::<(), crate::OutOfMemory>(())
                })?;
            Ok(())
        }
    }

    impl BoundUpperIncremental for GteCell<'_> {
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
            let range = super::super::prepare_ub_range(self, range);
            if range.is_empty() {
                return Ok(());
            }
            let mut vals = self.db.borrow()[self.root.id].vals(
                self.root.rev_map_round_up(range.start + 1)
                    ..=self.root.rev_map(range.end + self.max_leaf_weight),
            );
            vals.try_for_each(|val| {
                self.db
                    .borrow_mut()
                    .define_weighted(self.root.id, val, collector, var_manager)?
                    .unwrap();
                Ok::<(), crate::OutOfMemory>(())
            })?;
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::GeneralizedTotalizer;
    use crate::{
        encodings::{
            card,
            pb::{BoundUpper, BoundUpperIncremental, EncodeIncremental},
            EncodeStats, EnforceError,
        },
        instances::{BasicVarManager, Cnf, ManageVars},
        lit,
        types::RsHashMap,
        var,
    };

    #[test]
    fn ub_gte_functions() {
        let mut gte = GeneralizedTotalizer::default();
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 5);
        lits.insert(lit![2], 3);
        lits.insert(lit![3], 3);
        gte.extend(lits);
        assert_eq!(gte.enforce_ub(4), Err(EnforceError::NotEncoded));
        let mut var_manager = BasicVarManager::default();
        gte.encode_ub(0..7, &mut Cnf::new(), &mut var_manager)
            .unwrap();
        assert_eq!(gte.depth(), 3);
        assert_eq!(gte.n_vars(), 10);
    }

    #[test]
    fn ub_gte_incremental_building() {
        let mut gte1 = GeneralizedTotalizer::default();
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 5);
        lits.insert(lit![2], 3);
        lits.insert(lit![3], 3);
        gte1.extend(lits.clone());
        let mut var_manager = BasicVarManager::default();
        let mut cnf1 = Cnf::new();
        gte1.encode_ub(0..5, &mut cnf1, &mut var_manager).unwrap();
        let mut gte2 = GeneralizedTotalizer::default();
        gte2.extend(lits);
        let mut var_manager = BasicVarManager::default();
        let mut cnf2 = Cnf::new();
        gte2.encode_ub(0..3, &mut cnf2, &mut var_manager).unwrap();
        gte2.encode_ub_change(0..5, &mut cnf2, &mut var_manager)
            .unwrap();
        assert_eq!(cnf1.len(), cnf2.len());
        assert_eq!(cnf1.len(), gte1.n_clauses());
        assert_eq!(cnf2.len(), gte2.n_clauses());
    }

    #[test]
    fn from_capi() {
        let mut gte1 = GeneralizedTotalizer::default();
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 1);
        lits.insert(lit![1], 2);
        lits.insert(lit![2], 3);
        lits.insert(lit![3], 4);
        gte1.extend(lits);
        let mut var_manager = BasicVarManager::from_next_free(var![4]);
        let mut cnf = Cnf::new();
        gte1.encode_ub(0..=6, &mut cnf, &mut var_manager).unwrap();
        debug_assert_eq!(var_manager.n_used(), 24);
        debug_assert_eq!(cnf.len(), 25);
    }

    #[test]
    fn ub_gte_multiplication() {
        let mut gte1 = GeneralizedTotalizer::default();
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 5);
        lits.insert(lit![2], 3);
        lits.insert(lit![3], 3);
        gte1.extend(lits);
        let mut var_manager = BasicVarManager::default();
        let mut cnf1 = Cnf::new();
        gte1.encode_ub(0..5, &mut cnf1, &mut var_manager).unwrap();
        let mut gte2 = GeneralizedTotalizer::default();
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 10);
        lits.insert(lit![1], 10);
        lits.insert(lit![2], 6);
        lits.insert(lit![3], 6);
        gte2.extend(lits);
        let mut var_manager = BasicVarManager::default();
        let mut cnf2 = Cnf::new();
        gte2.encode_ub(0..9, &mut cnf2, &mut var_manager).unwrap();
        assert_eq!(cnf1.len(), cnf2.len());
        assert_eq!(cnf1.len(), gte1.n_clauses());
        assert_eq!(cnf2.len(), gte2.n_clauses());
    }

    #[test]
    fn ub_gte_equals_tot() {
        let mut var_manager_gte = BasicVarManager::default();
        var_manager_gte.increase_next_free(var![7]);
        let mut var_manager_tot = var_manager_gte.clone();
        // Set up GTE
        let mut gte = GeneralizedTotalizer::default();
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 1);
        lits.insert(lit![1], 1);
        lits.insert(lit![2], 1);
        lits.insert(lit![3], 1);
        lits.insert(lit![4], 1);
        lits.insert(lit![5], 1);
        lits.insert(lit![6], 1);
        gte.extend(lits);
        let mut gte_cnf = Cnf::new();
        gte.encode_ub(3..8, &mut gte_cnf, &mut var_manager_gte)
            .unwrap();
        // Set up Tot
        let mut tot = card::Totalizer::default();
        tot.extend(vec![
            lit![0],
            lit![1],
            lit![2],
            lit![3],
            lit![4],
            lit![5],
            lit![6],
        ]);
        let mut tot_cnf = Cnf::new();
        card::BoundUpper::encode_ub(&mut tot, 3..8, &mut tot_cnf, &mut var_manager_tot).unwrap();
        println!("{gte_cnf:?}");
        println!("{tot_cnf:?}");
        assert_eq!(var_manager_gte.new_var(), var_manager_tot.new_var());
        assert_eq!(gte_cnf.len(), tot_cnf.len());
        assert_eq!(gte_cnf.len(), gte.n_clauses());
        assert_eq!(tot_cnf.len(), tot.n_clauses());
    }

    #[test]
    fn reserve() {
        let mut gte = GeneralizedTotalizer::default();
        gte.extend(vec![(lit![0], 1), (lit![1], 2), (lit![2], 3), (lit![3], 4)]);
        let mut var_manager = BasicVarManager::from_next_free(var![4]);
        gte.reserve(&mut var_manager);
        assert_eq!(var_manager.n_used(), 24);
        let mut cnf = Cnf::new();
        gte.encode_ub(0..3, &mut cnf, &mut var_manager).unwrap();
        assert_eq!(var_manager.n_used(), 24);
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
            encodings::pb::cert::BoundUpper,
            instances::{Cnf, SatInstance},
            types::{constraints::PbConstraint, Var},
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
            let inst_path = format!("{manifest}/data/single-ub.opb");
            let constr: SatInstance = SatInstance::from_opb_path(
                &inst_path,
                crate::instances::fio::opb::Options::default(),
            )
            .unwrap();
            let (constr, mut vm) = constr.into_pbs();
            assert_eq!(constr.len(), 1);
            let Some(PbConstraint::Lb(constr)) = constr.into_iter().next() else {
                panic!()
            };
            let constr = constr.invert();
            let mut cnf = Cnf::new();
            let mut proof = new_proof(1, false);
            super::GeneralizedTotalizer::encode_ub_constr_cert(
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
