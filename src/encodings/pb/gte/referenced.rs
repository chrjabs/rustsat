//! Generalized totalizer encoding types that do not own but reference their [`totdb::Db`]
#![cfg(feature = "_internals")]

use crate::encodings::CollectClauses;
use crate::encodings::EnforceError;
use crate::encodings::nodedb::NodeCon;
use crate::encodings::nodedb::NodeLike;
use crate::encodings::pb::BoundUpperIncremental;
use crate::encodings::pb::Encode;
use crate::encodings::totdb;
use crate::instances::ManageVars;
use crate::types::Lit;

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

/// Generalized totalizer encoding with a [`std::cell::RefCell`] to a totalizer
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
    db: &'totdb std::cell::RefCell<&'totdb mut totdb::Db>,
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

    /// Gets a specific output of the totalizer
    #[must_use]
    pub fn output(&self, value: usize) -> Option<Lit> {
        self.db[self.root.id].lit(value).copied()
    }

    /// Gets an iterator over the output literals of the totalizer
    ///
    /// The first parameter holds the corresponding value of the output. The literals are guaranteed
    /// to be returned in order of increasing value.
    pub fn outputs(&self) -> impl Iterator<Item = (usize, Option<Lit>)> + '_ {
        self.db[self.root.id].outputs()
    }
}

impl<'totdb> GteCell<'totdb> {
    /// Constructs a new GTE encoding referencing a totalizer database
    pub fn new(
        root: NodeCon,
        max_leaf_weight: usize,
        db: &'totdb std::cell::RefCell<&'totdb mut totdb::Db>,
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

    /// Gets a specific output of the totalizer
    #[must_use]
    pub fn output(&self, value: usize) -> Option<Lit> {
        self.db.borrow()[self.root.id].lit(value).copied()
    }
}

impl crate::encodings::pb::Encode for Gte<'_> {
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

impl crate::encodings::pb::Encode for GteCell<'_> {
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

impl crate::encodings::pb::EncodeIncremental for Gte<'_> {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.db.reserve_vars(self.root, var_manager);
    }
}

impl crate::encodings::pb::EncodeIncremental for GteCell<'_> {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.db.borrow_mut().reserve_vars(self.root, var_manager);
    }
}

impl crate::encodings::pb::BoundUpper for Gte<'_> {
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

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EnforceError> {
        if ub >= self.weight_sum() {
            return Ok(vec![]);
        }

        let mut assumps = vec![];
        // Enforce bound on internal tree
        for val in self.db[self.root.id]
            .vals(self.root.rev_map_round_up(ub + 1)..=self.root.rev_map(ub + self.max_leaf_weight))
        {
            match &self.db[self.root.id] {
                totdb::Node::Leaf(lit) => {
                    assumps.push(!*lit);
                }
                totdb::Node::Unit(node) => {
                    let totdb::LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = node.lits[val - 1]
                    else {
                        return Err(EnforceError::NotEncoded);
                    };
                    if !semantics.has_if() {
                        return Err(EnforceError::NotEncoded);
                    }
                    assumps.push(!lit);
                }
                totdb::Node::General(node) => {
                    let Some(totdb::LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    }) = node.lit_data(val)
                    else {
                        return Err(EnforceError::NotEncoded);
                    };
                    if !semantics.has_if() {
                        return Err(EnforceError::NotEncoded);
                    }
                    assumps.push(!lit);
                }
                totdb::Node::Dummy => panic!(),
            }
        }
        Ok(assumps)
    }
}

impl crate::encodings::pb::BoundUpper for GteCell<'_> {
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

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EnforceError> {
        if ub >= self.weight_sum() {
            return Ok(vec![]);
        }

        let mut assumps = vec![];
        // Enforce bound on internal tree
        for val in self.db.borrow()[self.root.id]
            .vals(self.root.rev_map_round_up(ub + 1)..=self.root.rev_map(ub + self.max_leaf_weight))
        {
            match &self.db.borrow()[self.root.id] {
                totdb::Node::Leaf(lit) => {
                    assumps.push(!*lit);
                }
                totdb::Node::Unit(node) => {
                    let totdb::LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = node.lits[val - 1]
                    else {
                        return Err(EnforceError::NotEncoded);
                    };
                    if !semantics.has_if() {
                        return Err(EnforceError::NotEncoded);
                    }
                    assumps.push(!lit);
                }
                totdb::Node::General(node) => {
                    let Some(totdb::LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    }) = node.lit_data(val)
                    else {
                        return Err(EnforceError::NotEncoded);
                    };
                    if !semantics.has_if() {
                        return Err(EnforceError::NotEncoded);
                    }
                    assumps.push(!lit);
                }
                totdb::Node::Dummy => panic!(),
            }
        }
        Ok(assumps)
    }
}

impl crate::encodings::pb::BoundUpperIncremental for Gte<'_> {
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
        R: std::ops::RangeBounds<usize>,
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
