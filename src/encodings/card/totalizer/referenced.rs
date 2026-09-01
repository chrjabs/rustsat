//! Totalizer encoding types that do not own but reference their [`totdb::Db`]
#![cfg(feature = "_internals")]

use crate::encodings::card::BoundLowerIncremental;
use crate::encodings::card::BoundUpperIncremental;
use crate::encodings::card::Encode;
use crate::encodings::nodedb::NodeCon;
use crate::encodings::nodedb::NodeId;
use crate::encodings::nodedb::NodeLike;
use crate::encodings::totdb;
use crate::encodings::CollectClauses;
use crate::encodings::EnforceError;
use crate::encodings::NotEncoded;
use crate::instances::ManageVars;
use crate::types::Lit;

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
/// This uses a [`std::cell::RefCell`] to a totalizer database.
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
    db: &'totdb std::cell::RefCell<&'totdb mut totdb::Db>,
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
    pub fn new(root: NodeId, db: &'totdb std::cell::RefCell<&'totdb mut totdb::Db>) -> Self {
        Self { root, db }
    }

    /// Gets the maximum depth of the tree
    #[must_use]
    pub fn depth(&self) -> usize {
        self.db.borrow()[self.root].depth()
    }
}

impl crate::encodings::card::Encode for Tot<'_> {
    fn n_lits(&self) -> usize {
        self.db[self.root].len()
    }
}

impl crate::encodings::card::Encode for TotCell<'_> {
    fn n_lits(&self) -> usize {
        self.db.borrow()[self.root].len()
    }
}

impl crate::encodings::card::EncodeIncremental for Tot<'_> {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.db.reserve_vars(NodeCon::full(self.root), var_manager);
    }
}

impl crate::encodings::card::EncodeIncremental for TotCell<'_> {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.db
            .borrow_mut()
            .reserve_vars(NodeCon::full(self.root), var_manager);
    }
}

impl crate::encodings::card::BoundUpper for Tot<'_> {
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
                Ok(vec![!*lit])
            }
            totdb::Node::Unit(node) => {
                let totdb::LitData::Lit {
                    lit,
                    semantics: Some(semantics),
                } = node.lits[ub]
                else {
                    return Err(NotEncoded);
                };
                if !semantics.has_if() {
                    return Err(NotEncoded);
                }
                Ok(vec![!lit])
            }
            totdb::Node::General(_) | totdb::Node::Dummy => unreachable!(),
        }
    }
}

impl crate::encodings::card::BoundUpper for TotCell<'_> {
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
                Ok(vec![!*lit])
            }
            totdb::Node::Unit(node) => {
                let totdb::LitData::Lit {
                    lit,
                    semantics: Some(semantics),
                } = node.lits[ub]
                else {
                    return Err(NotEncoded);
                };
                if !semantics.has_if() {
                    return Err(NotEncoded);
                }
                Ok(vec![!lit])
            }
            totdb::Node::General(_) | totdb::Node::Dummy => unreachable!(),
        }
    }
}

impl crate::encodings::card::BoundLower for Tot<'_> {
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
                Ok(vec![*lit])
            }
            totdb::Node::Unit(node) => {
                let totdb::LitData::Lit {
                    lit,
                    semantics: Some(semantics),
                } = node.lits[lb - 1]
                else {
                    return Err(EnforceError::NotEncoded);
                };
                if !semantics.has_only_if() {
                    return Err(EnforceError::NotEncoded);
                }
                Ok(vec![lit])
            }
            totdb::Node::General(_) | totdb::Node::Dummy => unreachable!(),
        }
    }
}

impl crate::encodings::card::BoundLower for TotCell<'_> {
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
                Ok(vec![*lit])
            }
            totdb::Node::Unit(node) => {
                let totdb::LitData::Lit {
                    lit,
                    semantics: Some(semantics),
                } = node.lits[lb - 1]
                else {
                    return Err(EnforceError::NotEncoded);
                };
                if !semantics.has_only_if() {
                    return Err(EnforceError::NotEncoded);
                }
                Ok(vec![lit])
            }
            totdb::Node::General(_) | totdb::Node::Dummy => unreachable!(),
        }
    }
}

impl crate::encodings::card::BoundUpperIncremental for Tot<'_> {
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

impl crate::encodings::card::BoundUpperIncremental for TotCell<'_> {
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

impl crate::encodings::card::BoundLowerIncremental for Tot<'_> {
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

impl crate::encodings::card::BoundLowerIncremental for TotCell<'_> {
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

impl crate::encodings::card::BoundBoth for Tot<'_> {
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

impl crate::encodings::card::BoundBoth for TotCell<'_> {
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

impl crate::encodings::card::BoundBothIncremental for Tot<'_> {}

impl crate::encodings::card::BoundBothIncremental for TotCell<'_> {}
