//! Dynamic polynomial watchdog encoding types that do not own but reference their [`totdb::Db`]
#![cfg(feature = "_internals")]

use crate::encodings::CollectClauses;
use crate::encodings::EnforceError;
use crate::encodings::nodedb::NodeCon;
use crate::encodings::nodedb::NodeLike;
use crate::encodings::pb::BoundUpperIncremental;
use crate::encodings::totdb;
use crate::instances::ManageVars;
use crate::types::Lit;

/// Dynamic polynomial watchdog structure with a _mutable reference_ to a totalizer
/// database rather than owning it.
///
/// ## References
///
/// - \[1\] Tobias Paxian and Sven Reimer and Bernd Becker: _Dynamic Polynomial
///   Watchdog Encoding for Solving Weighted MaxSAT_, SAT 2018.
#[derive(Debug)]
pub struct DynamicPolyWatchdog<'totdb> {
    /// The encoding root and the tares
    structure: &'totdb super::Structure,
    /// The node database of the totalizer
    db: &'totdb mut totdb::Db,
}

/// Dynamic polynomial watchdog structure with a [`std::cell::RefCell`] to a totalizer
/// database rather than owning it.
///
/// ## References
///
/// - \[1\] Tobias Paxian and Sven Reimer and Bernd Becker: _Dynamic Polynomial
///   Watchdog Encoding for Solving Weighted MaxSAT_, SAT 2018.
#[derive(Debug)]
pub struct DynamicPolyWatchdogCell<'totdb> {
    /// The encoding root and the tares
    structure: &'totdb super::Structure,
    /// The node database of the totalizer
    db: &'totdb std::cell::RefCell<&'totdb mut totdb::Db>,
}

impl<'totdb> DynamicPolyWatchdog<'totdb> {
    /// Constructs a new DPW encoding referencing a totalizer database
    pub fn new(structure: &'totdb super::Structure, db: &'totdb mut totdb::Db) -> Self {
        Self { structure, db }
    }

    /// Gets the maximum depth of the tree
    #[must_use]
    pub fn depth(&self) -> usize {
        self.db[self.structure.root()].depth()
    }
}

impl<'totdb> DynamicPolyWatchdogCell<'totdb> {
    /// Constructs a new DPW encoding referencing a totalizer database
    pub fn new(
        structure: &'totdb super::Structure,
        db: &'totdb std::cell::RefCell<&'totdb mut totdb::Db>,
    ) -> Self {
        Self { structure, db }
    }

    /// Gets the maximum depth of the tree
    #[must_use]
    pub fn depth(&self) -> usize {
        self.db.borrow()[self.structure.root()].depth()
    }
}

impl crate::encodings::pb::Encode for DynamicPolyWatchdog<'_> {
    fn weight_sum(&self) -> usize {
        let output_weight = 1 << self.structure.output_power();
        self.db[self.structure.root()].len() * output_weight
    }
}

impl crate::encodings::pb::Encode for DynamicPolyWatchdogCell<'_> {
    fn weight_sum(&self) -> usize {
        let output_weight = 1 << self.structure.output_power();
        self.db.borrow()[self.structure.root()].len() * output_weight
    }
}

impl crate::encodings::pb::EncodeIncremental for DynamicPolyWatchdog<'_> {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.db
            .reserve_vars(NodeCon::full(self.structure.root()), var_manager);
    }
}

impl crate::encodings::pb::EncodeIncremental for DynamicPolyWatchdogCell<'_> {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.db
            .borrow_mut()
            .reserve_vars(NodeCon::full(self.structure.root()), var_manager);
    }
}

impl crate::encodings::pb::BoundUpper for DynamicPolyWatchdog<'_> {
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
        super::enforce_ub(self.structure, ub, self.db)
    }

    fn coarse_ub(&self, ub: usize) -> usize {
        let output_weight = 1 << self.structure.output_power();
        ub / output_weight * output_weight
    }
}

impl crate::encodings::pb::BoundUpper for DynamicPolyWatchdogCell<'_> {
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
        super::enforce_ub(self.structure, ub, &self.db.borrow())
    }

    fn coarse_ub(&self, ub: usize) -> usize {
        let output_weight = 1 << self.structure.output_power();
        ub / output_weight * output_weight
    }
}

impl crate::encodings::pb::BoundUpperIncremental for DynamicPolyWatchdog<'_> {
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
        let output_weight = 1 << self.structure.output_power();
        let output_range = (range.start / output_weight)..=((range.end - 1) / output_weight);
        for oidx in output_range {
            super::encode_output(self.structure, oidx, self.db, collector, var_manager)?;
        }
        Ok(())
    }
}

impl crate::encodings::pb::BoundUpperIncremental for DynamicPolyWatchdogCell<'_> {
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
        let output_weight = 1 << self.structure.output_power();
        let output_range = (range.start / output_weight)..=((range.end - 1) / output_weight);
        for oidx in output_range {
            super::encode_output(
                self.structure,
                oidx,
                &mut self.db.borrow_mut(),
                collector,
                var_manager,
            )?;
        }
        Ok(())
    }
}
