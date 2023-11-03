//! # Dynamic Polynomial Watchdog Encoding
//!
//! Implementation of the dynamic polynomial watchdog (DPW) encoding \[1\].
//!
//! **Note**:
//! This implementation of the  DPW encoding only supports incrementally
//! changing the bound, but not adding new input literals. Calling extend after
//! encoding resets the entire encoding and with the next encode and entirely
//! new encoding will be returned.
//!
//! ## References
//!
//! - \[1\] Tobias Paxian and Sven Reimer and Bernd Becker: _Dynamic Polynomial
//!   Watchdog Encoding for Solving Weighted MaxSAT_, SAT 2018.

use std::{
    collections::BTreeMap,
    num::{NonZeroU8, NonZeroUsize},
    ops::RangeBounds,
};

use crate::{
    encodings::{
        card::dbtotalizer::{Node, TotDb},
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
        CollectClauses, EncodeStats, Error, IterWeightedInputs,
    },
    instances::ManageVars,
    types::{Lit, RsHashMap},
    utils,
};

use super::{BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental};

#[cfg(feature = "pyapi")]
use crate::instances::{BasicVarManager, Cnf};
#[cfg(feature = "pyapi")]
use pyo3::prelude::*;

/// Implementation of the dynamic polynomial watchdog (DPW) encoding \[1\].
///
/// **Note**:
/// This implementation of the  DPW encoding only supports incrementally
/// changing the bound, but not adding new input literals. Calling extend after
/// encoding resets the entire encoding and with the next encode and entirely
/// new encoding will be returned.
///
/// ## References
///
/// - \[1\] Tobias Paxian and Sven Reimer and Bernd Becker: _Dynamic Polynomial
///   Watchdog Encoding for Solving Weighted MaxSAT_, SAT 2018.
#[cfg_attr(feature = "pyapi", pyclass)]
#[derive(Default)]
pub struct DynamicPolyWatchdog {
    /// Input literals and weights for the encoding
    pub(crate) in_lits: RsHashMap<Lit, usize>,
    /// The encoding root and the tares
    pub(crate) structure: Option<Structure>,
    /// Sum of all input weight
    pub(crate) weight_sum: usize,
    /// The number of variables
    n_vars: u32,
    /// The number of clauses
    n_clauses: usize,
    /// The node database of the totalizer
    db: TotDb,
}

impl DynamicPolyWatchdog {
    /// Gets the maximum depth of the tree
    pub fn depth(&self) -> usize {
        match &self.structure {
            Some(Structure { root, .. }) => self.db[*root].depth(),
            None => 0,
        }
    }
}

#[cfg_attr(feature = "internals", visibility::make(pub))]
#[derive(Clone)]
pub(crate) struct Structure {
    /// The root of the structure
    pub root: NodeId,
    /// The tare variables needed to enforce specific bounds. First in vector is
    /// the tare to the second largest top bucket, then decreasing.
    pub tares: Vec<Lit>,
}

impl Structure {
    /// Gets the power of the output literals (they represent a weight of
    /// 2^power)
    pub fn output_power(&self) -> usize {
        self.tares.len()
    }
}

impl Encode for DynamicPolyWatchdog {
    fn weight_sum(&self) -> usize {
        self.weight_sum
    }
}

impl IterWeightedInputs for DynamicPolyWatchdog {
    type Iter<'a> = DpwIter<'a>;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().map(copy_key_val)
    }
}

impl EncodeIncremental for DynamicPolyWatchdog {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        if let Some(Structure { root, .. }) = &self.structure {
            self.db.reserve_vars(*root, var_manager);
        }
    }
}

impl BoundUpper for DynamicPolyWatchdog {
    fn encode_ub<Col, R>(&mut self, range: R, collector: &mut Col, var_manager: &mut dyn ManageVars)
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        self.db.reset_encoded();
        self.encode_ub_change(range, collector, var_manager)
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
        match &self.structure {
            Some(structure) => enforce_ub(structure, ub, &self.db),
            None => Ok(vec![]),
        }
    }

    fn coarse_ub(&self, ub: usize) -> usize {
        match &self.structure {
            Some(structure) => {
                let output_weight = 1 << (structure.output_power());
                if ub < output_weight {
                    return ub;
                }
                ub / output_weight * output_weight - 1
            }
            None => ub,
        }
    }
}

impl BoundUpperIncremental for DynamicPolyWatchdog {
    fn encode_ub_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        let range = super::prepare_ub_range(self, range);
        if range.is_empty() {
            return;
        }
        let n_vars_before = var_manager.n_used();
        if self.structure.is_none() && !self.in_lits.is_empty() {
            self.structure = Some(build_lit_structure(
                self.in_lits.iter().map(|(&l, &w)| (l, w)),
                &mut self.db,
                var_manager,
            ));
        }
        match &self.structure {
            Some(structure) => {
                let n_clauses_before = collector.n_clauses();
                let output_weight = 1 << (structure.output_power());
                let output_range = range.start / output_weight..(range.end - 1) / output_weight + 1;
                for oidx in output_range {
                    encode_output(structure, oidx, &mut self.db, collector, var_manager);
                }
                self.n_clauses += collector.n_clauses() - n_clauses_before;
                self.n_vars += var_manager.n_used() - n_vars_before;
            }
            None => (),
        }
    }
}

impl EncodeStats for DynamicPolyWatchdog {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        self.n_vars
    }
}

impl From<RsHashMap<Lit, usize>> for DynamicPolyWatchdog {
    fn from(lits: RsHashMap<Lit, usize>) -> Self {
        let weight_sum = lits.iter().fold(0, |sum, (_, w)| sum + *w);
        Self {
            in_lits: lits.clone(),
            structure: Default::default(),
            weight_sum,
            n_vars: Default::default(),
            n_clauses: Default::default(),
            db: Default::default(),
        }
    }
}

impl FromIterator<(Lit, usize)> for DynamicPolyWatchdog {
    fn from_iter<T: IntoIterator<Item = (Lit, usize)>>(iter: T) -> Self {
        let lits: RsHashMap<Lit, usize> = RsHashMap::from_iter(iter);
        Self::from(lits)
    }
}

#[cfg(feature = "internals")]
pub mod referenced {
    use std::{cell::RefCell, ops::RangeBounds};

    use crate::{
        encodings::{card::dbtotalizer::TotDb, nodedb::NodeLike, CollectClauses, Error},
        instances::ManageVars,
        types::Lit,
    };

    use super::{
        encode_output, enforce_ub, BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental,
        Structure,
    };

    /// Dynamic polynomial watchdog structure with a _mutable reference_ to a totalizer
    /// database rather than owning it.
    ///
    /// ## References
    ///
    /// - \[1\] Tobias Paxian and Sven Reimer and Bernd Becker: _Dynamic Polynomial
    ///   Watchdog Encoding for Solving Weighted MaxSAT_, SAT 2018.
    pub struct DynamicPolyWatchdog<'totdb> {
        /// The encoding root and the tares
        structure: &'totdb Structure,
        /// The node database of the totalizer
        db: &'totdb mut TotDb,
    }

    /// Dynamic polynomial watchdog structure with a [`RefCell`] to a totalizer
    /// database rather than owning it.
    ///
    /// ## References
    ///
    /// - \[1\] Tobias Paxian and Sven Reimer and Bernd Becker: _Dynamic Polynomial
    ///   Watchdog Encoding for Solving Weighted MaxSAT_, SAT 2018.
    pub struct DynamicPolyWatchdogCell<'totdb> {
        /// The encoding root and the tares
        structure: &'totdb Structure,
        /// The node database of the totalizer
        db: &'totdb RefCell<&'totdb mut TotDb>,
    }

    impl<'totdb> DynamicPolyWatchdog<'totdb> {
        /// Constructs a new DPW encoding referencing a totalizer database
        pub fn new(structure: &'totdb Structure, db: &'totdb mut TotDb) -> Self {
            Self { structure, db }
        }

        /// Gets the maximum depth of the tree
        pub fn depth(&self) -> usize {
            self.db[self.structure.root].depth()
        }
    }

    impl<'totdb> DynamicPolyWatchdogCell<'totdb> {
        /// Constructs a new DPW encoding referencing a totalizer database
        pub fn new(structure: &'totdb Structure, db: &'totdb RefCell<&'totdb mut TotDb>) -> Self {
            Self { structure, db }
        }

        /// Gets the maximum depth of the tree
        pub fn depth(&self) -> usize {
            self.db.borrow()[self.structure.root].depth()
        }
    }

    impl Encode for DynamicPolyWatchdog<'_> {
        fn weight_sum(&self) -> usize {
            let output_weight = 1 << self.structure.output_power();
            self.db[self.structure.root].len() * output_weight
        }
    }

    impl Encode for DynamicPolyWatchdogCell<'_> {
        fn weight_sum(&self) -> usize {
            let output_weight = 1 << self.structure.output_power();
            self.db.borrow()[self.structure.root].len() * output_weight
        }
    }

    impl EncodeIncremental for DynamicPolyWatchdog<'_> {
        fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
            self.db.reserve_vars(self.structure.root, var_manager);
        }
    }

    impl EncodeIncremental for DynamicPolyWatchdogCell<'_> {
        fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
            self.db
                .borrow_mut()
                .reserve_vars(self.structure.root, var_manager);
        }
    }

    impl BoundUpper for DynamicPolyWatchdog<'_> {
        fn encode_ub<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) where
            Col: CollectClauses,
            R: RangeBounds<usize>,
        {
            self.db.reset_encoded();
            self.encode_ub_change(range, collector, var_manager)
        }

        fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
            enforce_ub(self.structure, ub, self.db)
        }

        fn coarse_ub(&self, ub: usize) -> usize {
            let output_weight = 1 << self.structure.output_power();
            ub / output_weight * output_weight
        }
    }

    impl BoundUpper for DynamicPolyWatchdogCell<'_> {
        fn encode_ub<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) where
            Col: CollectClauses,
            R: RangeBounds<usize>,
        {
            self.db.borrow_mut().reset_encoded();
            self.encode_ub_change(range, collector, var_manager)
        }

        fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
            enforce_ub(self.structure, ub, &self.db.borrow())
        }

        fn coarse_ub(&self, ub: usize) -> usize {
            let output_weight = 1 << self.structure.output_power();
            ub / output_weight * output_weight
        }
    }

    impl BoundUpperIncremental for DynamicPolyWatchdog<'_> {
        fn encode_ub_change<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) where
            Col: CollectClauses,
            R: RangeBounds<usize>,
        {
            let range = super::super::prepare_ub_range(self, range);
            if range.is_empty() {
                return;
            }
            let output_weight = 1 << self.structure.output_power();
            let output_range = range.start / output_weight..(range.end - 1) / output_weight + 1;
            for oidx in output_range {
                encode_output(self.structure, oidx, self.db, collector, var_manager);
            }
        }
    }

    impl BoundUpperIncremental for DynamicPolyWatchdogCell<'_> {
        fn encode_ub_change<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) where
            Col: CollectClauses,
            R: RangeBounds<usize>,
        {
            let range = super::super::prepare_ub_range(self, range);
            if range.is_empty() {
                return;
            }
            let output_weight = 1 << self.structure.output_power();
            let output_range = range.start / output_weight..(range.end - 1) / output_weight + 1;
            for oidx in output_range {
                encode_output(
                    self.structure,
                    oidx,
                    &mut self.db.borrow_mut(),
                    collector,
                    var_manager,
                );
            }
        }
    }
}

fn copy_key_val(key_val_refs: (&Lit, &usize)) -> (Lit, usize) {
    (*key_val_refs.0, *key_val_refs.1)
}
type DpwIter<'a> = std::iter::Map<
    std::collections::hash_map::Iter<'a, Lit, usize>,
    fn((&Lit, &usize)) -> (Lit, usize),
>;

#[cfg_attr(feature = "internals", visibility::make(pub))]
fn build_lit_structure<LI: Iterator<Item = (Lit, usize)>>(
    lits: LI,
    tot_db: &mut TotDb,
    var_manager: &mut dyn ManageVars,
) -> Structure {
    let lit_to_con = |(lit, weight)| {
        let node = tot_db.insert(Node::Leaf(lit));
        NodeCon::weighted(node, weight)
    };
    let cons: Vec<_> = lits.map(lit_to_con).collect();
    build_structure(cons.into_iter(), tot_db, var_manager)
}

#[cfg_attr(feature = "internals", visibility::make(pub))]
fn build_structure<CI: Iterator<Item = NodeCon>>(
    cons: CI,
    tot_db: &mut TotDb,
    var_manager: &mut dyn ManageVars,
) -> Structure {
    // Initialize weight queue
    let mut weight_queue: BTreeMap<usize, Vec<NodeCon>> = BTreeMap::new();
    for con in cons {
        if let Some(cons) = weight_queue.get_mut(&con.multiplier()) {
            cons.push(NodeCon {
                multiplier: NonZeroUsize::new(1).unwrap(),
                ..con
            });
        } else {
            weight_queue.insert(
                con.multiplier(),
                vec![NodeCon {
                    multiplier: NonZeroUsize::new(1).unwrap(),
                    ..con
                }],
            );
        }
    }
    let basis_len = utils::digits(*weight_queue.iter().next_back().unwrap().0, 2) as usize;

    // Children to be merged to a given top bucket
    let mut top_buckets = vec![vec![]; basis_len];
    // Converts a digit number to a corresponding index in the
    // `top_buckets`. Top buckets are ordered from smallest to highest.
    let tb_idx = |digits: u32| (digits - 1) as usize;

    // Loop while there are new weights that need to be added and distribute
    // them to relevant top buckets
    while !weight_queue.is_empty() {
        let (weight, cons) = weight_queue.pop_last().unwrap();
        let merged = tot_db.merge_balanced(&cons);
        let digits = utils::digits(weight, 2);
        let current_weight = 1 << (digits - 1);
        top_buckets[tb_idx(digits)].push(merged);
        // Insert remainder of totalizer as new child
        let remaining_weight = weight & !current_weight;
        if remaining_weight > 0 {
            if let Some(cons) = weight_queue.get_mut(&remaining_weight) {
                cons.push(merged);
            } else {
                weight_queue.insert(remaining_weight, vec![merged]);
            }
        }
    }

    if basis_len == 1 {
        debug_assert_eq!(top_buckets[0].len(), 1);
        return Structure {
            root: top_buckets[0][0].id,
            tares: vec![],
        };
    }

    // Prepare tares
    let mut tares: Vec<_> = (0..basis_len - 1)
        .map(|_| var_manager.new_var().pos_lit())
        .collect();
    let tare_nodes: Vec<_> = tares
        .iter()
        .map(|&lit| tot_db.insert(Node::Leaf(lit)))
        .collect();
    tares.shrink_to_fit();

    // Merge top buckets and merge with bottom buckets
    let mut last_bottom_bucket = None;
    for (idx, mut cons) in top_buckets.into_iter().enumerate() {
        if idx != basis_len - 1 {
            // Merge top bucket (except for last) with tare
            cons.push(NodeCon::full(tare_nodes[idx]));
        }
        cons.sort_unstable_by_key(|&con| tot_db.con_len(con));
        let top_bucket = tot_db.merge_balanced(&cons);
        if last_bottom_bucket.is_none() {
            // special case: lowest bucket does not need bottom buckets
            if tot_db.con_len(top_bucket) == 1 {
                // top bucket is empty (except for tare), tare can be
                // omitted: shift to next layer
                continue;
            }
            debug_assert_eq!(top_bucket.divisor(), 1);
            last_bottom_bucket = Some(NodeCon {
                id: top_bucket.id,
                offset: top_bucket.offset,
                divisor: NonZeroU8::new(2).unwrap(),
                multiplier: NonZeroUsize::new(1).unwrap(),
                len_limit: None,
            });
            continue;
        }

        let right = last_bottom_bucket.unwrap();
        let bottom = tot_db.insert(Node::internal(top_bucket, right, tot_db));
        last_bottom_bucket = Some(NodeCon {
            id: bottom,
            offset: 0,
            divisor: NonZeroU8::new(2).unwrap(),
            multiplier: NonZeroUsize::new(1).unwrap(),
            len_limit: None,
        });
    }

    let root = last_bottom_bucket.unwrap();
    debug_assert_eq!(root.offset(), 0);
    debug_assert_eq!(root.divisor(), 2);
    Structure {
        root: root.id,
        tares,
    }
}

#[cfg_attr(feature = "internals", visibility::make(pub))]
fn encode_output<Col>(
    dpw: &Structure,
    oidx: usize,
    tot_db: &mut TotDb,
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
) where
    Col: CollectClauses,
{
    if oidx >= tot_db[dpw.root].max_val() {
        return;
    }
    tot_db.define_pos_tot(dpw.root, oidx, collector, var_manager);
}

#[cfg_attr(feature = "internals", visibility::make(pub))]
fn enforce_ub(dpw: &Structure, ub: usize, tot_db: &TotDb) -> Result<Vec<Lit>, Error> {
    let output_weight = 1 << (dpw.output_power());
    let oidx = ub / output_weight;
    if oidx >= tot_db[dpw.root].max_val() {
        return Ok(vec![]);
    }
    let olit = match tot_db[dpw.root].lit(oidx + 1) {
        Some(&lit) => lit,
        None => return Err(Error::NotEncoded),
    };
    let mut assumps = vec![!olit];
    // inputs <= enforced_weight at this stage
    let mut enforced_weight = (oidx + 1) * output_weight - 1;
    debug_assert!(enforced_weight >= ub);
    // Set needed tares
    for power in (0..dpw.output_power()).rev() {
        let weight = 1 << power;
        if ub + weight <= enforced_weight {
            enforced_weight -= weight;
            assumps.push(dpw.tares[power]);
        }
        if ub == enforced_weight {
            break;
        }
    }
    debug_assert!(ub == enforced_weight);

    Ok(assumps)
}

#[cfg(feature = "pyapi")]
#[pymethods]
impl DynamicPolyWatchdog {
    #[new]
    fn new(lits: Vec<(Lit, usize)>) -> Self {
        Self::from_iter(lits)
    }

    /// Gets the sum of weights in the encoding
    #[pyo3(name = "weight_sum")]
    fn py_weight_sum(&self) -> usize {
        self.weight_sum()
    }

    /// Gets the number of clauses in the encoding
    #[pyo3(name = "n_clauses")]
    fn py_n_clauses(&self) -> usize {
        self.n_clauses()
    }

    /// Gets the number of variables in the encoding
    #[pyo3(name = "n_vars")]
    fn py_n_vars(&self) -> u32 {
        self.n_vars()
    }

    /// Incrementally builds the DPW encoding to that upper bounds
    /// in the range `max_ub..=min_ub` can be enforced. New variables will
    /// be taken from `var_manager`.
    #[pyo3(name = "encode_ub")]
    fn py_encode_ub(
        &mut self,
        max_ub: usize,
        min_ub: usize,
        var_manager: &mut BasicVarManager,
    ) -> Cnf {
        let mut cnf = Cnf::new();
        <Self as BoundUpperIncremental>::encode_ub_change(
            self,
            max_ub..=min_ub,
            &mut cnf,
            var_manager,
        );
        cnf
    }

    /// Gets assumptions to enforce the given upper bound. Make sure that
    /// the required encoding is built first.
    #[pyo3(name = "enforce_ub")]
    fn py_enforce_ub(&self, ub: usize) -> PyResult<Vec<Lit>> {
        Ok(self.enforce_ub(ub)?)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        encodings::{pb::BoundUpper, EncodeStats},
        instances::{BasicVarManager, Cnf},
        lit,
        types::RsHashMap,
    };

    use super::DynamicPolyWatchdog;

    #[test]
    fn basic() {
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 1);
        lits.insert(lit![1], 1);
        lits.insert(lit![2], 2);
        lits.insert(lit![3], 2);
        let mut dpw = DynamicPolyWatchdog::from(lits);
        let mut var_manager = BasicVarManager::default();
        let mut cnf = Cnf::new();
        dpw.encode_ub(0..=6, &mut cnf, &mut var_manager);
        assert_eq!(dpw.n_vars(), 9);
        assert_eq!(cnf.len(), 13);
    }

    #[test]
    fn coarse_convergence() {
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 3);
        lits.insert(lit![2], 8);
        lits.insert(lit![3], 7);
        let mut dpw = DynamicPolyWatchdog::from(lits);
        let mut var_manager = BasicVarManager::default();
        let mut cnf = Cnf::new();
        dpw.encode_ub(0..=23, &mut cnf, &mut var_manager);
        for ub in 8..=23 {
            let coarse_ub = dpw.coarse_ub(ub);
            debug_assert!(coarse_ub <= ub);
            let assumps = dpw.enforce_ub(coarse_ub).unwrap();
            debug_assert_eq!(assumps.len(), 1);
        }
    }
}
