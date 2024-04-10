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
    cmp,
    collections::BTreeMap,
    num::{NonZeroU8, NonZeroUsize},
    ops::RangeBounds,
};

use crate::{
    encodings::{
        atomics,
        card::dbtotalizer::{GeneralNode, LitData, Node, TotDb, UnitNode},
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
        CollectClauses, EncodeStats, Error, IterWeightedInputs,
    },
    instances::ManageVars,
    types::{Lit, RsHashMap},
    utils,
};

use super::{BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental};

type WeightQ = BTreeMap<usize, Vec<NodeCon>>;

/// Errors related to incremental precision
#[derive(Error, Debug, PartialEq, Eq)]
pub enum PrecisionError {
    /// Precision divisor was not a power of 2
    #[error("precision divisor must be a power of 2")]
    NotPow2,
    /// Precision divisor was higher than previous one
    #[error("precision can only be increased")]
    PrecisionDecreased,
}

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
#[derive(Default)]
pub struct DynamicPolyWatchdog {
    /// Input literals and weights for the encoding
    in_lits: RsHashMap<Lit, usize>,
    /// The encoding root and the tares
    structure: Option<Structure>,
    /// Queue by weight of children that still have to be added to the tree
    weight_queue: WeightQ,
    /// The current precision divisor of the encoding
    prec_div: usize,
    /// Sum of all input weight
    weight_sum: usize,
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
            Some(structure) => self.db[structure.root()].depth(),
            None => 0,
        }
    }

    /// Helper for the C-API to add input literals to an already existing object. Errors if the
    /// object is already encoded.
    #[cfg(feature = "internals")]
    pub fn add_input(&mut self, lit: Lit, weight: usize) -> Result<(), crate::NotAllowed> {
        if self.structure.is_some() {
            return Err(crate::NotAllowed(
                "cannot add inputs after building the encoding",
            ));
        }
        if let Some(lweight) = self.in_lits.get_mut(&lit) {
            *lweight += weight;
        } else {
            self.in_lits.insert(lit, weight);
        }
        self.weight_sum += weight;
        let node = self.db.insert(Node::Leaf(lit));
        let con = NodeCon::full(node);
        if let Some(cons) = self.weight_queue.get_mut(&weight) {
            cons.push(con);
        } else {
            self.weight_queue.insert(weight, vec![con]);
        }
        Ok(())
    }

    /// Set the precision at which to build the encoding at. With `divisor = 8` the encoding will
    /// effectively be built such that the weight of every input literal is divided by `divisor`
    /// (interger division, rounding down). Divisor values must be powers of 2. After building
    /// the encoding, the precision can only be increased, i.e., only call this function with
    /// _decreasing_ divisor values.
    ///
    /// # Errors
    ///
    /// Returns an error if the divisor value is not a power of 2 or was increased.
    pub fn set_precision(&mut self, divisor: usize) -> Result<(), PrecisionError> {
        if !(divisor <= 1 || (divisor & (divisor - 1)) == 0) {
            return Err(PrecisionError::NotPow2);
        }
        if self.structure.is_some() && divisor > self.prec_div {
            return Err(PrecisionError::PrecisionDecreased);
        }
        self.prec_div = divisor;
        Ok(())
    }

    /// Gets the next possible precision divisor value
    ///
    /// Note that this is not the next possible precision value from the last _set_ precision but
    /// from the last _encoded_ precision. The divisor value will always be a power of two so that
    /// calling `set_precision` and then encoding will produce the smalles non-empty next segment
    /// of the encoding.
    pub fn next_precision(&self) -> usize {
        if self.weight_queue.is_empty() {
            return 1;
        }
        let digits = utils::digits(*self.weight_queue.iter().next_back().unwrap().0, 2) as usize;
        1 << (digits - 1)
    }
}

#[cfg_attr(feature = "internals", visibility::make(pub))]
#[derive(Clone)]
pub(crate) struct Structure {
    /// The bottom buckets of the encoding. The first one of them is the root of the encoding.
    /// Sorted from highest to lowest.
    pub bottom_buckets: Vec<NodeId>,
    /// The tare variables needed to enforce specific bounds. First in vector is
    /// the tare to the second largest top bucket, then decreasing.
    pub tares: Vec<Lit>,
}

impl Structure {
    /// Gets the root of the structure
    pub fn root(&self) -> NodeId {
        self.bottom_buckets[0]
    }
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
        if let Some(structure) = &self.structure {
            self.db.reserve_vars(structure.root(), var_manager);
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
            None => {
                if self.weight_sum() <= ub {
                    return Ok(vec![]);
                }
                if self.in_lits.len() > 1 {
                    return Err(Error::NotEncoded);
                }
                debug_assert_eq!(self.in_lits.len(), 1);
                let (l, w) = self.in_lits.iter().next().unwrap();
                debug_assert!(*w > ub);
                Ok(vec![-(*l)])
            }
        }
    }

    fn coarse_ub(&self, ub: usize) -> usize {
        match &self.structure {
            Some(structure) => {
                let output_weight = 1 << (structure.output_power());
                if output_weight == 1 {
                    return ub;
                }
                if ub < output_weight {
                    return ub;
                }
                (ub + 1) / output_weight * output_weight - 1
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
        if range.is_empty() || self.in_lits.len() <= 1 {
            return;
        }
        let n_vars_before = var_manager.n_used();
        let mut fresh = false;
        if self.structure.is_none() && !self.in_lits.is_empty() {
            fresh = true;
            self.structure = Some(build_structure(
                &mut self.weight_queue,
                self.prec_div,
                true,
                &mut self.db,
                var_manager,
            ))
        }
        match &mut self.structure {
            Some(structure) => {
                let n_clauses_before = collector.n_clauses();
                if !fresh
                    && !self.weight_queue.is_empty()
                    && self.weight_queue.iter().next_back().unwrap().0 >= &self.prec_div
                {
                    // precision has been increased, need to extend encoding
                    let new_struct = build_structure(
                        &mut self.weight_queue,
                        self.prec_div,
                        false,
                        &mut self.db,
                        var_manager,
                    );
                    merge_structures(structure, new_struct, &mut self.db, collector, var_manager);
                }
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
        let mut db = Default::default();
        let weight_queue = lit_weight_queue(lits.clone().into_iter(), &mut db);
        Self {
            in_lits: lits,
            structure: Default::default(),
            weight_queue,
            prec_div: 1,
            weight_sum,
            n_vars: Default::default(),
            n_clauses: Default::default(),
            db,
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
            self.db[self.structure.root()].depth()
        }
    }

    impl<'totdb> DynamicPolyWatchdogCell<'totdb> {
        /// Constructs a new DPW encoding referencing a totalizer database
        pub fn new(structure: &'totdb Structure, db: &'totdb RefCell<&'totdb mut TotDb>) -> Self {
            Self { structure, db }
        }

        /// Gets the maximum depth of the tree
        pub fn depth(&self) -> usize {
            self.db.borrow()[self.structure.root()].depth()
        }
    }

    impl Encode for DynamicPolyWatchdog<'_> {
        fn weight_sum(&self) -> usize {
            let output_weight = 1 << self.structure.output_power();
            self.db[self.structure.root()].len() * output_weight
        }
    }

    impl Encode for DynamicPolyWatchdogCell<'_> {
        fn weight_sum(&self) -> usize {
            let output_weight = 1 << self.structure.output_power();
            self.db.borrow()[self.structure.root()].len() * output_weight
        }
    }

    impl EncodeIncremental for DynamicPolyWatchdog<'_> {
        fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
            self.db.reserve_vars(self.structure.root(), var_manager);
        }
    }

    impl EncodeIncremental for DynamicPolyWatchdogCell<'_> {
        fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
            self.db
                .borrow_mut()
                .reserve_vars(self.structure.root(), var_manager);
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
fn lit_weight_queue<LI: Iterator<Item = (Lit, usize)>>(lits: LI, tot_db: &mut TotDb) -> WeightQ {
    let lit_to_con = |(lit, weight)| {
        let node = tot_db.insert(Node::Leaf(lit));
        NodeCon::weighted(node, weight)
    };
    con_weight_queue(lits.map(lit_to_con))
}

#[cfg_attr(feature = "internals", visibility::make(pub))]
fn con_weight_queue<CI: Iterator<Item = NodeCon>>(cons: CI) -> WeightQ {
    let mut weight_queue: WeightQ = BTreeMap::new();
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
    weight_queue
}

#[cfg_attr(feature = "internals", visibility::make(pub))]
fn build_structure(
    weight_queue: &mut WeightQ,
    prec_div: usize,
    topmost: bool,
    tot_db: &mut TotDb,
    var_manager: &mut dyn ManageVars,
) -> Structure {
    // prec_div has to be a power of 2
    debug_assert!(prec_div <= 1 || (prec_div & (prec_div - 1)) == 0);
    let skipped_levels = utils::digits(prec_div, 2) as usize - 1;

    let basis_len = utils::digits(*weight_queue.iter().next_back().unwrap().0, 2) as usize;
    let mut structure = Structure {
        bottom_buckets: Vec::with_capacity(basis_len),
        tares: Vec::with_capacity(basis_len - 1),
    };

    // Children to be merged to a given top bucket
    let mut top_buckets = vec![vec![]; basis_len - skipped_levels];
    // Converts a digit number to a corresponding index in the
    // `top_buckets`. Top buckets are ordered from smallest to highest.
    let tb_idx = |digits: usize| (digits - 1 - skipped_levels) as usize;

    // Loop while there are new weights that need to be added and distribute
    // them to relevant top buckets
    while !weight_queue.is_empty() && weight_queue.iter().next_back().unwrap().0 >= &prec_div {
        let (weight, cons) = weight_queue.pop_last().unwrap();
        let merged = tot_db.merge_balanced(&cons);
        let digits = utils::digits(weight, 2) as usize;
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

    if basis_len == 1 && topmost {
        debug_assert_eq!(top_buckets[0].len(), 1);
        debug_assert_eq!(top_buckets[0][0].offset(), 0);
        debug_assert_eq!(top_buckets[0][0].multiplier(), 1);
        debug_assert_eq!(top_buckets[0][0].divisor(), 1);
        debug_assert!(structure.bottom_buckets.is_empty());
        return Structure {
            bottom_buckets: vec![top_buckets[0][0].id],
            tares: vec![],
        };
    }

    // Prepare tares
    structure.tares.extend(
        (0..basis_len - skipped_levels - if topmost { 1 } else { 0 })
            .map(|_| var_manager.new_var().pos_lit()),
    );
    let tare_nodes: Vec<_> = structure
        .tares
        .iter()
        .map(|&lit| tot_db.insert(Node::Leaf(lit)))
        .collect();

    // Merge top buckets and merge with bottom buckets
    let mut bottom_buckets = Vec::with_capacity(basis_len - skipped_levels);
    let mut bb_offset = 0;
    for (idx, mut cons) in top_buckets.into_iter().enumerate() {
        let has_tare = if !topmost || idx != basis_len - skipped_levels - 1 {
            // Merge top bucket (except for last) with tare
            cons.push(NodeCon::full(tare_nodes[idx]));
            true
        } else {
            false
        };
        cons.sort_unstable_by_key(|&con| tot_db.con_len(con));
        let top_bucket = tot_db.merge_balanced(&cons);
        if bottom_buckets.is_empty() {
            // special case: lowest bucket either gets dummy or no bottom bucket
            // TODO: figure out how to skip levels in the middle if they are empty
            if has_tare && tot_db.con_len(top_bucket) == 1 {
                // top bucket is empty (except for tare), tare can be
                // omitted: shift to next layer
                continue;
            }
            debug_assert_eq!(top_bucket.divisor(), 1);
            if prec_div <= 1 {
                // very last bottom bucket does not need bottom bucket
                bottom_buckets.push(top_bucket.id);
                bb_offset = top_bucket.offset;
            } else {
                // last bottom bucket for this segment, leave dummy node to path in extension
                let dummy = tot_db.insert(Node::Dummy);
                let right = NodeCon::full(dummy);
                let bottom = tot_db.insert(Node::internal(top_bucket, right, tot_db));
                bottom_buckets.push(bottom);
                bb_offset = 0;
            }
            continue;
        }

        let right = NodeCon {
            id: *bottom_buckets.last().unwrap(),
            offset: bb_offset,
            divisor: NonZeroU8::new(2).unwrap(),
            multiplier: NonZeroUsize::new(1).unwrap(),
            len_limit: None,
        };
        let bottom = tot_db.insert(Node::internal(top_bucket, right, tot_db));
        bottom_buckets.push(bottom);
        bb_offset = 0;
    }

    debug_assert_eq!(bottom_buckets.len(), basis_len - skipped_levels);
    structure
        .bottom_buckets
        .extend(bottom_buckets.into_iter().rev());
    structure
}

#[cfg_attr(feature = "internals", visibility::make(pub))]
fn merge_structures<Col>(
    bot_struct: &mut Structure,
    top_struct: Structure,
    tot_db: &mut TotDb,
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
) where
    Col: CollectClauses,
{
    debug_assert_eq!(bot_struct.bottom_buckets.len(), bot_struct.tares.len() + 1);
    debug_assert_eq!(top_struct.bottom_buckets.len(), top_struct.tares.len());
    let last_bottom = *bot_struct.bottom_buckets.last().unwrap();
    debug_assert_eq!(tot_db[tot_db[last_bottom].right().unwrap().id], Node::Dummy);
    // patch together structures
    match &mut tot_db[last_bottom] {
        Node::Leaf(_) | Node::Dummy => panic!(),
        Node::Unit(UnitNode { right, .. }) | Node::General(GeneralNode { right, .. }) => {
            *right = NodeCon {
                id: *top_struct.bottom_buckets.first().unwrap(),
                offset: 0,
                divisor: NonZeroU8::new(2).unwrap(),
                multiplier: NonZeroUsize::new(1).unwrap(),
                len_limit: None,
            }
        }
    }
    // extend old bottom buckets
    let mut old_right_max = 0;
    for &bbid in bot_struct.bottom_buckets.iter().rev() {
        let bot_buck = &tot_db[bbid];
        let right = bot_buck.right().unwrap();
        let right_max = tot_db.con_len(right);
        let left = bot_buck.left().unwrap();
        let left_max = tot_db.con_len(left);
        debug_assert_eq!(right.divisor(), 2);
        // encode outputs with new rlits
        let bot_buck = tot_db[bbid].unit();
        let olits_to_extend: Vec<_> = bot_buck
            .lits
            .iter()
            .enumerate()
            .filter_map(|(idx, litdat)| {
                if let &LitData::Lit { lit, enc_pos } = litdat {
                    if enc_pos && idx + 1 >= old_right_max {
                        return Some((lit, idx + 1));
                    }
                }
                None
            })
            .collect();
        for (olit, val) in olits_to_extend {
            for rval in tot_db[right.id].vals(
                right.rev_map(old_right_max + 1)..right.rev_map(cmp::min(right_max + 1, val)) + 1,
            ) {
                let lval = val - right.map(rval);
                if left.is_possible(lval) {
                    let rlit = tot_db.define_pos_tot(right.id, rval - 1, collector, var_manager);
                    if lval == 0 {
                        collector.extend([atomics::lit_impl_lit(rlit, olit)]);
                    } else {
                        debug_assert_eq!(left.divisor(), 1);
                        let llit = tot_db.define_pos_tot(left.id, lval - 1, collector, var_manager);
                        collector.extend([atomics::cube_impl_lit(&[rlit, llit], olit)]);
                    }
                }
            }
        }
        // next old right max
        let bot_buck = tot_db[bbid].mut_unit();
        old_right_max = bot_buck.lits.len() / 2;
        // add new output literals
        let len = right_max + left_max;
        debug_assert!(bot_buck.lits.len() <= len);
        bot_buck.lits.resize(len, LitData::None);
    }
    // extend structure
    bot_struct.bottom_buckets.extend(top_struct.bottom_buckets);
    let old_tares = bot_struct.tares.len();
    bot_struct.tares.resize(
        bot_struct.tares.len() + top_struct.tares.len(),
        Lit::new(0, false),
    );
    bot_struct.tares[..].copy_within(..old_tares, top_struct.tares.len());
    bot_struct.tares[..top_struct.tares.len()].copy_from_slice(&top_struct.tares)
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
    if oidx >= tot_db[dpw.root()].max_val() {
        return;
    }
    tot_db.define_pos_tot(dpw.root(), oidx, collector, var_manager);
}

#[cfg_attr(feature = "internals", visibility::make(pub))]
fn enforce_ub(dpw: &Structure, ub: usize, tot_db: &TotDb) -> Result<Vec<Lit>, Error> {
    let output_weight = 1 << (dpw.output_power());
    let oidx = ub / output_weight;
    if oidx >= tot_db[dpw.root()].max_val() {
        return Ok(vec![]);
    }
    let olit = match tot_db[dpw.root()].lit(oidx + 1) {
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

#[cfg(test)]
mod tests {
    use crate::{
        encodings::{pb::BoundUpper, EncodeStats},
        instances::{BasicVarManager, Cnf},
        lit,
        types::RsHashMap,
        types::Var,
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
        let mut var_manager = BasicVarManager::from_next_free(Var::new(4));
        let mut cnf = Cnf::new();
        dpw.encode_ub(0..=6, &mut cnf, &mut var_manager);
        assert_eq!(dpw.n_vars(), 9);
        assert_eq!(cnf.len(), 13);
    }

    #[test]
    fn single_lit() {
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 4);
        let mut dpw = DynamicPolyWatchdog::from(lits);
        let mut var_manager = BasicVarManager::from_next_free(Var::new(1));
        let mut cnf = Cnf::new();
        dpw.encode_ub(0..=6, &mut cnf, &mut var_manager);
        assert_eq!(dpw.n_vars(), 0);
        assert_eq!(cnf.len(), 0);
        debug_assert!(dpw.enforce_ub(4).unwrap().is_empty());
        let assumps = dpw.enforce_ub(2).unwrap();
        debug_assert_eq!(assumps.len(), 1);
        debug_assert_eq!(assumps[0], -lit![0]);
    }

    #[test]
    fn no_lit() {
        let lits = RsHashMap::default();
        let mut dpw = DynamicPolyWatchdog::from(lits);
        let mut var_manager = BasicVarManager::default();
        let mut cnf = Cnf::new();
        dpw.encode_ub(0..=6, &mut cnf, &mut var_manager);
        assert_eq!(dpw.n_vars(), 0);
        assert_eq!(cnf.len(), 0);
        debug_assert!(dpw.enforce_ub(4).unwrap().is_empty());
        debug_assert!(dpw.enforce_ub(0).unwrap().is_empty());
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
        dpw.encode_ub(0..23, &mut cnf, &mut var_manager);
        for ub in 7..23 {
            let coarse_ub = dpw.coarse_ub(ub);
            debug_assert!(coarse_ub <= ub);
            if ub % 8 == 7 {
                debug_assert_eq!(coarse_ub, ub);
            }
            let assumps = dpw.enforce_ub(coarse_ub).unwrap();
            debug_assert_eq!(assumps.len(), 1);
        }
    }

    #[test]
    fn coarse_convergence_unweighted() {
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 1);
        lits.insert(lit![1], 1);
        lits.insert(lit![2], 1);
        lits.insert(lit![3], 1);
        let mut dpw = DynamicPolyWatchdog::from(lits);
        let mut var_manager = BasicVarManager::default();
        let mut cnf = Cnf::new();
        dpw.encode_ub(0..=4, &mut cnf, &mut var_manager);
        for ub in 0..4 {
            let coarse_ub = dpw.coarse_ub(ub);
            debug_assert_eq!(coarse_ub, ub);
            let assumps = dpw.enforce_ub(coarse_ub).unwrap();
            debug_assert_eq!(assumps.len(), 1);
        }
    }

    #[test]
    fn incremental_precision() {
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 3);
        lits.insert(lit![2], 8);
        lits.insert(lit![3], 7);
        let mut dpw = DynamicPolyWatchdog::from(lits);
        let mut var_manager = BasicVarManager::default();
        // step 1
        debug_assert_eq!(dpw.next_precision(), 8);
        dpw.set_precision(8).unwrap();
        let mut cnf = Cnf::new();
        dpw.encode_ub(0..=4, &mut cnf, &mut var_manager);
        debug_assert!(!cnf.is_empty());
        // step 2
        debug_assert_eq!(dpw.next_precision(), 4);
        dpw.set_precision(4).unwrap();
        let mut cnf = Cnf::new();
        dpw.encode_ub(0..=4, &mut cnf, &mut var_manager);
        debug_assert!(!cnf.is_empty());
        // step 3
        debug_assert_eq!(dpw.next_precision(), 2);
        dpw.set_precision(2).unwrap();
        let mut cnf = Cnf::new();
        dpw.encode_ub(0..=4, &mut cnf, &mut var_manager);
        debug_assert!(!cnf.is_empty());
        // step 3
        debug_assert_eq!(dpw.next_precision(), 1);
        dpw.set_precision(1).unwrap();
        let mut cnf = Cnf::new();
        dpw.encode_ub(0..=4, &mut cnf, &mut var_manager);
        debug_assert!(!cnf.is_empty());
        // last check
        debug_assert_eq!(dpw.next_precision(), 1);
    }
}
