//! # GTE Based On a Node Database
//!
//! This is an alternative implementation of the
//! [`crate::encodings::pb::GeneralizedTotalizer`] encoding.

use std::ops::RangeBounds;

use crate::{
    encodings::{
        card::dbtotalizer::{LitData, Node, TotDb},
        nodedb::{NodeById, NodeCon, NodeLike},
        CollectClauses, EncodeStats, Error,
    },
    instances::ManageVars,
    types::{Lit, RsHashMap},
};

use super::{BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental};

#[cfg(feature = "pyapi")]
use crate::instances::{BasicVarManager, Cnf};
#[cfg(feature = "pyapi")]
use pyo3::prelude::*;

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
#[cfg_attr(feature = "pyapi", pyclass(name = "GeneralizedTotalizer"))]
#[derive(Default)]
pub struct DbGte {
    /// Input literals and weights not yet in the tree
    lit_buffer: RsHashMap<Lit, usize>,
    /// The root of the tree, if constructed
    root: Option<NodeCon>,
    /// Maximum weight of a leaf, needed for computing how much more than
    /// `max_rhs` to encode
    max_leaf_weight: usize,
    /// Sum of all input weight
    weight_sum: usize,
    /// The number of variables in the totalizer
    n_vars: u32,
    /// The number of clauses in the totalizer
    n_clauses: usize,
    /// The node database of the totalizer
    db: TotDb,
}

impl DbGte {
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

    pub fn depth(&self) -> usize {
        self.root.map_or(0, |con| self.db[con.id].depth())
    }
}

impl Encode for DbGte {
    fn weight_sum(&self) -> usize {
        self.weight_sum
    }

    fn next_higher(&self, val: usize) -> usize {
        if let Some(con) = self.root {
            self.db[con.id]
                .vals(con.rev_map_round_up(val + 1)..)
                .next()
                .map(|val| con.map(val))
                .unwrap_or(val + 1)
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
                .map(|val| con.map(val))
                .unwrap_or(0);
        }
        val - 1
    }
}

impl EncodeIncremental for DbGte {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        if let Some(con) = self.root {
            self.db.reserve_vars(con.id, var_manager)
        }
    }
}

impl BoundUpper for DbGte {
    fn encode_ub<Col, R>(&mut self, range: R, collector: &mut Col, var_manager: &mut dyn ManageVars)
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        self.db.reset_encoded();
        self.encode_ub_change(range, collector, var_manager);
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
        if ub >= self.weight_sum {
            return Ok(vec![]);
        }

        let mut assumps = vec![];
        self.lit_buffer.iter().try_for_each(|(&l, &w)| {
            if w <= ub {
                Err(Error::NotEncoded)
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
                        Node::Leaf(lit) => {
                            assumps.push(!*lit);
                            return Ok(());
                        }
                        Node::Unit(node) => {
                            if let LitData::Lit { lit, enc_pos } = node.lits[val - 1] {
                                if enc_pos {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        Node::General(node) => {
                            if let LitData::Lit { lit, enc_pos } = node.lits[&val] {
                                if enc_pos {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                    }
                    Err(Error::NotEncoded)
                })?
        };
        Ok(assumps)
    }
}

impl BoundUpperIncremental for DbGte {
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
        let n_clauses_before = collector.n_clauses();
        self.extend_tree(range.end - 1);
        if let Some(con) = self.root {
            self.db[con.id]
                .vals(
                    con.rev_map_round_up(range.start + 1)
                        ..=con.rev_map(range.end + self.max_leaf_weight),
                )
                .for_each(|val| {
                    self.db
                        .define_pos(con.id, val, collector, var_manager)
                        .unwrap();
                })
        }
        self.n_clauses += collector.n_clauses() - n_clauses_before;
        self.n_vars += var_manager.n_used() - n_vars_before;
    }
}

impl EncodeStats for DbGte {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        self.n_vars
    }
}

impl From<RsHashMap<Lit, usize>> for DbGte {
    fn from(lits: RsHashMap<Lit, usize>) -> Self {
        let weight_sum = lits.iter().fold(0, |sum, (_, w)| sum + *w);
        Self {
            lit_buffer: lits,
            weight_sum,
            ..Default::default()
        }
    }
}

impl FromIterator<(Lit, usize)> for DbGte {
    fn from_iter<T: IntoIterator<Item = (Lit, usize)>>(iter: T) -> Self {
        let lits: RsHashMap<Lit, usize> = RsHashMap::from_iter(iter);
        Self::from(lits)
    }
}

impl Extend<(Lit, usize)> for DbGte {
    fn extend<T: IntoIterator<Item = (Lit, usize)>>(&mut self, iter: T) {
        iter.into_iter().for_each(|(l, w)| {
            self.weight_sum += w;
            // Insert into buffer to be added to tree
            match self.lit_buffer.get_mut(&l) {
                Some(old_w) => *old_w += w,
                None => {
                    self.lit_buffer.insert(l, w);
                }
            };
        });
    }
}

#[cfg(feature = "internals")]
pub mod referenced {
    use std::{cell::RefCell, ops::RangeBounds};

    use crate::{
        encodings::{
            card::dbtotalizer::{LitData, Node, TotDb},
            nodedb::{NodeCon, NodeLike},
            pb::{BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental},
            CollectClauses, Error,
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
    pub struct Gte<'totdb> {
        /// A node connection to the root
        root: NodeCon,
        /// The maximum weight of any leaf
        max_leaf_weight: usize,
        /// The node database of the totalizer
        db: &'totdb mut TotDb,
    }

    /// Generalized totalizer encoding with a [`RefCell`] to a totalizer
    /// database rather than owning it.
    ///
    /// ## References
    ///
    /// - \[1\] Saurabh Joshi and Ruben Martins and Vasco Manquinho: _Generalized
    ///   Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.
    pub struct GteCell<'totdb> {
        /// A node connection to the root
        root: NodeCon,
        /// The maximum weight of any leaf
        max_leaf_weight: usize,
        /// The node database of the totalizer
        db: &'totdb RefCell<&'totdb mut TotDb>,
    }

    impl<'totdb> Gte<'totdb> {
        /// Constructs a new GTE encoding referencing a totalizer database
        pub fn new(root: NodeCon, max_leaf_weight: usize, db: &'totdb mut TotDb) -> Self {
            Self {
                root,
                max_leaf_weight,
                db,
            }
        }

        /// Gets the maximum depth of the tree
        pub fn depth(&self) -> usize {
            self.db[self.root.id].depth()
        }
    }

    impl<'totdb> GteCell<'totdb> {
        /// Constructs a new GTE encoding referencing a totalizer database
        pub fn new(
            root: NodeCon,
            max_leaf_weight: usize,
            db: &'totdb RefCell<&'totdb mut TotDb>,
        ) -> Self {
            Self {
                root,
                max_leaf_weight,
                db,
            }
        }

        /// Gets the maximum depth of the tree
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
                .map(|val| self.root.map(val))
                .unwrap_or(val + 1)
        }

        fn next_lower(&self, val: usize) -> usize {
            self.db[self.root.id]
                .vals(self.root.offset()..self.root.rev_map_round_up(val))
                .next_back()
                .map(|val| self.root.map(val))
                .unwrap_or(val - 1)
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
                .map(|val| self.root.map(val))
                .unwrap_or(val + 1)
        }

        fn next_lower(&self, val: usize) -> usize {
            self.db.borrow()[self.root.id]
                .vals(self.root.offset()..self.root.rev_map_round_up(val))
                .next_back()
                .map(|val| self.root.map(val))
                .unwrap_or(val - 1)
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
        ) where
            Col: CollectClauses,
            R: RangeBounds<usize>,
        {
            self.db.reset_encoded();
            self.encode_ub_change(range, collector, var_manager)
        }

        fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
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
                        Node::Leaf(lit) => {
                            assumps.push(!*lit);
                            return Ok(());
                        }
                        Node::Unit(node) => {
                            if let LitData::Lit { lit, enc_pos } = node.lits[val - 1] {
                                if enc_pos {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        Node::General(node) => {
                            if let LitData::Lit { lit, enc_pos } = node.lits[&val] {
                                if enc_pos {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                    }
                    Err(Error::NotEncoded)
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
        ) where
            Col: CollectClauses,
            R: RangeBounds<usize>,
        {
            self.db.borrow_mut().reset_encoded();
            self.encode_ub_change(range, collector, var_manager)
        }

        fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
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
                        Node::Leaf(lit) => {
                            assumps.push(!*lit);
                            return Ok(());
                        }
                        Node::Unit(node) => {
                            if let LitData::Lit { lit, enc_pos } = node.lits[val - 1] {
                                if enc_pos {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        Node::General(node) => {
                            if let LitData::Lit { lit, enc_pos } = node.lits[&val] {
                                if enc_pos {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                    }
                    Err(Error::NotEncoded)
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
        ) where
            Col: CollectClauses,
            R: RangeBounds<usize>,
        {
            let range = super::super::prepare_ub_range(self, range);
            if range.is_empty() {
                return;
            }
            self.db[self.root.id]
                .vals(
                    self.root.rev_map_round_up(range.start + 1)
                        ..=self.root.rev_map(range.end + self.max_leaf_weight),
                )
                .for_each(|val| {
                    self.db
                        .define_pos(self.root.id, val, collector, var_manager)
                        .unwrap();
                });
        }
    }

    impl BoundUpperIncremental for GteCell<'_> {
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
            let vals = self.db.borrow()[self.root.id].vals(
                self.root.rev_map_round_up(range.start + 1)
                    ..=self.root.rev_map(range.end + self.max_leaf_weight),
            );
            vals.for_each(|val| {
                self.db
                    .borrow_mut()
                    .define_pos(self.root.id, val, collector, var_manager)
                    .unwrap();
            });
        }
    }
}

#[cfg(feature = "pyapi")]
#[pymethods]
impl DbGte {
    #[new]
    fn new(lits: Vec<(Lit, usize)>) -> Self {
        Self::from_iter(lits)
    }

    /// Adds additional input literals to the generalized totalizer
    #[pyo3(name = "extend")]
    fn py_extend(&mut self, lits: Vec<(Lit, usize)>) {
        self.extend(lits)
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

    /// Incrementally builds the GTE encoding to that upper bounds
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
    use super::DbGte;
    use crate::{
        encodings::{
            card,
            pb::{BoundUpper, BoundUpperIncremental},
            EncodeStats, Error,
        },
        instances::{BasicVarManager, Cnf, ManageVars},
        lit,
        types::RsHashMap,
        var,
    };

    #[test]
    fn ub_gte_functions() {
        let mut gte = DbGte::default();
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 5);
        lits.insert(lit![2], 3);
        lits.insert(lit![3], 3);
        gte.extend(lits);
        assert_eq!(gte.enforce_ub(4), Err(Error::NotEncoded));
        let mut var_manager = BasicVarManager::default();
        gte.encode_ub(0..7, &mut Cnf::new(), &mut var_manager);
        assert_eq!(gte.depth(), 3);
        assert_eq!(gte.n_vars(), 10);
    }

    #[test]
    fn ub_gte_incremental_building() {
        let mut gte1 = DbGte::default();
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 5);
        lits.insert(lit![2], 3);
        lits.insert(lit![3], 3);
        gte1.extend(lits.clone());
        let mut var_manager = BasicVarManager::default();
        let mut cnf1 = Cnf::new();
        gte1.encode_ub(0..5, &mut cnf1, &mut var_manager);
        let mut gte2 = DbGte::default();
        gte2.extend(lits);
        let mut var_manager = BasicVarManager::default();
        let mut cnf2 = Cnf::new();
        gte2.encode_ub(0..3, &mut cnf2, &mut var_manager);
        gte2.encode_ub_change(0..5, &mut cnf2, &mut var_manager);
        assert_eq!(cnf1.len(), cnf2.len());
        assert_eq!(cnf1.len(), gte1.n_clauses());
        assert_eq!(cnf2.len(), gte2.n_clauses());
    }

    #[test]
    fn ub_gte_multiplication() {
        let mut gte1 = DbGte::default();
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 5);
        lits.insert(lit![2], 3);
        lits.insert(lit![3], 3);
        gte1.extend(lits);
        let mut var_manager = BasicVarManager::default();
        let mut cnf1 = Cnf::new();
        gte1.encode_ub(0..5, &mut cnf1, &mut var_manager);
        let mut gte2 = DbGte::default();
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 10);
        lits.insert(lit![1], 10);
        lits.insert(lit![2], 6);
        lits.insert(lit![3], 6);
        gte2.extend(lits);
        let mut var_manager = BasicVarManager::default();
        let mut cnf2 = Cnf::new();
        gte2.encode_ub(0..9, &mut cnf2, &mut var_manager);
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
        let mut gte = DbGte::default();
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
        gte.encode_ub(3..8, &mut gte_cnf, &mut var_manager_gte);
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
        card::BoundUpper::encode_ub(&mut tot, 3..8, &mut tot_cnf, &mut var_manager_tot);
        println!("{:?}", gte_cnf);
        println!("{:?}", tot_cnf);
        assert_eq!(var_manager_gte.new_var(), var_manager_tot.new_var());
        assert_eq!(gte_cnf.len(), tot_cnf.len());
        assert_eq!(gte_cnf.len(), gte.n_clauses());
        assert_eq!(tot_cnf.len(), tot.n_clauses());
    }
}
