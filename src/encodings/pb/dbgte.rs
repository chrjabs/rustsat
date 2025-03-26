//! # GTE Based On a Node Database
//!
//! This is an alternative implementation of the
//! [`crate::encodings::pb::GeneralizedTotalizer`] encoding.

use std::ops::RangeBounds;

use crate::{
    encodings::{
        card::dbtotalizer::{INode, LitData, TotDb},
        nodedb::{NodeById, NodeCon, NodeLike},
        CollectClauses, EncodeStats, Error,
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
///     Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.
#[derive(Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DbGte {
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
    db: TotDb,
}

impl DbGte {
    /// Creates a generalized totalizer from its internal parts
    #[cfg(feature = "internals")]
    #[must_use]
    pub fn from_raw(root: NodeCon, db: TotDb, max_leaf_weight: usize) -> Self {
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
}

impl Encode for DbGte {
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

impl EncodeIncremental for DbGte {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.extend_tree(usize::MAX);
        if let Some(con) = self.root {
            self.db.reserve_vars(con.id, var_manager);
        }
    }
}

impl BoundUpper for DbGte {
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
        self.db.reset_encoded();
        self.encode_ub_change(range, collector, var_manager)
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
        if ub >= self.weight_sum() {
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
                    match &self.db[con.id].0 {
                        INode::Leaf(lit) => {
                            assumps.push(!*lit);
                            return Ok(());
                        }
                        INode::Unit(node) => {
                            if let LitData::Lit { lit, enc_pos } = node.lits[val - 1] {
                                if enc_pos {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        INode::General(node) => {
                            if let &LitData::Lit { lit, enc_pos } = node.lit_data(val).unwrap() {
                                if enc_pos {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        INode::Dummy => panic!(),
                    }
                    Err(Error::NotEncoded)
                })?;
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
                        .define_pos(con.id, val, collector, var_manager)?
                        .unwrap();
                    Ok::<(), crate::OutOfMemory>(())
                })?;
        }
        self.n_clauses += collector.n_clauses() - n_clauses_before;
        self.n_vars += var_manager.n_used() - n_vars_before;
        Ok(())
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
        Self {
            lit_buffer: lits,
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

/// Generalized totalizer encoding types that do not own but reference their [`TotDb`]
#[cfg(feature = "internals")]
pub mod referenced {
    use std::{cell::RefCell, ops::RangeBounds};

    use crate::{
        encodings::{
            card::dbtotalizer::{INode, LitData, TotDb},
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
    ///     Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.
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
    ///     Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.
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
            db: &'totdb RefCell<&'totdb mut TotDb>,
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
                    match &self.db[self.root.id].0 {
                        INode::Leaf(lit) => {
                            assumps.push(!*lit);
                            return Ok(());
                        }
                        INode::Unit(node) => {
                            if let LitData::Lit { lit, enc_pos } = node.lits[val - 1] {
                                if enc_pos {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        INode::General(node) => {
                            if let &LitData::Lit { lit, enc_pos } = node.lit_data(val).unwrap() {
                                if enc_pos {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        INode::Dummy => panic!(),
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
        ) -> Result<(), crate::OutOfMemory>
        where
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
                    match &self.db.borrow()[self.root.id].0 {
                        INode::Leaf(lit) => {
                            assumps.push(!*lit);
                            return Ok(());
                        }
                        INode::Unit(node) => {
                            if let LitData::Lit { lit, enc_pos } = node.lits[val - 1] {
                                if enc_pos {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        INode::General(node) => {
                            if let &LitData::Lit { lit, enc_pos } = node.lit_data(val).unwrap() {
                                if enc_pos {
                                    assumps.push(!lit);
                                    return Ok(());
                                }
                            }
                        }
                        INode::Dummy => panic!(),
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
                        .define_pos(self.root.id, val, collector, var_manager)?
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
                    .define_pos(self.root.id, val, collector, var_manager)?
                    .unwrap();
                Ok::<(), crate::OutOfMemory>(())
            })?;
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::DbGte;
    use crate::{
        encodings::{
            card,
            pb::{BoundUpper, BoundUpperIncremental, EncodeIncremental},
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
        gte.encode_ub(0..7, &mut Cnf::new(), &mut var_manager)
            .unwrap();
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
        gte1.encode_ub(0..5, &mut cnf1, &mut var_manager).unwrap();
        let mut gte2 = DbGte::default();
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
        let mut gte1 = DbGte::default();
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
        let mut gte1 = DbGte::default();
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 5);
        lits.insert(lit![2], 3);
        lits.insert(lit![3], 3);
        gte1.extend(lits);
        let mut var_manager = BasicVarManager::default();
        let mut cnf1 = Cnf::new();
        gte1.encode_ub(0..5, &mut cnf1, &mut var_manager).unwrap();
        let mut gte2 = DbGte::default();
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
        let mut gte = DbGte::default();
        gte.extend(vec![(lit![0], 1), (lit![1], 2), (lit![2], 3), (lit![3], 4)]);
        let mut var_manager = BasicVarManager::from_next_free(var![4]);
        gte.reserve(&mut var_manager);
        assert_eq!(var_manager.n_used(), 24);
        let mut cnf = Cnf::new();
        gte.encode_ub(0..3, &mut cnf, &mut var_manager).unwrap();
        assert_eq!(var_manager.n_used(), 24);
    }
}
