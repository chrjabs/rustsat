//! # Generalized Totalizer Encoding
//!
//! Implementation of the binary adder tree generalized totalizer encoding \[1\].
//! The implementation is incremental.
//! The implementation is recursive.
//!
//! ## References
//!
//! - \[1\] Saurabh Joshi and Ruben Martins and Vasco Manquinho: _Generalized Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.

use super::{BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental, Error};
use crate::{
    encodings::{atomics, CollectClauses, EncodeStats, IterWeightedInputs},
    instances::ManageVars,
    types::{Lit, RsHashMap},
};
use std::{
    cmp,
    collections::BTreeMap,
    ops::{Range, RangeBounds},
};

/// Implementation of the binary adder tree generalized totalizer encoding
/// \[1\]. The implementation is incremental. The implementation is recursive.
/// This encoding only support upper bounding. Lower bounding can be achieved by
/// negating the input literals. This is implemented in
/// [`super::simulators::Inverted`].
///
/// # References
///
/// - \[1\] Saurabh Joshi and Ruben Martins and Vasco Manquinho: _Generalized
///     Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.
#[derive(Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GeneralizedTotalizer {
    /// Input literals and weights for the encoding
    in_lits: RsHashMap<Lit, usize>,
    /// Input literals and weights not yet in the tree
    lit_buffer: RsHashMap<Lit, usize>,
    /// The root of the tree, if constructed
    root: Option<Node>,
    /// Maximum weight of a leaf, needed for computing how much more than `max_rhs` to encode
    max_leaf_weight: usize,
    /// Sum of all input weight
    weight_sum: usize,
    /// The number of variables in the GTE
    n_vars: u32,
    /// The number of clauses in the GTE
    n_clauses: usize,
}

impl GeneralizedTotalizer {
    /// Recursively builds the tree data structure. Uses weights out of
    /// `lit_buffer` to initialize leafs.
    fn build_tree(lits: &[(Lit, usize)]) -> Node {
        debug_assert_ne!(lits.len(), 0);

        if lits.len() == 1 {
            return Node::new_leaf(lits[0].0, lits[0].1);
        };

        let split = lits.len() / 2;
        let left = GeneralizedTotalizer::build_tree(&lits[..split]);
        let right = GeneralizedTotalizer::build_tree(&lits[split..]);

        Node::new_internal(left, right)
    }

    /// Extends the tree at the root node with added literals of maximum weight `max_weight`
    fn extend_tree(&mut self, max_weight: usize) {
        if !self.lit_buffer.is_empty() {
            let mut new_lits: Vec<(Lit, usize)> = self
                .lit_buffer
                .iter()
                .filter_map(|(&l, &w)| {
                    if w <= max_weight {
                        if w > self.max_leaf_weight {
                            // Track maximum leaf weight
                            self.max_leaf_weight = w;
                        }
                        Some((l, w))
                    } else {
                        None
                    }
                })
                .collect();
            if !new_lits.is_empty() {
                // Add nodes in sorted fashion to minimize clauses
                new_lits.sort_by_key(|(_, w)| *w);
                let subtree = GeneralizedTotalizer::build_tree(&new_lits[..]);
                self.root = match self.root.take() {
                    None => Some(subtree),
                    Some(old_root) => {
                        let new_root = Node::new_internal(old_root, subtree);
                        Some(new_root)
                    }
                };
                self.lit_buffer.retain(|_, w| *w > max_weight);
            }
        }
    }

    /// Gets the maximum depth of the tree
    pub fn depth(&mut self) -> usize {
        self.root.as_ref().map_or(0, Node::depth)
    }

    /// Fully builds the tree, then returns it
    #[cfg(feature = "internals")]
    #[must_use]
    pub fn tree(mut self) -> Option<Node> {
        self.extend_tree(usize::MAX);
        self.root
    }
}

impl Encode for GeneralizedTotalizer {
    fn weight_sum(&self) -> usize {
        self.weight_sum
    }

    fn next_higher(&self, val: usize) -> usize {
        if let Some(Node::Internal { out_lits, .. }) = &self.root {
            if let Some((&next, _)) = out_lits.range(val + 1..).next() {
                return next;
            }
        }
        val + 1
    }

    fn next_lower(&self, val: usize) -> usize {
        if val == 0 {
            return 0;
        }
        if let Some(Node::Internal { out_lits, .. }) = &self.root {
            return out_lits.range(..val).next_back().map_or(0, |(w, _)| *w);
        }
        val - 1
    }
}

impl IterWeightedInputs for GeneralizedTotalizer {
    type Iter<'a> = GteIter<'a>;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().map(copy_key_val)
    }
}

impl EncodeIncremental for GeneralizedTotalizer {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.extend_tree(usize::MAX);
        if let Some(root) = &mut self.root {
            root.reserve_all_vars_rec(var_manager);
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
        let range = super::prepare_ub_range(self, range);
        if range.is_empty() {
            return Ok(());
        };
        let n_vars_before = var_manager.n_used();
        let n_clauses_before = collector.n_clauses();
        self.extend_tree(range.end - 1);
        #[allow(clippy::range_plus_one)]
        match &mut self.root {
            None => (),
            Some(root) => root.rec_encode(
                (range.start + 1)..(range.end + self.max_leaf_weight) + 1,
                collector,
                var_manager,
            )?,
        };
        self.n_clauses += collector.n_clauses() - n_clauses_before;
        self.n_vars += var_manager.n_used() - n_vars_before;
        Ok(())
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
        if ub >= self.weight_sum {
            return Ok(vec![]);
        }

        // Assume literals that have higher weight than `ub`
        let mut assumps = Vec::with_capacity(self.lit_buffer.len());
        self.lit_buffer.iter().try_for_each(|(_, &w)| {
            if w <= ub {
                Err(Error::NotEncoded)
            } else {
                Ok(())
            }
        })?;
        self.in_lits.iter().for_each(|(&l, &w)| {
            if w > ub {
                assumps.push(!l);
            }
        });
        // Enforce bound on internal tree
        assumps.extend(match &self.root {
            None => {
                vec![]
            }
            Some(root_node) => match &root_node {
                // Assumes that literal is already enforced from wrapper function if it's weight is more than `ub`
                Node::Leaf { .. } => vec![],
                Node::Internal {
                    out_lits,
                    enc_range,
                    max_val,
                    ..
                } => {
                    if ub >= *max_val {
                        vec![]
                    } else if enc_range.contains(&(ub + 1))
                        && enc_range.contains(&cmp::min(*max_val, ub + self.max_leaf_weight))
                    {
                        out_lits
                            .range(ub + 1..=ub + self.max_leaf_weight)
                            .map(|(_, &l)| !l)
                            .collect()
                    } else {
                        return Err(Error::NotEncoded);
                    }
                }
            },
        });
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
        };
        let n_vars_before = var_manager.n_used();
        let n_clauses_before = collector.n_clauses();
        self.extend_tree(range.end - 1);
        if let Some(root) = self.root.as_mut() {
            root.rec_encode_change(
                range.start + 1..range.end + self.max_leaf_weight,
                collector,
                var_manager,
            )?;
        }
        self.n_clauses += collector.n_clauses() - n_clauses_before;
        self.n_vars += var_manager.n_used() - n_vars_before;
        Ok(())
    }
}

impl EncodeStats for GeneralizedTotalizer {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        self.n_vars
    }
}

pub(super) fn copy_key_val(key_val_refs: (&Lit, &usize)) -> (Lit, usize) {
    (*key_val_refs.0, *key_val_refs.1)
}
pub(super) type GteIter<'a> = std::iter::Map<
    std::collections::hash_map::Iter<'a, Lit, usize>,
    fn((&Lit, &usize)) -> (Lit, usize),
>;

impl From<RsHashMap<Lit, usize>> for GeneralizedTotalizer {
    fn from(lits: RsHashMap<Lit, usize>) -> Self {
        let weight_sum = lits.iter().fold(0, |sum, (_, w)| sum + *w);
        Self {
            in_lits: lits.clone(),
            lit_buffer: lits,
            weight_sum,
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
            self.weight_sum += w;
            // Insert into buffer to be added to tree
            match self.lit_buffer.get_mut(&l) {
                Some(old_w) => *old_w += w,
                None => {
                    self.lit_buffer.insert(l, w);
                }
            };
            // Insert into map of input literals
            match self.in_lits.get_mut(&l) {
                Some(old_w) => *old_w += w,
                None => {
                    self.in_lits.insert(l, w);
                }
            };
        });
    }
}

/// A node in the generalized totalizer tree. This is only exposed publicly to
/// be reused in more complex encodings, for using the GTE, this should
/// not be directly accessed but only through [`GeneralizedTotalizer`].
///
/// The Totalizer nodes are _only_ for upper bounding. Lower bounding in the GTE
/// is possible by negating input literals. This conversion entirely happens in
/// the [`super::InvertedGeneralizedTotalizer`] struct. Equally, bounds given on the
/// encode methods for this type strictly refer to the output literals that
/// should be encoded. Converting right hand sides to required encoded output
/// literals happens in the [`GeneralizedTotalizer`] or
/// [`super::InvertedGeneralizedTotalizer`] structs.
#[cfg_attr(feature = "internals", visibility::make(pub))]
#[cfg_attr(docsrs, doc(cfg(feature = "internals")))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
enum Node {
    /// A weighted input literal, i.e., a leaf node of the tree
    Leaf {
        /// The input literal to the tree
        lit: Lit,
        /// The weight of the input literal
        weight: usize,
    },
    /// An internal weighted node of the tree
    Internal {
        /// The weighted output literals of this node
        out_lits: BTreeMap<usize, Lit>,
        /// The path length to the leaf furthest away in the sub-tree
        depth: usize,
        /// The number of clauses this node produced
        n_clauses: usize,
        /// The maximum output this node can have
        max_val: usize,
        /// The encoded range of this node
        enc_range: Range<usize>,
        /// The left child
        left: Box<Node>,
        /// The right child
        right: Box<Node>,
    },
}

impl Node {
    /// Constructs a new leaf node
    #[must_use]
    pub fn new_leaf(lit: Lit, weight: usize) -> Node {
        Node::Leaf { lit, weight }
    }

    /// Constructs a new internal node
    #[must_use]
    pub fn new_internal(left: Node, right: Node) -> Node {
        Node::Internal {
            out_lits: BTreeMap::new(),
            depth: cmp::max(left.depth() + 1, right.depth() + 1),
            n_clauses: 0,
            enc_range: 0..0,
            max_val: left.max_val() + right.max_val(),
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Gets the maximum depth of the sub-tree rooted in this node
    #[must_use]
    pub fn depth(&self) -> usize {
        match self {
            Node::Leaf { .. } => 1,
            Node::Internal { depth, .. } => *depth,
        }
    }

    /// Gets the maximum value that the node represents
    #[must_use]
    pub fn max_val(&self) -> usize {
        match self {
            Node::Leaf { weight, .. } => *weight,
            Node::Internal { max_val, .. } => *max_val,
        }
    }

    /// Gets a reference to the output literals. The temporary map is needed in
    /// case the node is not internal.
    fn lit_map<'a>(&'a self, tmp_map: &'a mut BTreeMap<usize, Lit>) -> &'a BTreeMap<usize, Lit> {
        match &self {
            Node::Leaf { lit, weight } => {
                tmp_map.insert(*weight, *lit);
                tmp_map
            }
            Node::Internal { out_lits, .. } => out_lits,
        }
    }

    /// Encodes the output literals for this node in a given range. This method
    /// only produces the encoding and does _not_ change any of the stats of the
    /// node.
    fn encode_range<Col>(
        &mut self,
        range: Range<usize>,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        let range = self.limit_range(range);
        if range.is_empty() {
            return Ok(());
        }

        // Reserve vars if needed
        self.reserve_vars_range(range.clone(), var_manager);
        match &*self {
            Node::Leaf { .. } => (),
            Node::Internal {
                out_lits,
                left,
                right,
                ..
            } => {
                let mut left_tmp_map = BTreeMap::new();
                let mut right_tmp_map = BTreeMap::new();
                let left_lits = left.lit_map(&mut left_tmp_map);
                let right_lits = right.lit_map(&mut right_tmp_map);
                // Encode adder for current node
                // Propagate left value
                collector.extend_clauses(left_lits.range(range.clone()).map(
                    |(left_val, &left_lit)| {
                        atomics::lit_impl_lit(left_lit, *out_lits.get(left_val).unwrap())
                    },
                ))?;
                // Propagate right value
                collector.extend_clauses(right_lits.range(range.clone()).map(
                    |(right_val, &right_lit)| {
                        atomics::lit_impl_lit(right_lit, *out_lits.get(right_val).unwrap())
                    },
                ))?;
                // Propagate sum
                if range.end > 1 {
                    let clause_from_data =
                        |left_val: usize, right_val: usize, left_lit: Lit, right_lit: Lit| {
                            let sum_val = left_val + right_val;
                            if !range.contains(&sum_val) {
                                return None;
                            }
                            Some(atomics::cube_impl_lit(
                                &[left_lit, right_lit],
                                *out_lits.get(&sum_val).unwrap(),
                            ))
                        };
                    let right_min =
                        |range_start: usize, left_val| range_start.saturating_sub(left_val);
                    let clause_iter =
                        left_lits
                            .range(1..range.end - 1)
                            .flat_map(|(&left_val, &left_lit)| {
                                right_lits
                                    .range(right_min(range.start, left_val)..range.end - left_val)
                                    .filter_map(move |(&right_val, &right_lit)| {
                                        clause_from_data(left_val, right_val, left_lit, right_lit)
                                    })
                            });
                    collector.extend_clauses(clause_iter)?;
                }
            }
        };
        Ok(())
    }

    /// Encodes the output literals from the children to this node in a given
    /// range. Recurses depth first. Always encodes the full requested CNF
    /// encoding.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    pub fn rec_encode<Col>(
        &mut self,
        range: Range<usize>,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        let range = self.limit_range(range);
        if range.is_empty() {
            return Ok(());
        }

        // Ignore all previous encoding and encode from scratch
        match self {
            Node::Leaf { .. } => (),
            Node::Internal { left, right, .. } => {
                let left_range = Node::compute_required_min_enc(range.clone(), right.max_val());
                let right_range = Node::compute_required_min_enc(range.clone(), left.max_val());
                // Recurse
                left.rec_encode(left_range, collector, var_manager)?;
                right.rec_encode(right_range, collector, var_manager)?;

                // Encode current node
                let n_clauses_before = collector.n_clauses();
                self.encode_range(range.clone(), collector, var_manager)?;

                self.update_stats(range, collector.n_clauses() - n_clauses_before);
            }
        };

        Ok(())
    }

    /// Encodes the output literals from the children to this node in a given
    /// range. Recurses depth first. Incrementally only encodes new clauses.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    pub fn rec_encode_change<Col>(
        &mut self,
        range: Range<usize>,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        let range = self.limit_range(range);
        if range.is_empty() {
            return Ok(());
        }

        match self {
            Node::Leaf { .. } => (),
            Node::Internal {
                left,
                right,
                enc_range,
                ..
            } => {
                // Copy to avoid borrow checker
                let enc_range = enc_range.clone();

                let left_range = Node::compute_required_min_enc(range.clone(), right.max_val());
                let right_range = Node::compute_required_min_enc(range.clone(), left.max_val());
                // Recurse
                left.rec_encode_change(left_range, collector, var_manager)?;
                right.rec_encode_change(right_range, collector, var_manager)?;

                // Encode changes for current node
                let n_clauses_before = collector.n_clauses();
                if enc_range.is_empty() {
                    // First time encoding this node
                    self.encode_range(range.clone(), collector, var_manager)?;
                } else {
                    // Partially encoded
                    if range.start < enc_range.start {
                        self.encode_range(range.start..enc_range.start, collector, var_manager)?;
                    };
                    if range.end > enc_range.end {
                        self.encode_range(enc_range.end..range.end, collector, var_manager)?;
                    };
                };

                self.update_stats(range, collector.n_clauses() - n_clauses_before);
            }
        };
        Ok(())
    }

    /// Reserves variables this node might need in a given range
    fn reserve_vars_range(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) {
        let range = self.limit_range(range);
        if range.is_empty() {
            return;
        }
        match self {
            Node::Leaf { .. } => (),
            Node::Internal {
                out_lits,
                left,
                right,
                ..
            } => {
                let mut left_tmp_map = BTreeMap::new();
                let mut right_tmp_map = BTreeMap::new();
                let left_lits = left.lit_map(&mut left_tmp_map);
                let right_lits = right.lit_map(&mut right_tmp_map);
                // Reserve vars
                for (&left_val, _) in left_lits.range(range.clone()) {
                    out_lits
                        .entry(left_val)
                        .or_insert_with(|| var_manager.new_var().pos_lit());
                }
                for (&right_val, _) in right_lits.range(range.clone()) {
                    out_lits
                        .entry(right_val)
                        .or_insert_with(|| var_manager.new_var().pos_lit());
                }
                if range.end > 1 {
                    for (&left_val, _) in left_lits.range(1..range.end - 1) {
                        let right_min = if range.start > left_val {
                            range.start - left_val
                        } else {
                            0
                        };
                        for (&right_val, _) in right_lits.range(right_min..range.end - left_val) {
                            let sum_val = left_val + right_val;
                            if !range.contains(&sum_val) {
                                continue;
                            }
                            out_lits
                                .entry(sum_val)
                                .or_insert_with(|| var_manager.new_var().pos_lit());
                        }
                    }
                }
            }
        }
    }

    /// Reserves all variables this node might need. This is used if variables
    /// in the totalizer should have consecutive indices.
    pub fn reserve_all_vars(&mut self, var_manager: &mut dyn ManageVars) {
        let max_val = match self {
            Node::Leaf { .. } => return,
            Node::Internal { max_val, .. } => *max_val,
        };
        #[allow(clippy::range_plus_one)]
        self.reserve_vars_range(0..max_val + 1, var_manager);
    }

    /// Reserves all variables this node and the lower sub-tree might need. This
    /// is used if variables in the totalizer should have consecutive indices.
    pub fn reserve_all_vars_rec(&mut self, var_manager: &mut dyn ManageVars) {
        match self {
            Node::Leaf { .. } => return,
            Node::Internal { left, right, .. } => {
                // Recursion
                left.reserve_all_vars_rec(var_manager);
                right.reserve_all_vars_rec(var_manager);
            }
        };
        self.reserve_all_vars(var_manager);
    }

    /// Computes the required encoding range for a node given a requested range
    /// for the parent and the maximum value of the sibling.
    fn compute_required_min_enc(requested_range: Range<usize>, max_sibling: usize) -> Range<usize> {
        if requested_range.is_empty() {
            0..0
        } else if requested_range.start > max_sibling {
            requested_range.start - max_sibling..requested_range.end
        } else {
            0..requested_range.end
        }
    }

    /// Limits a range by the maximum of the node
    fn limit_range(&self, range: Range<usize>) -> Range<usize> {
        match self {
            Node::Leaf { .. } => range.start..cmp::min(2, range.end),
            Node::Internal { max_val, .. } => range.start..cmp::min(*max_val + 1, range.end),
        }
    }

    /// Updates the statistics of the node by increasing the number of clauses
    /// and updating the encoded range
    fn update_stats(&mut self, new_enc_range: Range<usize>, new_n_clauses: usize) {
        match self {
            Node::Leaf { .. } => debug_assert_eq!(new_n_clauses, 0),
            Node::Internal {
                n_clauses,
                enc_range,
                max_val,
                ..
            } => {
                *n_clauses += new_n_clauses;
                *enc_range = if (*enc_range).is_empty() {
                    new_enc_range.start..cmp::min(*max_val + 1, new_enc_range.end)
                } else {
                    cmp::min(new_enc_range.start, enc_range.start)
                        ..cmp::min(*max_val + 1, cmp::max(new_enc_range.end, enc_range.end))
                };
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::{GeneralizedTotalizer, Node};
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
    fn adder_1() {
        // Child nodes
        let child1 = Node::new_leaf(lit![0], 5);
        let child2 = Node::new_leaf(lit![1], 3);
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::default();
        let mut cnf = Cnf::new();
        node.encode_range(0..9, &mut cnf, &mut var_manager).unwrap();
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 3),
        };
        assert_eq!(cnf.len(), 3);
    }

    #[test]
    fn adder_2() {
        // (Inconsistent) child nodes
        let mut lits = BTreeMap::new();
        lits.insert(3, lit![1]);
        lits.insert(5, lit![2]);
        lits.insert(8, lit![3]);
        let child1 = Node::Internal {
            out_lits: lits,
            depth: 1,
            n_clauses: 0,
            max_val: 8,
            enc_range: 0..9,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0], 5)),
            right: Box::new(Node::new_leaf(lit![0], 3)),
        };
        let mut lits = BTreeMap::new();
        lits.insert(3, lit![4]);
        lits.insert(5, lit![5]);
        lits.insert(8, lit![6]);
        let child2 = Node::Internal {
            out_lits: lits,
            depth: 1,
            n_clauses: 0,
            max_val: 8,
            enc_range: 0..9,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0], 5)),
            right: Box::new(Node::new_leaf(lit![0], 3)),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::default();
        let mut cnf = Cnf::new();
        node.encode_range(0..7, &mut cnf, &mut var_manager).unwrap();
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 3),
        };
        assert_eq!(cnf.len(), 5);
    }

    #[test]
    fn partial_adder_1() {
        // (Inconsistent) child nodes
        let mut lits = BTreeMap::new();
        lits.insert(3, lit![1]);
        lits.insert(5, lit![2]);
        lits.insert(8, lit![3]);
        let child1 = Node::Internal {
            out_lits: lits,
            depth: 1,
            n_clauses: 0,
            max_val: 8,
            enc_range: 0..9,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0], 5)),
            right: Box::new(Node::new_leaf(lit![0], 3)),
        };
        let mut lits = BTreeMap::new();
        lits.insert(3, lit![4]);
        lits.insert(5, lit![5]);
        lits.insert(8, lit![6]);
        let child2 = Node::Internal {
            out_lits: lits,
            depth: 1,
            n_clauses: 0,
            max_val: 8,
            enc_range: 0..9,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0], 5)),
            right: Box::new(Node::new_leaf(lit![0], 3)),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::default();
        let mut cnf = Cnf::new();
        node.encode_range(4..7, &mut cnf, &mut var_manager).unwrap();
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 2),
        };
        assert_eq!(cnf.len(), 3);
    }

    #[test]
    fn partial_adder_already_encoded() {
        // (Inconsistent) child nodes
        let mut lits = BTreeMap::new();
        lits.insert(3, lit![1]);
        lits.insert(5, lit![2]);
        lits.insert(8, lit![3]);
        let child1 = Node::Internal {
            out_lits: lits,
            depth: 1,
            n_clauses: 0,
            max_val: 8,
            enc_range: 0..9,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0], 5)),
            right: Box::new(Node::new_leaf(lit![0], 3)),
        };
        let mut lits = BTreeMap::new();
        lits.insert(3, lit![4]);
        lits.insert(5, lit![5]);
        lits.insert(8, lit![6]);
        let child2 = Node::Internal {
            out_lits: lits,
            depth: 1,
            n_clauses: 0,
            max_val: 8,
            enc_range: 0..9,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0], 5)),
            right: Box::new(Node::new_leaf(lit![0], 3)),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::default();
        let mut cnf = Cnf::new();
        #[allow(clippy::reversed_empty_ranges)]
        node.encode_range(6..5, &mut cnf, &mut var_manager).unwrap();
        assert_eq!(cnf.len(), 0);
    }

    #[test]
    fn ub_gte_functions() {
        let mut gte = GeneralizedTotalizer::default();
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
        assert_eq!(var_manager.n_used(), 20);
        let mut cnf = Cnf::new();
        gte.encode_ub(0..3, &mut cnf, &mut var_manager).unwrap();
        assert_eq!(var_manager.n_used(), 20);
    }
}
