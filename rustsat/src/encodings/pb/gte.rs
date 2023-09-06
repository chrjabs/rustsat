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
    encodings::EncodeStats,
    instances::{Cnf, ManageVars},
    types::{Lit, RsHashMap},
};
use std::{
    cmp,
    collections::BTreeMap,
    ops::{Bound, Range},
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
///   Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.
#[derive(Default)]
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
    n_vars: usize,
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
                new_lits[..].sort_by(|(_, w1), (_, w2)| w1.cmp(w2));
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
        match &self.root {
            None => 0,
            Some(root_node) => root_node.depth(),
        }
    }

    /// Fully builds the tree, then returns it
    #[cfg(feature = "internals")]
    pub fn tree(mut self) -> Option<Node> {
        self.extend_tree(usize::MAX);
        self.root
    }
}

impl Encode for GeneralizedTotalizer {
    type Iter<'a> = GTEIter<'a>;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().map(copy_key_val)
    }

    fn weight_sum(&self) -> usize {
        self.weight_sum
    }

    fn next_higher(&self, val: usize) -> usize {
        if let Some(Node::Internal { out_lits, .. }) = &self.root {
            if let Some((&next, _)) = out_lits
                .range((Bound::Excluded(val), Bound::Unbounded))
                .next()
            {
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
            if let Some((&next, _)) = out_lits
                .range((Bound::Unbounded, Bound::Excluded(val)))
                .next_back()
            {
                return next;
            } else {
                return 0;
            }
        }
        val - 1
    }
}

impl EncodeIncremental for GeneralizedTotalizer {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        if let Some(root) = &mut self.root {
            root.reserve_all_vars_rec(var_manager);
        }
    }
}

impl BoundUpper for GeneralizedTotalizer {
    fn encode_ub(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf {
        if range.is_empty() {
            return Cnf::new();
        };
        let n_vars_before = var_manager.n_used();
        self.extend_tree(range.end - 1);
        let cnf = match &mut self.root {
            None => Cnf::new(),
            Some(root) => root.rec_encode(
                range.start + 1..range.end + self.max_leaf_weight + 1,
                var_manager,
            ),
        };
        self.n_clauses += cnf.n_clauses();
        self.n_vars += var_manager.n_used() - n_vars_before;
        cnf
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
        let mut assumps = vec![];
        // Assume literals that have higher weight than `ub`
        assumps.reserve(self.lit_buffer.len());
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
                            .range((
                                Bound::Excluded(ub),
                                Bound::Included(ub + self.max_leaf_weight),
                            ))
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
    fn encode_ub_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf {
        if range.is_empty() {
            return Cnf::new();
        };
        let n_vars_before = var_manager.n_used();
        self.extend_tree(range.end - 1);
        let cnf = match &mut self.root {
            None => Cnf::new(),
            Some(root) => root.rec_encode_change(
                range.start + 1..range.end + self.max_leaf_weight,
                var_manager,
            ),
        };
        self.n_clauses += cnf.n_clauses();
        self.n_vars += var_manager.n_used() - n_vars_before;
        cnf
    }
}

impl EncodeStats for GeneralizedTotalizer {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> usize {
        self.n_vars
    }
}

fn copy_key_val(key_val_refs: (&Lit, &usize)) -> (Lit, usize) {
    (*key_val_refs.0, *key_val_refs.1)
}
type GTEIter<'a> = std::iter::Map<
    std::collections::hash_map::Iter<'a, Lit, usize>,
    fn((&Lit, &usize)) -> (Lit, usize),
>;

impl From<RsHashMap<Lit, usize>> for GeneralizedTotalizer {
    fn from(lits: RsHashMap<Lit, usize>) -> Self {
        Self {
            in_lits: lits.clone(),
            lit_buffer: lits,
            root: Default::default(),
            max_leaf_weight: Default::default(),
            weight_sum: Default::default(),
            n_vars: Default::default(),
            n_clauses: Default::default(),
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
enum Node {
    Leaf {
        /// The input literal to the tree
        lit: Lit,
        /// The weight of the input literal
        weight: usize,
    },
    Internal {
        /// The weighted output literals of this node
        out_lits: BTreeMap<usize, Lit>,
        /// The path length to the leaf furthest away in the subtree
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
    pub fn new_leaf(lit: Lit, weight: usize) -> Node {
        Node::Leaf { lit, weight }
    }

    /// Constructs a new internal node
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

    /// Gets the maximum depth of the subtree rooted in this node
    pub fn depth(&self) -> usize {
        match self {
            Node::Leaf { .. } => 1,
            Node::Internal { depth, .. } => *depth,
        }
    }

    /// Gets the maximum value that the node represents
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
    fn encode_range(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf {
        let range = self.limit_range(range);
        if range.is_empty() {
            return Cnf::new();
        }

        // Reserve vars if needed
        self.reserve_vars_range(range.clone(), var_manager);
        match &*self {
            Node::Leaf { .. } => Cnf::new(),
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
                let mut cnf = Cnf::new();
                // Propagate left value
                for (&left_val, &left_lit) in left_lits.range(range.clone()) {
                    cnf.add_lit_impl_lit(left_lit, *out_lits.get(&left_val).unwrap());
                }
                // Propagate right value
                for (&right_val, &right_lit) in right_lits.range(range.clone()) {
                    cnf.add_lit_impl_lit(right_lit, *out_lits.get(&right_val).unwrap());
                }
                // Propagate sum
                if range.end > 1 {
                    for (&left_val, &left_lit) in left_lits.range(1..range.end - 1) {
                        let right_min = if range.start > left_val {
                            range.start - left_val
                        } else {
                            0
                        };
                        for (&right_val, &right_lit) in
                            right_lits.range(right_min..range.end - left_val)
                        {
                            let sum_val = left_val + right_val;
                            if !range.contains(&sum_val) {
                                continue;
                            }
                            cnf.add_cube_impl_lit(
                                vec![left_lit, right_lit],
                                *out_lits.get(&sum_val).unwrap(),
                            );
                        }
                    }
                }
                cnf
            }
        }
    }

    /// Encodes the output literals from the children to this node in a given
    /// range. Recurses depth first. Always encodes the full requested CNF
    /// encoding.
    pub fn rec_encode(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf {
        let range = self.limit_range(range);
        if range.is_empty() {
            return Cnf::new();
        }

        // Ignore all previous encoding and encode from scratch
        match self {
            Node::Leaf { .. } => Cnf::new(),
            Node::Internal { left, right, .. } => {
                let left_range = Node::compute_required_min_enc(range.clone(), right.max_val());
                let right_range = Node::compute_required_min_enc(range.clone(), left.max_val());
                // Recurse
                let mut cnf = left.rec_encode(left_range, var_manager);
                cnf.extend(right.rec_encode(right_range, var_manager));

                // Encode current node
                let local_cnf = self.encode_range(range.clone(), var_manager);

                self.update_stats(range, local_cnf.n_clauses());
                cnf.join(local_cnf)
            }
        }
    }

    /// Encodes the output literals from the children to this node in a given
    /// range. Recurses depth first. Incrementally only encodes new clauses.
    pub fn rec_encode_change(
        &mut self,
        range: Range<usize>,
        var_manager: &mut dyn ManageVars,
    ) -> Cnf {
        let range = self.limit_range(range);
        if range.is_empty() {
            return Cnf::new();
        }

        match self {
            Node::Leaf { .. } => Cnf::new(),
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
                let mut cnf = left.rec_encode_change(left_range, var_manager);
                cnf.extend(right.rec_encode_change(right_range, var_manager));

                // Encode changes for current node
                let local_cnf = if enc_range.is_empty() {
                    // First time encoding this node
                    self.encode_range(range.clone(), var_manager)
                } else {
                    // Partially encoded
                    let mut local_cnf = Cnf::new();
                    if range.start < enc_range.start {
                        local_cnf
                            .extend(self.encode_range(range.start..enc_range.start, var_manager));
                    };
                    if range.end > enc_range.end {
                        local_cnf.extend(self.encode_range(enc_range.end..range.end, var_manager));
                    };
                    local_cnf
                };

                self.update_stats(range, local_cnf.n_clauses());
                cnf.join(local_cnf)
            }
        }
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
        self.reserve_vars_range(0..max_val + 1, var_manager);
    }

    /// Reserves all variables this node and the lower subtree might need. This
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
        self.reserve_all_vars(var_manager)
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
            pb::{BoundUpper, BoundUpperIncremental},
            EncodeStats, Error,
        },
        instances::{BasicVarManager, ManageVars},
        lit,
        types::{Lit, RsHashMap, Var},
        var,
    };

    #[test]
    fn adder_1() {
        // Child nodes
        let child1 = Node::new_leaf(lit![0], 5);
        let child2 = Node::new_leaf(lit![1], 3);
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::default();
        let cnf = node.encode_range(0..9, &mut var_manager);
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 3),
        };
        assert_eq!(cnf.n_clauses(), 3);
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
        let cnf = node.encode_range(0..7, &mut var_manager);
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 3),
        };
        assert_eq!(cnf.n_clauses(), 5);
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
        let cnf = node.encode_range(4..7, &mut var_manager);
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 2),
        };
        assert_eq!(cnf.n_clauses(), 3);
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
        let cnf = node.encode_range(6..5, &mut var_manager);
        assert_eq!(cnf.n_clauses(), 0);
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
        gte.encode_ub(0..7, &mut var_manager);
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
        let cnf1 = gte1.encode_ub(0..5, &mut var_manager);
        let mut gte2 = GeneralizedTotalizer::default();
        gte2.extend(lits);
        let mut var_manager = BasicVarManager::default();
        let mut cnf2 = gte2.encode_ub(0..3, &mut var_manager);
        cnf2.extend(gte2.encode_ub_change(0..5, &mut var_manager));
        assert_eq!(cnf1.n_clauses(), cnf2.n_clauses());
        assert_eq!(cnf1.n_clauses(), gte1.n_clauses());
        assert_eq!(cnf2.n_clauses(), gte2.n_clauses());
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
        let cnf1 = gte1.encode_ub(0..5, &mut var_manager);
        let mut gte2 = GeneralizedTotalizer::default();
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 10);
        lits.insert(lit![1], 10);
        lits.insert(lit![2], 6);
        lits.insert(lit![3], 6);
        gte2.extend(lits);
        let mut var_manager = BasicVarManager::default();
        let cnf2 = gte2.encode_ub(0..9, &mut var_manager);
        assert_eq!(cnf1.n_clauses(), cnf2.n_clauses());
        assert_eq!(cnf1.n_clauses(), gte1.n_clauses());
        assert_eq!(cnf2.n_clauses(), gte2.n_clauses());
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
        let gte_cnf = gte.encode_ub(3..8, &mut var_manager_gte);
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
        let tot_cnf = card::BoundUpper::encode_ub(&mut tot, 3..8, &mut var_manager_tot);
        println!("{:?}", gte_cnf);
        println!("{:?}", tot_cnf);
        assert_eq!(var_manager_gte.new_var(), var_manager_tot.new_var());
        assert_eq!(gte_cnf.n_clauses(), tot_cnf.n_clauses());
        assert_eq!(gte_cnf.n_clauses(), gte.n_clauses());
        assert_eq!(tot_cnf.n_clauses(), tot.n_clauses());
    }
}
