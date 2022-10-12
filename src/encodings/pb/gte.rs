//! # Generalized Totalizer Encoding
//!
//! Implementation of the binary adder tree generalized totalizer encoding \[1\].
//! The implementation is incremental.
//! The implementation is recursive.
//!
//! ## References
//!
//! - \[1\] Saurabh Joshi and Ruben Martins and Vasco Manquinho: _Generalized Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.

use super::{BoundType, EncodePB, EncodingError, IncEncodePB};
use crate::{
    instances::{ManageVars, CNF},
    types::Lit,
};
use std::{
    cmp,
    collections::{BTreeMap, HashMap},
    ops::Bound,
};

/// Implementation of the binary adder tree generalized totalizer encoding \[1\].
/// The implementation is incremental.
/// The implementation is recursive.
///
/// # References
///
/// - \[1\] Saurabh Joshi and Ruben Martins and Vasco Manquinho: _Generalized Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.
pub struct GeneralizedTotalizer {
    /// Input literals and weights already in the tree
    in_lits: HashMap<Lit, usize>,
    /// Input literals and weights not yet in the tree
    lit_buffer: HashMap<Lit, usize>,
    /// The root of the tree, if constructed
    root: Option<Box<Node>>,
    /// The bound type that the totalizer encodes
    bound_type: BoundType,
    /// Whether or not to reserve all variables when constructing the tree
    reserve_vars: bool,
    /// Maximum weight of a leaf, needed for computing how much more than `max_rhs` to encode
    max_leaf_weight: usize,
    /// Sum of all input weight
    total_weight: usize,
}

impl GeneralizedTotalizer {
    /// Recursively builds the tree data structure. Uses weights out of
    /// `lit_buffer` to initialize leafs.
    fn build_tree(lits: &[(Lit, usize)]) -> Node {
        assert_ne!(lits.len(), 0);

        if lits.len() == 1 {
            return Node::new_leaf(lits[0].0, lits[0].1);
        };

        let split = lits.len() / 2;
        let left = GeneralizedTotalizer::build_tree(&lits[..split]);
        let right = GeneralizedTotalizer::build_tree(&lits[split..]);

        Node::new_internal(left, right)
    }

    /// Extends the tree at the root node with added literals of maximum weight `max_weight`
    fn extend_tree<VM: ManageVars>(&mut self, max_weight: usize, var_manager: &mut VM) {
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
                        Some((
                            if self.bound_type == BoundType::UB {
                                l
                            } else {
                                // Negate literals for lower bounding
                                !l
                            },
                            w,
                        ))
                    } else {
                        None
                    }
                })
                .collect();
            if !new_lits.is_empty() {
                // Add nodes in sorted fashion to minimize clauses
                new_lits[..].sort_by(|(_, w1), (_, w2)| w1.cmp(w2));
                let mut subtree = GeneralizedTotalizer::build_tree(&new_lits[..]);
                if self.reserve_vars {
                    subtree.reserve_all_vars_rec(var_manager, &self.bound_type);
                }
                self.root = match self.root.take() {
                    None => Some(Box::new(subtree)),
                    Some(old_root) => {
                        let mut new_root = Node::new_internal(*old_root, subtree);
                        if self.reserve_vars {
                            new_root.reserve_all_vars(var_manager, &self.bound_type)
                        };
                        Some(Box::new(new_root))
                    }
                };
                // Update total weights in tree
                self.lit_buffer.iter_mut().for_each(|(l, w)| {
                    if *w <= max_weight {
                        match self.in_lits.get(l) {
                            Some(old_w) => self.in_lits.insert(*l, *old_w + *w),
                            None => self.in_lits.insert(*l, *w),
                        };
                        *w = 0;
                    }
                });
                self.lit_buffer.retain(|_, v| *v != 0);
            }
        }
    }

    /// Converts an outside lower bound to an internal upper bound on the actual
    /// tree. This method should only ever be called if the GTE is in lower
    /// bounding mode. Might return an [`EncodingError::Unsat`] error.
    fn convert_lb_ub(&self, bound: usize) -> Result<usize, EncodingError> {
        assert_eq!(self.bound_type, BoundType::LB);
        if self.total_weight > bound {
            Ok(self.total_weight - bound)
        } else {
            Err(EncodingError::Unsat)
        }
    }

    /// Enforce an upper bound on the internal tree.
    fn enforce_tree_ub(&self, ub: usize) -> Result<Vec<Lit>, EncodingError> {
        match &self.root {
            None => {
                assert!(self.in_lits.is_empty());
                Ok(vec![])
            }
            Some(root_node) => match &**root_node {
                // Assumes that literal is already enforced from wrapper function if it's weight is more than `ub`
                Node::Leaf { .. } => Ok(vec![]),
                Node::Internal {
                    out_lits,
                    min_max_enc,
                    max_val,
                    ..
                } => {
                    if ub >= *max_val {
                        Ok(vec![])
                    } else if let Some((min_enc, max_enc)) = *min_max_enc {
                        if max_enc < cmp::min(ub + self.max_leaf_weight, *max_val)
                            || min_enc > ub + 1
                        {
                            Err(EncodingError::NotEncoded)
                        } else {
                            Ok(out_lits
                                .range((
                                    Bound::Excluded(ub),
                                    Bound::Included(ub + self.max_leaf_weight),
                                ))
                                .map(|(_, &l)| !l)
                                .collect())
                        }
                    } else {
                        Err(EncodingError::NotEncoded)
                    }
                }
            },
        }
    }

    /// Gets the maximum depth of the tree
    pub fn get_depth(&mut self) -> usize {
        match &self.root {
            None => 0,
            Some(root_node) => root_node.get_depth(),
        }
    }
}

impl EncodePB for GeneralizedTotalizer {
    fn new(bound_type: BoundType) -> Result<Self, EncodingError> {
        match bound_type {
            BoundType::BOTH => Err(EncodingError::NoTypeSupport),
            _ => Ok(GeneralizedTotalizer {
                in_lits: HashMap::new(),
                lit_buffer: HashMap::new(),
                root: None,
                bound_type,
                reserve_vars: false,
                max_leaf_weight: 0,
                total_weight: 0,
            }),
        }
    }

    fn add(&mut self, lits: HashMap<Lit, usize>) {
        lits.iter().for_each(|(l, w)| {
            self.total_weight += w;
            match self.lit_buffer.get(l) {
                Some(old_w) => self.lit_buffer.insert(*l, *old_w + *w),
                None => self.lit_buffer.insert(*l, *w),
            };
        });
    }

    fn encode<VM: ManageVars>(
        &mut self,
        min_rhs: usize,
        max_rhs: usize,
        var_manager: &mut VM,
    ) -> Result<CNF, EncodingError> {
        if min_rhs > max_rhs {
            return Err(EncodingError::InvalidBounds);
        };
        Ok(if self.bound_type == BoundType::UB {
            self.extend_tree(max_rhs, var_manager);
            match &mut self.root {
                None => CNF::new(),
                Some(root) => root.encode_rec(
                    min_rhs + 1,
                    max_rhs + self.max_leaf_weight,
                    var_manager,
                    &BoundType::UB,
                ),
            }
        } else {
            let int_min_rhs = self.convert_lb_ub(max_rhs).unwrap_or(0);
            let int_max_rhs = self.convert_lb_ub(min_rhs).unwrap_or(0);
            self.extend_tree(int_max_rhs, var_manager);
            match &mut self.root {
                None => CNF::new(),
                Some(root) => root.encode_rec(
                    int_min_rhs + 1,
                    int_max_rhs + self.max_leaf_weight,
                    var_manager,
                    &BoundType::UB,
                ),
            }
        })
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EncodingError> {
        match self.bound_type {
            BoundType::LB => Err(EncodingError::NoObjectSupport),
            _ => {
                let mut assumps = vec![];
                // Assume literals that have higher weight than `ub`
                assumps.reserve(self.lit_buffer.len());
                self.lit_buffer
                    .iter()
                    .fold(Ok(()), |res, (&l, &w)| match res {
                        Err(err) => Err(err),
                        Ok(_) => {
                            if w <= ub {
                                Err(EncodingError::NotEncoded)
                            } else {
                                assumps.push(!l);
                                Ok(())
                            }
                        }
                    })?;
                self.in_lits.iter().for_each(|(&l, &w)| {
                    if w > ub {
                        assumps.push(!l);
                    }
                });
                assumps.extend(self.enforce_tree_ub(ub)?);
                Ok(assumps)
            }
        }
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EncodingError> {
        match self.bound_type {
            BoundType::UB => Err(EncodingError::NoObjectSupport),
            _ => {
                let ub = self.convert_lb_ub(lb)?;
                let mut assumps = vec![];
                // Assume literals that have higher weight than `ub`
                assumps.reserve(self.lit_buffer.len());
                self.lit_buffer
                    .iter()
                    .fold(Ok(()), |res, (&l, &w)| match res {
                        Err(err) => Err(err),
                        Ok(_) => {
                            if w <= ub {
                                Err(EncodingError::NotEncoded)
                            } else {
                                assumps.push(l);
                                Ok(())
                            }
                        }
                    })?;
                self.in_lits.iter().for_each(|(&l, &w)| {
                    if w > ub {
                        assumps.push(l);
                    }
                });
                assumps.extend(self.enforce_tree_ub(ub)?);
                Ok(assumps)
            }
        }
    }
}

impl IncEncodePB for GeneralizedTotalizer {
    fn new_reserving(bound_type: BoundType) -> Result<Self, EncodingError> {
        match bound_type {
            BoundType::BOTH => Err(EncodingError::NoTypeSupport),
            _ => Ok(GeneralizedTotalizer {
                in_lits: HashMap::new(),
                lit_buffer: HashMap::new(),
                root: None,
                bound_type,
                reserve_vars: true,
                max_leaf_weight: 0,
                total_weight: 0,
            }),
        }
    }

    fn encode_change<VM: ManageVars>(
        &mut self,
        min_rhs: usize,
        max_rhs: usize,
        var_manager: &mut VM,
    ) -> Result<CNF, EncodingError> {
        if min_rhs > max_rhs {
            return Err(EncodingError::InvalidBounds);
        };
        Ok(if self.bound_type == BoundType::UB {
            self.extend_tree(max_rhs, var_manager);
            match &mut self.root {
                None => CNF::new(),
                Some(root) => root.encode_change_rec(
                    min_rhs + 1,
                    max_rhs + self.max_leaf_weight,
                    var_manager,
                    &BoundType::UB,
                ),
            }
        } else {
            let int_min_rhs = self.convert_lb_ub(max_rhs).unwrap_or(0);
            let int_max_rhs = self.convert_lb_ub(min_rhs).unwrap_or(0);
            self.extend_tree(int_max_rhs, var_manager);
            match &mut self.root {
                None => CNF::new(),
                Some(root) => root.encode_change_rec(
                    int_min_rhs + 1,
                    int_max_rhs + self.max_leaf_weight,
                    var_manager,
                    &BoundType::UB,
                ),
            }
        })
    }
}

/// The Totalzier nodes are _only_ for upper bounding. Lower bounding in the GTE
/// is possible by negating input literals. This conversion entirely happens in
/// the [`GeneralizedTotalizer`] struct. Equally, bounds given on the encode
/// methods for this type strictly refer to the output literals that should be
/// encoded. Converting right hand sides to required encoded output literals
/// happens in the [`GeneralizedTotalizer`] struct.
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
        /// The minimum and maximum output weight that is encoded by this node
        min_max_enc: Option<(usize, usize)>,
        /// The left child
        left: Box<Node>,
        /// The right child
        right: Box<Node>,
    },
}

impl Node {
    /// Constructs a new leaf node
    fn new_leaf(lit: Lit, weight: usize) -> Node {
        Node::Leaf { lit, weight }
    }

    /// Constructs a new internal node
    fn new_internal(left: Node, right: Node) -> Node {
        let left_depth = match left {
            Node::Leaf { .. } => 1,
            Node::Internal { depth, .. } => depth,
        };
        let right_depth = match right {
            Node::Leaf { .. } => 1,
            Node::Internal { depth, .. } => depth,
        };
        Node::Internal {
            out_lits: BTreeMap::new(),
            depth: if left_depth > right_depth {
                left_depth + 1
            } else {
                right_depth + 1
            },
            n_clauses: 0,
            min_max_enc: None,
            max_val: match left {
                Node::Leaf { weight, .. } => weight,
                Node::Internal { max_val, .. } => max_val,
            } + match right {
                Node::Leaf { weight, .. } => weight,
                Node::Internal { max_val, .. } => max_val,
            },
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Gets the maximum depth of the subtree rooted in this node
    fn get_depth(&self) -> usize {
        match self {
            Node::Leaf { .. } => 1,
            Node::Internal { depth, .. } => *depth,
        }
    }

    fn get_child_lit_maps<'a>(
        left: &'a Box<Node>,
        right: &'a Box<Node>,
        tmp_map_1: &'a mut BTreeMap<usize, Lit>,
        tmp_map_2: &'a mut BTreeMap<usize, Lit>,
    ) -> (&'a BTreeMap<usize, Lit>, &'a BTreeMap<usize, Lit>) {
        (
            match &**left {
                Node::Leaf { lit, weight } => {
                    tmp_map_1.insert(*weight, *lit);
                    tmp_map_1
                }
                Node::Internal { out_lits, .. } => out_lits,
            },
            match &**right {
                Node::Leaf { lit, weight } => {
                    tmp_map_2.insert(*weight, *lit);
                    tmp_map_2
                }
                Node::Internal { out_lits, .. } => out_lits,
            },
        )
    }

    /// Encodes the output literals for this node from values `min_enc` to
    /// `max_enc`. This method only produces the encoding and does _not_ change
    /// any of the stats of the node.
    fn encode_from_till<VM: ManageVars>(
        &mut self,
        min_enc: usize,
        max_enc: usize,
        var_manager: &mut VM,
        bound_type: &BoundType,
    ) -> CNF {
        assert_eq!(*bound_type, BoundType::UB);
        if min_enc > max_enc {
            return CNF::new();
        };
        // Reserve vars if needed
        self.reserve_vars_till(min_enc, max_enc, var_manager, bound_type);
        match &*self {
            Node::Leaf { .. } => return CNF::new(),
            Node::Internal {
                out_lits,
                max_val,
                left,
                right,
                ..
            } => {
                let mut left_tmp_map = BTreeMap::new();
                let mut right_tmp_map = BTreeMap::new();
                let (left_lits, right_lits) =
                    Node::get_child_lit_maps(left, right, &mut left_tmp_map, &mut right_tmp_map);
                if min_enc > *max_val {
                    return CNF::new();
                };
                // Encode adder for current node
                let mut cnf = CNF::new();
                // Propagate left value
                for (&left_val, &left_lit) in
                    left_lits.range((Bound::Included(min_enc), Bound::Included(max_enc)))
                {
                    cnf.add_lit_impl_lit(left_lit, *out_lits.get(&left_val).unwrap());
                }
                // Propagate right value
                for (&right_val, &right_lit) in
                    right_lits.range((Bound::Included(min_enc), Bound::Included(max_enc)))
                {
                    cnf.add_lit_impl_lit(right_lit, *out_lits.get(&right_val).unwrap());
                }
                // Propagate sum
                for (&left_val, &left_lit) in
                    left_lits.range((Bound::Excluded(0), Bound::Excluded(max_enc)))
                {
                    let right_min = if min_enc > left_val {
                        min_enc - left_val
                    } else {
                        0
                    };
                    for (&right_val, &right_lit) in right_lits.range((
                        Bound::Included(right_min),
                        Bound::Included(max_enc - left_val),
                    )) {
                        let sum_val = left_val + right_val;
                        if sum_val > max_enc || sum_val < min_enc {
                            continue;
                        }
                        cnf.add_cube_impl_lit(
                            vec![left_lit, right_lit],
                            *out_lits.get(&sum_val).unwrap(),
                        );
                    }
                }
                cnf
            }
        }
    }

    /// Encodes the output literals from the children to this node from values
    /// `min_enc` to `max_enc`. Recurses depth first. Always encodes the full
    /// requested CNF encoding.
    fn encode_rec<VM: ManageVars>(
        &mut self,
        min_enc: usize,
        max_enc: usize,
        var_manager: &mut VM,
        bound_type: &BoundType,
    ) -> CNF {
        // Ignore all previous encoding and encode from scratch
        let mut cnf = match self {
            Node::Leaf { .. } => return CNF::new(),
            Node::Internal { left, right, .. } => {
                let left_min_enc = Node::compute_required_min_enc(min_enc, max_enc, right);
                let right_min_enc = Node::compute_required_min_enc(min_enc, max_enc, left);
                // Recurse
                let mut cnf = left.encode_rec(left_min_enc, max_enc, var_manager, bound_type);
                cnf.extend(right.encode_rec(right_min_enc, max_enc, var_manager, bound_type));
                cnf
            }
        };
        let local_cnf = self.encode_from_till(min_enc, max_enc, var_manager, bound_type);
        match self {
            Node::Leaf { .. } => local_cnf,
            Node::Internal {
                min_max_enc,
                max_val,
                n_clauses,
                ..
            } => {
                // Update stats
                *min_max_enc = Some((min_enc, cmp::min(*max_val, max_enc)));
                *n_clauses += local_cnf.n_clauses();
                cnf.extend(local_cnf);
                cnf
            }
        }
    }

    /// Encodes the output literals from the children to this node from values
    /// `min_enc` to `max_enc`. Recurses depth first. Incrementally only encodes
    /// new clauses.
    fn encode_change_rec<VM: ManageVars>(
        &mut self,
        min_enc: usize,
        max_enc: usize,
        var_manager: &mut VM,
        bound_type: &BoundType,
    ) -> CNF {
        let (mut cnf, min_max_already_encoded) = match self {
            Node::Leaf { .. } => return CNF::new(),
            Node::Internal {
                left,
                right,
                min_max_enc,
                ..
            } => {
                let left_min_enc = Node::compute_required_min_enc(min_enc, max_enc, right);
                let right_min_enc = Node::compute_required_min_enc(min_enc, max_enc, left);
                // Recurse
                let mut cnf =
                    left.encode_change_rec(left_min_enc, max_enc, var_manager, bound_type);
                cnf.extend(right.encode_change_rec(
                    right_min_enc,
                    max_enc,
                    var_manager,
                    bound_type,
                ));
                (cnf, *min_max_enc)
            }
        };
        // Encode changes for current node
        let local_cnf = match min_max_already_encoded {
            None => {
                // First time encoding this node
                self.encode_from_till(min_enc, max_enc, var_manager, bound_type)
            }
            Some((old_min_enc, old_max_enc)) => {
                // Part already encoded
                let mut local_cnf = CNF::new();
                if min_enc < old_min_enc {
                    local_cnf.extend(self.encode_from_till(
                        min_enc,
                        old_min_enc - 1,
                        var_manager,
                        bound_type,
                    ));
                };
                if max_enc > old_max_enc {
                    local_cnf.extend(self.encode_from_till(
                        old_max_enc + 1,
                        max_enc,
                        var_manager,
                        bound_type,
                    ));
                };
                local_cnf
            }
        };
        match self {
            Node::Leaf { .. } => local_cnf,
            Node::Internal {
                min_max_enc,
                max_val,
                n_clauses,
                ..
            } => {
                // Update stats
                *n_clauses += local_cnf.n_clauses();
                *min_max_enc = if let Some((old_min_enc, old_max_enc)) = *min_max_enc {
                    Some((
                        cmp::min(min_enc, old_min_enc),
                        cmp::min(*max_val, cmp::max(max_enc, old_max_enc)),
                    ))
                } else {
                    Some((min_enc, cmp::min(max_enc, *max_val)))
                };
                cnf.extend(local_cnf);
                cnf
            }
        }
    }

    /// Reserves variables this node might need up to `max_res`.
    fn reserve_vars_till<VM: ManageVars>(
        &mut self,
        min_enc: usize,
        max_enc: usize,
        var_manager: &mut VM,
        bound_type: &BoundType,
    ) {
        assert_eq!(*bound_type, BoundType::UB);
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
                let (left_lits, right_lits) =
                    Node::get_child_lit_maps(left, right, &mut left_tmp_map, &mut right_tmp_map);
                // Reserve vars
                for (&left_val, _) in
                    left_lits.range((Bound::Included(min_enc), Bound::Included(max_enc)))
                {
                    if !out_lits.contains_key(&left_val) {
                        out_lits.insert(left_val, var_manager.next_free().pos_lit());
                    }
                }
                for (&right_val, _) in
                    right_lits.range((Bound::Included(min_enc), Bound::Included(max_enc)))
                {
                    if !out_lits.contains_key(&right_val) {
                        out_lits.insert(right_val, var_manager.next_free().pos_lit());
                    }
                }
                for (&left_val, _) in
                    left_lits.range((Bound::Excluded(0), Bound::Excluded(max_enc)))
                {
                    let right_min = if min_enc > left_val {
                        min_enc - left_val
                    } else {
                        0
                    };
                    for (&right_val, _) in right_lits.range((
                        Bound::Included(right_min),
                        Bound::Included(max_enc - left_val),
                    )) {
                        if left_val + right_val > max_enc || left_val + right_val < min_enc {
                            continue;
                        }
                        if !out_lits.contains_key(&(left_val + right_val)) {
                            out_lits
                                .insert(left_val + right_val, var_manager.next_free().pos_lit());
                        }
                    }
                }
            }
        }
    }

    /// Reserves all variables this node might need. This is used if variables
    /// in the totalizer should have consecutive indices.
    fn reserve_all_vars<VM: ManageVars>(&mut self, var_manager: &mut VM, bound_type: &BoundType) {
        let max_val = match self {
            Node::Leaf { .. } => return,
            Node::Internal { max_val, .. } => *max_val,
        };
        self.reserve_vars_till(0, max_val, var_manager, bound_type);
    }

    /// Reserves all variables this node and the lower subtree might need. This
    /// is used if variables in the totalizer should have consecutive indices.
    fn reserve_all_vars_rec<VM: ManageVars>(
        &mut self,
        var_manager: &mut VM,
        bound_type: &BoundType,
    ) {
        match self {
            Node::Leaf { .. } => return,
            Node::Internal { left, right, .. } => {
                // Recursion
                left.reserve_all_vars_rec(var_manager, bound_type);
                right.reserve_all_vars_rec(var_manager, bound_type);
            }
        };
        self.reserve_all_vars(var_manager, bound_type)
    }

    /// Computes the required `min_enc` for a node given a requested `min_enc`
    /// and `max_enc` of the parent and its sibling.
    fn compute_required_min_enc(
        min_enc_requested: usize,
        max_enc_requested: usize,
        sibling: &Box<Node>,
    ) -> usize {
        match **sibling {
            Node::Leaf { .. } => {
                if min_enc_requested > 2 {
                    min_enc_requested - 1
                } else {
                    1
                }
            }
            Node::Internal { max_val, .. } => {
                if max_enc_requested < max_val {
                    if min_enc_requested > max_enc_requested {
                        min_enc_requested - max_enc_requested
                    } else {
                        1
                    }
                } else if min_enc_requested > max_val {
                    min_enc_requested - max_val
                } else {
                    1
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};

    use super::{GeneralizedTotalizer, Node};
    use crate::{
        encodings::{
            card::{EncodeCard, Totalizer},
            pb::{EncodePB, IncEncodePB},
            BoundType, EncodingError,
        },
        instances::{BasicVarManager, ManageVars},
        lit,
        types::{Lit, Var},
        var,
    };

    #[test]
    fn adder_1() {
        // Child nodes
        let child1 = Node::new_leaf(lit![0], 5);
        let child2 = Node::new_leaf(lit![1], 3);
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let cnf = node.encode_from_till(0, 8, &mut var_manager, &BoundType::UB);
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
            max_val: 2,
            min_max_enc: Some((0, 8)),
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
            max_val: 2,
            min_max_enc: Some((0, 8)),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0], 5)),
            right: Box::new(Node::new_leaf(lit![0], 3)),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let cnf = node.encode_from_till(0, 6, &mut var_manager, &BoundType::UB);
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
            max_val: 2,
            min_max_enc: Some((0, 8)),
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
            max_val: 2,
            min_max_enc: Some((0, 8)),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0], 5)),
            right: Box::new(Node::new_leaf(lit![0], 3)),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let cnf = node.encode_from_till(4, 6, &mut var_manager, &BoundType::UB);
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
            max_val: 2,
            min_max_enc: Some((0, 8)),
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
            max_val: 2,
            min_max_enc: Some((0, 8)),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0], 5)),
            right: Box::new(Node::new_leaf(lit![0], 3)),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let cnf = node.encode_from_till(6, 4, &mut var_manager, &BoundType::UB);
        assert_eq!(cnf.n_clauses(), 0);
    }

    #[test]
    fn gte_functions() {
        let mut gte = GeneralizedTotalizer::new(BoundType::UB).unwrap();
        let mut lits = HashMap::new();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 5);
        lits.insert(lit![2], 3);
        lits.insert(lit![3], 3);
        gte.add(lits);
        assert_eq!(gte.enforce_ub(4), Err(EncodingError::NotEncoded));
        assert_eq!(gte.enforce_lb(4), Err(EncodingError::NoObjectSupport));
        let mut var_manager = BasicVarManager::new();
        gte.encode(0, 6, &mut var_manager).unwrap();
        assert_eq!(gte.get_depth(), 3);
    }

    #[test]
    fn gte_incremental_building_ub() {
        let mut gte1 = GeneralizedTotalizer::new(BoundType::UB).unwrap();
        let mut lits = HashMap::new();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 5);
        lits.insert(lit![2], 3);
        lits.insert(lit![3], 3);
        gte1.add(lits.clone());
        let mut var_manager = BasicVarManager::new();
        let cnf1 = gte1.encode(0, 4, &mut var_manager).unwrap();
        let mut gte2 = GeneralizedTotalizer::new(BoundType::UB).unwrap();
        gte2.add(lits);
        let mut var_manager = BasicVarManager::new();
        let mut cnf2 = gte2.encode(0, 2, &mut var_manager).unwrap();
        cnf2.extend(gte2.encode_change(0, 4, &mut var_manager).unwrap());
        assert_eq!(cnf1.n_clauses(), cnf2.n_clauses());
    }

    #[test]
    fn gte_incremental_building_lb() {
        let mut gte1 = GeneralizedTotalizer::new(BoundType::LB).unwrap();
        let mut lits = HashMap::new();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 5);
        lits.insert(lit![2], 3);
        lits.insert(lit![3], 3);
        gte1.add(lits.clone());
        let mut var_manager = BasicVarManager::new();
        var_manager.increase_next_free(var![4]);
        let cnf1 = gte1.encode(0, 4, &mut var_manager.clone()).unwrap();
        let mut gte2 = GeneralizedTotalizer::new(BoundType::LB).unwrap();
        gte2.add(lits);
        let mut cnf2 = gte2.encode(2, 4, &mut var_manager).unwrap();
        cnf2.extend(gte2.encode_change(0, 4, &mut var_manager).unwrap());
        assert_eq!(cnf1.n_clauses(), cnf2.n_clauses());
    }

    #[test]
    fn gte_multiplication() {
        let mut gte1 = GeneralizedTotalizer::new(BoundType::UB).unwrap();
        let mut lits = HashMap::new();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 5);
        lits.insert(lit![2], 3);
        lits.insert(lit![3], 3);
        gte1.add(lits);
        let mut var_manager = BasicVarManager::new();
        let cnf1 = gte1.encode(0, 4, &mut var_manager).unwrap();
        let mut gte2 = GeneralizedTotalizer::new(BoundType::UB).unwrap();
        let mut lits = HashMap::new();
        lits.insert(lit![0], 10);
        lits.insert(lit![1], 10);
        lits.insert(lit![2], 6);
        lits.insert(lit![3], 6);
        gte2.add(lits);
        let mut var_manager = BasicVarManager::new();
        let cnf2 = gte2.encode(0, 8, &mut var_manager).unwrap();
        assert_eq!(cnf1.n_clauses(), cnf2.n_clauses());
    }

    #[test]
    fn invalid_useage() {
        let mut gte = GeneralizedTotalizer::new(BoundType::LB).unwrap();
        let mut lits = HashMap::new();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 3);
        gte.add(lits);
        assert_eq!(gte.enforce_ub(1), Err(EncodingError::NoObjectSupport));
        let mut gte = GeneralizedTotalizer::new(BoundType::UB).unwrap();
        let mut lits = HashMap::new();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 3);
        gte.add(lits);
        assert_eq!(gte.enforce_lb(1), Err(EncodingError::NoObjectSupport));
        let mut var_manager = BasicVarManager::new();
        assert_eq!(
            gte.encode(5, 4, &mut var_manager),
            Err(EncodingError::InvalidBounds)
        );
        match GeneralizedTotalizer::new(BoundType::BOTH) {
            Ok(_) => panic!(),
            Err(err) => assert_eq!(err, EncodingError::NoTypeSupport),
        };
    }

    #[test]
    fn gte_equals_tot() {
        let mut var_manager_gte = BasicVarManager::new();
        var_manager_gte.increase_next_free(var![7]);
        let mut var_manager_tot = var_manager_gte.clone();
        // Set up GTE
        let mut gte = GeneralizedTotalizer::new(BoundType::UB).unwrap();
        let mut lits = HashMap::new();
        lits.insert(lit![0], 1);
        lits.insert(lit![1], 1);
        lits.insert(lit![2], 1);
        lits.insert(lit![3], 1);
        lits.insert(lit![4], 1);
        lits.insert(lit![5], 1);
        lits.insert(lit![6], 1);
        gte.add(lits);
        let gte_cnf = gte.encode(3, 7, &mut var_manager_gte).unwrap();
        // Set up Tot
        let mut tot = Totalizer::new(BoundType::UB).unwrap();
        tot.add(vec![
            lit![0],
            lit![1],
            lit![2],
            lit![3],
            lit![4],
            lit![5],
            lit![6],
        ]);
        let tot_cnf = tot.encode(3, 7, &mut var_manager_tot).unwrap();
        println!("{:?}", gte_cnf);
        println!("{:?}", tot_cnf);
        assert_eq!(var_manager_gte.next_free(), var_manager_tot.next_free());
        assert_eq!(gte_cnf.n_clauses(), tot_cnf.n_clauses());
    }
}
