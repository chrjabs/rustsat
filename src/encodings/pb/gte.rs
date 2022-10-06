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

    /// Extends the tree at the root node with added literals
    fn extend_tree<VM: ManageVars>(&mut self, var_manager: &mut VM) {
        if !self.lit_buffer.is_empty() {
            let new_lits: Vec<(Lit, usize)> =
                self.lit_buffer.iter().map(|(&l, &w)| (l, w)).collect();
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
            self.lit_buffer.iter().for_each(|(l, w)| {
                match self.in_lits.get(l) {
                    Some(old_w) => self.in_lits.insert(*l, *old_w + *w),
                    None => self.in_lits.insert(*l, *w),
                };
            });
            self.lit_buffer.clear();
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
        Ok(GeneralizedTotalizer {
            in_lits: HashMap::new(),
            lit_buffer: HashMap::new(),
            root: None,
            bound_type,
            reserve_vars: false,
        })
    }

    fn add(&mut self, lits: HashMap<Lit, usize>) {
        lits.iter().for_each(|(l, w)| {
            match self.lit_buffer.get(l) {
                Some(old_w) => self.lit_buffer.insert(*l, *old_w + *w),
                None => self.lit_buffer.insert(*l, *w),
            };
        });
    }

    fn encode<VM: ManageVars>(&mut self, max_rhs: usize, var_manager: &mut VM) -> CNF {
        self.extend_tree(var_manager);
        match &mut self.root {
            None => CNF::new(),
            Some(root) => root.encode_rec(max_rhs, var_manager, &self.bound_type),
        }
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EncodingError> {
        match self.bound_type {
            BoundType::LB => Err(EncodingError::NoObjectSupport),
            _ => {
                if !self.lit_buffer.is_empty() {
                    return Err(EncodingError::NotEncoded);
                };
                match &self.root {
                    None => Err(EncodingError::NotEncoded),
                    Some(root_node) => match &**root_node {
                        Node::Leaf { .. } => todo!(),
                        Node::Internal {
                            max_rhs, max_val, ..
                        } => {
                            if ub >= *max_val {
                                Ok(vec![])
                            } else if *max_rhs < ub {
                                Err(EncodingError::NotEncoded)
                            } else {
                                todo!()
                            }
                        }
                    },
                }
            }
        }
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EncodingError> {
        match self.bound_type {
            BoundType::UB => Err(EncodingError::NoObjectSupport),
            _ => {
                if !self.lit_buffer.is_empty() {
                    return Err(EncodingError::NotEncoded);
                };
                if lb >= self.in_lits.len() {
                    return Err(EncodingError::Unsat);
                };
                match &self.root {
                    None => Err(EncodingError::NotEncoded),
                    Some(root_node) => match &**root_node {
                        Node::Leaf { .. } => todo!(),
                        Node::Internal {
                            max_rhs, max_val, ..
                        } => {
                            if lb > *max_val {
                                Err(EncodingError::Unsat)
                            } else if *max_rhs < lb {
                                Err(EncodingError::NotEncoded)
                            } else {
                                todo!()
                            }
                        }
                    },
                }
            }
        }
    }
}

impl IncEncodePB for GeneralizedTotalizer {
    fn new_reserving(bound_type: BoundType) -> Result<Self, EncodingError> {
        Ok(GeneralizedTotalizer {
            in_lits: HashMap::new(),
            lit_buffer: HashMap::new(),
            root: None,
            bound_type,
            reserve_vars: true,
        })
    }

    fn encode_change<VM: ManageVars>(&mut self, max_rhs: usize, var_manager: &mut VM) -> CNF {
        self.extend_tree(var_manager);
        match &mut self.root {
            None => CNF::new(),
            Some(root) => root.encode_change_rec(max_rhs, var_manager, &self.bound_type),
        }
    }
}

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
        /// The maximum right hand side encoded by this node
        max_rhs: usize,
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
            max_rhs: 0,
            max_val: match left {
                Node::Leaf { .. } => 1,
                Node::Internal { max_val, .. } => max_val,
            } + match right {
                Node::Leaf { .. } => 1,
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

    /// Encodes the adder for this node from values `min_enc` to `max_enc`.
    /// This method only produces the encoding and does _not_ change any of the stats of the node.
    fn encode_from_till<VM: ManageVars>(
        &mut self,
        min_rhs: usize,
        max_rhs: usize,
        var_manager: &mut VM,
        bound_type: &BoundType,
    ) -> CNF {
        assert_eq!(*bound_type, BoundType::UB);
        // Reserve vars if needed
        self.reserve_vars_till(max_rhs, var_manager, bound_type);
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
                if min_rhs > *max_val {
                    return CNF::new();
                };
                // Encode adder for current node
                let mut cnf = CNF::new();
                // Propagate left value
                for (&left_val, &left_lit) in
                    left_lits.range((Bound::Included(min_rhs), Bound::Included(max_rhs)))
                {
                    cnf.add_lit_impl_lit(left_lit, *out_lits.get(&left_val).unwrap());
                }
                // Propagate right value
                for (&right_val, &right_lit) in
                    right_lits.range((Bound::Included(min_rhs), Bound::Included(max_rhs)))
                {
                    cnf.add_lit_impl_lit(right_lit, *out_lits.get(&right_val).unwrap());
                }
                // Propagate sum
                for (&left_val, &left_lit) in
                    left_lits.range((Bound::Excluded(0), Bound::Included(max_rhs)))
                {
                    for (&right_val, &right_lit) in right_lits.range((
                        Bound::Included(min_rhs - left_val),
                        Bound::Included(max_rhs - left_val),
                    )) {
                        let sum_val = left_val + right_val;
                        if sum_val > max_rhs || sum_val < min_rhs {
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

    /// Encodes the adder from the children to this node up to a given maximum
    /// right hand side. Recurses depth first. Returns  the number of newly
    /// added clauses. Always encodes the full totalizer.
    fn encode_rec<VM: ManageVars>(
        &mut self,
        max_enc: usize,
        var_manager: &mut VM,
        bound_type: &BoundType,
    ) -> CNF {
        let mut cnf = match self {
            Node::Leaf { .. } => CNF::new(),
            Node::Internal { left, right, .. } => {
                // Ignore all previous encoding and encode from scratch
                // Recurse
                let mut cnf = left.encode_rec(max_enc, var_manager, bound_type);
                cnf.extend(right.encode_rec(max_enc, var_manager, bound_type));
                cnf
            }
        };
        let local_cnf = self.encode_from_till(0, max_enc, var_manager, bound_type);
        match self {
            Node::Leaf { .. } => local_cnf,
            Node::Internal {
                max_rhs,
                max_val,
                n_clauses,
                ..
            } => {
                // Update stats
                *max_rhs = if max_enc < *max_val {
                    max_enc
                } else {
                    *max_val
                };
                *n_clauses += local_cnf.n_clauses();
                cnf.extend(local_cnf);
                cnf
            }
        }
    }

    /// Encodes the adder from the children to this node up to a given maximum
    /// right hand side. Recurses depth first. Returns the new `next_idx` and
    /// the number of newly added clauses. Incrementally only encodes new
    /// clauses.
    fn encode_change_rec<VM: ManageVars>(
        &mut self,
        max_enc: usize,
        var_manager: &mut VM,
        bound_type: &BoundType,
    ) -> CNF {
        let (mut cnf, min_enc) = match self {
            Node::Leaf { .. } => (CNF::new(), 0),
            Node::Internal {
                left,
                right,
                max_rhs,
                ..
            } => {
                // Ignore all previous encoding and encode from scratch
                // Recurse
                let mut cnf = left.encode_change_rec(max_enc, var_manager, bound_type);
                cnf.extend(right.encode_change_rec(max_enc, var_manager, bound_type));
                (cnf, *max_rhs)
            }
        };
        // Encode adder for current node
        let local_cnf = self.encode_from_till(min_enc, max_enc, var_manager, bound_type);
        match self {
            Node::Leaf { .. } => local_cnf,
            Node::Internal {
                max_rhs,
                max_val,
                n_clauses,
                ..
            } => {
                // Update stats
                *n_clauses += local_cnf.n_clauses();
                *max_rhs = if max_enc < *max_val {
                    max_enc
                } else {
                    *max_val
                };
                cnf.extend(local_cnf);
                cnf
            }
        }
    }

    /// Reserves variables this node might need up to `max_res`.
    fn reserve_vars_till<VM: ManageVars>(
        &mut self,
        max_rhs: usize,
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
                    left_lits.range((Bound::Excluded(0), Bound::Included(max_rhs)))
                {
                    if !out_lits.contains_key(&left_val) {
                        out_lits.insert(left_val, var_manager.next_free().pos_lit());
                    }
                }
                for (&right_val, _) in
                    right_lits.range((Bound::Excluded(0), Bound::Included(max_rhs)))
                {
                    if !out_lits.contains_key(&right_val) {
                        out_lits.insert(right_val, var_manager.next_free().pos_lit());
                    }
                }
                for (&left_val, _) in
                    left_lits.range((Bound::Excluded(0), Bound::Included(max_rhs)))
                {
                    for (&right_val, _) in
                        right_lits.range((Bound::Excluded(0), Bound::Included(max_rhs - left_val)))
                    {
                        if left_val + right_val > max_rhs {
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
        let max_enc = match self {
            Node::Leaf { .. } => 0,
            Node::Internal { max_val, .. } => *max_val,
        };
        self.reserve_vars_till(max_enc, var_manager, bound_type);
    }

    /// Reserves all variables this node and the lower subtree might need. This
    /// is used if variables in the totalizer should have consecutive indices.
    fn reserve_all_vars_rec<VM: ManageVars>(
        &mut self,
        var_manager: &mut VM,
        bound_type: &BoundType,
    ) {
        match self {
            Node::Leaf { .. } => (),
            Node::Internal { left, right, .. } => {
                // Recursion
                left.reserve_all_vars_rec(var_manager, bound_type);
                right.reserve_all_vars_rec(var_manager, bound_type);
            }
        };
        self.reserve_all_vars(var_manager, bound_type)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, BTreeMap};

    use super::{Node, GeneralizedTotalizer};
    use crate::{
        encodings::{pb::EncodePB, BoundType, EncodingError},
        instances::{BasicVarManager, ManageVars},
        lit,
        types::Lit,
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
            max_rhs: 2,
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
            max_rhs: 2,
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
            max_rhs: 2,
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
            max_rhs: 2,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0], 5)),
            right: Box::new(Node::new_leaf(lit![0], 3)),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let cnf = node.encode_from_till(4, 6, &mut var_manager, &BoundType::UB);
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 4),
        };
        assert_eq!(cnf.n_clauses(), 3);
    }

    #[test]
    fn gte_functions() {
        let mut tot = GeneralizedTotalizer::new(BoundType::UB).unwrap();
        let mut lits = HashMap::new();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 5);
        lits.insert(lit![2], 3);
        lits.insert(lit![3], 3);
        tot.add(lits);
        assert_eq!(tot.enforce_ub(2), Err(EncodingError::NotEncoded));
        assert_eq!(tot.enforce_lb(2), Err(EncodingError::NoObjectSupport));
        let mut var_manager = BasicVarManager::new();
        let cnf = tot.encode(4, &mut var_manager);
        assert_eq!(tot.get_depth(), 3);
        assert_eq!(cnf.n_clauses(), 14);
    }

    #[test]
    fn invalid_useage() {
        let mut tot = GeneralizedTotalizer::new(BoundType::LB).unwrap();
        let mut lits = HashMap::new();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 3);
        tot.add(lits);
        assert_eq!(tot.enforce_ub(1), Err(EncodingError::NoObjectSupport));
        let mut tot = GeneralizedTotalizer::new(BoundType::UB).unwrap();
        let mut lits = HashMap::new();
        lits.insert(lit![0], 5);
        lits.insert(lit![1], 3);
        tot.add(lits);
        assert_eq!(tot.enforce_lb(1), Err(EncodingError::NoObjectSupport));
        match GeneralizedTotalizer::new(BoundType::BOTH) {
            Ok(_) => panic!(),
            Err(err) => assert_eq!(err, EncodingError::NoTypeSupport),
        };
    }
}
