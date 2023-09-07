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

use std::collections::BTreeMap;

use crate::{
    encodings::{
        card::dbtotalizer::{Node, TotDb},
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
    },
    instances::ManageVars,
    types::{Lit, RsHashMap},
    utils,
};

use super::Encode;

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
    /// Flag to know when new literals where added and the encoding needs to be reconstructed
    lits_added: bool,
    /// The encoding root and the tares
    encoding: Option<Encoding>,
    /// Sum of all input weight
    weight_sum: usize,
    /// The number of variables
    n_vars: usize,
    /// The number of clauses
    n_clauses: usize,
    /// The node database of the totalizer
    db: TotDb,
}

impl DynamicPolyWatchdog {
    /// Resets the totalizer database and builds a new tree structure over the input literals
    fn build_tree(&mut self, var_manager: &mut dyn ManageVars) {
        // Reset totalizer db and encoding
        self.db = Default::default();
        self.encoding = Default::default();

        // Initialize weight queue
        let mut weight_queue: BTreeMap<usize, Vec<NodeCon>> = BTreeMap::new();
        for (&lit, &weight) in self.in_lits.iter() {
            let node = self.db.insert(Node::Leaf(lit));
            if let Some(cons) = weight_queue.get_mut(&weight) {
                cons.push(NodeCon::full(node));
            } else {
                weight_queue.insert(weight, vec![NodeCon::full(node)]);
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
            let merged = self.db.merge_balanced(&cons);
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
            self.encoding = Some(Encoding {
                root: top_buckets[0][0].id,
                tares: vec![],
            });
            self.lits_added = false;
            return;
        }

        // Prepare tares
        let tares: Vec<_> = (0..basis_len)
            .map(|_| var_manager.new_var().pos_lit())
            .collect();
        let tare_nodes: Vec<_> = tares
            .iter()
            .map(|&lit| self.db.insert(Node::Leaf(lit)))
            .collect();

        // Prepare lowest top bucket
        top_buckets[0].push(NodeCon::full(tare_nodes[0]));
        top_buckets[0].sort_unstable_by_key(|&con| self.db.max_value(con));

        // Merge top buckets and merge with bottom buckets
        let mut next_right = None;
        for (idx, mut cons) in top_buckets.into_iter().enumerate() {
            if !idx == basis_len - 1 {
                // Merge top bucket (except for last) with tare
                cons.push(NodeCon::full(tare_nodes[idx]));
            }
            cons.sort_unstable_by_key(|&con| self.db.max_value(con));
            let top_bucket = self.db.merge_balanced(&cons);
            if next_right.is_none() {
                // special case: lowest bucket does not need bottom buckets
                if self.db.max_value(top_bucket) == 1 {
                    // top bucket is empty (except for tare), tare can be
                    // omitted: shift to next layer
                    continue;
                }
                debug_assert_eq!(top_bucket.divisor, 1);
                next_right = Some(NodeCon {
                    id: top_bucket.id,
                    offset: top_bucket.offset,
                    divisor: 2,
                });
                continue;
            }

            let right = next_right.unwrap();
            let len = self.db.max_value(top_bucket) + self.db.max_value(right);
            let bottom = self.db.insert(Node::internal(len, top_bucket, right));
            next_right = Some(NodeCon {
                id: bottom,
                offset: 0,
                divisor: 2,
            });
        }
        
        // TODO: safe encoding

        self.lits_added = false;
    }
}

struct Encoding {
    /// The root of the encoding
    root: NodeId,
    /// The tare variables needed to enforce specific bounds. First in vector is
    /// the tare to the second largest top bucket, then decreasing.
    tares: Vec<Lit>,
}

impl Encode for DynamicPolyWatchdog {
    type Iter<'a> = DpwIter<'a>;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().map(copy_key_val)
    }

    fn weight_sum(&self) -> usize {
        self.weight_sum
    }

    fn next_higher(&self, val: usize) -> usize {
        val + 1
    }

    fn next_lower(&self, val: usize) -> usize {
        val - 1
    }
}

impl From<RsHashMap<Lit, usize>> for DynamicPolyWatchdog {
    fn from(lits: RsHashMap<Lit, usize>) -> Self {
        let weight_sum = lits.iter().fold(0, |sum, (_, w)| sum + *w);
        Self {
            in_lits: lits.clone(),
            lits_added: true,
            encoding: Default::default(),
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

impl Extend<(Lit, usize)> for DynamicPolyWatchdog {
    fn extend<T: IntoIterator<Item = (Lit, usize)>>(&mut self, iter: T) {
        iter.into_iter().for_each(|(l, w)| {
            self.weight_sum += w;
            // Insert into map of input literals
            match self.in_lits.get_mut(&l) {
                Some(old_w) => *old_w += w,
                None => {
                    self.in_lits.insert(l, w);
                }
            };
        });
        self.lits_added = true;
    }
}

fn copy_key_val(key_val_refs: (&Lit, &usize)) -> (Lit, usize) {
    (*key_val_refs.0, *key_val_refs.1)
}
type DpwIter<'a> = std::iter::Map<
    std::collections::hash_map::Iter<'a, Lit, usize>,
    fn((&Lit, &usize)) -> (Lit, usize),
>;
