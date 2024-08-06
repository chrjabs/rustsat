//! # Totalizer Encoding Based On a Node Database
//!
//! This is an alternative implementation of the
//! [`crate::encodings::card::Totalizer`] encoding.

use std::ops::RangeBounds;

use crate::{
    encodings::{
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
        totdb, CollectClauses, EncodeStats, Error,
    },
    instances::ManageVars,
    types::Lit,
};

use super::{
    BoundLower, BoundLowerIncremental, BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental,
};

/// Implementation of the binary adder tree totalizer encoding \[1\].
/// The implementation is incremental as extended in \[2\].
/// The implementation is based on a node database.
/// For now, this implementation only supports upper bounding.
///
/// # References
///
/// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality
///     Constraints_, CP 2003.
/// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental
///     Cardinality Constraints for MaxSAT_, CP 2014.
#[derive(Default)]
pub struct DbTotalizer {
    /// Literals added but not yet in the encoding
    lit_buffer: Vec<Lit>,
    /// The root of the tree, if constructed
    root: Option<NodeId>,
    /// The number of variables in the totalizer
    n_vars: u32,
    /// The number of clauses in the totalizer
    n_clauses: usize,
    /// The node database of the totalizer
    db: totdb::Db,
}

impl DbTotalizer {
    /// Creates a totalizer from its internal parts
    #[cfg(feature = "internals")]
    #[must_use]
    pub fn from_raw(root: NodeId, db: totdb::Db) -> Self {
        Self {
            root: Some(root),
            db,
            ..Default::default()
        }
    }

    fn extend_tree(&mut self) {
        if self.lit_buffer.is_empty() {
            return;
        }
        let new_tree = self.db.lit_tree(&self.lit_buffer);
        self.root = Some(match self.root {
            Some(old_root) => {
                self.db
                    .merge(&[NodeCon::full(old_root), NodeCon::full(new_tree)])
                    .id
            }
            None => new_tree,
        });
        self.lit_buffer.clear();
    }

    /// Gets the maximum depth of the tree
    #[must_use]
    pub fn depth(&self) -> usize {
        match &self.root {
            None => 0,
            Some(root) => self.db[*root].depth(),
        }
    }
}

impl Encode for DbTotalizer {
    fn n_lits(&self) -> usize {
        self.lit_buffer.len()
            + match self.root {
                Some(id) => self.db[id].len(),
                None => 0,
            }
    }
}

impl EncodeIncremental for DbTotalizer {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        if let Some(root) = self.root {
            self.db.reserve_vars(root, var_manager);
        }
    }
}

impl BoundUpper for DbTotalizer {
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
        self.db.reset_encoded(totdb::Semantics::If);
        self.encode_ub_change(range, collector, var_manager)
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
        if ub >= self.n_lits() {
            return Ok(vec![]);
        }
        if !self.lit_buffer.is_empty() {
            return Err(Error::NotEncoded);
        }
        if let Some(id) = self.root {
            match &self.db[id] {
                totdb::Node::Leaf(lit) => {
                    debug_assert_eq!(ub, 0);
                    return Ok(vec![!*lit]);
                }
                totdb::Node::Unit(node) => {
                    if let totdb::LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = node.lits[ub]
                    {
                        if semantics.has_if() {
                            return Ok(vec![!lit]);
                        }
                    }
                }
                totdb::Node::General(_) | totdb::Node::Dummy => unreachable!(),
            }
        }
        Err(Error::NotEncoded)
    }
}

impl BoundUpperIncremental for DbTotalizer {
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
        self.extend_tree();
        if let Some(id) = self.root {
            let n_vars_before = var_manager.n_used();
            let n_clauses_before = collector.n_clauses();
            for idx in range {
                self.db
                    .define_unweighted(id, idx, totdb::Semantics::If, collector, var_manager)?;
            }
            self.n_clauses += collector.n_clauses() - n_clauses_before;
            self.n_vars += var_manager.n_used() - n_vars_before;
        };
        Ok(())
    }
}

impl BoundLower for DbTotalizer {
    fn encode_lb<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        self.db.reset_encoded(totdb::Semantics::OnlyIf);
        self.encode_lb_change(range, collector, var_manager)
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, Error> {
        if lb == 0 {
            return Ok(vec![]);
        }
        if lb > self.n_lits() {
            return Err(Error::Unsat);
        }
        if !self.lit_buffer.is_empty() {
            return Err(Error::NotEncoded);
        }
        if let Some(id) = self.root {
            match &self.db[id] {
                totdb::Node::Leaf(lit) => {
                    debug_assert_eq!(lb, 1);
                    return Ok(vec![*lit]);
                }
                totdb::Node::Unit(node) => {
                    if let totdb::LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = node.lits[lb - 1]
                    {
                        if semantics.has_only_if() {
                            return Ok(vec![lit]);
                        }
                    }
                }
                totdb::Node::General(_) | totdb::Node::Dummy => unreachable!(),
            }
        }
        Err(Error::NotEncoded)
    }
}

impl BoundLowerIncremental for DbTotalizer {
    fn encode_lb_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        let range = super::prepare_lb_range(self, range);
        if range.is_empty() {
            return Ok(());
        }
        self.extend_tree();
        if let Some(id) = self.root {
            let n_vars_before = var_manager.n_used();
            let n_clauses_before = collector.n_clauses();
            for idx in range {
                self.db.define_unweighted(
                    id,
                    idx - 1,
                    totdb::Semantics::OnlyIf,
                    collector,
                    var_manager,
                )?;
            }
            self.n_clauses += collector.n_clauses() - n_clauses_before;
            self.n_vars += var_manager.n_used() - n_vars_before;
        };
        Ok(())
    }
}

impl EncodeStats for DbTotalizer {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        self.n_vars
    }
}

impl From<Vec<Lit>> for DbTotalizer {
    fn from(lits: Vec<Lit>) -> Self {
        Self {
            lit_buffer: lits,
            root: None,
            n_vars: 0,
            n_clauses: 0,
            db: totdb::Db::default(),
        }
    }
}

impl FromIterator<Lit> for DbTotalizer {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            lit_buffer: Vec::from_iter(iter),
            root: None,
            n_vars: 0,
            n_clauses: 0,
            db: totdb::Db::default(),
        }
    }
}

impl Extend<Lit> for DbTotalizer {
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        self.lit_buffer.extend(iter);
    }
}

#[cfg(feature = "proof-logging")]
impl super::cert::BoundUpper for DbTotalizer {
    fn encode_ub_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: crate::encodings::CollectCertClauses,
        R: RangeBounds<usize>,
        W: std::io::Write,
    {
        use super::cert::BoundUpperIncremental;
        self.db.reset_encoded(totdb::Semantics::If);
        self.encode_ub_change_cert(range, collector, var_manager, proof)
    }
}

#[cfg(feature = "proof-logging")]
impl super::cert::BoundUpperIncremental for DbTotalizer {
    fn encode_ub_change_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: crate::encodings::CollectCertClauses,
        R: RangeBounds<usize>,
        W: std::io::Write,
    {
        let range = super::prepare_ub_range(self, range);
        if range.is_empty() {
            return Ok(());
        }
        self.extend_tree();
        let mut leafs = vec![crate::lit![0]; self.n_lits()];
        if let Some(id) = self.root {
            let n_vars_before = var_manager.n_used();
            let n_clauses_before = collector.n_clauses();
            for idx in range {
                self.db.define_unweighted_cert(
                    id,
                    idx,
                    totdb::Semantics::If,
                    collector,
                    var_manager,
                    proof,
                    &mut leafs,
                )?;
            }
            self.n_clauses += collector.n_clauses() - n_clauses_before;
            self.n_vars += var_manager.n_used() - n_vars_before;
        };
        Ok(())
    }
}

#[cfg(feature = "proof-logging")]
impl super::cert::BoundLower for DbTotalizer {
    fn encode_lb_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: crate::encodings::CollectCertClauses,
        R: RangeBounds<usize>,
        W: std::io::Write,
    {
        use super::cert::BoundLowerIncremental;
        self.db.reset_encoded(totdb::Semantics::OnlyIf);
        self.encode_lb_change_cert(range, collector, var_manager, proof)
    }
}

#[cfg(feature = "proof-logging")]
impl super::cert::BoundLowerIncremental for DbTotalizer {
    fn encode_lb_change_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: crate::encodings::CollectCertClauses,
        R: RangeBounds<usize>,
        W: std::io::Write,
    {
        let range = super::prepare_lb_range(self, range);
        if range.is_empty() {
            return Ok(());
        }
        self.extend_tree();
        let mut leafs = vec![crate::lit![0]; self.n_lits()];
        if let Some(id) = self.root {
            let n_vars_before = var_manager.n_used();
            let n_clauses_before = collector.n_clauses();
            for idx in range {
                self.db.define_unweighted_cert(
                    id,
                    idx - 1,
                    totdb::Semantics::OnlyIf,
                    collector,
                    var_manager,
                    proof,
                    &mut leafs,
                )?;
            }
            self.n_clauses += collector.n_clauses() - n_clauses_before;
            self.n_vars += var_manager.n_used() - n_vars_before;
        };
        Ok(())
    }
}

/// Totalizer encoding types that do not own but reference their [`totdb::Db`]
#[cfg(feature = "internals")]
pub mod referenced {
    use std::cell::RefCell;

    use crate::{
        encodings::{
            card::{BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental},
            nodedb::{NodeId, NodeLike},
            totdb, CollectClauses, Error,
        },
        instances::ManageVars,
        types::Lit,
    };

    /// Implementation of the binary adder tree totalizer encoding \[1\].
    /// The implementation is incremental as extended in \[2\].
    /// This uses a _mutable reference_ to a totalizer database.
    ///
    /// # References
    ///
    /// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
    /// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.
    pub struct Tot<'totdb> {
        /// The root of the tree, if constructed
        root: NodeId,
        /// The node database of the totalizer
        db: &'totdb mut totdb::Db,
    }

    /// Implementation of the binary adder tree totalizer encoding \[1\].
    /// The implementation is incremental as extended in \[2\].
    /// This uses a [`RefCell`] to a totalizer database.
    ///
    /// # References
    ///
    /// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
    /// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.
    pub struct TotCell<'totdb> {
        /// The root of the tree, if constructed
        root: NodeId,
        /// The node database of the totalizer
        db: &'totdb RefCell<&'totdb mut totdb::Db>,
    }

    impl<'totdb> Tot<'totdb> {
        /// Constructs a new Totalizer encoding referencing a totalizer database
        pub fn new(root: NodeId, db: &'totdb mut totdb::Db) -> Self {
            Self { root, db }
        }

        /// Gets the maximum depth of the tree
        #[must_use]
        pub fn depth(&self) -> usize {
            self.db[self.root].depth()
        }
    }

    impl<'totdb> TotCell<'totdb> {
        /// Constructs a new Totalizer encoding referencing a totalizer database
        pub fn new(root: NodeId, db: &'totdb RefCell<&'totdb mut totdb::Db>) -> Self {
            Self { root, db }
        }

        /// Gets the maximum depth of the tree
        #[must_use]
        pub fn depth(&self) -> usize {
            self.db.borrow()[self.root].depth()
        }
    }

    impl Encode for Tot<'_> {
        fn n_lits(&self) -> usize {
            self.db[self.root].len()
        }
    }

    impl Encode for TotCell<'_> {
        fn n_lits(&self) -> usize {
            self.db.borrow()[self.root].len()
        }
    }

    impl EncodeIncremental for Tot<'_> {
        fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
            self.db.reserve_vars(self.root, var_manager);
        }
    }

    impl EncodeIncremental for TotCell<'_> {
        fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
            self.db.borrow_mut().reserve_vars(self.root, var_manager);
        }
    }

    impl BoundUpper for Tot<'_> {
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

        fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
            if ub >= self.n_lits() {
                return Ok(vec![]);
            }
            match &self.db[self.root] {
                totdb::Node::Leaf(lit) => {
                    debug_assert_eq!(ub, 0);
                    return Ok(vec![!*lit]);
                }
                totdb::Node::Unit(node) => {
                    if let totdb::LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = node.lits[ub]
                    {
                        if semantics.has_if() {
                            return Ok(vec![!lit]);
                        }
                    }
                }
                totdb::Node::General(_) | totdb::Node::Dummy => unreachable!(),
            }
            Err(Error::NotEncoded)
        }
    }

    impl BoundUpper for TotCell<'_> {
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

        fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
            if ub >= self.n_lits() {
                return Ok(vec![]);
            }
            match &self.db.borrow()[self.root] {
                totdb::Node::Leaf(lit) => {
                    debug_assert_eq!(ub, 0);
                    return Ok(vec![!*lit]);
                }
                totdb::Node::Unit(node) => {
                    if let totdb::LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = node.lits[ub]
                    {
                        if semantics.has_if() {
                            return Ok(vec![!lit]);
                        }
                    }
                }
                totdb::Node::General(_) | totdb::Node::Dummy => unreachable!(),
            }
            Err(Error::NotEncoded)
        }
    }

    impl BoundUpperIncremental for Tot<'_> {
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
            for idx in range {
                self.db.define_unweighted(
                    self.root,
                    idx,
                    totdb::Semantics::If,
                    collector,
                    var_manager,
                )?;
            }
            Ok(())
        }
    }

    impl BoundUpperIncremental for TotCell<'_> {
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
            for idx in range {
                self.db.borrow_mut().define_unweighted(
                    self.root,
                    idx,
                    totdb::Semantics::If,
                    collector,
                    var_manager,
                )?;
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::DbTotalizer;
    use crate::{
        encodings::{
            card::{BoundUpper, BoundUpperIncremental},
            EncodeStats, Error,
        },
        instances::{BasicVarManager, Cnf, ManageVars},
        lit, var,
    };

    #[test]
    fn functions() {
        let mut tot = DbTotalizer::default();
        tot.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        assert_eq!(tot.enforce_ub(2), Err(Error::NotEncoded));
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf = Cnf::new();
        tot.encode_ub(0..5, &mut cnf, &mut var_manager).unwrap();
        assert_eq!(tot.depth(), 3);
        println!("len: {}, {:?}", cnf.len(), cnf);
        assert_eq!(cnf.len(), 14);
        assert_eq!(tot.n_clauses(), 14);
        assert_eq!(tot.n_vars(), 8);
        assert_eq!(tot.enforce_ub(2).unwrap().len(), 1);
    }

    #[test]
    fn functions_min_rhs() {
        let mut tot = DbTotalizer::default();
        tot.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf = Cnf::new();
        tot.encode_ub(3..4, &mut cnf, &mut var_manager).unwrap();
        assert_eq!(tot.depth(), 3);
        assert_eq!(cnf.len(), 3);
        assert_eq!(cnf.len(), tot.n_clauses());
    }

    #[test]
    fn incremental_building_ub() {
        let mut tot1 = DbTotalizer::default();
        tot1.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf1 = Cnf::new();
        tot1.encode_ub(0..5, &mut cnf1, &mut var_manager).unwrap();
        let mut tot2 = DbTotalizer::default();
        tot2.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf2 = Cnf::new();
        tot2.encode_ub(0..3, &mut cnf2, &mut var_manager).unwrap();
        tot2.encode_ub_change(0..5, &mut cnf2, &mut var_manager)
            .unwrap();
        assert_eq!(cnf1.len(), cnf2.len());
        assert_eq!(cnf1.len(), tot1.n_clauses());
        assert_eq!(cnf2.len(), tot2.n_clauses());
    }
}
