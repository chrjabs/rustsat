//! # Support Functionality for Including Pindakaas Encodings

use std::num::NonZeroI32;

use crate::{
    instances::ManageVars,
    types::{Clause, Lit, Var},
};

/// Implements [`pindakaas::ClauseDatabase`] for a `Col` that implements [`super::CollectClauses`]
/// and a dynamic type that implements [`ManageVars`]
pub struct ClauseDb<'db, Col> {
    collector: &'db mut Col,
    var_manager: &'db mut dyn ManageVars,
}

impl<'db, Col> ClauseDb<'db, Col> {
    pub fn new(collector: &'db mut Col, var_manager: &'db mut dyn ManageVars) -> Self {
        ClauseDb {
            collector,
            var_manager,
        }
    }
}

impl<Col> pindakaas::ClauseDatabase for ClauseDb<'_, Col>
where
    Col: super::CollectClauses,
{
    fn add_clause_from_slice(
        &mut self,
        clause: &[pindakaas::Lit],
    ) -> Result<(), pindakaas::Unsatisfiable> {
        let clause: Clause = clause.iter().copied().map(Lit::from).collect();
        self.collector
            .add_clause(clause)
            .expect("clause collector ran out of memory");
        Ok(())
    }

    fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange {
        let start = self.var_manager.max_var().map_or(Var::new(0), |v| v + 1);
        let end = start + u32::try_from(len - 1).expect("variable range too large");
        self.var_manager.increase_next_free(end + 1);
        pindakaas::VarRange::new(start.into(), end.into())
    }
}

/// Implements [`pindakaas::ClauseDatabase`] for a `Col` that implements [`super::CollectClauses`]
/// and a dynamic type that implements [`ManageVars`]. Adds a fake reification literal to all added
/// clauses.
pub struct ReifClauseDb<'db, Col> {
    collector: &'db mut Col,
    var_manager: &'db mut dyn ManageVars,
    reification: Lit,
}

impl<'db, Col> ReifClauseDb<'db, Col> {
    pub fn new(collector: &'db mut Col, var_manager: &'db mut dyn ManageVars) -> Self {
        let reification = var_manager.new_lit();
        ReifClauseDb {
            collector,
            var_manager,
            reification,
        }
    }

    pub fn reification(&self) -> Lit {
        self.reification
    }
}

impl<Col> pindakaas::ClauseDatabase for ReifClauseDb<'_, Col>
where
    Col: super::CollectClauses,
{
    fn add_clause_from_slice(
        &mut self,
        clause: &[pindakaas::Lit],
    ) -> Result<(), pindakaas::Unsatisfiable> {
        let mut clause: Clause = clause.iter().copied().map(Lit::from).collect();
        clause.add(self.reification);
        self.collector
            .add_clause(clause)
            .expect("clause collector ran out of memory");
        Ok(())
    }

    fn new_var_range(&mut self, len: usize) -> pindakaas::VarRange {
        let start = self.var_manager.max_var().map_or(Var::new(0), |v| v + 1);
        let end = start + u32::try_from(len - 1).expect("variable range too large");
        self.var_manager.increase_next_free(end + 1);
        pindakaas::VarRange::new(start.into(), end.into())
    }
}

impl From<Lit> for pindakaas::Lit {
    fn from(value: Lit) -> Self {
        // NOTE: pindakaas uses ipasir literal representation
        pindakaas::Lit::from_raw(
            NonZeroI32::try_from(value.to_ipasir()).expect("IPASIR lit is never zero"),
        )
    }
}

impl From<pindakaas::Lit> for Lit {
    fn from(value: pindakaas::Lit) -> Self {
        let ipasir = NonZeroI32::from(value);
        Lit::from_ipasir(ipasir.get()).expect("lit is non-zero")
    }
}

impl From<Var> for pindakaas::Var {
    fn from(value: Var) -> Self {
        // NOTE: there seems to be no direct way of constructing a variable in pindakaas
        pindakaas::Lit::from(value.pos_lit()).var()
    }
}

impl From<pindakaas::Var> for Var {
    fn from(value: pindakaas::Var) -> Self {
        let idx = (NonZeroI32::from(value).get() - 1).unsigned_abs();
        Var::new(idx)
    }
}
