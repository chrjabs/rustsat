//! # Operator Implementations for easily building Formulas

use crate::instances::Cnf;
use crate::instances::ManageVars;
use crate::instances::SatInstance;

use super::Clause;
use super::Lit;
use super::Var;

// === Negation ===

// --- Var ---

impl std::ops::Not for Var {
    type Output = Lit;

    #[inline]
    fn not(self) -> Lit {
        self.neg_lit()
    }
}

impl std::ops::Neg for Var {
    type Output = Lit;

    #[inline]
    fn neg(self) -> Lit {
        self.neg_lit()
    }
}

// --- Lit ---

impl std::ops::Not for Lit {
    type Output = Lit;

    #[inline]
    fn not(self) -> Lit {
        Lit {
            lidx: self.lidx ^ 1u32,
        }
    }
}

impl std::ops::Neg for Lit {
    type Output = Lit;

    #[inline]
    fn neg(self) -> Lit {
        Lit {
            lidx: self.lidx ^ 1u32,
        }
    }
}

// === Or ===

// --- Var ---

impl std::ops::BitOr<Var> for Var {
    type Output = Clause;

    fn bitor(self, rhs: Var) -> Self::Output {
        Clause::from([self.pos_lit(), rhs.pos_lit()])
    }
}

impl std::ops::BitOr<Lit> for Var {
    type Output = Clause;

    fn bitor(self, rhs: Lit) -> Self::Output {
        Clause::from([self.pos_lit(), rhs])
    }
}

impl std::ops::BitOr<Clause> for Var {
    type Output = Clause;

    fn bitor(self, rhs: Clause) -> Self::Output {
        let mut cl = Clause::from([self.pos_lit()]);
        cl.extend(rhs);
        cl
    }
}

// --- Lit ---

impl std::ops::BitOr<Var> for Lit {
    type Output = Clause;

    fn bitor(self, rhs: Var) -> Self::Output {
        Clause::from([self, rhs.pos_lit()])
    }
}

impl std::ops::BitOr<Lit> for Lit {
    type Output = Clause;

    fn bitor(self, rhs: Lit) -> Self::Output {
        Clause::from([self, rhs])
    }
}

impl std::ops::BitOr<Clause> for Lit {
    type Output = Clause;

    fn bitor(self, rhs: Clause) -> Self::Output {
        let mut cl = Clause::from([self]);
        cl.extend(rhs);
        cl
    }
}

// --- Clause ---

impl std::ops::BitOr<Var> for Clause {
    type Output = Clause;

    fn bitor(mut self, rhs: Var) -> Self::Output {
        self.add(rhs.pos_lit());
        self
    }
}

impl std::ops::BitOr<Lit> for Clause {
    type Output = Clause;

    fn bitor(mut self, rhs: Lit) -> Self::Output {
        self.add(rhs);
        self
    }
}

impl std::ops::BitOr<Clause> for Clause {
    type Output = Clause;

    fn bitor(mut self, rhs: Clause) -> Self::Output {
        self.extend(rhs);
        self
    }
}

impl std::ops::BitOrAssign<Var> for Clause {
    fn bitor_assign(&mut self, rhs: Var) {
        self.add(rhs.pos_lit());
    }
}

impl std::ops::BitOrAssign<Lit> for Clause {
    fn bitor_assign(&mut self, rhs: Lit) {
        self.add(rhs);
    }
}

impl std::ops::BitOrAssign<Clause> for Clause {
    fn bitor_assign(&mut self, rhs: Clause) {
        self.extend(rhs);
    }
}

// === And ===

// --- Var ---

impl std::ops::BitAnd<Var> for Var {
    type Output = Cnf;

    fn bitand(self, rhs: Var) -> Self::Output {
        Cnf::from_iter([
            Clause::from([self.pos_lit()]),
            Clause::from([rhs.pos_lit()]),
        ])
    }
}

impl std::ops::BitAnd<Lit> for Var {
    type Output = Cnf;

    fn bitand(self, rhs: Lit) -> Self::Output {
        Cnf::from_iter([Clause::from([self.pos_lit()]), Clause::from([rhs])])
    }
}

impl std::ops::BitAnd<Clause> for Var {
    type Output = Cnf;

    fn bitand(self, rhs: Clause) -> Self::Output {
        Cnf::from_iter([Clause::from([self.pos_lit()]), rhs])
    }
}

impl std::ops::BitAnd<Cnf> for Var {
    type Output = Cnf;

    fn bitand(self, rhs: Cnf) -> Self::Output {
        let mut cnf = Cnf::from_iter([Clause::from([self.pos_lit()])]);
        cnf.extend(rhs);
        cnf
    }
}

// --- Lit ---

impl std::ops::BitAnd<Var> for Lit {
    type Output = Cnf;

    fn bitand(self, rhs: Var) -> Self::Output {
        Cnf::from_iter([Clause::from([self]), Clause::from([rhs.pos_lit()])])
    }
}

impl std::ops::BitAnd<Lit> for Lit {
    type Output = Cnf;

    fn bitand(self, rhs: Lit) -> Self::Output {
        Cnf::from_iter([Clause::from([self]), Clause::from([rhs])])
    }
}

impl std::ops::BitAnd<Clause> for Lit {
    type Output = Cnf;

    fn bitand(self, rhs: Clause) -> Self::Output {
        Cnf::from_iter([Clause::from([self]), rhs])
    }
}

impl std::ops::BitAnd<Cnf> for Lit {
    type Output = Cnf;

    fn bitand(self, rhs: Cnf) -> Self::Output {
        let mut cnf = Cnf::from_iter([Clause::from([self])]);
        cnf.extend(rhs);
        cnf
    }
}

// --- Clause ---

impl std::ops::BitAnd<Var> for Clause {
    type Output = Cnf;

    fn bitand(self, rhs: Var) -> Self::Output {
        Cnf::from_iter([self, Clause::from([rhs.pos_lit()])])
    }
}

impl std::ops::BitAnd<Lit> for Clause {
    type Output = Cnf;

    fn bitand(self, rhs: Lit) -> Self::Output {
        Cnf::from_iter([self, Clause::from([rhs])])
    }
}

impl std::ops::BitAnd<Clause> for Clause {
    type Output = Cnf;

    fn bitand(self, rhs: Clause) -> Self::Output {
        Cnf::from_iter([self, rhs])
    }
}

impl std::ops::BitAnd<Cnf> for Clause {
    type Output = Cnf;

    fn bitand(self, rhs: Cnf) -> Self::Output {
        let mut cnf = Cnf::from_iter([self]);
        cnf.extend(rhs);
        cnf
    }
}

// --- Cnf ---

impl std::ops::BitAnd<Var> for Cnf {
    type Output = Cnf;

    fn bitand(mut self, rhs: Var) -> Self::Output {
        self.add_clause(Clause::from([rhs.pos_lit()]));
        self
    }
}

impl std::ops::BitAnd<Lit> for Cnf {
    type Output = Cnf;

    fn bitand(mut self, rhs: Lit) -> Self::Output {
        self.add_clause(Clause::from([rhs]));
        self
    }
}

impl std::ops::BitAnd<Clause> for Cnf {
    type Output = Cnf;

    fn bitand(mut self, rhs: Clause) -> Self::Output {
        self.add_clause(rhs);
        self
    }
}

impl std::ops::BitAnd<Cnf> for Cnf {
    type Output = Cnf;

    fn bitand(mut self, rhs: Cnf) -> Self::Output {
        self.extend(rhs);
        self
    }
}

impl std::ops::BitAndAssign<Var> for Cnf {
    fn bitand_assign(&mut self, rhs: Var) {
        self.add_clause(Clause::from([rhs.pos_lit()]));
    }
}

impl std::ops::BitAndAssign<Lit> for Cnf {
    fn bitand_assign(&mut self, rhs: Lit) {
        self.add_clause(Clause::from([rhs]));
    }
}

impl std::ops::BitAndAssign<Clause> for Cnf {
    fn bitand_assign(&mut self, rhs: Clause) {
        self.add_clause(rhs);
    }
}

impl std::ops::BitAndAssign<Cnf> for Cnf {
    fn bitand_assign(&mut self, rhs: Cnf) {
        self.extend(rhs);
    }
}

// --- SatInstance ---

impl<VM: ManageVars> std::ops::BitAnd<Var> for SatInstance<VM> {
    type Output = SatInstance<VM>;

    fn bitand(mut self, rhs: Var) -> Self::Output {
        self.add_clause(Clause::from([rhs.pos_lit()]));
        self
    }
}

impl<VM: ManageVars> std::ops::BitAnd<Lit> for SatInstance<VM> {
    type Output = SatInstance<VM>;

    fn bitand(mut self, rhs: Lit) -> Self::Output {
        self.add_clause(Clause::from([rhs]));
        self
    }
}

impl<VM: ManageVars> std::ops::BitAnd<Clause> for SatInstance<VM> {
    type Output = SatInstance<VM>;

    fn bitand(mut self, rhs: Clause) -> Self::Output {
        self.add_clause(rhs);
        self
    }
}

impl<VM: ManageVars> std::ops::BitAnd<Cnf> for SatInstance<VM> {
    type Output = SatInstance<VM>;

    fn bitand(mut self, rhs: Cnf) -> Self::Output {
        <SatInstance<VM> as Extend<Clause>>::extend(&mut self, rhs);
        self
    }
}

impl<VM: ManageVars> std::ops::BitAnd<SatInstance<VM>> for SatInstance<VM> {
    type Output = SatInstance<VM>;

    fn bitand(mut self, rhs: SatInstance<VM>) -> Self::Output {
        self.extend(rhs);
        self
    }
}

impl<VM: ManageVars> std::ops::BitAndAssign<Var> for SatInstance<VM> {
    fn bitand_assign(&mut self, rhs: Var) {
        self.add_clause(Clause::from([rhs.pos_lit()]));
    }
}

impl<VM: ManageVars> std::ops::BitAndAssign<Lit> for SatInstance<VM> {
    fn bitand_assign(&mut self, rhs: Lit) {
        self.add_clause(Clause::from([rhs]));
    }
}

impl<VM: ManageVars> std::ops::BitAndAssign<Clause> for SatInstance<VM> {
    fn bitand_assign(&mut self, rhs: Clause) {
        self.add_clause(rhs);
    }
}

impl<VM: ManageVars> std::ops::BitAndAssign<Cnf> for SatInstance<VM> {
    fn bitand_assign(&mut self, rhs: Cnf) {
        <SatInstance<VM> as Extend<Clause>>::extend(self, rhs);
    }
}

impl<VM: ManageVars> std::ops::BitAndAssign<SatInstance<VM>> for SatInstance<VM> {
    fn bitand_assign(&mut self, rhs: SatInstance<VM>) {
        self.extend(rhs);
    }
}
