//! # Pairwise At-Most-1 Encoding
//!
//! ## References
//!
//! - Steven D. Prestwich: _CNF Encodings_, in Handbook of Satisfiability 2021.

use crate::encodings::CollectClauses;
use crate::encodings::EncodeStats;
use crate::encodings::IterInputs;
use crate::instances::ManageVars;
use crate::types::Lit;

use super::Encode;

/// Implementations of the pairwise at-most-1 encoding.
///
/// # References
///
/// - Steven D. Prestwich: _CNF Encodings_, in Handbook of Satisfiability 2021.
#[derive(Default, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Pairwise {
    /// Input literals
    in_lits: Vec<Lit>,
    /// The number of clauses in the encoding
    n_clauses: usize,
}

impl Encode for Pairwise {
    fn n_lits(&self) -> usize {
        self.in_lits.len()
    }

    fn encode<Col>(
        &mut self,
        collector: &mut Col,
        _var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        let prev_clauses = collector.n_clauses();
        let lits = &self.in_lits;
        let clause_iter = (0..self.in_lits.len()).flat_map(|first| {
            (first + 1..self.in_lits.len()).map(move |second| !lits[first] | !lits[second])
        });
        collector.extend_clauses(clause_iter)?;
        self.n_clauses = collector.n_clauses() - prev_clauses;
        Ok(())
    }
}

#[cfg(feature = "proof-logging")]
impl super::cert::Encode for Pairwise {
    fn encode_cert<Col, W>(
        &mut self,
        id: pigeons::AbsConstraintId,
        collector: &mut Col,
        _var_manager: &mut dyn crate::instances::ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), crate::encodings::cert::EncodingError>
    where
        Col: crate::encodings::cert::CollectClauses,
        W: std::io::Write,
    {
        let prev_clauses = collector.n_clauses();
        for this in 0..self.in_lits.len() - 1 {
            for &other in &self.in_lits[this + 1..] {
                let clause = !self.in_lits[this] | !other;
                let id = proof.reverse_unit_prop(&clause, [id.into()])?;
                collector.add_cert_clause(clause, id)?;
            }
        }
        self.n_clauses = collector.n_clauses() - prev_clauses;
        Ok(())
    }
}

impl IterInputs for Pairwise {
    type Iter<'a> = std::iter::Copied<std::slice::Iter<'a, Lit>>;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().copied()
    }
}

impl EncodeStats for Pairwise {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        0
    }
}

impl From<Vec<Lit>> for Pairwise {
    fn from(lits: Vec<Lit>) -> Self {
        Self {
            in_lits: lits,
            n_clauses: Default::default(),
        }
    }
}

impl FromIterator<Lit> for Pairwise {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            in_lits: Vec::from_iter(iter),
            n_clauses: Default::default(),
        }
    }
}

impl Extend<Lit> for Pairwise {
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        self.in_lits.extend(iter);
    }
}

#[cfg(test)]
mod tests {
    use crate::encodings::am1::Encode;
    use crate::instances::BasicVarManager;
    use crate::instances::Cnf;
    use crate::instances::ManageVars;
    use crate::lit;
    use crate::var;

    #[test]
    fn basic() {
        let mut enc: super::Pairwise = [lit![0], lit![1], lit![2], lit![3]].into_iter().collect();
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![4]);
        enc.encode(&mut cnf, &mut vm).unwrap();
        assert_eq!(vm.n_used(), 4);
        assert_eq!(cnf.len(), 6);
    }

    #[cfg(feature = "proof-logging")]
    mod proofs {
        use std::io::BufRead;

        use crate::encodings::am1::cert::Encode;
        use crate::instances::Cnf;
        use crate::instances::SatInstance;
        use crate::types::Var;
        use crate::types::constraints::CardConstraint;

        fn print_file<P: AsRef<std::path::Path>>(path: P) {
            println!();
            for line in
                std::io::BufReader::new(std::fs::File::open(path).expect("could not open file"))
                    .lines()
            {
                println!("{}", line.unwrap());
            }
            println!();
        }

        fn verify_proof<P1: AsRef<std::path::Path>, P2: AsRef<std::path::Path>>(
            instance: P1,
            proof: P2,
        ) {
            if let Ok(veripb) = std::env::var("VERIPB_CHECKER") {
                println!("start checking proof");
                let out = std::process::Command::new(veripb)
                    .arg(instance.as_ref())
                    .arg(proof.as_ref())
                    .output()
                    .expect("failed to run veripb");
                print_file(proof);
                if out.status.success() {
                    return;
                }
                panic!("verification failed: {out:?}")
            }
            println!("`$VERIPB_CHECKER` not set, omitting proof checking");
        }

        fn new_proof(
            num_constraints: usize,
            optimization: bool,
        ) -> pigeons::Proof<tempfile::NamedTempFile> {
            let file =
                tempfile::NamedTempFile::new().expect("failed to create temporary proof file");
            pigeons::Proof::new(file, num_constraints, optimization).expect("failed to start proof")
        }

        #[test]
        fn constraint() {
            let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
            let inst_path = format!("{manifest}/data/single-am1.opb");
            let constr: SatInstance = SatInstance::from_opb_path(
                &inst_path,
                crate::instances::fio::opb::Options::default(),
            )
            .unwrap();
            let (constr, mut vm) = constr.into_pbs();
            assert_eq!(constr.len(), 1);
            let constr = constr.into_iter().next().unwrap();
            let constr = constr.into_card_constr().unwrap();
            let CardConstraint::Ub(constr) = constr else {
                panic!()
            };
            let (lits, bound) = constr.decompose();
            assert_eq!(bound, 1);
            let mut cnf = Cnf::new();
            let mut proof = new_proof(1, false);
            let mut enc: crate::encodings::am1::Pairwise = lits.into_iter().collect();
            enc.encode_cert(
                pigeons::AbsConstraintId::new(1),
                &mut cnf,
                &mut vm,
                &mut proof,
            )
            .unwrap();
            let proof_file = proof
                .conclude::<Var>(&pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
                .unwrap();
            verify_proof(&inst_path, proof_file.path());
        }
    }
}
