//! # Integration Tests Copied from VeriPB

use std::{
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
    process::Command,
};

use pigeons::{
    Conclusion, ConstraintId as Id, ConstraintLike, OperationLike, OperationSequence,
    OutputGuarantee, Proof, ProofGoal, ProofGoalId, SubproofElement, VarLike,
};

type OpsSeq = OperationSequence<&'static str>;

struct Constr<'slf> {
    terms: Vec<(isize, bool, &'slf str)>,
    rhs: isize,
}

impl<'slf> Constr<'slf> {
    fn parse(constr: &'slf str) -> Self {
        let mut iter = constr.split(' ');
        let mut slf = Constr {
            terms: vec![],
            rhs: 0,
        };
        loop {
            let cf = iter.next().unwrap();
            let lit = iter.next().unwrap();
            if cf == ">=" {
                slf.rhs = lit.parse().unwrap();
                return slf;
            }
            let cf = cf.parse().unwrap();
            let (neg, var) = if let Some(var) = lit.strip_prefix('!') {
                (true, var)
            } else {
                (false, lit)
            };
            slf.terms.push((cf, neg, var));
        }
    }
}

impl<'slf> ConstraintLike<&'slf str> for Constr<'slf> {
    fn rhs(&self) -> isize {
        self.rhs
    }

    fn sum_iter(&self) -> impl Iterator<Item = (isize, pigeons::Axiom<&'slf str>)> {
        self.terms
            .iter()
            .map(|(cf, neg, v)| (*cf, (*v).axiom(*neg)))
    }
}

fn print_file<P: AsRef<Path>>(path: P) {
    for line in BufReader::new(File::open(path).expect("could not open file")).lines() {
        println!("{}", line.unwrap());
    }
}

fn verify_proof<P1: AsRef<Path>, P2: AsRef<Path>>(instance: P1, proof: P2) {
    if let Ok(veripb) = std::env::var("VERIPB_CHECKER") {
        println!("start checking proof");
        let out = Command::new(veripb)
            .arg(instance.as_ref())
            .arg(proof.as_ref())
            .output()
            .expect("failed to run veripb");
        print_file(proof);
        if out.status.success() {
            return;
        }
        panic!("verification failed: {out:?}")
    } else {
        println!("`$VERIPB_CHECKER` not set, omitting proof checking");
    }
}

fn new_proof(num_constraints: usize, optimization: bool) -> Proof<tempfile::NamedTempFile> {
    let file = tempfile::NamedTempFile::new().expect("failed to create temporary proof file");
    pigeons::Proof::new(file, num_constraints, optimization).expect("failed to start proof")
}

#[test]
fn all_diff() {
    let mut proof = new_proof(15, false);
    let new1 = proof
        .operations(&(OpsSeq::from(Id::abs(3)) + Id::abs(4) + Id::abs(5)))
        .unwrap();
    let new2 = proof
        .operations(
            &(OpsSeq::from(Id::abs(14))
                + Id::abs(15)
                + "y_x1_8".pos_axiom()
                + "y_x2_8".pos_axiom()
                + "y_x1_9".pos_axiom()
                + "y_x2_9".pos_axiom()),
        )
        .unwrap();
    let contrad = proof.operations(&(OpsSeq::from(new1) + new2)).unwrap();
    let proof_file = proof
        .conclude::<&'static str>(
            OutputGuarantee::None,
            &Conclusion::Unsat(Some(contrad.into())),
        )
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(format!("{manifest}/data/all_diff.opb"), proof_file.path());
}

#[test]
fn implication_weaker() {
    let mut proof = new_proof(1, false);
    proof
        .implied(&Constr::parse("1 x1 2 x2 4 x3 >= 3"), Some(Id::abs(1)))
        .unwrap();
    proof
        .implied_add(&Constr::parse("1 x1 2 x2 4 x3 >= 3"), Some(Id::abs(1)))
        .unwrap();
    proof
        .equals(&Constr::parse("1 x1 2 x2 4 x3 >= 3"), Some(Id::last(1)))
        .unwrap();
    proof
        .equals_add(&Constr::parse("1 x1 2 x2 4 x3 >= 3"), Some(Id::last(1)))
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(OutputGuarantee::None, &Conclusion::None)
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/implication_weaker.opb"),
        proof_file.path(),
    );
}

#[test]
fn g3_g5() {
    let mut proof = new_proof(361, false);
    let a = proof.redundant(
        &Constr::parse("-1 x0_0 -1 x1_0 -1 x2_0 -1 x3_0 -1 x4_0 -1 x5_0 -1 x6_0 -1 x7_0 -1 x8_0 -1 x9_0 >= -1"),
        [],
        None
    ).unwrap();
    let b = proof
        .redundant(
            &Constr::parse("1 ~x0_0 1 x9_1 1 x9_2 1 x9_3 1 x9_4 1 x9_5 1 x9_6 1 x9_7 1 x9_8 1 x9_9 1 x9_10 >= 1"),
            [],
            None,
        )
        .unwrap();
    let c = proof
        .redundant(
            &Constr::parse("1 ~x9_1 1 x1_0 1 x1_2 1 x1_10 >= 1"),
            [],
            None,
        )
        .unwrap();
    let d = proof
        .redundant(
            &Constr::parse("1 ~x9_2 1 x1_0 1 x1_1 1 x1_3 >= 1"),
            [],
            None,
        )
        .unwrap();
    let e = proof
        .redundant(
            &Constr::parse("1 ~x9_3 1 x1_0 1 x1_2 1 x1_4 >= 1"),
            [],
            None,
        )
        .unwrap();
    let f = proof
        .redundant(
            &Constr::parse("1 ~x9_4 1 x1_0 1 x1_3 1 x1_5 >= 1"),
            [],
            None,
        )
        .unwrap();
    let g = proof
        .redundant(
            &Constr::parse("1 ~x9_5 1 x1_0 1 x1_4 1 x1_6 >= 1"),
            [],
            None,
        )
        .unwrap();
    let h = proof
        .redundant(
            &Constr::parse("1 ~x9_6 1 x1_0 1 x1_5 1 x1_7 >= 1"),
            [],
            None,
        )
        .unwrap();
    let i = proof
        .redundant(
            &Constr::parse("1 ~x9_7 1 x1_0 1 x1_6 1 x1_8 >= 1"),
            [],
            None,
        )
        .unwrap();
    let j = proof
        .redundant(
            &Constr::parse("1 ~x9_8 1 x1_0 1 x1_7 1 x1_9 >= 1"),
            [],
            None,
        )
        .unwrap();
    let k = proof
        .redundant(
            &Constr::parse("1 ~x9_9 1 x1_0 1 x1_8 1 x1_10 >= 1"),
            [],
            None,
        )
        .unwrap();
    let l = proof
        .redundant(
            &Constr::parse("1 ~x9_10 1 x1_0 1 x1_1 1 x1_9 >= 1"),
            [],
            None,
        )
        .unwrap();
    proof.set_level(1).unwrap();
    let sum = proof
        .operations(
            &[c, d, e, f, g, h, i, j, k, l]
                .into_iter()
                .fold(OpsSeq::from(b), |seq, id| seq + id)
                .saturate(),
        )
        .unwrap();
    proof.implied_add(&Constr::parse("1 ~x0_0 1 x1_0 1 x1_1 1 x1_2 1 x1_3 1 x1_4 1 x1_5 1 x1_6 1 x1_7 1 x1_8 1 x1_9 1 x1_10 >= 1"), Some(Id::from(sum))).unwrap();
    let sum2 = proof
        .operations(&(OpsSeq::from(sum) + a).saturate())
        .unwrap();
    let implied = proof
        .implied_add(
            &Constr::parse("1 ~x0_0 1 x1_1 1 x1_2 1 x1_3 1 x1_4 1 x1_5 1 x1_6 1 x1_7 1 x1_8 1 x1_9 1 x1_10 >= 1"),
            Some(Id::from(sum2)),
        )
        .unwrap();
    proof.set_level(0).unwrap();
    proof
        .implied_add(
            &Constr::parse("1 ~x0_0 1 x1_1 1 x1_2 1 x1_3 1 x1_4 1 x1_5 1 x1_6 1 x1_7 1 x1_8 1 x1_9 1 x1_10 >= 1"),
            Some(Id::from(implied)),
        )
        .unwrap();
    proof.wipe_level(1).unwrap();
    let proof_file = proof
        .conclude::<&'static str>(OutputGuarantee::None, &Conclusion::None)
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(format!("{manifest}/data/g3-g5.opb"), proof_file.path());
}

#[test]
fn strengthening_to_core() {
    let mut proof = new_proof(4, false);
    proof.strengthening_to_core(true).unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(3)) * 1 + OpsSeq::from(Id::abs(4)) * 1))
        .unwrap();
    proof
        .redundant(
            &Constr::parse("1 x3 >= 1"),
            ["x3".substitute_fixed(true)],
            None,
        )
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(OutputGuarantee::None, &Conclusion::None)
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/strengthening_to_core.opb"),
        proof_file.path(),
    );
}

#[test]
fn strengthening_to_core_proof_by_contradiction() {
    let mut proof = new_proof(4, false);
    proof.strengthening_to_core(true).unwrap();
    proof
        .redundant(
            &Constr::parse("1 ~x3 2 x4 2 x5 2 x6 >= 4"),
            [],
            [SubproofElement::Derivation(
                (OpsSeq::from(Id::abs(3)) * 1 + OpsSeq::from(Id::abs(4)) * 1 + Id::last(1)).into(),
            )],
        )
        .unwrap();
    proof
        .redundant(
            &Constr::parse("1 x3 >= 1"),
            ["x3".substitute_fixed(true)],
            None,
        )
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(OutputGuarantee::None, &Conclusion::None)
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/strengthening_to_core.opb"),
        proof_file.path(),
    );
}

#[test]
fn subproof() {
    let mut proof = new_proof(7, false);
    proof
        .operations(&(OpsSeq::from(Id::abs(1)).saturate()))
        .unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(8)) + Id::abs(2) + Id::abs(3)))
        .unwrap();
    proof.operations(&(OpsSeq::from(Id::abs(9)) / 2)).unwrap();
    proof
        .redundant(
            &Constr::parse("1 x1 >= 1"),
            [
                "x1".substitute_literal("x3".pos_axiom()),
                "x3".substitute_literal("x5".pos_axiom()),
                "x5".substitute_literal("x1".pos_axiom()),
                "x2".substitute_literal("x4".pos_axiom()),
                "x4".substitute_literal("x6".pos_axiom()),
                "x6".substitute_literal("x2".pos_axiom()),
            ],
            [
                ProofGoal::new(
                    ProofGoalId::specific(1),
                    [
                        (OpsSeq::from(Id::last(1)) + Id::last(2) + Id::abs(5) + Id::abs(6)).into(),
                        (OpsSeq::from(Id::last(1)) + Id::abs(4)).into(),
                        (OpsSeq::from(Id::last(1)) + "x6".pos_axiom()).into(),
                    ],
                )
                .into(),
                ProofGoal::new(
                    ProofGoalId::from(Id::abs(1)),
                    [(OpsSeq::from(Id::last(1)) + Id::abs(2)).into()],
                )
                .into(),
            ],
        )
        .unwrap();
    let id = proof
        .reverse_unit_prop(&Constr::parse(">= 1"), None)
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(OutputGuarantee::None, &Conclusion::Unsat(Some(id.into())))
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(format!("{manifest}/data/subproof.opb"), proof_file.path());
}

#[test]
fn miniproof_polishnotation_1() {
    let (file, proof_file) = tempfile::NamedTempFile::new()
        .expect("failed to create temporary proof file")
        .into_parts();
    let mut proof = pigeons::Proof::new_with_conclusion::<&'static str>(
        file,
        5,
        false,
        OutputGuarantee::None,
        &Conclusion::Unsat(Some(Id::abs(9))),
    )
    .expect("failed to start proof");
    proof
        .operations(&(OpsSeq::from(Id::abs(3)) * 1 + OpsSeq::from(Id::abs(4)) * 1).saturate())
        .unwrap();
    proof
        .equals(
            &Constr::parse("1 x1 +1 x3 >= 1"),
            Some(proof.first_proof_id().into()),
        )
        .unwrap();
    let next_id = proof.next_id();
    proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2) + Id::abs(6)))
        .unwrap();
    proof
        .equals(
            &Constr::parse("+2 x1 +2 x2 +2 x3 >= 3"),
            Some(next_id.into()),
        )
        .unwrap();
    proof
        .operations(&((OpsSeq::from(Id::abs(1)) + Id::abs(2) + Id::abs(6)) / 2))
        .unwrap();
    proof
        .equals(&Constr::parse("1 x1 1 x2 1 x3 >= 2"), Some(Id::abs(8)))
        .unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(5)) * 2 + OpsSeq::from(Id::abs(8)) * 2))
        .unwrap();
    proof
        .equals(&Constr::parse(">= 2"), Some(Id::abs(9)))
        .unwrap();
    drop(proof);
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/miniProof_polishnotation_1.opb"),
        proof_file,
    );
}

#[test]
fn decision_sat() {
    let mut proof = new_proof(4, false);
    proof
        .solution([
            "x1".pos_axiom(),
            "x2".pos_axiom(),
            "x3".pos_axiom(),
            "x4".pos_axiom(),
        ])
        .unwrap();
    let proof_file = proof
        .conclude(
            OutputGuarantee::None,
            &Conclusion::Sat(Some(vec![
                "x1".pos_axiom(),
                "x2".pos_axiom(),
                "x3".pos_axiom(),
                "x4".pos_axiom(),
            ])),
        )
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/decision_sat.opb"),
        proof_file.path(),
    );
}

#[test]
fn optimization_2() {
    let mut proof = new_proof(3, true);
    proof
        .obj_equals(&[(-2, "x1"), (-2, "x2"), (-2, "x3")])
        .unwrap();
    proof
        .operations(&((OpsSeq::from(Id::abs(1)) + Id::abs(2) + Id::abs(3)) / 2))
        .unwrap();
    proof
        .improve_solution(["x1".pos_axiom(), "x2".neg_axiom(), "x3".neg_axiom()])
        .unwrap();
    proof
        .equals(
            &Constr::parse("-2 ~x1 -2 ~x2 -2 ~x3 >= -3"),
            Some(Id::abs(5)),
        )
        .unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(4)) * 2 + Id::abs(5)))
        .unwrap();
    proof
        .reverse_unit_prop(&Constr::parse("2 ~x3 2 ~x2 2 ~x1 >= 4"), None)
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(
            OutputGuarantee::None,
            &Conclusion::Bounds {
                range: -2..-1,
                lb_id: None,
                ub_sol: None,
            },
        )
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/optimization_2.opb"),
        proof_file.path(),
    )
}
