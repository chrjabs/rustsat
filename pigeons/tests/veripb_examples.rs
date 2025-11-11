//! # Integration Tests Copied from VeriPB

use std::{
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
    process::Command,
};

use pigeons::{
    Conclusion, ConstraintId as Id, ConstraintLike, Derivation, ObjectiveLike, ObjectiveUpdate,
    OperationLike, OperationSequence, Order, OrderVar, OutputGuarantee, OutputType, Proof,
    ProofGoal, ProofGoalId, SubproofElement, Substitution, VarLike,
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

struct Obj<'slf> {
    terms: Vec<(isize, bool, &'slf str)>,
    offset: isize,
}

impl<'slf> Obj<'slf> {
    fn parse(constr: &'slf str) -> Self {
        let mut iter = constr.split(' ');
        let mut slf = Obj {
            terms: vec![],
            offset: 0,
        };
        loop {
            let Some(cf) = iter.next() else { return slf };
            let cf = cf.parse().unwrap();
            let Some(lit) = iter.next() else {
                slf.offset = cf;
                return slf;
            };
            let (neg, var) = if let Some(var) = lit.strip_prefix('!') {
                (true, var)
            } else {
                (false, lit)
            };
            slf.terms.push((cf, neg, var));
        }
    }
}

impl<'slf> ObjectiveLike<&'slf str> for Obj<'slf> {
    fn sum_iter(&self) -> impl Iterator<Item = (isize, pigeons::Axiom<&'slf str>)> {
        self.terms
            .iter()
            .map(|(cf, neg, v)| (*cf, (*v).axiom(*neg)))
    }

    fn offset(&self) -> isize {
        self.offset
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

fn verify_output<P1: AsRef<Path>, P2: AsRef<Path>, P3: AsRef<Path>>(
    instance: P1,
    proof: P2,
    output: P3,
) {
    if let Ok(veripb) = std::env::var("VERIPB_CHECKER") {
        println!("start checking proof");
        let out = Command::new(veripb)
            .arg(instance.as_ref())
            .arg(proof.as_ref())
            .arg(output.as_ref())
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
            &OutputGuarantee::None,
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
        .implied(&Constr::parse("1 x1 2 x2 4 x3 >= 3"), None)
        .unwrap();
    proof
        .implied_add(&Constr::parse("1 x1 2 x2 4 x3 >= 3"), Some(Id::abs(1)))
        .unwrap();
    proof
        .equals(&Constr::parse("1 x1 2 x2 4 x3 >= 3"), Some(Id::last(1)))
        .unwrap();
    proof
        .equals(&Constr::parse("1 x1 2 x2 4 x3 >= 3"), None)
        .unwrap();
    #[cfg(feature = "version2")]
    proof
        .equals_add(&Constr::parse("1 x1 2 x2 4 x3 >= 3"), Some(Id::last(1)))
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
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
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
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
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
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
        .proof_by_contradiction(
            &Constr::parse("1 ~x3 2 x4 2 x5 2 x6 >= 4"),
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
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
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
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::Unsat(Some(id.into())))
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
            &OutputGuarantee::None,
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
            &OutputGuarantee::None,
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

#[test]
fn deletion_multiple() {
    let mut proof = new_proof(0, false);
    let a = proof
        .redundant(
            &Constr::parse("1 ~x1 >= 1"),
            [Substitution::from("x1".neg_axiom())],
            None,
        )
        .unwrap();
    let b = proof
        .redundant(
            &Constr::parse("1 ~x2 >= 1"),
            [Substitution::from("x2".neg_axiom())],
            None,
        )
        .unwrap();
    let c = proof
        .reverse_unit_prop(&Constr::parse("1 ~x1 >= 1"), None)
        .unwrap();
    proof
        .redundant(
            &Constr::parse("1 x1 1 x2 1 x3 1 x4 >= 2"),
            [
                Substitution::from("x3".pos_axiom()),
                Substitution::from("x4".pos_axiom()),
            ],
            None,
        )
        .unwrap();
    let e = proof
        .reverse_unit_prop(&Constr::parse("1 ~x1 >= 1"), None)
        .unwrap();
    proof
        .delete_ids::<&'static str, Constr, _, _>([a.into(), b.into(), c.into(), e.into()], None)
        .unwrap();
    proof
        .reverse_unit_prop(&Constr::parse("2 x1 2 x2 1 x3 1 x4 >= 2"), None)
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path())
}

#[test]
fn deletion_range() {
    let mut proof = new_proof(0, false);
    let a = proof
        .redundant(
            &Constr::parse("1 ~x1 >= 1"),
            [Substitution::from("x1".neg_axiom())],
            None,
        )
        .unwrap();
    proof
        .redundant(
            &Constr::parse("1 ~x2 >= 1"),
            [Substitution::from("x2".neg_axiom())],
            None,
        )
        .unwrap();
    proof
        .reverse_unit_prop(&Constr::parse("1 ~x1 >= 1"), [a.into()])
        .unwrap();
    proof
        .redundant(
            &Constr::parse("1 x1 1 x2 1 x3 1 x4 >= 2"),
            [
                Substitution::from("x3".pos_axiom()),
                Substitution::from("x4".pos_axiom()),
            ],
            None,
        )
        .unwrap();
    let e = proof
        .reverse_unit_prop(&Constr::parse("1 ~x1 >= 1"), None)
        .unwrap();
    proof.delete_id_range(Id::from(a)..=Id::from(e)).unwrap();
    let proof_file = proof
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path())
}

#[test]
fn deletion_multiple_derived() {
    let mut proof = new_proof(0, false);
    let a = proof
        .redundant(
            &Constr::parse("1 ~x1 >= 1"),
            [Substitution::from("x1".neg_axiom())],
            None,
        )
        .unwrap();
    let b = proof
        .redundant(
            &Constr::parse("1 ~x2 >= 1"),
            [Substitution::from("x2".neg_axiom())],
            None,
        )
        .unwrap();
    proof.delete_derived_ids([a.into(), b.into()]).unwrap();
    let proof_file = proof
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path())
}

#[test]
fn deletion_multiple_core() {
    let mut proof = new_proof(3, false);
    proof.delete_core_ids([Id::abs(2), Id::abs(3)]).unwrap();
    let proof_file = proof
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/deletion_multiple_core.opb"),
        proof_file.path(),
    )
}

#[test]
fn deletion_find() {
    let mut proof = new_proof(2, false);
    let constr = Constr::parse("2 x1 2 x2 2 ~x3 >= 3");
    let last = proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2)))
        .unwrap();
    proof.equals(&constr, Some(last.into())).unwrap();
    proof
        .delete_ids::<&'static str, Constr, _, _>([last.into()], None)
        .unwrap();
    // is_deleted 2 x1 2 x2 2 ~x3 >= 3 ;
    let last = proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2)))
        .unwrap();
    proof.equals(&constr, Some(last.into())).unwrap();
    proof.delete_constr(&constr).unwrap();
    // is_deleted 2 x1 2 x2 2 ~x3 >= 3 ;
    let a = proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2)))
        .unwrap();
    let b = proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2)))
        .unwrap();
    proof.delete_constr(&constr).unwrap();
    proof.equals(&constr, Some(Id::last(1))).unwrap();
    proof.equals(&constr, Some(Id::last(2))).unwrap();
    proof
        .delete_ids::<&'static str, Constr, _, _>([a.into(), b.into()], None)
        .unwrap();
    // is_deleted 2 x1 2 x2 2 ~x3 >= 3 ;
    proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2)))
        .unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2)))
        .unwrap();
    proof.delete_constr(&constr).unwrap();
    proof.equals(&constr, Some(Id::last(1))).unwrap();
    proof.equals(&constr, Some(Id::last(2))).unwrap();
    proof.delete_constr(&constr).unwrap();
    // is_deleted 2 x1 2 x2 2 ~x3 >= 3 ;
    proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2)))
        .unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2)))
        .unwrap();
    proof.delete_constr(&constr).unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2)))
        .unwrap();
    proof.delete_constr(&constr).unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2)))
        .unwrap();
    proof.equals(&constr, Some(Id::last(1))).unwrap();
    proof.equals(&constr, Some(Id::last(2))).unwrap();
    proof.equals(&constr, Some(Id::last(3))).unwrap();
    proof.equals(&constr, Some(Id::last(4))).unwrap();
    proof.delete_constr(&constr).unwrap();
    proof.delete_constr(&constr).unwrap();
    // is_deleted 2 x1 2 x2 2 ~x3 >= 3 ;
    let proof_file = proof
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/deletion_find.opb"),
        proof_file.path(),
    )
}

#[test]
fn objective_update_diff() {
    let mut proof = new_proof(3, true);
    proof
        .operations(&((OpsSeq::from(Id::abs(1)) + Id::abs(2) + Id::abs(3)) / 2))
        .unwrap();
    proof.move_ids_to_core([Id::last(1)]).unwrap();
    proof
        .redundant(
            &Constr::parse("3 ~y1 1 ~x1 1 ~x2 1 ~x3 >= 3"),
            ["y1".neg_axiom().into()],
            None,
        )
        .unwrap();
    proof
        .redundant(
            &Constr::parse("1 y1 1 x1 1 x2 1 x3 >= 1"),
            ["y1".pos_axiom().into()],
            None,
        )
        .unwrap();
    proof.move_ids_to_core([Id::last(1)]).unwrap();
    proof
        .operations(&((OpsSeq::from(Id::abs(4)) * 2 + Id::abs(5)) / 3))
        .unwrap();
    proof.move_ids_to_core([Id::last(1)]).unwrap();
    // obju diff 1 y1 -1 ~x1 -1 ~x2 -1 ~x3 2 ;
    proof
        .update_objective(&ObjectiveUpdate::<_, _, Constr>::diff(Obj::parse(
            "1 y1 -1 ~x1 -1 ~x2 -1 ~x3 2",
        )))
        .unwrap();
    // soli x1 ~x2 ~x3
    proof
        .improve_solution(["x1".pos_axiom(), "x2".neg_axiom(), "x3".neg_axiom()])
        .unwrap();
    // e 1 ~y1 >= 2 ; -1
    proof
        .equals(&Constr::parse("1 ~y1 >= 2"), Some(Id::last(1)))
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(
            &OutputGuarantee::None,
            &Conclusion::Bounds {
                range: 2..3,
                lb_id: None,
                ub_sol: None,
            },
        )
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/objective_update.opb"),
        proof_file.path(),
    )
}

#[test]
fn objective_update() {
    let mut proof = new_proof(3, true);
    proof
        .operations(&((OpsSeq::from(Id::abs(1)) + Id::abs(2) + Id::abs(3)) / 2))
        .unwrap();
    proof.move_ids_to_core([Id::last(1)]).unwrap();
    proof
        .redundant(
            &Constr::parse("3 ~y1 1 ~x1 1 ~x2 1 ~x3 >= 3"),
            ["y1".neg_axiom().into()],
            None,
        )
        .unwrap();
    proof
        .redundant(
            &Constr::parse("1 y1 1 x1 1 x2 1 x3 >= 1"),
            ["y1".pos_axiom().into()],
            None,
        )
        .unwrap();
    proof.move_ids_to_core([Id::last(1)]).unwrap();
    proof
        .operations(&((OpsSeq::from(Id::abs(4)) * 2 + Id::abs(5)) / 3))
        .unwrap();
    proof.move_ids_to_core([Id::last(1)]).unwrap();
    // obju diff 1 y1 -1 ~x1 -1 ~x2 -1 ~x3 2 ;
    proof
        .update_objective(&ObjectiveUpdate::<_, _, Constr>::new(
            Obj::parse("1 y1 2"),
            None,
        ))
        .unwrap();
    // soli x1 ~x2 ~x3
    proof
        .improve_solution(["x1".pos_axiom(), "x2".neg_axiom(), "x3".neg_axiom()])
        .unwrap();
    // e 1 ~y1 >= 2 ; -1
    proof
        .equals(&Constr::parse("1 ~y1 >= 2"), Some(Id::last(1)))
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(
            &OutputGuarantee::None,
            &Conclusion::Bounds {
                range: 2..3,
                lb_id: None,
                ub_sol: None,
            },
        )
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/objective_update.opb"),
        proof_file.path(),
    )
}

struct OrderConstr<'slf> {
    terms: Vec<(isize, bool, OrderVar<&'slf str>)>,
    rhs: isize,
}

impl<'slf> ConstraintLike<OrderVar<&'slf str>> for OrderConstr<'slf> {
    fn rhs(&self) -> isize {
        self.rhs
    }

    fn sum_iter(&self) -> impl Iterator<Item = (isize, pigeons::Axiom<OrderVar<&'slf str>>)> {
        self.terms
            .iter()
            .map(|(cf, neg, v)| (*cf, (*v).axiom(*neg)))
    }
}

#[test]
fn dominance_simple_order() {
    let mut proof = new_proof(10, false);
    let mut order = Order::<&'static str, OrderConstr>::new("simple".to_string());
    let (left, right) = order.use_var("x1");
    order.add_definition_constraint(
        OrderConstr {
            terms: vec![(-1, false, left), (1, false, right)],
            rhs: 0,
        },
        vec![Derivation::Operations(
            OperationSequence::from(Id::last(2)) + Id::last(3) + Id::last(1),
        )],
        None,
    );
    proof.define_order(&order).unwrap();
    proof.load_order("simple", ["x1"]).unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2)))
        .unwrap();
    proof
        .redundant(
            &Constr::parse("1 a3 1 x1 >= 1"),
            ["a3".pos_axiom().into()],
            None,
        )
        .unwrap();
    proof
        .dominated(
            &Constr::parse("1 ~x1 1 x2 >= 1"),
            [
                "x1".substitute_literal("x2".pos_axiom()),
                "x2".substitute_literal("x1".pos_axiom()),
            ],
            None,
        )
        .unwrap();
    proof.load_order::<&'static str, _>("", []).unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2)))
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/dominance_simple_order.opb"),
        proof_file.path(),
    )
}

#[test]
fn output_file() {
    let mut proof = new_proof(0, false);
    let a = proof
        .redundant(
            &Constr::parse("1 ~x1 >= 1"),
            [Substitution::from("x1".neg_axiom())],
            None,
        )
        .unwrap();
    let b = proof
        .redundant(
            &Constr::parse("1 ~x2 >= 1"),
            [Substitution::from("x2".neg_axiom())],
            None,
        )
        .unwrap();
    proof.move_ids_to_core([a.into(), b.into()]).unwrap();
    let proof_file = proof
        .conclude::<&'static str>(
            &OutputGuarantee::Derivable(OutputType::File),
            &Conclusion::None,
        )
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_output(
        format!("{manifest}/data/empty.opb"),
        proof_file.path(),
        format!("{manifest}/data/derived.opb"),
    )
}

#[test]
fn output_constraints() {
    let mut proof = new_proof(0, false);
    let constr_a = Constr::parse("1 ~x1 >= 1");
    let a = proof
        .redundant(&constr_a, [Substitution::from("x1".neg_axiom())], None)
        .unwrap();
    let constr_b = Constr::parse("1 ~x2 >= 1");
    let b = proof
        .redundant(&constr_b, [Substitution::from("x2".neg_axiom())], None)
        .unwrap();
    proof.move_ids_to_core([a.into(), b.into()]).unwrap();
    let proof_file = proof
        .conclude::<&'static str>(
            &OutputGuarantee::Derivable(OutputType::constraints(
                [constr_a, constr_b],
                Option::<Obj>::None,
            )),
            &Conclusion::None,
        )
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path())
}

#[test]
fn output_permutation() {
    let mut proof = new_proof(0, false);
    let a = proof
        .redundant(
            &Constr::parse("1 ~x1 >= 1"),
            [Substitution::from("x1".neg_axiom())],
            None,
        )
        .unwrap();
    let b = proof
        .redundant(
            &Constr::parse("1 ~x2 >= 1"),
            [Substitution::from("x2".neg_axiom())],
            None,
        )
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(
            &OutputGuarantee::Derivable(OutputType::permutation([a.into(), b.into()])),
            &Conclusion::None,
        )
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_output(
        format!("{manifest}/data/empty.opb"),
        proof_file.path(),
        format!("{manifest}/data/derived.opb"),
    )
}
