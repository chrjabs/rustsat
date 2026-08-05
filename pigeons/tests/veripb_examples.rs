//! # Integration Tests Copied from VeriPB

use std::io::BufRead;

use pigeons::Conclusion;
use pigeons::ConstraintId as Id;
use pigeons::ConstraintLike;
use pigeons::ObjectiveLike;
use pigeons::ObjectiveUpdate;
use pigeons::OperationLike;
use pigeons::OperationSequence;
use pigeons::OutputGuarantee;
use pigeons::OutputType;
use pigeons::Proof;
use pigeons::ProofGoalId;
use pigeons::Substitution;
use pigeons::VarLike;

type OpsSeq = OperationSequence<&'static str>;

struct Constr<V: VarLike = &'static str> {
    terms: Vec<(isize, bool, V)>,
    rhs: isize,
}

macro_rules! c {
    ($($coeff:literal $neg:literal $var:expr),* ; $rhs:literal) => {
        Constr {
            terms: vec![$(($coeff, $neg, $var),)*],
            rhs: $rhs,
        }
    };
    ($($rneg:literal $rvar:literal),+ ==> $($coeff:literal $neg:literal $var:expr),* ; $rhs:literal) => {
        pigeons::reified!($({$rvar.axiom($rneg)}),+ ==> c!($($coeff $neg $var),* ; $rhs))
    };
    ($rneg:literal $rvar:literal <== $($coeff:literal $neg:literal $var:expr),* ; $rhs:literal) => {
        pigeons::reified!({$rvar.axiom($rneg)} <== c!($($coeff $neg $var),* ; $rhs))
    };
    ($opb:literal) => {Constr::parse($opb)}
}

impl<'slf> Constr<&'slf str> {
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

impl<V: VarLike> ConstraintLike for Constr<V> {
    type Var = V;

    fn rhs(&self) -> isize {
        self.rhs
    }

    fn sum_iter(&self) -> impl Iterator<Item = (isize, pigeons::Axiom<V>)> {
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

impl<'slf> ObjectiveLike for Obj<'slf> {
    type Var = &'slf str;

    fn sum_iter(&self) -> impl Iterator<Item = (isize, pigeons::Axiom<&'slf str>)> {
        self.terms
            .iter()
            .map(|(cf, neg, v)| (*cf, (*v).axiom(*neg)))
    }

    fn offset(&self) -> isize {
        self.offset
    }
}

fn print_file<P: AsRef<std::path::Path>>(path: P) {
    for line in
        std::io::BufReader::new(std::fs::File::open(path).expect("could not open file")).lines()
    {
        println!("{}", line.unwrap());
    }
}

fn verify_proof<P1: AsRef<std::path::Path>, P2: AsRef<std::path::Path>>(instance: P1, proof: P2) {
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
    } else {
        println!("`$VERIPB_CHECKER` not set, omitting proof checking");
    }
}

fn verify_output<P1, P2, P3>(instance: P1, proof: P2, output: P3)
where
    P1: AsRef<std::path::Path>,
    P2: AsRef<std::path::Path>,
    P3: AsRef<std::path::Path>,
{
    if let Ok(veripb) = std::env::var("VERIPB_CHECKER") {
        println!("start checking proof");
        let out = std::process::Command::new(veripb)
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
        .implied(&c!("1 x1 2 x2 4 x3 >= 3"), Some(Id::abs(1)))
        .unwrap();
    proof.implied(&c!("1 x1 2 x2 4 x3 >= 3"), None).unwrap();
    proof
        .implied_add(&c!("1 x1 2 x2 4 x3 >= 3"), Some(Id::abs(1)))
        .unwrap();
    proof
        .equals(&c!("1 x1 2 x2 4 x3 >= 3"), Some(Id::last(1)))
        .unwrap();
    proof.equals(&c!("1 x1 2 x2 4 x3 >= 3"), None).unwrap();
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
        &c!("-1 x0_0 -1 x1_0 -1 x2_0 -1 x3_0 -1 x4_0 -1 x5_0 -1 x6_0 -1 x7_0 -1 x8_0 -1 x9_0 >= -1"),
        [],
    ).unwrap().finish().unwrap();
    let b = proof
        .redundant(
            &c!("1 ~x0_0 1 x9_1 1 x9_2 1 x9_3 1 x9_4 1 x9_5 1 x9_6 1 x9_7 1 x9_8 1 x9_9 1 x9_10 >= 1"),
            [],
        )
        .unwrap().finish().unwrap();
    let c = proof
        .redundant(&c!("1 ~x9_1 1 x1_0 1 x1_2 1 x1_10 >= 1"), [])
        .unwrap()
        .finish()
        .unwrap();
    let d = proof
        .redundant(&c!("1 ~x9_2 1 x1_0 1 x1_1 1 x1_3 >= 1"), [])
        .unwrap()
        .finish()
        .unwrap();
    let e = proof
        .redundant(&c!("1 ~x9_3 1 x1_0 1 x1_2 1 x1_4 >= 1"), [])
        .unwrap()
        .finish()
        .unwrap();
    let f = proof
        .redundant(&c!("1 ~x9_4 1 x1_0 1 x1_3 1 x1_5 >= 1"), [])
        .unwrap()
        .finish()
        .unwrap();
    let g = proof
        .redundant(&c!("1 ~x9_5 1 x1_0 1 x1_4 1 x1_6 >= 1"), [])
        .unwrap()
        .finish()
        .unwrap();
    let h = proof
        .redundant(&c!("1 ~x9_6 1 x1_0 1 x1_5 1 x1_7 >= 1"), [])
        .unwrap()
        .finish()
        .unwrap();
    let i = proof
        .redundant(&c!("1 ~x9_7 1 x1_0 1 x1_6 1 x1_8 >= 1"), [])
        .unwrap()
        .finish()
        .unwrap();
    let j = proof
        .redundant(&c!("1 ~x9_8 1 x1_0 1 x1_7 1 x1_9 >= 1"), [])
        .unwrap()
        .finish()
        .unwrap();
    let k = proof
        .redundant(&c!("1 ~x9_9 1 x1_0 1 x1_8 1 x1_10 >= 1"), [])
        .unwrap()
        .finish()
        .unwrap();
    let l = proof
        .redundant(&c!("1 ~x9_10 1 x1_0 1 x1_1 1 x1_9 >= 1"), [])
        .unwrap()
        .finish()
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
    proof.implied_add(&c!("1 ~x0_0 1 x1_0 1 x1_1 1 x1_2 1 x1_3 1 x1_4 1 x1_5 1 x1_6 1 x1_7 1 x1_8 1 x1_9 1 x1_10 >= 1"), Some(Id::from(sum))).unwrap();
    let sum2 = proof
        .operations(&(OpsSeq::from(sum) + a).saturate())
        .unwrap();
    let implied = proof
        .implied_add(
            &c!("1 ~x0_0 1 x1_1 1 x1_2 1 x1_3 1 x1_4 1 x1_5 1 x1_6 1 x1_7 1 x1_8 1 x1_9 1 x1_10 >= 1"),
            Some(Id::from(sum2)),
        )
        .unwrap();
    proof.set_level(0).unwrap();
    proof
        .implied_add(
            &c!("1 ~x0_0 1 x1_1 1 x1_2 1 x1_3 1 x1_4 1 x1_5 1 x1_6 1 x1_7 1 x1_8 1 x1_9 1 x1_10 >= 1"),
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
        .redundant(&c!("1 x3 >= 1"), ["x3".substitute_fixed(true)])
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
    let mut subproof = proof
        .proof_by_contradiction(&c!("1 ~x3 2 x4 2 x5 2 x6 >= 4"))
        .unwrap();
    subproof
        .operations(&(OpsSeq::from(Id::abs(3)) * 1 + OpsSeq::from(Id::abs(4)) * 1 + Id::last(1)))
        .unwrap();
    subproof.finish().unwrap();
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
    let mut subproof = proof
        .redundant(
            &c!("1 x1 >= 1"),
            [
                "x1".substitute_literal("x3".pos_axiom()),
                "x3".substitute_literal("x5".pos_axiom()),
                "x5".substitute_literal("x1".pos_axiom()),
                "x2".substitute_literal("x4".pos_axiom()),
                "x4".substitute_literal("x6".pos_axiom()),
                "x6".substitute_literal("x2".pos_axiom()),
            ],
        )
        .unwrap();
    let mut subsubproof = subproof.proof_goal(ProofGoalId::specific(1)).unwrap();
    subsubproof
        .operations(&(OpsSeq::from(Id::last(1)) + Id::last(2) + Id::abs(5) + Id::abs(6)))
        .unwrap();
    subsubproof
        .operations(&(OpsSeq::from(Id::last(1)) + Id::abs(4)))
        .unwrap();
    subsubproof
        .operations(&(OpsSeq::from(Id::last(1)) + "x6".pos_axiom()))
        .unwrap();
    subsubproof.finish().unwrap();
    let mut subsubproof = subproof.proof_goal(ProofGoalId::from(Id::abs(1))).unwrap();
    subsubproof
        .operations(&(OpsSeq::from(Id::last(1)) + Id::abs(2)))
        .unwrap();
    subsubproof.finish().unwrap();
    subproof.finish().unwrap();
    let id = proof.reverse_unit_prop(&c!(">= 1"), None).unwrap();
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
        .equals(&c!("1 x1 +1 x3 >= 1"), Some(proof.first_proof_id().into()))
        .unwrap();
    let next_id = proof.next_id();
    proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2) + Id::abs(6)))
        .unwrap();
    proof
        .equals(&c!("+2 x1 +2 x2 +2 x3 >= 3"), Some(next_id.into()))
        .unwrap();
    proof
        .operations(&((OpsSeq::from(Id::abs(1)) + Id::abs(2) + Id::abs(6)) / 2))
        .unwrap();
    proof
        .equals(&c!("1 x1 1 x2 1 x3 >= 2"), Some(Id::abs(8)))
        .unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(5)) * 2 + OpsSeq::from(Id::abs(8)) * 2))
        .unwrap();
    proof.equals(&c!(">= 2"), Some(Id::abs(9))).unwrap();
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
        .equals(&c!("-2 ~x1 -2 ~x2 -2 ~x3 >= -3"), Some(Id::abs(5)))
        .unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(4)) * 2 + Id::abs(5)))
        .unwrap();
    proof
        .reverse_unit_prop(&c!("2 ~x3 2 ~x2 2 ~x1 >= 4"), None)
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
        .redundant(&c!("1 ~x1 >= 1"), [Substitution::from("x1".neg_axiom())])
        .unwrap()
        .finish()
        .unwrap();
    let b = proof
        .redundant(&c!("1 ~x2 >= 1"), [Substitution::from("x2".neg_axiom())])
        .unwrap()
        .finish()
        .unwrap();
    let c = proof.reverse_unit_prop(&c!("1 ~x1 >= 1"), None).unwrap();
    proof
        .redundant(
            &c!("1 x1 1 x2 1 x3 1 x4 >= 2"),
            [
                Substitution::from("x3".pos_axiom()),
                Substitution::from("x4".pos_axiom()),
            ],
        )
        .unwrap()
        .finish()
        .unwrap();
    let e = proof.reverse_unit_prop(&c!("1 ~x1 >= 1"), None).unwrap();
    proof
        .delete_ids([a.into(), b.into(), c.into(), e.into()])
        .unwrap()
        .finish()
        .unwrap();
    proof
        .reverse_unit_prop(&c!("2 x1 2 x2 1 x3 1 x4 >= 2"), None)
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
        .redundant(&c!("1 ~x1 >= 1"), [Substitution::from("x1".neg_axiom())])
        .unwrap()
        .finish()
        .unwrap();
    proof
        .redundant(&c!("1 ~x2 >= 1"), [Substitution::from("x2".neg_axiom())])
        .unwrap()
        .finish()
        .unwrap();
    proof
        .reverse_unit_prop(&c!("1 ~x1 >= 1"), [a.into()])
        .unwrap();
    proof
        .redundant(
            &c!("1 x1 1 x2 1 x3 1 x4 >= 2"),
            [
                Substitution::from("x3".pos_axiom()),
                Substitution::from("x4".pos_axiom()),
            ],
        )
        .unwrap()
        .finish()
        .unwrap();
    let e = proof.reverse_unit_prop(&c!("1 ~x1 >= 1"), None).unwrap();
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
        .redundant(&c!("1 ~x1 >= 1"), [Substitution::from("x1".neg_axiom())])
        .unwrap()
        .finish()
        .unwrap();
    let b = proof
        .redundant(&c!("1 ~x2 >= 1"), [Substitution::from("x2".neg_axiom())])
        .unwrap()
        .finish()
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
    let constr = c!("2 x1 2 x2 2 ~x3 >= 3");
    let last = proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2)))
        .unwrap();
    proof.equals(&constr, Some(last.into())).unwrap();
    proof.delete_ids([last.into()]).unwrap().finish().unwrap();
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
        .delete_ids([a.into(), b.into()])
        .unwrap()
        .finish()
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
            &c!("3 ~y1 1 ~x1 1 ~x2 1 ~x3 >= 3"),
            ["y1".neg_axiom().into()],
        )
        .unwrap()
        .finish()
        .unwrap();
    proof
        .redundant(&c!("1 y1 1 x1 1 x2 1 x3 >= 1"), ["y1".pos_axiom().into()])
        .unwrap()
        .finish()
        .unwrap();
    proof.move_ids_to_core([Id::last(1)]).unwrap();
    proof
        .operations(&((OpsSeq::from(Id::abs(4)) * 2 + Id::abs(5)) / 3))
        .unwrap();
    proof.move_ids_to_core([Id::last(1)]).unwrap();
    // obju diff 1 y1 -1 ~x1 -1 ~x2 -1 ~x3 2 ;
    proof
        .update_objective(&ObjectiveUpdate::diff(Obj::parse(
            "1 y1 -1 ~x1 -1 ~x2 -1 ~x3 2",
        )))
        .unwrap()
        .finish()
        .unwrap();
    // soli x1 ~x2 ~x3
    proof
        .improve_solution(["x1".pos_axiom(), "x2".neg_axiom(), "x3".neg_axiom()])
        .unwrap();
    // e 1 ~y1 >= 2 ; -1
    proof.equals(&c!("1 ~y1 >= 2"), Some(Id::last(1))).unwrap();
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
            &c!("3 ~y1 1 ~x1 1 ~x2 1 ~x3 >= 3"),
            ["y1".neg_axiom().into()],
        )
        .unwrap()
        .finish()
        .unwrap();
    proof
        .redundant(&c!("1 y1 1 x1 1 x2 1 x3 >= 1"), ["y1".pos_axiom().into()])
        .unwrap()
        .finish()
        .unwrap();
    proof.move_ids_to_core([Id::last(1)]).unwrap();
    proof
        .operations(&((OpsSeq::from(Id::abs(4)) * 2 + Id::abs(5)) / 3))
        .unwrap();
    proof.move_ids_to_core([Id::last(1)]).unwrap();
    // obju diff 1 y1 -1 ~x1 -1 ~x2 -1 ~x3 2 ;
    proof
        .update_objective(&ObjectiveUpdate::new(Obj::parse("1 y1 2")))
        .unwrap()
        .finish()
        .unwrap();
    // soli x1 ~x2 ~x3
    proof
        .improve_solution(["x1".pos_axiom(), "x2".neg_axiom(), "x3".neg_axiom()])
        .unwrap();
    // e 1 ~y1 >= 2 ; -1
    proof.equals(&c!("1 ~y1 >= 2"), Some(Id::last(1))).unwrap();
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
fn dominance_simple_order() {
    let mut proof = new_proof(10, false);

    let mut order = proof.define_order("simple").unwrap();
    let ovar = order.add_input_var("x1");
    let mut order = order.definition().unwrap();
    let goal = order
        .definition_constraint(&c!(-1 false ovar.left(), 1 false ovar.right(); 0))
        .unwrap();
    let mut order = order.transitivity_proof().unwrap();
    let mut goal = order.proof_goal(goal).unwrap();
    let negated_constraint = goal.negated_constraint_id();
    goal.operations(&(OpsSeq::from(Id::last(2)) + Id::last(3) + negated_constraint))
        .unwrap();
    goal.finish().unwrap();
    let order = order.finish().unwrap();
    proof.load_order(&order, ["x1"]).unwrap();

    proof
        .operations(&(OpsSeq::from(Id::abs(1)) + Id::abs(2)))
        .unwrap();
    proof
        .redundant(&c!("1 a3 1 x1 >= 1"), ["a3".pos_axiom().into()])
        .unwrap()
        .finish()
        .unwrap();
    proof
        .dominated(
            &c!("1 ~x1 1 x2 >= 1"),
            [
                "x1".substitute_literal("x2".pos_axiom()),
                "x2".substitute_literal("x1".pos_axiom()),
            ],
        )
        .unwrap()
        .finish()
        .unwrap();
    proof.unload_order().unwrap();
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
fn delete_core_subproof_proofgoal() {
    let mut proof = new_proof(3, false);
    let mut subproof = proof.delete_ids([Id::abs(2)]).unwrap();
    subproof
        .operations(&(OpsSeq::from(Id::last(1)) + Id::abs(1) + OpsSeq::from(Id::abs(3)) * 2))
        .unwrap();
    subproof.finish().unwrap();
    proof.is_deleted(&c!("1 x1 1 x2 2 ~x3 >= 2")).unwrap();
    let proof_file = proof
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
        .unwrap();

    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/delete_core_subproof_proofgoal.opb"),
        proof_file.path(),
    )
}

#[test]
fn variable_form_division() {
    let mut proof = new_proof(4, false);
    proof
        .operations(&(OpsSeq::from(Id::abs(1)).variable_form_division(3)))
        .unwrap();
    proof
        .equals(&c!("-1 x3 -1 x4 >= -1"), Some(Id::last(1)))
        .unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(3)).variable_form_division(2)))
        .unwrap();
    proof.equals(&c!(">= -1"), Some(Id::last(1))).unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(4)).variable_form_division(2)))
        .unwrap();
    proof.equals(&c!(">= 0"), Some(Id::last(1))).unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(2)) + Id::abs(5)))
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(
            &OutputGuarantee::None,
            &Conclusion::Unsat(Some(Id::last(1))),
        )
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/variable_form_division.opb"),
        proof_file.path(),
    );
}

#[test]
fn normalized_mir_cut() {
    let mut proof = new_proof(4, false);
    proof
        .operations(&(OpsSeq::from(Id::abs(1)).normalized_form_mir_cut(3)))
        .unwrap();
    proof
        .equals(&c!("1 ~x1 2 x2 2 ~x3 3 x4 >= 4"), Some(Id::last(1)))
        .unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(2)) + Id::last(1)))
        .unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(3)).normalized_form_mir_cut(2)))
        .unwrap();
    proof
        .equals(&c!("1 ~x1 1 x2 1 x3 >= 1"), Some(Id::last(1)))
        .unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(4)).normalized_form_mir_cut(2)))
        .unwrap();
    proof
        .equals(&c!("1 ~x1 1 x2 1 x3 1 x5 >= 2"), Some(Id::last(1)))
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::Unsat(Some(Id::abs(6))))
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/normalized_mir_cut.opb"),
        proof_file.path(),
    );
}

#[test]
fn variable_form_mir_cut() {
    let mut proof = new_proof(4, false);
    proof
        .operations(&(OpsSeq::from(Id::abs(1)).variable_form_mir_cut(3)))
        .unwrap();
    proof
        .equals(&c!("1 x1 -1 x2 -2 x3 3 x4 >= 2"), Some(Id::last(1)))
        .unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(2)) + Id::last(1)))
        .unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(3)).variable_form_mir_cut(2)))
        .unwrap();
    proof.equals(&c!("1 x3 >= 0"), Some(Id::last(1))).unwrap();
    proof
        .operations(&(OpsSeq::from(Id::abs(4)).variable_form_mir_cut(2)))
        .unwrap();
    proof
        .equals(&c!("1 x2 1 x5 >= 1"), Some(Id::last(1)))
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::Unsat(Some(Id::abs(6))))
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/variable_form_mir_cut.opb"),
        proof_file.path(),
    );
}

#[test]
fn lower_rhs() {
    let mut proof = new_proof(1, false);
    proof.operations(&(OpsSeq::from(Id::abs(1)) - 5)).unwrap();
    proof
        .equals(&c!("1 x1 3 x2 5 x3 >= 3"), Some(Id::last(1)))
        .unwrap();
    proof.operations(&(OpsSeq::from(Id::abs(2)) - 5)).unwrap();
    proof
        .equals(&c!("1 x1 3 x2 5 x3 >= -2"), Some(Id::last(1)))
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(format!("{manifest}/data/lower_rhs.opb"), proof_file.path());
}

#[test]
#[should_panic]
fn fail() {
    let mut proof = new_proof(0, false);
    proof.fail_checking().unwrap();
    let proof_file = proof
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
}

#[test]
fn dominance_with_aux_vars() {
    let mut proof = new_proof(1, false);
    let mut order = proof.define_order("lex").unwrap();

    let x_s = [
        order.add_input_var("x1"),
        order.add_input_var("x2"),
        order.add_input_var("x3"),
        order.add_input_var("x4"),
        order.add_input_var("x5"),
    ];
    let a_s: Vec<_> = (1..=4).map(|idx| format!("a{idx}")).collect();
    let a_s: Vec<_> = a_s
        .iter()
        .map(|name| order.add_aux_var(name.as_str()))
        .collect();
    let d_s: Vec<_> = (1..=5).map(|idx| format!("d{idx}")).collect();
    let d_s: Vec<_> = d_s
        .iter()
        .map(|name| order.add_aux_var(name.as_str()))
        .collect();

    let mut spec = order.specification().unwrap();
    spec.redundant(
        &c![1 true a_s[0].aux(), 1 false x_s[0].left(), 1 true x_s[0].right(); 1],
        [a_s[0].aux().substitute_fixed(false)],
    )
    .unwrap()
    .finish()
    .unwrap();
    spec.redundant(
        &c![2 false a_s[0].aux(), 1 true x_s[0].left(), 1 false x_s[0].right(); 2],
        [a_s[0].aux().substitute_fixed(true)],
    )
    .unwrap()
    .finish()
    .unwrap();

    for idx in 2..=4 {
        spec.redundant(
            &c![3 true a_s[idx-1].aux(), 2 false a_s[idx-2].aux(), 1 false
            x_s[idx-1].left(), 1 true x_s[idx-1].right(); 3],
            [a_s[idx - 1].aux().substitute_fixed(false)],
        )
        .unwrap()
        .finish()
        .unwrap();
        spec.redundant(
            &c![2 false a_s[idx-1].aux(), 2 true a_s[idx-2].aux(), 1 true
            x_s[idx-1].left(), 1 false x_s[idx-1].right(); 2],
            [a_s[idx - 1].aux().substitute_fixed(true)],
        )
        .unwrap()
        .finish()
        .unwrap();
    }

    spec.redundant(
        &c![1 true d_s[0].aux(), 1 true x_s[0].left(), 1 false x_s[0].right();
        1],
        [d_s[0].aux().substitute_fixed(false)],
    )
    .unwrap()
    .finish()
    .unwrap();
    spec.redundant(
        &c![2 false d_s[0].aux(), 1 false x_s[0].left(), 1 true x_s[0].right();
        2],
        [d_s[0].aux().substitute_fixed(true)],
    )
    .unwrap()
    .finish()
    .unwrap();

    for idx in 2..=5 {
        spec.redundant(
            &c![4 true d_s[idx-1].aux(), 3 false d_s[idx-2].aux(), 1 true
            a_s[idx-2].aux(), 1 true x_s[idx-1].left(), 1 false x_s[idx-1].right(); 4],
            [d_s[idx - 1].aux().substitute_fixed(false)],
        )
        .unwrap()
        .finish()
        .unwrap();
        spec.redundant(
            &c![3 false d_s[idx-1].aux(), 3 true d_s[idx-2].aux(), 1 false
            a_s[idx-2].aux(), 1 false x_s[idx-1].left(), 1 true x_s[idx-1].right(); 3],
            [d_s[idx - 1].aux().substitute_fixed(true)],
        )
        .unwrap()
        .finish()
        .unwrap();
    }

    let mut def = spec.definition().unwrap();

    let pid = def
        .definition_constraint(&c![1 false d_s[4].aux(); 1])
        .unwrap();

    let mut trans_proof = def.transitivity_proof().unwrap();
    let mut tp_goal = trans_proof.proof_goal(pid).unwrap();
    tp_goal
        .operations(&(OpsSeq::from(Id::abs(55)) * 4 + Id::abs(17)))
        .unwrap();

    for idx in 0..3 {
        let d = d_s[3 - idx].aux();
        tp_goal.reverse_unit_prop(&c![1 false d; 1], None).unwrap();
        tp_goal
            .operations(&OperationSequence::from(Id::last(2)).weaken(d))
            .unwrap();
        tp_goal
            .operations(&(OpsSeq::from(Id::last(2)) * 4 + Id::abs(15 - 2 * idx)))
            .unwrap();
    }

    let d = d_s[0].aux();
    tp_goal.reverse_unit_prop(&c![1 false d; 1], None).unwrap();
    tp_goal
        .operations(&OperationSequence::from(Id::last(2)).weaken(d))
        .unwrap();
    tp_goal
        .operations(&(OpsSeq::from(Id::last(2)) + Id::abs(9)))
        .unwrap();
    tp_goal
        .operations(&(OpsSeq::from(Id::abs(56)) * 4 + Id::abs(35)))
        .unwrap();

    for idx in 0..3 {
        let d = d_s[3 - idx].fresh_1();
        tp_goal.reverse_unit_prop(&c![1 false d; 1], None).unwrap();
        tp_goal
            .operations(&OperationSequence::from(Id::last(2)).weaken(d))
            .unwrap();
        tp_goal
            .operations(&(OpsSeq::from(Id::last(2)) * 4 + Id::abs(33 - 2 * idx)))
            .unwrap();
    }

    let d = d_s[0].fresh_1();
    tp_goal.reverse_unit_prop(&c![1 false d; 1], None).unwrap();
    tp_goal
        .operations(&OperationSequence::from(Id::last(2)).weaken(d))
        .unwrap();
    tp_goal
        .operations(&(OpsSeq::from(Id::last(2)) + Id::abs(27)))
        .unwrap();
    tp_goal
        .operations(&(OpsSeq::from(Id::abs(2)) + Id::abs(37) + Id::last(1)).saturate())
        .unwrap();
    tp_goal
        .operations(&(OpsSeq::from(Id::abs(20)) + Id::abs(37) + Id::abs(70)).saturate())
        .unwrap();

    for idx in 0..3 {
        let u = x_s[idx + 1].left();
        let w = x_s[idx + 1].fresh_right();
        let c = a_s[idx].fresh_2();
        tp_goal
            .operations(
                &OperationSequence::from(Id::abs(39 + idx * 2))
                    .weaken(u)
                    .weaken(w)
                    .saturate(),
            )
            .unwrap();
        tp_goal
            .operations(&(OpsSeq::from(Id::last(1)) + Id::last(3)))
            .unwrap();
        tp_goal
            .operations(&(OpsSeq::from(Id::last(2)) + Id::last(3)))
            .unwrap();
        tp_goal
            .operations(
                &OperationSequence::from(Id::abs(39 + idx * 2))
                    .weaken(c)
                    .saturate(),
            )
            .unwrap();
        tp_goal
            .operations(
                &(OpsSeq::from(Id::last(2))
                    + Id::abs(82 - idx * 3)
                    + Id::last(1)
                    + (OpsSeq::from(Id::last(3)) * 2)
                    + Id::abs(4 + idx * 2))
                .saturate(),
            )
            .unwrap();
        tp_goal
            .operations(
                &(OpsSeq::from(Id::last(4))
                    + Id::abs(69 - idx * 3)
                    + Id::last(2)
                    + (OpsSeq::from(Id::last(3)) * 2)
                    + Id::abs(22 + idx * 2))
                .saturate(),
            )
            .unwrap();
    }

    tp_goal
        .operations(&(OpsSeq::from(Id::abs(70)) + Id::abs(83)))
        .unwrap();

    for idx in 0..4 {
        tp_goal
            .operations(&(OpsSeq::from(Id::last(1)) + Id::abs(46 + idx * 2)).saturate())
            .unwrap();
        tp_goal
            .operations(
                &((OpsSeq::from(Id::abs(69 - idx * 3))
                    + Id::abs(82 - idx * 3)
                    + Id::abs(84 + idx * 6)
                    + Id::abs(85 + idx * 6))
                .saturate()
                    + (OpsSeq::from(Id::last(1)) * 3)),
            )
            .unwrap();
    }

    tp_goal
        .operations(&(OpsSeq::from(Id::last(1)) + Id::abs(54)).saturate())
        .unwrap();
    let negated_constraint = tp_goal.negated_constraint_id();
    tp_goal
        .operations(&(OpsSeq::from(Id::last(1)) + negated_constraint))
        .unwrap();
    tp_goal.finish().unwrap();

    let mut ref_proof = trans_proof.reflexivity_proof().unwrap();
    let mut rp_goal = ref_proof.proof_goal(pid).unwrap();
    rp_goal
        .reverse_unit_prop::<Constr, _>(&c![; 1], None)
        .unwrap();
    rp_goal.finish().unwrap();

    let order = ref_proof.finish().unwrap();

    proof
        .load_order(&order, ["x1", "x2", "x3", "x4", "x5"])
        .unwrap();

    let mut subproof = proof
        .dominated(
            &c!(1 false "x5"; 1),
            [
                "x5".substitute_fixed(true),
                "x4".substitute_literal("x3".pos_axiom()),
                "x3".substitute_literal("x2".pos_axiom()),
                "x2".substitute_literal("x1".pos_axiom()),
                "x1".substitute_literal("x5".pos_axiom()),
            ],
        )
        .unwrap();
    let mut leq_scope = subproof.leq_scope().unwrap();
    let mut goal = leq_scope.proof_goal(ProofGoalId::specific(1)).unwrap();
    let neg_constr = goal.negated_constraint_id();
    goal.reverse_unit_prop(
        &c![1 true "x1"; 1],
        [
            Id::abs(2),
            Id::abs(3),
            Id::abs(5),
            Id::abs(7),
            Id::abs(9),
            Id::abs(12),
            Id::abs(14),
            Id::abs(16),
            Id::abs(18),
            Id::abs(20),
            neg_constr.into(),
        ],
    )
    .unwrap();
    goal.reverse_unit_prop(&c![1 true "x2"; 1], None).unwrap();
    goal.reverse_unit_prop(&c![1 true "x3"; 1], None).unwrap();
    goal.reverse_unit_prop(&c![1 true "x4"; 1], None).unwrap();
    goal.reverse_unit_prop::<Constr, _>(&c![;1], None).unwrap();
    goal.finish().unwrap();
    leq_scope.finish().unwrap();
    let mut geq_scope = subproof.geq_scope().unwrap();
    let mut goal = geq_scope.proof_goal(ProofGoalId::specific(2)).unwrap();
    goal.reverse_unit_prop::<Constr, _>(&c![;1], None).unwrap();
    goal.finish().unwrap();
    geq_scope.finish().unwrap();
    subproof.finish().unwrap();

    let proof_file = proof
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(
        format!("{manifest}/data/dominance_with_aux_vars.opb"),
        proof_file.path(),
    );
}

#[test]
fn implication_parsing() {
    let mut proof = new_proof(0, true);
    proof
        .redundant(
            &c!(false "x1" ==> 1 false "x2", 2 false "x3" ; 3),
            ["x1".neg_axiom().into()],
        )
        .unwrap()
        .finish()
        .unwrap();
    proof
        .redundant(
            &c!(false "x1" <== 1 false "x2", 2 false "x3" ; 3),
            ["x1".pos_axiom().into()],
        )
        .unwrap()
        .finish()
        .unwrap();
    let proof_file = proof
        .conclude::<&'static str>(&OutputGuarantee::None, &Conclusion::None)
        .unwrap();
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
}

#[test]
fn output_file() {
    let mut proof = new_proof(0, false);
    let a = proof
        .redundant(&c!("1 ~x1 >= 1"), [Substitution::from("x1".neg_axiom())])
        .unwrap()
        .finish()
        .unwrap();
    let b = proof
        .redundant(&c!("1 ~x2 >= 1"), [Substitution::from("x2".neg_axiom())])
        .unwrap()
        .finish()
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

// Not yet implemented in checker
// #[test]
// fn output_constraints() {
//     let mut proof = new_proof(0, false);
//     let constr_a = c!("1 ~x1 >= 1");
//     let a = proof
//         .redundant(&constr_a, [Substitution::from("x1".neg_axiom())], None)
//         .unwrap();
//     let constr_b = c!("1 ~x2 >= 1");
//     let b = proof
//         .redundant(&constr_b, [Substitution::from("x2".neg_axiom())], None)
//         .unwrap();
//     proof.move_ids_to_core([a.into(), b.into()]).unwrap();
//     let proof_file = proof
//         .conclude::<&'static str>(
//             &OutputGuarantee::Derivable(OutputType::constraints(
//                 [constr_a, constr_b],
//                 Option::<Obj>::None,
//             )),
//             &Conclusion::None,
//         )
//         .unwrap();
//     let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
//     verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path())
// }

// Not yet implemented in checker
// #[test]
// fn output_permutation() {
//     let mut proof = new_proof(0, false);
//     let a = proof
//         .redundant(
//             &c!("1 ~x1 >= 1"),
//             [Substitution::from("x1".neg_axiom())],
//             None,
//         )
//         .unwrap();
//     let b = proof
//         .redundant(
//             &c!("1 ~x2 >= 1"),
//             [Substitution::from("x2".neg_axiom())],
//             None,
//         )
//         .unwrap();
//     let proof_file = proof
//         .conclude::<&'static str>(
//             &OutputGuarantee::Derivable(OutputType::permutation([a.into(), b.into()])),
//             &Conclusion::None,
//         )
//         .unwrap();
//     let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
//     verify_output(
//         format!("{manifest}/data/empty.opb"),
//         proof_file.path(),
//         format!("{manifest}/data/derived.opb"),
//     )
// }
