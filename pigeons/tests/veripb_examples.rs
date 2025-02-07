//! # Integration Tests Copied from VeriPB

use std::{
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
    process::Command,
};

use pigeons::{
    Conclusion, ConstraintId as Id, ConstraintLike, OperationLike, OperationSequence,
    OutputGuarantee, Proof, VarLike,
};

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
        .operations(
            &(OperationSequence::<&'static str>::from(Id::abs(3)) + Id::abs(4) + Id::abs(5)),
        )
        .unwrap();
    let new2 = proof
        .operations(
            &(OperationSequence::<&'static str>::from(Id::abs(14))
                + Id::abs(15)
                + "y_x1_8".pos_axiom()
                + "y_x2_8".pos_axiom()
                + "y_x1_9".pos_axiom()
                + "y_x2_9".pos_axiom()),
        )
        .unwrap();
    let contrad = proof
        .operations(&(OperationSequence::<&'static str>::from(new1) + new2))
        .unwrap();
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
        .implied_add(&Constr::parse("1 x1 2 x2 4 x3 >= 3"), Some(Id::abs(1)))
        .unwrap();
    proof
        .equals(&Constr::parse("1 x1 2 x2 4 x3 >= 3"), Some(Id::last(1)))
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
                .fold(OperationSequence::<&'static str>::from(b), |seq, id| {
                    seq + id
                })
                .saturate(),
        )
        .unwrap();
    proof.implied_add(&Constr::parse("1 ~x0_0 1 x1_0 1 x1_1 1 x1_2 1 x1_3 1 x1_4 1 x1_5 1 x1_6 1 x1_7 1 x1_8 1 x1_9 1 x1_10 >= 1"), Some(Id::from(sum))).unwrap();
    let sum2 = proof
        .operations(&(OperationSequence::<&'static str>::from(sum) + a).saturate())
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
