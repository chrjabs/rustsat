use rustsat::{algs::maxsat, encodings::pb, instances::OptInstance};

#[test]
fn sis_small_gte() {
    type Alg =
        maxsat::SolutionImprovingSearch<rustsat_minisat::core::Minisat, pb::GeneralizedTotalizer>;
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let inst: OptInstance =
        OptInstance::from_dimacs_path(format!("{manifest}/data/inc-sis-fails.wcnf")).unwrap();
    let sol = inst.solve_maxsat::<Alg>();
    dbg!(&sol);
    assert!(matches!(sol, Some((_, 8632))));
}

#[test]
fn sis_gte() {
    type Alg =
        maxsat::SolutionImprovingSearch<rustsat_minisat::core::Minisat, pb::GeneralizedTotalizer>;
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let inst: OptInstance = OptInstance::from_dimacs_path(format!(
        "{manifest}/data/auctions_wt-cat_sched_60_70_0003.txt.wcnf"
    ))
    .unwrap();
    let sol = inst.solve_maxsat::<Alg>();
    dbg!(&sol);
    assert!(matches!(sol, Some((_, 61169))));
}

#[test]
fn sis_small_adder() {
    type Alg = maxsat::SolutionImprovingSearch<rustsat_minisat::core::Minisat, pb::BinaryAdder>;
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let inst: OptInstance =
        OptInstance::from_dimacs_path(format!("{manifest}/data/inc-sis-fails.wcnf")).unwrap();
    let sol = inst.solve_maxsat::<Alg>();
    dbg!(&sol);
    assert!(matches!(sol, Some((_, 8632))));
}

#[test]
fn sis_adder() {
    type Alg = maxsat::SolutionImprovingSearch<rustsat_minisat::core::Minisat, pb::BinaryAdder>;
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let inst: OptInstance = OptInstance::from_dimacs_path(format!(
        "{manifest}/data/auctions_wt-cat_sched_60_70_0003.txt.wcnf"
    ))
    .unwrap();
    let sol = inst.solve_maxsat::<Alg>();
    dbg!(&sol);
    assert!(matches!(sol, Some((_, 61169))));
}
