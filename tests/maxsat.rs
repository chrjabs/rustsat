use rustsat::{algs::maxsat, encodings::pb, instances::OptInstance};

#[test]
fn sis_small() {
    type Alg = maxsat::SolutionImprovingSearch<rustsat_minisat::core::Minisat, pb::DbGte>;
    let inst: OptInstance = OptInstance::from_dimacs_path("./data/inc-sis-fails.wcnf").unwrap();
    let sol = inst.solve_maxsat::<Alg>();
    dbg!(&sol);
    assert!(matches!(sol, Some((_, 8632))));
}

#[test]
fn sis() {
    type Alg = maxsat::SolutionImprovingSearch<rustsat_minisat::core::Minisat, pb::DbGte>;
    let inst: OptInstance =
        OptInstance::from_dimacs_path("./data/auctions_wt-cat_sched_60_70_0003.txt.wcnf").unwrap();
    let sol = inst.solve_maxsat::<Alg>();
    dbg!(&sol);
    assert!(matches!(sol, Some((_, 61169))));
}
