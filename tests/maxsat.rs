use rustsat::instances::OptInstance;

#[test]
fn sis() {
    let inst: OptInstance = OptInstance::from_dimacs_path("./data/inc-sis-fails.wcnf").unwrap();
    let sol = inst
        .solution_improving_search::<rustsat_minisat::core::Minisat, rustsat::encodings::pb::DbGte>(
        );
    dbg!(&sol);
    assert!(matches!(sol, Some((_, 8632))));
}
