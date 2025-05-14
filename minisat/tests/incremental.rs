mod core {
    rustsat_solvertests::incremental_tests!(rustsat_minisat::core::Minisat);
}

mod simp {
    rustsat_solvertests::incremental_tests!({
        let mut solver = rustsat_minisat::simp::Minisat::default();
        for i in 0..4 {
            rustsat::solvers::FreezeVar::freeze_var(&mut solver, rustsat::types::Var::new(i))
                .unwrap();
        }
        solver
    });
}
