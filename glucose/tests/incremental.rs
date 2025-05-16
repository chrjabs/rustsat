mod core {
    rustsat_solvertests::incremental_tests!(rustsat_glucose::core::Glucose);
}

mod simp {
    rustsat_solvertests::incremental_tests!({
        let mut solver = rustsat_glucose::simp::Glucose::default();
        for i in 0..4 {
            rustsat::solvers::FreezeVar::freeze_var(&mut solver, rustsat::types::Var::new(i))
                .unwrap();
        }
        solver
    });
}
