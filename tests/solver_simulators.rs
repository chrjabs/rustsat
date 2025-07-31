mod incremental {
    mod minisat {
        use rustsat::solvers::simulators;

        rustsat_solvertests::base_tests!(
            simulators::Incremental<rustsat_minisat::core::Minisat>,
            false,
            true,
            false
        );

        rustsat_solvertests::incremental_tests!(
            simulators::Incremental<rustsat_minisat::core::Minisat>,
        );
    }
}
