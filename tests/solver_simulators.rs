mod incremental {
    mod minisat {
        use rustsat::solvers::simulators;

        rustsat_solvertests::integration!(base:
            simulators::Incremental<rustsat_minisat::core::Minisat>,
            false,
            true
        );

        rustsat_solvertests::integration!(incremental:
            simulators::Incremental<rustsat_minisat::core::Minisat>
        );
    }
}
