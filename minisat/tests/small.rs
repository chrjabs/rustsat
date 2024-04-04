mod core {
    rustsat_solvertests::base_tests!(rustsat_minisat::core::Minisat, false, true);
}

mod simp {
    rustsat_solvertests::base_tests!(rustsat_minisat::simp::Minisat, false, true);
}
