mod core {
    rustsat_solvertests::phasing_tests!(rustsat_minisat::core::Minisat);
}

mod simp {
    rustsat_solvertests::phasing_tests!(rustsat_minisat::simp::Minisat);
}
