mod core {
    rustsat_solvertests::integration!(base: rustsat_minisat::core::Minisat, false, true);
}

mod simp {
    rustsat_solvertests::integration!(base: rustsat_minisat::simp::Minisat, false, true);
}
