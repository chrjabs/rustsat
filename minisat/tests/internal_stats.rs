mod core {
    rustsat_solvertests::integration!(internal-stats: rustsat_minisat::core::Minisat);
}

mod simp {
    rustsat_solvertests::integration!(internal-stats: rustsat_minisat::simp::Minisat);
}
