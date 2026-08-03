mod core {
    rustsat_solvertests::integration!(phasing: rustsat_minisat::core::Minisat);
}

mod simp {
    rustsat_solvertests::integration!(phasing: rustsat_minisat::simp::Minisat);
}
