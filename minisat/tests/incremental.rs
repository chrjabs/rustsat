mod core {
    rustsat_solvertests::incremental_tests!(rustsat_minisat::core::Minisat);
}

// Note: Cannot test prepro version of minisat with this small example because
// the variable are eliminated by preprocessing
