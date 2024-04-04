mod core {
    rustsat_solvertests::incremental_tests!(rustsat_glucose::core::Glucose);
}

// Note: Cannot test prepro version of glucose with this small example because
// the variable are eliminated by preprocessing
