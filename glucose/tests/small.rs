mod core {
    rustsat_solvertests::base_tests!(rustsat_glucose::core::Glucose, false, true);
}

mod simp {
    rustsat_solvertests::base_tests!(rustsat_glucose::simp::Glucose, false, true);
}
