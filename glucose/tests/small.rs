mod core {
    rustsat_solvertests::integration!(base: rustsat_glucose::core::Glucose, false, true);
}

mod simp {
    rustsat_solvertests::integration!(base: rustsat_glucose::simp::Glucose, false, true);
}
