mod core {
    rustsat_solvertests::integration!(internal-stats: rustsat_glucose::core::Glucose);
}

mod simp {
    rustsat_solvertests::integration!(internal-stats: rustsat_glucose::simp::Glucose);
}
