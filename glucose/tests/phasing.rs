mod core {
    rustsat_solvertests::integration!(phasing: rustsat_glucose::core::Glucose);
}

mod simp {
    rustsat_solvertests::integration!(phasing: rustsat_glucose::simp::Glucose);
}
