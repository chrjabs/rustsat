rustsat_solvertests::phasing_tests!({
    let mut slv = rustsat_cadical::CaDiCaL::default();
    slv.set_option("lucky", 0).unwrap();
    slv
});
