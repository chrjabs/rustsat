rustsat_solvertests::integration!(phasing: {
    let mut slv = rustsat_cadical::CaDiCaL::default();
    slv.set_option("lucky", 0).unwrap();
    slv
});
