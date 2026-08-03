mod base {
    rustsat_solvertests::integration!(base: rustsat_cadical::CaDiCaL);
}

mod sat {
    rustsat_solvertests::integration!(base: {
        let mut slv = rustsat_cadical::CaDiCaL::default();
        slv.set_configuration(rustsat_cadical::Config::Sat).unwrap();
        slv
    });
}

mod unsat {
    rustsat_solvertests::integration!(base: {
        let mut slv = rustsat_cadical::CaDiCaL::default();
        slv.set_configuration(rustsat_cadical::Config::Unsat)
            .unwrap();
        slv
    });
}
