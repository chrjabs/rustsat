mod base {
    rustsat_solvertests::base_tests!(rustsat_cadical::CaDiCaL);
}

mod sat {
    rustsat_solvertests::base_tests!({
        let mut slv = rustsat_cadical::CaDiCaL::default();
        slv.set_configuration(rustsat_cadical::Config::SAT).unwrap();
        slv
    });
}

mod unsat {
    rustsat_solvertests::base_tests!({
        let mut slv = rustsat_cadical::CaDiCaL::default();
        slv.set_configuration(rustsat_cadical::Config::UNSAT)
            .unwrap();
        slv
    });
}
