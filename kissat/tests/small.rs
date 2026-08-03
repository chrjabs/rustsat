mod base {
    rustsat_solvertests::integration!(base: rustsat_kissat::Kissat);
}

mod sat {
    rustsat_solvertests::integration!(base: {
        let mut slv = rustsat_kissat::Kissat::default();
        slv.set_configuration(rustsat_kissat::Config::Sat).unwrap();
        slv
    });
}

mod unsat {
    rustsat_solvertests::integration!(base: {
        let mut slv = rustsat_kissat::Kissat::default();
        slv.set_configuration(rustsat_kissat::Config::Unsat)
            .unwrap();
        slv
    });
}
