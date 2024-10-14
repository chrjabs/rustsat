// >= v1.5.4
#![cfg(all(
    not(feature = "v1-5-3"),
    not(feature = "v1-5-2"),
    not(feature = "v1-5-1"),
    not(feature = "v1-5-0")
))]
rustsat_solvertests::flipping_tests!(rustsat_cadical::CaDiCaL);
