{
  pkgs,
  # from shared
  stdenv,
  tests,
  externalCadical,
  externalKissat,
  externalGimsatul,
  docTests,
  doc,
  pyapiDoc,
  ...
}:
{
  tools = pkgs.callPackage ../tools { };

  testCoverage = stdenv.mkDerivation {
    name = "rustsat-test-coverage";
    unpackPhase = "true";
    buildPhase = ''
      mkdir -p $out
      cp ${tests}/coverage.lcov $out/tests.lcov
      cp ${externalCadical}/coverage.lcov $out/external-cadical.lcov
      cp ${externalKissat}/coverage.lcov $out/external-kissat.lcov
      cp ${externalGimsatul}/coverage.lcov $out/external-gimsatul.lcov
      cp ${docTests}/coverage.lcov $out/doc-tests.lcov
      for cov in $out/*.lcov; do
        substituteInPlace $cov --replace-fail '/build/source/' './'
      done
    '';
  };

  pages = stdenv.mkDerivation {
    name = "rustsat-pages";
    unpackPhase = "true";
    buildPhase = ''
      mkdir -p $out
      cp -r ${doc}/share/doc $out/main
      cp -r ${pyapiDoc}/share/doc $out/pyapi
    '';
  };
}
