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
  cargoArtifacts,
  ...
}:
{
  inherit doc pyapiDoc;

  devDeps = cargoArtifacts;

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

  testRecordings = stdenv.mkDerivation {
    name = "rustsat-test-recordings";
    unpackPhase = "true";
    buildPhase = ''
      mkdir -p $out
      cp ${tests}/nextest-run-archive.zip $out/tests-run-archive.zip
      cp ${externalCadical}/nextest-run-archive.zip $out/external-cadical-run-archive.zip
      cp ${externalKissat}/nextest-run-archive.zip $out/external-kissat-run-archive.zip
      cp ${externalGimsatul}/nextest-run-archive.zip $out/external-gimsatul-run-archive.zip
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
