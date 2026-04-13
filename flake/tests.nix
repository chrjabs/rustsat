{ inputs, config, ... }:
{
  perSystem =
    {
      lib,
      pkgs,
      self',
      ...
    }:
    let
      craneLib = (inputs.crane.mkLib pkgs).overrideToolchain (_: self'.packages.rust-toolchain);
      commonArgs = config.flake.shared.commonCraneArgs pkgs;
      nextestRecordingArgs = config.flake.shared.nextestRecordingArgs pkgs;

      externalSolverTest =
        slv:
        (craneLib.cargoNextest (
          commonArgs
          // nextestRecordingArgs
          // {
            cargoArtifacts = self'.packages.cargoDevArtifacts;
            cargoExtraArgs = "--locked --features=_test,_internals";
            cargoNextestExtraArgs =
              nextestRecordingArgs.cargoNextestExtraArgs + " -p rustsat --test external_solver -- --ignored";
            withLlvmCov = true;
            cargoLlvmCovExtraArgs = "--lcov --output-path $out/coverage.lcov";
            RS_EXT_SOLVER = slv;
          }
        ));
    in
    {
      checks = {
        tests = craneLib.cargoNextest (
          commonArgs
          // nextestRecordingArgs
          // {
            cargoArtifacts = self'.packages.cargoDevArtifacts;
            cargoNextestExtraArgs = nextestRecordingArgs.cargoNextestExtraArgs + " --exclude rustsat-pyapi";
            nativeBuildInputs = commonArgs.nativeBuildInputs ++ (with pkgs; [ jq ]);
            withLlvmCov = true;
            cargoLlvmCovExtraArgs = "--lcov --output-path $out/coverage.lcov --exclude-from-report rustsat-codegen";
            preCheck = config.flake.shared.setupAsan + nextestRecordingArgs.preCheck;
            VERIPB_CHECKER = lib.getExe pkgs.veripb;
          }
        );

        docTests = craneLib.mkCargoDerivation (
          commonArgs
          // {
            pnameSuffix = "-doctests";
            doCheck = true;
            nativeBuildInputs = commonArgs.nativeBuildInputs ++ (with pkgs; [ cargo-llvm-cov ]);
            cargoArtifacts = self'.packages.cargoDevArtifacts;
            cargoTestExtraArgs = "--exclude rustsat-capi --exclude rustsat-pyapi";
            buildPhaseCargoCommand = "mkdir -p $out";
            checkPhaseCargoCommand = ''
              cargo llvm-cov --doc --workspace \
                --exclude rustsat-ipasir \
                --exclude rustsat-capi \
                --exclude rustsat-pyapi \
                --features=_test,_internals --lcov --output-path $out/coverage.lcov
            '';
          }
        );

        externalCadical = externalSolverTest (lib.getExe' pkgs.cadical "cadical");
        externalKissat = externalSolverTest (lib.getExe pkgs.kissat);
        externalGimsatul = externalSolverTest (lib.getExe pkgs.gimsatul);
      };

      packages = {
        testCoverage = pkgs.clangStdenv.mkDerivation {
          name = "rustsat-test-coverage";
          unpackPhase = "true";
          buildPhase = ''
            mkdir -p $out
            cp ${self'.checks.tests}/coverage.lcov $out/tests.lcov
            cp ${self'.checks.externalCadical}/coverage.lcov $out/external-cadical.lcov
            cp ${self'.checks.externalKissat}/coverage.lcov $out/external-kissat.lcov
            cp ${self'.checks.externalGimsatul}/coverage.lcov $out/external-gimsatul.lcov
            cp ${self'.checks.docTests}/coverage.lcov $out/doc-tests.lcov
            for cov in $out/*.lcov; do
              substituteInPlace $cov --replace-fail '/build/source/' './'
            done
          '';
        };

        testRecordings = pkgs.clangStdenv.mkDerivation {
          name = "rustsat-test-recordings";
          unpackPhase = "true";
          buildPhase = ''
            mkdir -p $out
            cp ${self'.checks.tests}/nextest-run-archive.zip $out/tests-run-archive.zip
            cp ${self'.checks.externalCadical}/nextest-run-archive.zip $out/external-cadical-run-archive.zip
            cp ${self'.checks.externalKissat}/nextest-run-archive.zip $out/external-kissat-run-archive.zip
            cp ${self'.checks.externalGimsatul}/nextest-run-archive.zip $out/external-gimsatul-run-archive.zip
          '';
        };
      };
    };
}
