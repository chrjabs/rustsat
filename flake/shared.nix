{
  lib,
  pkgs,
  inputs,
  ...
}:
let
  src =
    let
      additionalSrcFilter =
        path: _type:
        builtins.match ".*(data.*|cp?p?|hp?p?|j2|snap|CMakeLists.txt|VERSION|README.md)$" path != null;
      allSrc = path: type: (additionalSrcFilter path type) || (craneLib.filterCargoSources path type);
    in
    lib.cleanSourceWith {
      src = ../.;
      filter = allSrc;
      name = "source";
    };

  libDeps = with pkgs; [
    openssl
    xz
    bzip2
  ];

  craneLib = (inputs.crane.mkLib pkgs).overrideToolchain (p: p.rust-toolchain);

  wasmCraneLib = (inputs.crane.mkLib pkgs).overrideToolchain (p: p.wasm-toolchain);

  commonArgs = {
    inherit src;
    strictDeps = true;
    nativeBuildInputs = with pkgs; [
      llvmPackages.bintools
      pkg-config
      clang
      cmake
    ];
    cargoExtraArgs = "--locked --workspace --features=_test,_internals";
    cargoTestExtraArgs = "--no-run --exclude rustsat-pyapi";
    LIBCLANG_PATH = "${pkgs.libclang.lib}/lib";
    PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig";
    LD_LIBRARY_PATH = lib.makeLibraryPath libDeps;
    CARGO_PROFILE = "";
    NEXTEST_PROFILE = "ci";
    CI = "true";
  };

  cargoArtifacts = craneLib.buildDepsOnly (
    commonArgs
    // {
      nativeBuildInputs = commonArgs.nativeBuildInputs ++ (with pkgs; [ cargo-llvm-cov ]);
      # Also build tests for llvm cov
      checkPhaseCargoCommand = ''
        cargo test --locked --workspace --features=_test,_internals --no-run --exclude rustsat-pyapi
        source <(cargo llvm-cov show-env --export-prefix)
        cargo test --locked --workspace --features=_test,_internals --no-run --exclude rustsat-pyapi
        ln -s "." "''${CARGO_TARGET_DIR:-target}/llvm-cov-target"
      '';
    }
  );

  externalSolverTest =
    slv:
    (craneLib.cargoNextest (
      commonArgs
      // {
        inherit cargoArtifacts;
        cargoExtraArgs = "--locked --features=_test,_internals";
        cargoNextestExtraArgs = "-p rustsat --test external_solver -- --ignored";
        withLlvmCov = true;
        cargoLlvmCovExtraArgs = "--lcov --output-path $out/coverage.lcov";
        RS_EXT_SOLVER = slv;
      }
    ));
in
{
  inherit
    src
    libDeps
    craneLib
    wasmCraneLib
    commonArgs
    cargoArtifacts
    ;

  stdenv = pkgs.clangStdenv;

  cargoWasmArtifacts = wasmCraneLib.buildDepsOnly (
    commonArgs
    // {
      buildPhaseCargoCommand = "cargo check --locked --target wasm32-unknown-unknown -p rustsat-batsat";
      checkPhaseCargoCommand = "";
    }
  );

  docTests = craneLib.mkCargoDerivation (
    commonArgs
    // {
      pnameSuffix = "-doctests";
      doCheck = true;
      nativeBuildInputs = commonArgs.nativeBuildInputs ++ (with pkgs; [ cargo-llvm-cov ]);
      inherit cargoArtifacts;
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

  tests = craneLib.cargoNextest (
    commonArgs
    // {
      inherit cargoArtifacts;
      cargoNextestExtraArgs = "--exclude rustsat-pyapi";
      nativeBuildInputs = commonArgs.nativeBuildInputs ++ (with pkgs; [ jq ]);
      withLlvmCov = true;
      cargoLlvmCovExtraArgs = "--lcov --output-path $out/coverage.lcov --exclude-from-report rustsat-codegen";
      VERIPB_CHECKER = lib.getExe pkgs.veripb;
    }
  );

  externalCadical = externalSolverTest (lib.getExe' pkgs.cadical "cadical");
  externalKissat = externalSolverTest (lib.getExe pkgs.kissat);
  externalGimsatul = externalSolverTest (lib.getExe pkgs.gimsatul);

  doc = craneLib.cargoDoc (
    commonArgs
    // {
      inherit cargoArtifacts;
      cargoDocExtraArgs = "--no-deps -Zunstable-options -Zrustdoc-scrape-examples --features=_docs";
      env.RUSTDOCFLAGS = "--deny warnings";
    }
  );

  pyapi = pkgs.python3Packages.callPackage ../pyapi { };
  pyapiDoc = pkgs.callPackage ../pyapi/doc.nix { };
}
