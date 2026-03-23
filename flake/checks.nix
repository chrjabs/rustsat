{
  lib,
  pkgs,
  inputs,
  # from shared
  stdenv,
  commonArgs,
  craneLib,
  wasmCraneLib,
  cargoArtifacts,
  cargoWasmArtifacts,
  tests,
  externalCadical,
  externalKissat,
  externalGimsatul,
  docTests,
  doc,
  pyapi,
  pyapiDoc,
  ...
}:
let
  workspaceMsrv = (lib.importTOML ../Cargo.toml).workspace.package.rust-version;

  checkMsrv =
    crate:
    let
      craneLib = (inputs.crane.mkLib pkgs).overrideToolchain (
        p: (p.extend (import inputs.rust-overlay)).rust-bin.stable."${workspaceMsrv}".minimal
      );
      cargoArtifacts = craneLib.buildDepsOnly (
        commonArgs
        // {
          pnameSuffix = "-${workspaceMsrv}-deps";
          buildPhaseCargoCommand = "cargo build --workspace --exclude rustsat-codegen";
          checkPhaseCargoCommand = "";
        }
      );
    in
    craneLib.buildPackage (
      (builtins.removeAttrs commonArgs [ "cargoTestExtraArgs" ])
      // {
        inherit cargoArtifacts;
        pname = "${crate}-msrv";
        cargoExtraArgs = "--locked -p ${crate}";
        doCheck = false;
      }
    );
in
{
  # from shared
  inherit
    tests
    externalCadical
    externalKissat
    externalGimsatul
    docTests
    doc
    pyapi
    pyapiDoc
    ;

  # Dummy derivation merging multiple MSRV check
  msrv = stdenv.mkDerivation {
    name = "rustsat-check-msrv";
    nativeBuildInputs = map (crate: checkMsrv crate) [
      # keep-sorted start
      "pigeons"
      "rustsat"
      "rustsat-batsat"
      "rustsat-cadical"
      "rustsat-capi"
      "rustsat-glucose"
      "rustsat-ipasir"
      "rustsat-kissat"
      "rustsat-minisat"
      "rustsat-pyapi"
      "rustsat-tools"
      # keep-sorted end
    ];
    doCheck = false;
    unpackPhase = "true";
    buildPhase = ''
      mkdir -p $out
    '';
  };

  wasm = wasmCraneLib.mkCargoDerivation (
    commonArgs
    // {
      pnameSuffix = "-check-wasm";
      cargoArtifacts = cargoWasmArtifacts;
      buildPhaseCargoCommand = "cargo check --locked --target wasm32-unknown-unknown -p rustsat-batsat";
    }
  );

  clippy = craneLib.cargoClippy (
    commonArgs
    // {
      inherit cargoArtifacts;
      cargoClippyExtraArgs = "--all-targets -- --deny warnings";
    }
  );

  deny = craneLib.cargoDeny (
    commonArgs
    // {
      inherit cargoArtifacts;
      cargoDenyExtraArgs = "--exclude-unpublished --features=_test,_internals";
      cargoExtraArgs = "";
    }
  );

  machete = craneLib.mkCargoDerivation (
    commonArgs
    // {
      pnameSuffix = "-machete";
      cargoArtifacts = null;
      nativeBuildInputs = with pkgs; [ cargo-machete ];
      buildPhaseCargoCommand = ''
        cargo machete
      '';
    }
  );

  codegen = craneLib.mkCargoDerivation (
    commonArgs
    // {
      pnameSuffix = "-codegen-check";
      inherit cargoArtifacts;
      buildPhaseCargoCommand = ''
        cargo run -p rustsat-codegen -- --check
      '';
    }
  );

  readmes = craneLib.mkCargoDerivation (
    commonArgs
    // {
      pnameSuffix = "-readmes";
      inherit cargoArtifacts;
      nativeBuildInputs = with pkgs; [ cargo-rdme ];
      buildPhaseCargoCommand = ''
        cargo rdme --check
        # keep-sorted start
        cargo rdme --check --workspace-project pigeons
        cargo rdme --check --workspace-project rustsat-batsat
        cargo rdme --check --workspace-project rustsat-cadical
        cargo rdme --check --workspace-project rustsat-capi
        cargo rdme --check --workspace-project rustsat-glucose
        cargo rdme --check --workspace-project rustsat-ipasir
        cargo rdme --check --workspace-project rustsat-kissat
        cargo rdme --check --workspace-project rustsat-minisat
        cargo rdme --check --workspace-project rustsat-pyapi
        cargo rdme --check --workspace-project rustsat-tools
        # keep-sorted end
      '';
    }
  );

  spellcheck = stdenv.mkDerivation {
    name = "cargo-spellcheck-check";
    nativeBuildInputs = with pkgs; [ cargo-spellcheck ];
    doCheck = true;
    src = ../.;
    buildPhase = ''
      mkdir -p $out
    '';
    checkPhase = ''
      mkdir -p .cache
      HOME=$PWD cargo-spellcheck check --code 1
    '';
  };

  typos = stdenv.mkDerivation {
    name = "typos-check";
    nativeBuildInputs = with pkgs; [ typos ];
    doCheck = true;
    src = ../.;
    buildPhase = ''
      mkdir -p $out
    '';
    checkPhase = ''
      typos
    '';
  };

  featurePowerset = craneLib.mkCargoDerivation (
    commonArgs
    // {
      pname-suffix = "-feature-powerset";
      inherit cargoArtifacts;
      nativeBuildInputs =
        commonArgs.nativeBuildInputs
        ++ (with pkgs; [
          cargo-hack
          cargo-nextest
        ]);
      buildPhaseCargoCommand = ''
        cargo hack --feature-powerset --clean-per-run --depth 2 --exclude-features bench nextest run -p rustsat
      '';
    }
  );
}
