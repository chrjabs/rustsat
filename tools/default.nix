{
  lib,
  rustPlatform,
  openssl,
  pkg-config,
  cmake,
  withCadical ? true,
  withMinisat ? false,
}: let
  manifest = (lib.importTOML ./Cargo.toml).package;
in
  assert lib.assertMsg (withCadical && !withMinisat || !withCadical && withMinisat) "either withCadical or withMinisat, but not both must be set";
    rustPlatform.buildRustPackage {
      pname = manifest.name;
      version = manifest.version;

      src = lib.fileset.toSource {
        root = ../.;
        fileset = lib.fileset.unions [
          ../Cargo.lock
          # Need all workspace packages for build to work
          ../Cargo.toml
          ../src
          ../batsat/Cargo.toml
          ../batsat/src
          ../capi/Cargo.toml
          ../capi/src
          ../cadical/Cargo.toml
          ../cadical/build.rs
          ../cadical/src
          ../cadical/cppsrc
          ../cadical/cpp-extension
          ../cryptominisat/Cargo.toml
          ../cryptominisat/src
          ../glucose/Cargo.toml
          ../glucose/src
          ../ipasir/Cargo.toml
          ../ipasir/src
          ../kissat/Cargo.toml
          ../kissat/src
          ../minisat/Cargo.toml
          ../minisat/build.rs
          ../minisat/src
          ../minisat/cppsrc
          ../pyapi/Cargo.toml
          ../pyapi/src
          ../solvertests/Cargo.toml
          ../solvertests/src
          # Additional stuff required for build to work
          ../examples
          ../data
          ./data
          # The actual source of the project
          ./Cargo.toml
          ./src
        ];
      };
      buildAndTestSubdir = "tools";
      cargoLock.lockFile = ../Cargo.lock;

      defaultFeatures = false;
      buildFeatures = [] ++ (lib.optional withCadical ["cadical"]) ++ (lib.optional withMinisat ["minisat"]);

      buildInputs = [openssl rustPlatform.bindgenHook];
      nativeBuildInputs = [pkg-config cmake];

      meta = with lib; {
        description = manifest.description;
        homepage = manifest.homepage;
        license = licenses.mit;
        platforms = platforms.all;
      };
    }
