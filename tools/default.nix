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
  workspace-manifest = (lib.importTOML ../Cargo.toml).workspace.package;
in
  assert lib.assertMsg (withCadical && !withMinisat || !withCadical && withMinisat) "either withCadical or withMinisat, but not both must be set";
    rustPlatform.buildRustPackage {
      pname = manifest.name;
      version = workspace-manifest.version;

      src = ../.;
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
