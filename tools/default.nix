{
  lib,
  rustPlatform,
  openssl,
  pkg-config,
  cmake,
  fetchFromGitHub,
  srcOnly,
}: let
  manifest = (lib.importTOML ./Cargo.toml).package;
  cadicalSrc = srcOnly {
    name = "cadical-src";
    src = fetchFromGitHub {
      owner = "arminbiere";
      repo = "cadical";
      rev = "rel-2.1.0";
      sha256 = "sha256-sSvJgHxsRaJ/xHEK32fox0MFI7u+pj5ERLfNn2s8kC8=";
    };
    patches = [../cadical/patches/v210.patch];
  };
in
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

    # Build with CaDiCaL backend
    defaultFeatures = false;
    buildFeatures = ["cadical" "rustsat-cadical/v2-1-0"];

    preConfigure = ''
      export CADICAL_SRC_DIR=${cadicalSrc}
    '';

    buildInputs = [openssl rustPlatform.bindgenHook];
    nativeBuildInputs = [pkg-config cmake];

    meta = with lib; {
      description = manifest.description;
      homepage = manifest.homepage;
      license = licenses.mit;
      platforms = platforms.all;
    };
  }
