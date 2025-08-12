{
  lib,
  rust-toolchain-platform,
}:
let
  manifest = (lib.importTOML ./Cargo.toml).package;
  workspace-manifest = (lib.importTOML ../Cargo.toml).workspace.package;
in
rust-toolchain-platform.buildRustPackage {
  pname = manifest.name;
  version = workspace-manifest.version;

  src = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../Cargo.lock
      # Need all workspace packages for build to work
      ../Cargo.toml
      ../src/lib.rs
      ../batsat/Cargo.toml
      ../batsat/src/lib.rs
      ../capi/Cargo.toml
      ../capi/src/lib.rs
      ../cadical/Cargo.toml
      ../cadical/src/lib.rs
      ../glucose/Cargo.toml
      ../glucose/src/lib.rs
      ../ipasir/Cargo.toml
      ../ipasir/src/lib.rs
      ../kissat/Cargo.toml
      ../kissat/src/lib.rs
      ../minisat/Cargo.toml
      ../minisat/src/lib.rs
      ../pigeons/Cargo.toml
      ../pigeons/src/lib.rs
      ../pyapi/Cargo.toml
      ../pyapi/src/lib.rs
      ../solvertests/Cargo.toml
      ../solvertests/src
      ../tools/Cargo.toml
      ../tools/src/lib.rs
      # Additional stuff required for build to work
      ../examples
      # The actual source of the project
      ./Cargo.toml
      ./src
    ];
  };
  buildAndTestSubdir = "codegen";
  cargoLock.lockFile = ../Cargo.lock;

  meta = with lib; {
    description = manifest.description;
    homepage = manifest.homepage;
    license = licenses.mit;
    platforms = platforms.all;
  };
}
