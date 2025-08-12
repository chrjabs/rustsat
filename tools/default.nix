{
  lib,
  rust-toolchain-platform,
  openssl,
  pkg-config,
  cmake,
  withCadical ? true,
  withMinisat ? false,
}:
let
  manifest = (lib.importTOML ./Cargo.toml).package;
  workspace-manifest = (lib.importTOML ../Cargo.toml).workspace.package;
in
assert lib.assertMsg (
  withCadical && !withMinisat || !withCadical && withMinisat
) "either withCadical or withMinisat, but not both must be set";
rust-toolchain-platform.buildRustPackage {
  pname = manifest.name;
  version = workspace-manifest.version;

  src =
    let
      filter =
        path: type:
        type == "directory"
        || (
          builtins.match ".*(src/(lib|main).rs|Cargo.lock|-source/(data/.*|examples/.*rs|src/.*rs)|tools/(src/.*rs|data/.*)|(minisat|cadical)/(build.rs|src/.*rs|cpp(src|-extension)/.*(cp?p?|hp?p?|CMakeLists.txt|VERSION))|toml)$" path
          != null
        );
    in
    lib.cleanSourceWith {
      src = ../.;
      inherit filter;
      name = "source";
    };
  buildAndTestSubdir = "tools";
  cargoLock.lockFile = ../Cargo.lock;

  defaultFeatures = false;
  buildFeatures =
    [ ] ++ (lib.optional withCadical [ "cadical" ]) ++ (lib.optional withMinisat [ "minisat" ]);

  buildInputs = [
    openssl
    rust-toolchain-platform.bindgenHook
  ];
  nativeBuildInputs = [
    pkg-config
    cmake
  ];

  meta = with lib; {
    description = manifest.description;
    homepage = manifest.homepage;
    license = licenses.mit;
    platforms = platforms.all;
  };
}
