{
  perSystem =
    { pkgs, self', ... }:
    {
      packages.tools =
        pkgs.callPackage
          (
            {
              lib,
              rustPlatform,
              openssl,
              pkg-config,
              cmake,
              withCadical ? true,
              withMinisat ? false,
            }:
            let
              manifest = (lib.importTOML ../tools/Cargo.toml).package;
              workspace-manifest = (lib.importTOML ../Cargo.toml).workspace.package;
            in
            assert lib.assertMsg (
              withCadical && !withMinisat || !withCadical && withMinisat
            ) "either withCadical or withMinisat, but not both must be set";
            rustPlatform.buildRustPackage {
              pname = manifest.name;
              version = workspace-manifest.version;

              src =
                let
                  filter =
                    path: type:
                    type == "directory"
                    || (
                      builtins.match ".*(src/(lib|main).rs|Cargo.lock|-source/(data/.*|examples/.*rs|src/.*rs|benches/.*rs)|tools/(src/.*rs|data)|(minisat|cadical)/(build.rs|src/.*rs|(cpp-extension|vendor)/.*(cp?p?|hp?p?|CMakeLists.txt|VERSION))|toml)$" path
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
                rustPlatform.bindgenHook
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
          )
          {
            rustPlatform = pkgs.makeRustPlatform {
              cargo = self'.packages.rust-toolchain;
              rustc = self'.packages.rust-toolchain;
            };
          };
    };
}
