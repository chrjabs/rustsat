{
  perSystem =
    { pkgs, self', ... }:
    {
      packages.pyapi =
        pkgs.python3Packages.callPackage
          (
            {
              lib,
              buildPythonPackage,
              rustPlatform,
              pkg-config,
              openssl,
              mypy,
            }:
            let
              manifest = (lib.importTOML ../pyapi/Cargo.toml).package;
              workspace-manifest = (lib.importTOML ../Cargo.toml).workspace.package;
              libs = [
                openssl
              ];
            in
            buildPythonPackage {
              pname = manifest.name;
              version = workspace-manifest.version;

              src =
                let
                  filter =
                    path: type:
                    type == "directory"
                    || (
                      builtins.match ".*(src/(lib|main).rs|benches/.*rs|Cargo.lock|-source/(examples/.*rs|src/.*rs)|pyapi/(python/.*|README.md|build.rs|stubtest-allowlist.txt|src/.*rs|examples/.*py)|toml)$" path
                      != null
                    );
                in
                lib.cleanSourceWith {
                  src = ../.;
                  inherit filter;
                  name = "source";
                };
              buildAndTestSubdir = "pyapi";
              pyproject = true;
              cargoDeps = rustPlatform.importCargoLock { lockFile = ../Cargo.lock; };

              nativeBuildInputs = [
                pkg-config
                rustPlatform.cargoSetupHook
                rustPlatform.maturinBuildHook
              ];
              buildInputs = libs;

              nativeCheckInputs = [
                mypy
              ];

              checkPhase = ''
                runHook preCheck

                python pyapi/examples/pyapi-dpw.py
                stubtest --mypy-config-file pyapi/pyproject.toml --allowlist pyapi/stubtest-allowlist.txt rustsat

                runHook postCheck
              '';

              pythonImportsCheck = [
                "rustsat"
                "rustsat.encodings"
                "rustsat.encodings.am1"
                "rustsat.encodings.card"
                "rustsat.encodings.pb"
              ];

              LD_LIBRARY_PATH = lib.makeLibraryPath libs;
              PKG_CONFIG_PATH = "${openssl.dev}/lib/pkgconfig";
            }
          )
          {
            rustPlatform = pkgs.makeRustPlatform {
              cargo = self'.packages.rust-toolchain;
              rustc = self'.packages.rust-toolchain;
            };
          };

      checks.pyapi = self'.packages.pyapi;
    };
}
