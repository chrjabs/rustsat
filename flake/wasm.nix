{ inputs, config, ... }:
{
  perSystem =
    { pkgs, self', ... }:
    let
      wasmCraneLib = (inputs.crane.mkLib pkgs).overrideToolchain (_: self'.packages.wasm-toolchain);
      commonArgs = config.flake.shared.commonCraneArgs pkgs;
    in
    {
      packages = {
        wasm-toolchain =
          ((pkgs.extend (import inputs.rust-overlay)).rust-bin.fromRustupToolchainFile ../rust-toolchain.toml)
          .override
            {
              targets = [ "wasm32-unknown-unknown" ];
            };

        cargoWasmArtifacts = wasmCraneLib.buildDepsOnly (
          commonArgs
          // {
            nativeBuildInputs = with pkgs; [
              # keep-sorted start
              clang
              llvmPackages.bintools
              pkg-config
              # keep-sorted end
            ];
            buildPhaseCargoCommand = "cargo check --locked --target wasm32-unknown-unknown -p rustsat-batsat";
            checkPhaseCargoCommand = "";
          }
        );
      };

      checks.wasm = wasmCraneLib.mkCargoDerivation (
        commonArgs
        // {
          pnameSuffix = "-check-wasm";
          cargoArtifacts = self'.packages.cargoWasmArtifacts;
          buildPhaseCargoCommand = "cargo check --locked --target wasm32-unknown-unknown -p rustsat-batsat";
        }
      );
    };
}
