{ inputs, config, ... }:
{
  perSystem =
    { pkgs, self', ... }:
    let
      wasmCraneLib = (inputs.crane.mkLib pkgs).overrideToolchain (_: self'.packages.wasm-toolchain);
      commonArgs = config.flake.shared.commonCraneArgs pkgs;
      # `NODERAWFS` gives tests access to the instance files, `DEFAULT_TO_CXX` is needed to link the
      # C++ solvers in builds with emscripten assertions (e.g., doctests)
      emscriptenLinkArgs = "-C link-arg=-sNODERAWFS=1 -C link-arg=-sALLOW_MEMORY_GROWTH=1 -C link-arg=-sDEFAULT_TO_CXX";
      emscriptenArgs = commonArgs // {
        nativeBuildInputs = with pkgs; [
          # keep-sorted start
          clang
          cmake
          emscripten
          llvmPackages.bintools
          nodejs
          pkg-config
          # keep-sorted end
        ];
        CARGO_TARGET_WASM32_UNKNOWN_EMSCRIPTEN_RUNNER = "node";
        CARGO_TARGET_WASM32_UNKNOWN_EMSCRIPTEN_RUSTFLAGS = emscriptenLinkArgs;
        RUSTDOCFLAGS = emscriptenLinkArgs;
        # The emscripten cache in the Nix store is read-only, but emcc builds system libraries into it
        preBuild = ''
          export EM_CACHE="$TMPDIR/emscripten-cache"
          cp -r ${pkgs.emscripten}/share/emscripten/cache "$EM_CACHE"
          chmod -R u+w "$EM_CACHE"
        '';
      };
    in
    {
      packages = {
        wasm-toolchain =
          ((pkgs.extend (import inputs.rust-overlay)).rust-bin.fromRustupToolchainFile ../rust-toolchain.toml)
          .override
            {
              targets = [
                "wasm32-unknown-emscripten"
                "wasm32-unknown-unknown"
              ];
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

      # Multithreaded tests are skipped since the target is built without pthread support
      checks.emscripten = wasmCraneLib.mkCargoDerivation (
        emscriptenArgs
        // {
          pnameSuffix = "-test-emscripten";
          cargoArtifacts = null;
          buildPhaseCargoCommand = ''
            cargo test --locked --release --no-fail-fast --target wasm32-unknown-emscripten \
              -p rustsat-batsat -p rustsat-cadical -p rustsat-glucose -p rustsat-kissat -p rustsat-minisat \
              -- --skip multithreaded
          '';
        }
      );
    };
}
