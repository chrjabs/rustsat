{
  config,
  inputs,
  ...
}:
{
  perSystem =
    {
      pkgs,
      self',
      ...
    }:
    let
      craneLib = (inputs.crane.mkLib pkgs).overrideToolchain (_: self'.packages.rust-toolchain);
      commonArgs = config.flake.shared.commonCraneArgs pkgs;
    in
    {
      packages.cargoDevArtifacts = craneLib.buildDepsOnly (
        commonArgs
        // {
          nativeBuildInputs = commonArgs.nativeBuildInputs ++ (with pkgs; [ cargo-llvm-cov ]);
          # Setup ASAN
          preCheck = config.flake.shared.setupAsan;
          # Also build tests for llvm cov
          checkPhaseCargoCommand = ''
            cargo test --locked --workspace --features=_test,_internals --no-run --exclude rustsat-pyapi
            source <(cargo llvm-cov show-env --export-prefix)
            cargo test --locked --workspace --features=_test,_internals --no-run --exclude rustsat-pyapi
            ln -s "." "''${CARGO_TARGET_DIR:-target}/llvm-cov-target"
          '';
        }
      );
    };
}
