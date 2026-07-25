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
      craneLib =
        ((inputs.crane.mkLib pkgs).overrideScope (_: _: { stdenvSelector = ps: ps.clangStdenv; }))
        .overrideToolchain
          (_: self'.packages.rust-toolchain);
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
            source <(cargo llvm-cov show-env --sh)
            cargo test --locked --workspace --features=_test,_internals --no-run --exclude rustsat-pyapi
            ln -s "." "''${CARGO_TARGET_DIR:-target}/llvm-cov-target"
          '';
        }
      );
    };
}
