{ inputs, config, ... }:
{
  perSystem =
    { pkgs, self', ... }:
    let
      craneLib = (inputs.crane.mkLib pkgs).overrideToolchain (_: self'.packages.rust-toolchain);
      commonArgs = config.flake.shared.commonCraneArgs pkgs;
    in
    {
      checks.featurePowerset = craneLib.mkCargoDerivation (
        commonArgs
        // {
          pname-suffix = "-feature-powerset";
          cargoArtifacts = self'.packages.cargoDevArtifacts;
          nativeBuildInputs =
            commonArgs.nativeBuildInputs
            ++ (with pkgs; [
              cargo-hack
              cargo-nextest
            ]);
          buildPhaseCargoCommand = ''
            cargo hack --feature-powerset --clean-per-run --depth 2 --exclude-features bench nextest run -p rustsat
          '';
        }
      );
    };
}
