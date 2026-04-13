{ inputs, ... }:
{
  perSystem =
    { pkgs, self', ... }:
    let
      craneLib = (inputs.crane.mkLib pkgs).overrideToolchain (_: self'.packages.rust-toolchain);
    in
    {
      devShells = {
        semverChecks = self'.devShells.base.overrideAttrs (prevAttrs: {
          nativeBuildInputs =
            prevAttrs.nativeBuildInputs
            ++ (with pkgs; [
              # use the stable toolchain here for compatibility with semver-checks
              cargo
              cargo-semver-checks
            ]);
        });

        releasePlz = self'.devShells.base.overrideAttrs (prevAttrs: {
          nativeBuildInputs =
            prevAttrs.nativeBuildInputs
            ++ (with pkgs; [
              # use the stable toolchain here for compatibility with semver-checks
              cargo
              cargo-semver-checks
              release-plz
            ]);
        });

        cargoDeny = self'.devShells.base.overrideAttrs (prevAttrs: {
          nativeBuildInputs =
            prevAttrs.nativeBuildInputs
            ++ (with pkgs; [
              cargo-deny
              self'.packages.rust-toolchain
            ]);
        });

        ci = self'.devShells.base.overrideAttrs (prevAttrs: {
          nativeBuildInputs =
            prevAttrs.nativeBuildInputs
            ++ (with pkgs; [
              # keep-sorted start
              cargo-hack
              cargo-nextest
              craneLib.inheritCargoArtifactsHook
              self'.packages.rust-toolchain
              # keep-sorted end
            ]);
          cargoArtifacts = self'.packages.cargoDevArtifacts;
          CARGO_TARGET_DIR = "./target-ci/";
          shellHook = prevAttrs.shellHook + ''
            rm -rf "$CARGO_TARGET_DIR"
            inheritCargoArtifacts
          '';
        });
      };
    };
}
