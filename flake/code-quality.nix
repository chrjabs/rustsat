{ inputs, config, ... }:
{
  perSystem =
    { pkgs, self', ... }:
    let
      craneLib = (inputs.crane.mkLib pkgs).overrideToolchain (_: self'.packages.rust-toolchain);
      commonArgs = config.flake.shared.commonCraneArgs pkgs;
    in
    {
      checks = {
        clippy = craneLib.cargoClippy (
          commonArgs
          // {
            cargoArtifacts = self'.packages.cargoDevArtifacts;
            cargoClippyExtraArgs = "--all-targets -- --deny warnings";
          }
        );

        deny = craneLib.cargoDeny (
          commonArgs
          // {
            cargoArtifacts = self'.packages.cargoDevArtifacts;
            cargoDenyExtraArgs = "--exclude-unpublished --features=_test,_internals";
            cargoExtraArgs = "";
          }
        );

        machete = craneLib.mkCargoDerivation (
          commonArgs
          // {
            pnameSuffix = "-machete";
            cargoArtifacts = null;
            nativeBuildInputs = with pkgs; [ cargo-machete ];
            buildPhaseCargoCommand = ''
              cargo machete
            '';
          }
        );

        spellcheck = pkgs.clangStdenv.mkDerivation {
          name = "cargo-spellcheck-check";
          nativeBuildInputs = with pkgs; [ cargo-spellcheck ];
          doCheck = true;
          src = ../.;
          buildPhase = ''
            mkdir -p $out
          '';
          checkPhase = ''
            mkdir -p .cache
            HOME=$PWD cargo-spellcheck check --code 1
          '';
        };

        typos = pkgs.clangStdenv.mkDerivation {
          name = "typos-check";
          nativeBuildInputs = with pkgs; [ typos ];
          doCheck = true;
          src = ../.;
          buildPhase = ''
            mkdir -p $out
          '';
          checkPhase = ''
            typos
          '';
        };

        codegen = craneLib.mkCargoDerivation (
          commonArgs
          // {
            pnameSuffix = "-codegen-check";
            cargoArtifacts = self'.packages.cargoDevArtifacts;
            buildPhaseCargoCommand = ''
              cargo run -p rustsat-codegen -- --check
            '';
          }
        );

        readmes = craneLib.mkCargoDerivation (
          commonArgs
          // {
            pnameSuffix = "-readmes";
            cargoArtifacts = self'.packages.cargoDevArtifacts;
            nativeBuildInputs = with pkgs; [ cargo-rdme ];
            buildPhaseCargoCommand = ''
              cargo rdme --check
              # keep-sorted start
              cargo rdme --check --workspace-project pigeons
              cargo rdme --check --workspace-project rustsat-batsat
              cargo rdme --check --workspace-project rustsat-cadical
              cargo rdme --check --workspace-project rustsat-capi
              cargo rdme --check --workspace-project rustsat-glucose
              cargo rdme --check --workspace-project rustsat-ipasir
              cargo rdme --check --workspace-project rustsat-kissat
              cargo rdme --check --workspace-project rustsat-minisat
              cargo rdme --check --workspace-project rustsat-pyapi
              cargo rdme --check --workspace-project rustsat-tools
              # keep-sorted end
            '';
          }
        );
      };
    };
}
