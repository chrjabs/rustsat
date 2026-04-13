{ inputs, config, ... }:
{
  perSystem =
    { lib, pkgs, ... }:
    let
      commonArgs = config.flake.shared.commonCraneArgs pkgs;

      workspaceMsrv = (lib.importTOML ../Cargo.toml).workspace.package.rust-version;

      checkMsrv =
        crate:
        let
          craneLib = (inputs.crane.mkLib pkgs).overrideToolchain (
            p: (p.extend (import inputs.rust-overlay)).rust-bin.stable."${workspaceMsrv}".minimal
          );
          cargoArtifacts = craneLib.buildDepsOnly (
            commonArgs
            // {
              pnameSuffix = "-${workspaceMsrv}-deps";
              buildPhaseCargoCommand = "cargo build --workspace --exclude rustsat-codegen";
              checkPhaseCargoCommand = "";
            }
          );
        in
        craneLib.buildPackage (
          (builtins.removeAttrs commonArgs [ "cargoTestExtraArgs" ])
          // {
            inherit cargoArtifacts;
            pname = "${crate}-msrv";
            cargoExtraArgs = "--locked -p ${crate}";
            doCheck = false;
          }
        );
    in
    {
      checks.msrv = pkgs.clangStdenv.mkDerivation {
        name = "rustsat-check-msrv";
        nativeBuildInputs = map (crate: checkMsrv crate) [
          # keep-sorted start
          "pigeons"
          "rustsat"
          "rustsat-batsat"
          "rustsat-cadical"
          "rustsat-capi"
          "rustsat-glucose"
          "rustsat-ipasir"
          "rustsat-kissat"
          "rustsat-minisat"
          "rustsat-pyapi"
          "rustsat-tools"
          # keep-sorted end
        ];
        doCheck = false;
        unpackPhase = "true";
        buildPhase = ''
          mkdir -p $out
        '';
      };
    };
}
