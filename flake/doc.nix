{ inputs, config, ... }:
{
  perSystem =
    {
      lib,
      pkgs,
      self',
      ...
    }:
    let
      craneLib = (inputs.crane.mkLib pkgs).overrideToolchain (_: self'.packages.rust-toolchain);
      commonArgs = config.flake.shared.commonCraneArgs pkgs;
    in
    {
      packages = {
        doc = craneLib.cargoDoc (
          commonArgs
          // {
            cargoArtifacts = self'.packages.cargoDevArtifacts;
            cargoDocExtraArgs = "--no-deps -Zunstable-options -Zrustdoc-scrape-examples --features=_docs";
            env.RUSTDOCFLAGS = "--deny warnings";
          }
        );

        pyapiDoc =
          let
            manifest = (lib.importTOML ../pyapi/Cargo.toml).package;
            workspace-manifest = (lib.importTOML ../Cargo.toml).workspace.package;
          in
          pkgs.clangStdenv.mkDerivation {
            pname = "${manifest.name}-docs";
            version = workspace-manifest.version;

            nativeBuildInputs = [
              (pkgs.python3.withPackages (
                pp: with pp; [
                  pdoc
                  self'.packages.pyapi
                ]
              ))
            ];

            unpackPhase = "true";

            buildPhase = ''
              runHook preBuild

              mkdir -p $out/share/doc
              pdoc -o $out/share/doc --no-show-source rustsat

              runHook postBuild
            '';
          };

        pages = pkgs.clangStdenv.mkDerivation {
          name = "rustsat-pages";
          unpackPhase = "true";
          buildPhase = ''
            mkdir -p $out
            cp -r ${self'.packages.doc}/share/doc $out/main
            cp -r ${self'.packages.pyapiDoc}/share/doc $out/pyapi
          '';
        };
      };

      checks = {
        inherit (self'.packages) doc pyapiDoc;
      };
    };
}
