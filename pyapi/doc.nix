{
  lib,
  stdenv,
  python3,
  python3Packages,
}:
let
  manifest = (lib.importTOML ./Cargo.toml).package;
  workspace-manifest = (lib.importTOML ../Cargo.toml).workspace.package;
in
stdenv.mkDerivation {
  pname = "${manifest.name}-docs";
  version = workspace-manifest.version;

  nativeBuildInputs = [
    (python3.withPackages (
      pp: with pp; [
        pdoc
        (python3Packages.callPackage ./. { })
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
}
