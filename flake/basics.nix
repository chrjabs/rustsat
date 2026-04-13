{
  lib,
  inputs,
  config,
  ...
}:
{
  systems = [
    "x86_64-linux"
    "aarch64-linux"
    "x86_64-darwin"
    "aarch64-darwin"
  ];

  flake.shared = {
    libDeps = pkgs: [
      pkgs.openssl
      pkgs.xz
      pkgs.bzip2
    ];

    cleanedSrc =
      pkgs:
      let
        craneLib = inputs.crane.mkLib pkgs;
        additionalSrcFilter =
          path: _type:
          builtins.match ".*(data.*|cp?p?|hp?p?|j2|snap|CMakeLists.txt|VERSION|README.md)$" path != null;
        allSrc = path: type: (additionalSrcFilter path type) || (craneLib.filterCargoSources path type);
      in
      lib.cleanSourceWith {
        src = ../.;
        filter = allSrc;
        name = "source";
      };

    commonCraneArgs = pkgs: {
      src = config.flake.shared.cleanedSrc pkgs;
      stdenv = ps: ps.clangStdenv;
      strictDeps = true;
      nativeBuildInputs = with pkgs; [
        # keep-sorted start
        clang
        cmake
        llvmPackages.bintools
        pkg-config
        # keep-sorted end
      ];
      cargoExtraArgs = "--locked --workspace --features=_test,_internals";
      cargoTestExtraArgs = "--no-run --exclude rustsat-pyapi";
      LIBCLANG_PATH = "${pkgs.libclang.lib}/lib";
      PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig";
      LD_LIBRARY_PATH = lib.makeLibraryPath (config.flake.shared.libDeps pkgs);
      CARGO_PROFILE = "";
      NEXTEST_PROFILE = "ci";
      CI = "true";
    };

    nextestRecordingArgs = pkgs: {
      buildInputs = with pkgs; [ writableTmpDirAsHomeHook ];
      preCheck = ''
        mkdir nextest-config
        printf '[experimental]\nrecord = true\n\n[record]\nenabled = true\n' \
            > nextest-config/config.toml
        cat nextest-config/config.toml
      '';
      cargoNextestExtraArgs = "--user-config-file nextest-config/config.toml";
      postCheck = ''
        cargo nextest store export latest \
            --user-config-file nextest-config/config.toml \
            --archive-file $out/nextest-run-archive.zip
      '';
    };

    setupAsan = ''
      export CARGO_BUILD_TARGET=$(rustc -vV | sed -n 's|host: ||p')
      export CARGO_BUILD_TARGET_DIR="''${CARGO_TARGET_DIR:-target}/tests"
      export CFLAGS="-fsanitize=address"
      export CXXFLAGS="-fsanitize=address"
      export RUSTFLAGS="-Zsanitizer=address"
    '';
  };

  perSystem =
    {
      system,
      ...
    }:
    {
      _module.args.pkgs = import inputs.nixpkgs {
        inherit system;
        overlays = [
          inputs.nur-packages.overlays.default
        ];
      };
    };
}
