{pkgs ? import <nixpkgs> {}}: let
  overrides = builtins.fromTOML (builtins.readFile ./rust-toolchain.toml);
  rustHostTriple = "x86_64-unknown-linux-gnu";
  libs = with pkgs; [openssl xz bzip2];
in
  pkgs.mkShell rec {
    nativeBuildInputs = with pkgs; [
      llvmPackages_12.bintools
      pkg-config
      clang
      cmake
      rustup
      cargo-rdme
      cargo-nextest
    ];
    buildInputs = libs;
    RUSTC_VERSION = overrides.toolchain.channel;
    LIBCLANG_PATH = pkgs.lib.makeLibraryPath [pkgs.llvmPackages_12.libclang.lib];
    shellHook = ''
      export PATH=$PATH:''${CARGO_HOME:-~/.cargo}/bin/
      export PATH=$PATH:''${RUSTUP_HOME:-~/.rustup}/toolchains/${RUSTC_VERSION}-${rustHostTriple}/bin/
    '';
    LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath libs;
    PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig/";
  }
