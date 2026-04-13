{ inputs, ... }:
{
  perSystem =
    { pkgs, ... }:
    let
      rustPkgs = pkgs.extend (import inputs.rust-overlay);
    in
    {
      packages = {
        rust-toolchain = rustPkgs.rust-bin.fromRustupToolchainFile ../rust-toolchain.toml;
      };
    };
}
