{ pkgs ? import (fetchGit {
  url = https://github.com/NixOS/nixpkgs-channels;
  ref = "nixos-unstable";
}) {} }:
let cava_tools = (import ./default.nix { inherit pkgs; });
in
with pkgs;
mkShell {
  buildInputs = [
    cava_tools
  ];

  shellHook =
  ''
  export COQPATH=${coqPackages_8_10.coq-ext-lib}/lib/coq/8.10/user-contrib
  '';
}
