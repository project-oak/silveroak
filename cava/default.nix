{ pkgs ? import (fetchGit {
  url = https://github.com/NixOS/nixpkgs-channels;
  ref = "nixos-unstable";
}) {} }:
with pkgs;
buildEnv {
  name = "cava-tools";
  paths = [
    coq_8_11
    coqPackages_8_11.coq-ext-lib
    (haskell.packages.ghc865.ghcWithPackages (pkgs: with pkgs; [Cabal]))
    verilog
    gnumake
    stdenv
    coreutils
    bash
    binutils.bintools
    verilator
  ];
}
