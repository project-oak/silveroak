{ sources ? import ./nix/sources.nix
, pkgs ? import ./nix/packages.nix { inherit sources; }
, shell ? true
, withCoq ? true
, withHaskell ? false
, withVerilator ? false
}:

with pkgs;
with pkgs.lib;

stdenv.mkDerivation rec {
  name = "silveroak";

  buildInputs =
    [] ++
    optionals withCoq [
        coq_8_13
        dune_2

        (with ocamlPackages; [
            ocaml
            opam
            findlib

            zarith
            ppx_jane
            core
            parsexp

            (callPackage (import ./nix/hashcons.nix) {})
            (callPackage (import ./nix/koika.nix) {})

          ])
      ] ++
    optionals withHaskell [
        gmp
        (haskell.packages.ghc8104.ghcWithPackages (pkgs: with pkgs; [cabal-install]))
      ] ++
    optionals withVerilator [
        gcc
        boost.dev
        verilator
      ] ;

  meta = {
    description = "The SilverOak Project";
    longDescription = '' '';
    homepage = https://github.com/project-oak/silveroak;
  };
}

