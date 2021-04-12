{ sources ? import ./nix/sources.nix
, pkgs ? import ./nix/packages.nix { inherit sources; }
, shell ? true
, coq ? false
, haskell ? false
, verilator ? false
}:

with pkgs;
with pkgs.lib;

stdenv.mkDerivation rec {
  name = "silveroak";

  buildInputs = [] ++
    optionals coq [
        coq_8_12
        dune_2
        opam
        # ocamlPackages.findlib
      ] ++
    optionals haskell [
        (haskell.packages.ghc8104.ghcWithPackages (pkgs: with pkgs; [Cabal]))
      ] ++
    optionals verilator [
        gcc
        boost.dev
        verilator
      ] ;

  # propagatedBuildInputs = with ocamlPackages; [ ocaml findlib zarith ];
  # propagatedUserEnvPkgs = with ocamlPackages; [ ocaml findlib ];

  # src = null;

  preInstallCheck = ''
    export OCAMLPATH=$OCAMLFIND_DESTDIR:$OCAMLPATH
  '';


  meta = {
    description = "The SilverOak Project";
    longDescription = '' '';
    homepage = https://github.com/project-oak/silveroak;
  };
}

