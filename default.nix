{ sources ? import ./nix/sources.nix
, pkgs ? import ./nix/packages.nix { inherit sources; }
}:

let
  coq-tools = with pkgs; [
    # Building
    coq_8_12
    (haskell.packages.ghc865.ghcWithPackages (pkgs: with pkgs; [Cabal]))
    # (haskell.packages.ghc865.ghcWithPackages (pkgs: with pkgs; [Cabal ShellCheck]))

    # Common tools
    gcc
    git
    gnumake
    stdenv
    coreutils
    findutils
    bash
    binutils.bintools
    ocaml
  ] ;
in
rec {
  coq-shell = pkgs.mkShell {
      name = "coq-shell";
      buildInputs = coq-tools;
    };
  verilator-shell = pkgs.mkShell {
      name = "verilator";
      buildInputs = [pkgs.verilator];
    };

  docker-image-build = pkgs.dockerTools.buildLayeredImage {
    name = "gcr.io/oak-ci/oak-hardware";
    tag = "latest";
    contents = coq-tools;
    config = {
      WorkingDir = "/workspace";
      Volumes = {
        "/workspace" = {};
        "/tmp" = {};
      };
    };
    maxLayers = 120;
  };
}

