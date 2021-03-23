{ sources ? import ./nix/sources.nix
, pkgs ? import ./nix/packages.nix { inherit sources; }
, buildVerilator ? true
}:

let
  tools = with pkgs; [
    # Building
    coq_8_12
    (haskell.packages.ghc8104.ghcWithPackages (pkgs: with pkgs; [Cabal]))

    # Common tools
    gcc
    git
    gnumake
    stdenv
    coreutils
    findutils
    bash
    binutils.bintools
  ] ++
    # Verilator optional for parallel building
    # TODO(blaxill): Perhaps build verilator separately and don't make optional
    # here
    (if buildVerilator then [pkgs.verilator] else [])
  ;
in
rec {
  cava-shell = pkgs.mkShell {
      name = "cava-shell";
      buildInputs = tools;
    };

  docker-image-build = pkgs.dockerTools.buildLayeredImage {
    name = "gcr.io/oak-ci/oak-hardware";
    tag = "latest";
    contents = tools;
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

