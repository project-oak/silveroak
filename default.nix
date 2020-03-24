{ imageName, pkgs ? import <nixpkgs> {}}:
let cava_tools = (import ./cava/default.nix { inherit pkgs; });
in pkgs.dockerTools.buildLayeredImage {
  name = imageName;
  tag = "latest";
  contents = [
    cava_tools
  ];
  config = {
    WorkingDir = "/workspace";
    Volumes = {
      "/workspace" = {};
      "/tmp" = {};
    };
    Env = [
      "COQPATH=${pkgs.coqPackages_8_11.coq-ext-lib}/lib/coq/8.11/user-contrib"
    ];
  };
  maxLayers = 120;
}
