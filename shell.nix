{ pkgs ? import ./nix/packages.nix {}
, withCoq ? true
, withHaskell ? true
, withVerilator ? true
}:
let packages = (import ./default.nix { inherit pkgs withCoq withHaskell withVerilator; shell = true; }).buildInputs; in
pkgs.mkShell {
  buildInputs = packages;
}
