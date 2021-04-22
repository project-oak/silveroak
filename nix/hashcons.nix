{ lib, buildDunePackage, fetchFromGitHub
, ocaml, findlib, pkg-config
, gmp, dune_2
}:

buildDunePackage rec {
  pname = "hashcons";
  version = "1.3";
  src = fetchFromGitHub {
    owner = "backtracking";
    repo = "ocaml-hashcons";
    rev = "d733325eeb55878bed285120c2c088daf78f0e2b";
    sha256 = "0h4pvwj34pndaw3pajkhl710ywwinhc9pqimgllfmkl37wz2d8zq";
    fetchSubmodules = true;
  };
  useDune2 = true;
  minimumOCamlVersion = "4.06";

  propagatedBuildInputs = [ gmp ];
}
