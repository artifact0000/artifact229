{ pkgs ? import (<nixpkgs>) {}
, inCI ? false
, coqDeps ? !inCI
, ocamlDeps ? !inCI
, devTools ? !inCI
}:

with pkgs;

let inherit (lib) optionals; in

let coqPackages = coqPackages_8_18; in

let inherit (coqPackages.coq) ocamlPackages; in

stdenv.mkDerivation {
  name = "test";
  src = null;
  buildInputs = []
    ++ optionals coqDeps [
      coqPackages.coq
      coqPackages.coqide
      coqPackages.mathcomp
    ]
    ++ optionals ocamlDeps [ ocaml dune_3 ]
    ++ optionals devTools [ ]
    ;
}
