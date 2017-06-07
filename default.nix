with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "jasmin-0";
  src = ./.;
  buildInputs = [ ]
    ++ (with python3Packages; [ python pyyaml ])
    ++ (with coqPackages_8_6; [ coq mathcomp ])
    ++ (with ocamlPackages; [ ocaml findlib ocaml_batteries menhir zarith ])
    ;
}
