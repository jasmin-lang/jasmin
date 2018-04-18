with import <nixpkgs> {};

let coqword = callPackage ./coqword.nix {}; in

stdenv.mkDerivation {
  name = "jasmin-0";
  src = ./.;
  buildInputs = [ coqword ]
    ++ (with python3Packages; [ python pyyaml ])
    ++ (with coqPackages_8_7; [ coq mathcomp ])
    ++ (with ocamlPackages; [ ocaml findlib ocamlbuild batteries menhir merlin zarith ])
    ;
}
