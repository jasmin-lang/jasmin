with import <nixpkgs> {};

let coqPackages = coqPackages_8_8; in

let coqword = callPackage ./coqword.nix { inherit coqPackages; }; in

stdenv.mkDerivation {
  name = "jasmin-0";
  src = ./.;
  buildInputs = [ coqword ]
    ++ (with python3Packages; [ python pyyaml ])
    ++ (with coqPackages; [ coq mathcomp ])
    ++ (with ocamlPackages; [ ocaml findlib ocamlbuild batteries menhir merlin zarith ])
    ;
}
