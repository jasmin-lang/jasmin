with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "jasmin-0";
  src = ./.;
  buildInputs = [ ]
  ++ (with ocamlPackages; [ ocaml findlib ocamlbuild batteries menhir zarith  ])
  ;
}
