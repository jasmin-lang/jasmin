with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "jasmin-0";
  src = ./.;
  buildInputs = [ mpfr ppl ]
  ++ (with ocamlPackages; [ ocaml findlib ocamlbuild apron batteries camlidl menhir menhirLib zarith yojson])
  ;

  installPhase = ''
    mkdir -p $out/bin
    cp _build/entry/jasminc.native $out/bin/jasminc
  '';
}
