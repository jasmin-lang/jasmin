with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "jasmin-0";
  src = ./.;
  buildInputs = [ mpfr ppl ]
  ++ (with ocamlPackages; [ ocaml findlib dune_3 apron angstrom batteries camlidl cmdliner menhir menhirLib zarith yojson])
  ;

  installPhase = ''
    mkdir -p $out/bin
    for p in jasminc jasmin2tex jasmin-ct
    do
      cp -L _build/install/default/bin/$p $out/bin/$p
    done
  '';
}
