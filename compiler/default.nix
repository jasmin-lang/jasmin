with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "jasmin-0";
  src = ./.;
  buildInputs = [ dune mpfr ppl ]
  ++ (with ocamlPackages; [ ocaml findlib apron angstrom batteries camlidl cmdliner menhir menhirLib zarith yojson])
  ;

  installPhase = ''
    mkdir -p $out/bin
    for p in jasminc jasmin2tex jasmin-ct jasmin-checksafety
    do
      cp -L _build/install/default/bin/$p $out/bin/$p
    done
  '';
}
