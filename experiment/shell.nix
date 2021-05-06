with import <nixpkgs> {};

let coqPackages = coqPackages_8_9; in

let coqword = callPackage ../coqword.nix { inherit coqPackages; }; in
let inherit (coqPackages) coq; in

let jasmin =
stdenv.mkDerivation rec {
  name = "jasmin-20210408";
  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "jasmin";
    rev = "ac5e3c913a56e487abbcf73d3c0214199941269e";
    sha256 = "0s63c055hjxbs1mggnj42qvahzcssjk5c4w3fs7mz6b1x71iscl1";
  };

  buildInputs = [ coq coqword mpfr ppl ]
  ++ (with coq.ocamlPackages; [
    ocaml findlib ocamlbuild
    (batteries.overrideAttrs (_: { doCheck = false; }))
    menhir zarith camlidl apron yojson
  ])
  ;

  buildPhase = ''
    make -j $NIX_BUILD_CORES -C proofs
    make -C compiler CIL build
  '';

  installFlags = [ "PREFIX=$(out)" ];
}; in

stdenv.mkDerivation {
  name = "env";
  JASMIN_REF = "${jasmin}/bin";
  JASMIN_CT = "../compiler";
  buildInputs = [
    hyperfine
  ];

}
