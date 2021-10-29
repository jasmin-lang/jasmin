with import <nixpkgs> {};

let coqPackages = coqPackages_8_9; in

let coqword = callPackage ../coqword.nix { inherit coqPackages; }; in
let inherit (coqPackages) coq; in

let jasmin =
stdenv.mkDerivation rec {
  name = "jasmin-20210826";
  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "jasmin";
    rev = "7eedba4f4b68e8cf06b0ec9e1beaac1c6f54f104";
    sha256 = "1gmqdbkiwy3510zq76z05pg1lnmc5r79r18qy6gsd7bl17074mw9";
  };

  buildInputs = [ coq coqword mpfr ppl ]
  ++ (with coq.ocamlPackages; [
    ocaml findlib ocamlbuild
    (batteries.overrideAttrs (_: { doCheck = false; }))
    menhir zarith camlidl apron yojson
  ])
  ++ [ (coq.ocamlPackages.menhirLib or null) ]
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
