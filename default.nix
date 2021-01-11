{ pkgs ? import <nixpkgs> {}
, inCI ? false
, coqDeps ? !inCI
, ocamlDeps ? !inCI
, testDeps ? !inCI
, devTools ? !inCI
, enableFramePointers ? false
}:

with pkgs;

let inherit (stdenv.lib) optionals; in

let coqPackages = coqPackages_8_9; in

let coqword = callPackage ./coqword.nix { inherit coqPackages; }; in

let inherit (coqPackages.coq) ocamlPackages; in

let oP =
  if enableFramePointers
  then ocamlPackages.overrideScope' (self: super: {
    ocaml = super.ocaml.overrideAttrs (o: {
      configureFlags = o.configureFlags ++ [ "--enable-frame-pointers" ];
    });
  })
  else ocamlPackages
; in

if !lib.versionAtLeast oP.ocaml.version "4.08"
then throw "Jasmin requires OCaml ≥ 4.08"
else

stdenv.mkDerivation {
  name = "jasmin-0";
  src = null;
  buildInputs = []
    ++ optionals coqDeps [ coqPackages.coq coqword ]
    ++ optionals testDeps ([ ocamlPackages.apron.out ] ++ (with python3Packages; [ python pyyaml ]))
    ++ optionals ocamlDeps ([ mpfr ppl ] ++ (with oP; [
         ocaml findlib ocamlbuild
         (batteries.overrideAttrs (o: { doCheck = false; }))
         menhir yojson zarith camlidl apron ]))
    ++ optionals devTools (with oP; [ merlin ])
    ;
}
