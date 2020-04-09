{ pkgs ? import <nixpkgs> {}
, enableFramePointers ? false
}:

with pkgs;

let coqPackages = coqPackages_8_9; in

let coqword = callPackage ./coqword.nix { inherit coqPackages; }; in

let oP =
  if enableFramePointers
  then ocamlPackages.overrideScope' (self: super: {
    ocaml = super.ocaml.overrideAttrs (o: {
      configureFlags = o.configureFlags ++ [ "--enable-frame-pointers" ];
    });
  })
  else ocamlPackages
; in

stdenv.mkDerivation {
  name = "jasmin-0";
  src = ./.;
  buildInputs = [ coqPackages.coq coqword ]
    ++ (with python3Packages; [ python pyyaml ])
    ++ (with oP; [ ocaml findlib ocamlbuild
        (batteries.overrideAttrs (o: { doCheck = false; }))
         menhir merlin zarith mpfr camlidl apron ppl])
    ;
}
