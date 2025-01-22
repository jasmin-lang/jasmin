{ lib, mkCoqDerivation, coq, version, stdlib }:

mkCoqDerivation {
  pname = "elpi";
  repo  = "coq-elpi";
  owner = "LPCIC";
  inherit version;

  preConfigure = ''
    make elpi/dune
  '';

  mlPlugin = true;
  useDune = true;
  propagatedBuildInputs = [ stdlib ]
  ++ (with coq.ocamlPackages; [
    (elpi.override { version = "master"; })
    findlib
    ppx_optcomp
  ]);

}
