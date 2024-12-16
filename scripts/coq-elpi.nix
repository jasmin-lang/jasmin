{ lib, mkCoqDerivation, coq, version, stdlib }:

mkCoqDerivation {
  pname = "elpi";
  repo  = "coq-elpi";
  owner = "LPCIC";
  inherit version;

  mlPlugin = true;
  useDune = true;
  propagatedBuildInputs = [ stdlib ]
  ++ (with coq.ocamlPackages; [ elpi findlib ppx_optcomp ]);

}
