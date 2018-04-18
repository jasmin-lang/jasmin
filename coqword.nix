{ stdenv, fetchFromGitHub, coqPackages_8_7 }:

let inherit (coqPackages_8_7) coq mathcomp; in

let rev = "834a3cf733f87d43a27376f7cd4d379e9abe7b03"; in

stdenv.mkDerivation rec {
  version = "0.0-git-${builtins.substring 0 8 rev}";
  name = "coq${coq.coq-version}-coqword-${version}";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    sha256 = "0wh596n0xw411hci6pp3fg1qlnd91r49afb7dm8s9fhil4qqnma5";
  };

  buildInputs = [ coq ];

  propagatedBuildInputs = [ mathcomp ];

  installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];

  meta = {
    description = "Yet Another Coq Library on Machine Words";
    license = stdenv.lib.licenses.cecill-b;
    inherit (src.meta) homepage;
    inherit (coq.meta) platforms;
  };
}
