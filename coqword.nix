{ stdenv, fetchFromGitHub, coqPackages_8_7 }:

let inherit (coqPackages_8_7) coq mathcomp; in

let rev = "9fa315504c4cbf1dc62667844a33981de695e1e7"; in

stdenv.mkDerivation rec {
  version = "0.0-git-${builtins.substring 0 8 rev}";
  name = "coq${coq.coq-version}-coqword-${version}";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    sha256 = "00hapcdzhlnqzsflgdv8865wa50sz390l04x651if73llfgfbg0v";
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
