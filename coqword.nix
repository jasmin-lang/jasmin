{ stdenv, fetchFromGitHub, coqPackages }:

let inherit (coqPackages) coq mathcomp; in

let rev = "67c60daa1c5320d390055c6012e63602628f6e14"; in

stdenv.mkDerivation rec {
  version = "0.0-git-${builtins.substring 0 8 rev}";
  name = "coq${coq.coq-version}-coqword-${version}";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    sha256 = "12bgjmgmfkgx615z6lxpz6gfz79xm7qiqn5dk83s4l3llxy6c9xw";
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
