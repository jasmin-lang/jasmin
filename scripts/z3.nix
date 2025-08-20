{ z3, fetchFromGitHub }:

z3.overrideAttrs (_: rec {
  version = "4.13.4";
  src = fetchFromGitHub {
    owner = "Z3Prover";
    repo = "z3";
    tag = "z3-${version}";
    hash = "sha256-8hWXCr6IuNVKkOegEmWooo5jkdmln9nU7wI8T882BSE=";
  };
})
