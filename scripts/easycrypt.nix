{ ecRef
, lib
, stdenv
, fetchFromGitHub
, ocamlPackages
, python3Packages
, why3
}:


with {

  "dev" = {
    version = "main";
    rev = "????";
    src = builtins.fetchTarball "https://api.github.com/repos/easycrypt/easycrypt/tarball/main";
  };

  "release" = rec {
    version = "2023.09";
    rev = "r${version}";
    src = fetchFromGitHub {
      owner = "easycrypt";
      repo = "easycrypt";
      inherit rev;
      hash = "sha256-9xavU9jRisZekPqC87EyiLXtZCGu/9QeGzq6BJGt1+Y=";
    };
  };

}."${ecRef}";

let runtest = python3Packages.buildPythonApplication rec {
  pname = "easycrypt-runtest";
  format = "other";
  inherit src version;

  dontConfigure = true;
  dontBuild = true;
  doCheck = false;

  pythonPath = with python3Packages; [ pyyaml ];

  installPhase = ''
    runHook preInstall
    mkdir -p $out/bin
    cp scripts/testing/runtest $out/bin/ec-runtest
    runHook postInstall
  '';

}; in

stdenv.mkDerivation rec {
  pname = "easycrypt";
  inherit version src;

  buildInputs = with ocamlPackages; [
    ocaml findlib dune_3
    batteries camlp-streams dune-build-info dune-site inifiles menhir menhirLib why3 yojson zarith
  ];
  propagatedBuildInputs = [ why3.out ];

  preConfigure = ''
    substituteInPlace dune-project --replace '(name easycrypt)' '(name easycrypt)(version ${rev})'
  '';

  installPhase = ''
    runHook preInstall
    dune install --prefix $out -p $pname
    rm -rf $out/lib/easycrypt/ecLib
    rm $out/bin/ec-runtest
    runHook postInstall
  '';

  passthru = {
    inherit runtest;
  };

}
