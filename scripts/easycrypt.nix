{ lib, stdenv, fetchFromGitHub, ocamlPackages, python3Packages, why3 }:

let
  version = "2022.04";
  rev = "r${version}";
  src = fetchFromGitHub {
    owner = "easycrypt";
    repo = "easycrypt";
    inherit rev;
    sha256 = "sha256:09rdwcj70lkamkhd895p284rfpz4bcnsf55mcimhiqncd2a21ml7";
  };
in

let runtest = python3Packages.buildPythonApplication rec {
  pname = "easycrypt-runtest";
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
    ocaml findlib dune_2
    batteries inifiles dune-build-info menhir menhirLib yojson zarith
  ];
  propagatedBuildInputs = [ why3 ];

  preConfigure = ''
    substituteInPlace dune-project --replace '(name easycrypt)' '(name easycrypt)(version ${rev})'
  '';

  installPhase = ''
    runHook preInstall
    dune install --prefix $out -p $pname
    rm $out/bin/ec-runtest
    runHook postInstall
  '';

  passthru = {
    inherit runtest;
  };

}
