{ ecRef
, lib
, stdenv
, fetchFromGitHub
, fetchpatch
, ocamlPackages
, python3Packages
, why3
}:


with {

  "dev" = {
    version = "main";
    rev = "????";
    src = builtins.fetchTarball "https://api.github.com/repos/easycrypt/easycrypt/tarball/main";
    patches = [];
  };

  "release" = rec {
    version = "2022.04";
    rev = "r${version}";
    src = fetchFromGitHub {
      owner = "easycrypt";
      repo = "easycrypt";
      inherit rev;
      sha256 = "sha256:09rdwcj70lkamkhd895p284rfpz4bcnsf55mcimhiqncd2a21ml7";
    };

    patches = lib.lists.map fetchpatch [
      # Fix build with Why3 1.5
      { url = "https://github.com/EasyCrypt/easycrypt/commit/d226387432deb7f22738e1d5579346a2cbc9be7a.patch";
        hash = "sha256:1zvxij35fnr3h9b5wdl8ml17aqfx3a39rd4mgwmdvkapbg3pa4lm"; }
      # Fix build with Why3 1.6
      { url = "https://github.com/EasyCrypt/easycrypt/commit/876f2ed50a0434afdf2fb20e7c50b8a3e26bb06e.patch";
        hash = "sha256-UycfLZWYHNsppb7qHSRaAF4Y0UnwoFueEG0wUcBUPYE="; }
    ];
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
  inherit version patches src;

  buildInputs = with ocamlPackages; [
    ocaml findlib dune_3
    batteries camlp-streams dune-build-info inifiles menhir menhirLib yojson zarith
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
