{ ecRef
, lib
, stdenv
, fetchFromGitHub
, fetchpatch
, ocamlPackages
, python3
, why3
, fetchurl
}:

let markdown = with ocamlPackages;
  buildDunePackage {
    pname = "markdown";
    version = "0.2.1";
    src = fetchurl {
      url = "https://github.com/gildor478/ocaml-markdown/releases/download/v0.2.1/markdown-v0.2.1.tbz";
      hash = "sha256-nFdbdK0UIpqwiYGaNIoaj0UwI7/PHCDrxfxHNDYj3l4=";
    };
    propagatedBuildInputs = [
      batteries
      tyxml
    ];
  };
in

with {

  "dev" = {
    version = "main";
    rev = "????";
    src = builtins.fetchTarball "https://api.github.com/repos/easycrypt/easycrypt/tarball/main";
    extraBuildInputs = [ markdown ];
  };

  "release" = rec {
    version = "2025.11";
    rev = "r${version}";
    src = fetchFromGitHub {
      owner = "easycrypt";
      repo = "easycrypt";
      inherit rev;
      hash = "sha256-BLyC8AB075Nyhb5heIKVkxnWWt4Zn8Doo10ShsACJ4g=";
    };
    extraBuildInputs = [];
  };

}."${ecRef}";

stdenv.mkDerivation rec {
  pname = "easycrypt";
  inherit version src;

  nativeBuildInputs = with ocamlPackages; [
    dune_3
    findlib
    menhir
    ocaml
    python3.pkgs.wrapPython
  ];

  buildInputs = with ocamlPackages; [
    batteries
    dune-build-info
    dune-site
    pcre2
    why3
    yojson
    zarith
  ] ++ extraBuildInputs;

  propagatedBuildInputs = [ why3.out ];

  strictDeps = true;

  postPatch = ''
    substituteInPlace dune-project --replace-fail '(name easycrypt)' '(name easycrypt)(version ${rev})'
  '';

  pythonPath = with python3.pkgs; [ pyyaml ];

  installPhase = ''
    runHook preInstall
    dune install --prefix $out ${pname}
    rm -rf $out/lib/easycrypt/ecLib
    rm $out/bin/ec-runtest
    wrapPythonProgramsIn "$out/lib/easycrypt/commands" "$pythonPath"
    runHook postInstall
  '';

}
