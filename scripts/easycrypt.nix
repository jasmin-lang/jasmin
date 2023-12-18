{ ecRef
, lib
, stdenv
, fetchFromGitHub
, ocamlPackages
, python3
, why3
}:


with {

  "dev" = {
    version = "main";
    rev = "????";
    src = builtins.fetchTarball "https://api.github.com/repos/easycrypt/easycrypt/tarball/main";
  };

  "release" = rec {
    version = "2024.01";
    rev = "r${version}";
    src = fetchFromGitHub {
      owner = "easycrypt";
      repo = "easycrypt";
      inherit rev;
      hash = "sha256-UYDoVMi5TtYxgPq5nkp/oRtcMcHl2p7KAG8ptvuOL5U=";
    };
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
    inifiles
    why3
    yojson
    zarith
  ];

  propagatedBuildInputs = [ why3.out ];

  strictDeps = true;

  postPatch = ''
    substituteInPlace dune-project --replace '(name easycrypt)' '(name easycrypt)(version ${rev})'
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
