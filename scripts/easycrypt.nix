{ ecRef
, lib
, stdenv
, fetchFromGitHub
, applyPatches
, fetchpatch
, ocamlPackages
, python3
, why3
, fetchurl
}:

with {

  "dev" = {
    version = "main";
    rev = "????";
    src = builtins.fetchTarball "https://api.github.com/repos/easycrypt/easycrypt/tarball/main";
    local_why3 = why3.override { version = "1.8.0"; };
  };

  "release" = rec {
    version = "2024.09";
    rev = "r${version}";
    src = applyPatches {
      src = fetchFromGitHub {
        owner = "easycrypt";
        repo = "easycrypt";
        inherit rev;
        hash = "sha256-ZGYklG1eXfytRKzFvRSB6jFrOCm1gjyG8W78eMve5Ng=";
      };
      patches = fetchpatch {
        url = "https://github.com/EasyCrypt/easycrypt/commit/c8595b5fbb99b215f765b670ce206c235b326133.patch";
        hash = "sha256-DpCpDzoFW/BZu5doJwM/4iSbkZ085qESUZAdqxRVK3U=";
      };
    };
    local_why3 = why3.override { version = "1.7.2"; };
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
    local_why3
    yojson
    zarith
  ];

  propagatedBuildInputs = [ local_why3.out ];

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
