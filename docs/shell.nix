{ pkgs ? import <nixpkgs> { } }:

with pkgs;

mkShell {
  packages = [
    (python3.withPackages
      (ps: [ ps.myst-parser ps.sphinx ps.sphinx_rtd_theme ]))
  ];
}
