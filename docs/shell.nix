{ pkgs ? import <nixpkgs> { } }:

with pkgs;

mkShell {
  packages = [
    graphviz
    (python3.withPackages
      (ps: [ ps.myst-parser ps.sphinx ps.sphinx-rtd-theme ps.sphinx-copybutton ]))
  ];
}
