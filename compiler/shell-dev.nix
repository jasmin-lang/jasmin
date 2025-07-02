with import <nixpkgs> {};

let
  jasminCompiler = import ./default.nix;
in
pkgs.mkShell {
  inputsFrom = [ jasminCompiler ];
  nativeBuildInputs = ([llvmPackages.bintools-unwrapped]) ++ (with ocamlPackages; [ ocaml-lsp ocamlformat]) ;
}
