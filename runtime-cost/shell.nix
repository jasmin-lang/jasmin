{ pkgs ? import <nixpkgs> {}
}:

with pkgs;

stdenv.mkDerivation {

  name = "env";
  src = null;
  buildInputs = [ cargo rustfmt ];
  RUSTFLAGS = "-L./jlib";

}
