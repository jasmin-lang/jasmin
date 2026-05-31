# Jasmin

## About

Jasmin denotes both a language and a compiler designed for
writing high-assurance and high-speed cryptography.
Jasmin implementations aim at being efficient, safe, correct, and secure.

Reference documentation of the language and compiler are on [readthedocs](https://jasmin-lang.readthedocs.io).

## What is this repository?

The code in this repository is automatically extracted from
Jasmin’s source on [GitHub](https://github.com/jasmin-lang/jasmin/).
The original code is a mix of OCaml and Rocq, while this extracted
code contains OCaml only.
It enables compiling the Jasmin tools from source without having to install
Rocq and the Rocq dependencies used by Jasmin.

## Installation

For a complete installation guide covering several use cases, please read our
[documentation](https://jasmin-lang.readthedocs.io/en/stable/misc/installation_guide.html).

If you just want to install the Jasmin tools, here is a TL;DR:

- with APT (debian, ubuntu), a package is available in a dedicated repository,
  see the [documentation](https://jasmin-lang.readthedocs.io/en/stable/misc/installation_guide.html#on-debian-and-related-linux-distributions)

- from AUR (arch linux), a package is available in the Arch User Repository,
  see the [documentation](https://jasmin-lang.readthedocs.io/en/stable/misc/installation_guide.html#on-arch-linux)

- with nix
  ```
  nix-env -iA nixpkgs.jasmin-compiler
  ```

- with opam
  ```
  opam install jasmin
  ```

## Getting support

The [Formosa-Crypto Zulip Chat](https://formosa-crypto.zulipchat.com/) is meant for anybody interested in high-assurance cryptography using EasyCrypt, Jasmin, and related tools.

## License

Jasmin is free software. All files in this distribution are, unless specified
otherwise, licensed under the [MIT license](LICENSE).
