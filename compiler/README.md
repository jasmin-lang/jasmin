# Jasmin Compiler

More information about this compiler (build instructions in particular) can be
found on the online [wiki](https://github.com/jasmin-lang/jasmin/wiki).

The Jasmin compiler is free software. All files in this distribution are, by
default, licensed under the [MIT license](LICENSE). The exceptions are given
below.

The files `src/puf.ml` and `src/puf.mli` are distributed under the terms of the
GNU Library General Public License version 2.1, with the special exception on
linking described in file [`src/LICENSE.puf`](src/LICENSE.puf).

The contents of the `CIL` directory are extracted from Coq files from several sources:

 -  the Coq standard library (LGPL 2.1 only, see [`CIL/LICENSE.coq`](CIL/LICENSE.coq))
 -  the Mathematical Components library (CēCILL-B, see [`CIL/LICENSE.mathcomp`](CIL/LICENSE.mathcomp))
 -  the coqword library (MIT, see [`CIL/LICENSE.coqword`](CIL/LICENSE.coqword))
 -  the Jasmin coq source files (MIT, the [same license](LICENSE) as the rest of the compiler).
