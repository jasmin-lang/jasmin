# Easycrypt extraction

The Jasmin compiler is formally proven in Coq, this means that we have a formal proof ensuring that it preserves the semantics of safe programs. But how can we prove that a source Jasmin program satisfies properties that will be preserved by the compiler?
To that end, the compiler allows to extract Jasmin program to an equivalent EasyCrypt model. This extraction is correct on [safe programs](safety_checker).

## Command line for extraction

The command to extract EasyCrypt programs is the following: 

```
jasmin2ec -o extracted.ec source.jazz
```

The complete list of the options is given by `jasmin2ec --help`; the most useful
ones are described below.

By default, `jasmin2ec` will extract all the functions in a file, however a
(set of) specific function(s) can be extract using the `--function`
command-line parameter one of multiple times (this also extracts the functions
called the function to be extracted).

When no output file is specified, the extracted model is printed (but auxiliary
theories are not saved, so the model might not run through EasyCrypt
successfully).

The `--output-array` parameter allows to specify a separate directory to store
the generated auxiliary EasyCrypt theories. By default this is the same
directory as the directory of the output file.

The `--array-model` parameter selects how Jasmin arrays are represented in the
extracted model. With `barray` (the default), an array is a byte array: a
`stack u64[4]` variable is extracted as a value of type `BArray32.t` (32 being
the size of the array in bytes) and all its accesses, whatever their word size,
are operators of the `BArray32` theory. With `warray`, an array is a polymorphic
array of machine words: the same variable is extracted as a value of type
`W64.t Array4.t`; the accesses whose word size differs from the one of the array
go through auxiliary theories, generated together with the model. The `old`
model is deprecated: it uses the same representation as `warray`, but such
accesses are expanded into anonymous functions instead of using the functions of
the EasyCrypt library.

By specifying `--model=CT`, the extracted EasyCrypt model allows to verify that
the Jasmin program satisfies the cryptographic constant time property, as an alternative to `jasmin-ct`.
For more explanation on how to verify that a program is constant time, see the [Constant-time verification](ct) page.

The `--global-model` parameter selects how global variables are extracted: as
abbreviations (`abbrev`, the default), as operators (`op`), or as operators
declared with some options (`op=opaque`, `op="opaque smt_opaque"`, …).
It also selects how the machine words of global variables are printed: as
signed integers (`sign=signed`, the default) or as unsigned ones
(`sign=unsigned`). The parameter may be given several times to set both, e.g.
`--global-model op=smt_opaque --global-model sign=unsigned`; the last value of
each kind wins. The spaces around the `=` are optional, so `--global-model
"sign = unsigned"` is also accepted. See [Extraction of global
variables](#extraction-of-global-variables) below.

## Extraction of global variables

Each global variable is extracted as one EasyCrypt declaration, either an
abbreviation or an operator. The default is given by the `--global-model`
parameter described above; it can be overridden for a specific global variable
by annotating its declaration with `#[abbrev]` or `#[op]` (and, for the sign,
with `#[sign=signed]` or `#[sign=unsigned]`).

The `#[op]` annotation takes as (optional) attribute the options of the
EasyCrypt operator, written as an identifier or, when there are several of them,
as a string. For instance, the following declarations

```
#[abbrev]                  u64    g0 = 0;
#[op]                      u64    g1 = 1;
#[op=opaque]               u64    g2 = 2;
#[op="opaque smt_opaque"]  u64    g3 = 3;
#[op=smt_opaque]           u64[2] t  = { 4, 5 };
```

are extracted as

```
abbrev g0 = (W64.of_int 0).
op g1 = (W64.of_int 1).
op [opaque] g2 = (W64.of_int 2).
op [opaque smt_opaque] g3 = (W64.of_int 3).
op [smt_opaque] t = (BArray16.of_list64 [(W64.of_int 4); (W64.of_int 5)]).
```

The options are not interpreted by Jasmin, they are printed as such between
brackets; therefore any option understood by EasyCrypt can be used. The most
useful ones are `opaque`, which prevents the definition from being unfolded by
reduction, and `smt_opaque`, which prevents it from being sent to the SMT
solvers. Declaring large tables as `#[op=smt_opaque]` usually speeds up the
proofs a lot.

The values stored in global variables are machine words; the integer given to
`of_int` in the extracted model is, by default, the *signed* value of the word,
so that it may be negative. The `--global-model sign=unsigned` command-line
parameter asks for the *unsigned* value instead, and the `#[sign=signed]` and
`#[sign=unsigned]` annotations override that default for a specific global
variable. For instance, the declaration

```
u64[2] t = { 1, -1 };
```

is extracted as

```
abbrev t = (BArray16.of_list64 [(W64.of_int 1); (W64.of_int (-1))]).
```

by default, and as

```
abbrev t = (BArray16.of_list64 [(W64.of_int 1); (W64.of_int 18446744073709551615)]).
```

with `--global-model sign=unsigned` (or when the declaration is annotated with
`#[sign=unsigned]`). Both denote the same words, since `of_int` works modulo
2^n, but the second form does not use the unary minus: this makes large tables
noticeably cheaper to handle in EasyCrypt, in particular when they are computed
by reduction.

The two kinds of annotations can be combined, as in

```
#[op=smt_opaque, sign=unsigned] u64[2] t = { 1, -1 };
```

## Configure EasyCrypt to verify Jasmin programs

EasyCrypt models of Jasmin programs may refer to modules such as `JModel_x86`
or `JWord` These are part of the Jasmin library for EasyCrypt (to be found in
the source code of Jasmin, or available as part of one of the Jasmin software
packages).

To instruct `easycrypt` how to find these modules, set the
`EC_RDIRS=Jasmin:/path/to/easycrypt/jasmin/` environment variable (with the
correct path of the directory containing the modules).

You may also write a configuration file for EasyCrypt (usually in
`~/.config/easycrypt/easycrypt.conf`) or an `easycrypt.project` (in the
directory where you run EasyCrypt) with the following contents (with the
correct path depending on your local installation of Jasmin):
~~~
[general]
idirs=Jasmin:~/.nix-profile/lib/easycrypt/jasmin/
~~~

> Note: modules such as `JBArray8` are generated by `jasmin2ec`, they are not part of the library.

