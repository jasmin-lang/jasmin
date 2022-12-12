
# [unreleased]

## New features

- More x86 instructions are available:
  `VPMUL`
  ([PR #276](https://github.com/jasmin-lang/jasmin/pull/276)),
  `VPAVG`
  ([PR #285](https://github.com/jasmin-lang/jasmin/pull/285)).

## Bug fixes

- Safety checker handles the `#copy` operator
  ([PR #312](https://github.com/jasmin-lang/jasmin/pull/312);
  fixes [#308](https://github.com/jasmin-lang/jasmin/issues/308)).

# Jasmin 2022.09.0

## Bug fixes

- Fix printing of `while` loops
  ([PR #131](https://github.com/jasmin-lang/jasmin/pull/131)).

- Improved removal of assignments introduced by inlining
  ([PR #177](https://github.com/jasmin-lang/jasmin/pull/177);
  fixes [#175](https://github.com/jasmin-lang/jasmin/issues/175)).

- More precise pretyping for "reg const ptr" and function call.
  ([PR #178](https://github.com/jasmin-lang/jasmin/pull/178);
  fixes [#176](https://github.com/jasmin-lang/jasmin/issues/176)).

- Various fixes to the LATEX printer
  ([PR #212](https://github.com/jasmin-lang/jasmin/pull/212);
  fixes [#197](https://github.com/jasmin-lang/jasmin/issues/197)).

- Conditional function calls now produce a clearer error message
  ([PR #215](https://github.com/jasmin-lang/jasmin/pull/215);
  fixes [#199](https://github.com/jasmin-lang/jasmin/issues/199)).

- Fix lowering of not-equal conditions in assignments
  ([PR #216](https://github.com/jasmin-lang/jasmin/pull/216);
  fixes [#200](https://github.com/jasmin-lang/jasmin/issues/200)).

- Do not spuriously warn about missing “iinfo”
  ([PR #225](https://github.com/jasmin-lang/jasmin/pull/225);
  fixes [#224](https://github.com/jasmin-lang/jasmin/issues/224)).

- Fix inference of mutability of `ptr` parameters during stack-allocation
  ([PR #227](https://github.com/jasmin-lang/jasmin/pull/227);
  fixes [#190](https://github.com/jasmin-lang/jasmin/issues/190)).

- Fix possible crashes of stack-allocation
  ([PR #228](https://github.com/jasmin-lang/jasmin/pull/228);
  fixes [#58](https://github.com/jasmin-lang/jasmin/issues/58)).

- Fix a failing assertion in extraction to EasyCrypt for constant-time
  ([PR #229](https://github.com/jasmin-lang/jasmin/pull/229);
  fixes [#202](https://github.com/jasmin-lang/jasmin/issues/202)).

- Fix extraction to EasyCrypt for constant-time of intrinsics with zero-extend
  ([PR #251](https://github.com/jasmin-lang/jasmin/pull/251);
  fixes [#250](https://github.com/jasmin-lang/jasmin/issues/250)).

## New features

- Added instruction `#randombytes` to fill an array with “random” data
  ([PR #171](https://github.com/jasmin-lang/jasmin/pull/171)).
  The typical use is: `p = #randombytes(p);`.

- Added access to mmx registers
  ([PR #142](https://github.com/jasmin-lang/jasmin/pull/142)).
  + declaration:
    ```
         reg u64 x; // normal register
    #mmx reg u64 m; // mmx register
    ```
  + move from/to normal register: `x = m; m = x;`
  + move from/to normal register using intrinsics: `x = #MOVX(m); m = #MOVX(x);`
  + supported sizes: `MOVX_32` and `MOVX_64`

- Added option `-call-conv {windows|linux}` to select calling convention
  ([PR #163](https://github.com/jasmin-lang/jasmin/pull/163)).
  Default depends on host architecture.

- Added syntactic sugar for `else if` blocks
  ([PR #244](https://github.com/jasmin-lang/jasmin/pull/244)).
  I.e., you can now use constructions like:
  ```
  if x == 0 {
    // (...)
  } else if x == 1 {
    // (...)
  } else {
    // (...)
  }
  ```

- EasyCrypt extraction of array support libraries is controlled
  through the `-oecarray dir` command line argument
  ([PR #246](https://github.com/jasmin-lang/jasmin/pull/246)).

## Improvements

- Intrinsics present at source-level can no longer be removed by dead-code elimination
  ([PR #221](https://github.com/jasmin-lang/jasmin/pull/221);
  fixes [#220](https://github.com/jasmin-lang/jasmin/issues/220)).

- Lowering of a memory-to-memory copy always introduce an intermediate copy through a register
  ([PR #184](https://github.com/jasmin-lang/jasmin/pull/184)).

- `fun_info` are `FInfo.t`, `instr_info` are `IInfo.t`, and `var_info` are `Location.t`;
   this removes costly translations with `positive` and big conversion tables
   ([PR #209](https://github.com/jasmin-lang/jasmin/pull/209),
   [PR #226](https://github.com/jasmin-lang/jasmin/pull/226),
   [PR #233](https://github.com/jasmin-lang/jasmin/pull/233)).

- For loops and “inline”-annotated instructions that remain after
  “unrolling” yield a proper error message
  ([PR #243](https://github.com/jasmin-lang/jasmin/pull/243);
  fixes [#29](https://github.com/jasmin-lang/jasmin/issues/29),
  fixes [#150](https://github.com/jasmin-lang/jasmin/issues/150)).

- Using option `-oec` without option `-ec` extracts all functions.

- Extraction to EasyCrypt is now tested in continuous integration
  ([PR #260](https://github.com/jasmin-lang/jasmin/pull/260);
  fixes [#136](https://github.com/jasmin-lang/jasmin/issues/136),
  fixes [#104](https://github.com/jasmin-lang/jasmin/issues/104)).

# Jasmin 2022.04.0

This release is the result of more than two years of active development. It thus
contains a lot of new functionalities compared to Jasmin 21.0, the main ones
being listed below, but also a lot of breaking changes. Please upgrade with
care.

Here are the main changes of the release.
- **A new kind of function, subroutines,** in addition to inline functions and
  export functions. They are declared with `fn` only, while inline functions are
  declared with `inline fn` and export functions with `export fn`. This is a
  breaking change, since before `fn` was a synonym for `inline fn`. Unlike
  inline functions, they are proper functions. Unlike export functions, they are
  internal. As such, they do not need to respect any standard calling convention
  and are therefore a bit more flexible.

- **New storage modifiers `reg ptr` and `stack ptr`** to declare arrays.
  `reg ptr` is used to store the address of an array in a register. The
   main use of `reg ptr` arrays is to pass stack arrays as arguments to
   subroutines, since they do not accept stack arrays as arguments
  directly. `stack ptr` is used to spill a `reg ptr` on the stack. In the
  semantics, the storage modifiers are not taken into account, meaning that
  `stack`, `reg ptr` and `stack ptr` arrays are treated the same, which allows
  to reason easily about the source program. The compiler ensures that
  compilation does not change the semantics of the program. In the case it
  would, the compilation simply fails.

- **Support of global arrays.** These arrays are defined outside any function
  and are immutable. A global array must be initialized at the same time it is
  declared, specifying the array as comma-separated values between curly
  brackets. For instance, `u64[2] g = { 13, 29 };` is a valid global array
  declaration.

- **Support of sub-arrays.** A new syntax is introduced to manipulate slices of
  arrays. The concrete syntax is `a[pos:len]` to specify the slice of array `a`
  starting at index `pos` and of length `len`. For now, `pos` and `len` must be
  compile-time constants. This limitation is expected to be weakened in the
  future. This syntax cannot be used for `reg` arrays. The same remark as for
  `reg ptr` applies, if the compiler cannot prove that compilation does not
  change the semantics of the program, then it fails.

- **A flexible annotation system**. In addition to function declarations that
  were already supported, it is now possible to attach annotations
  to instructions, variable declarations and return types. The concrete syntax
  is the following: `#[annotation]` or `#[annotation=value]`.

- **Writing to the lower bits of a register.** Instead of computing a small
  value and writing it afterwards to a larger register, one can compute the
  value, write it to the lower bits of the large register and zero the higher
  bits in one go. This works only with certain assembly operators. The operator
  must be prefixed with a cast to the right size. Here is an example
  illustrating the feature.
  ```
  reg u64 x y; reg u256 z;
  z = (256u)#VPAND(x, y); // writes the bitwise AND of x and y to the lower bits
                          // of z, and zeroes the other bits of z
  ```

- **An include system.** Including a Jasmin file in another one is now a native
  feature of Jasmin. The concrete syntax is `require "file.jazz"`. If the path
  is relative, it is interpreted relatively to the location of the Jasmin file.
  To deal with more complex cases, an option `-I ident:path` was added to the
  compiler. It adds `path` (interpreted relatively to the current directory if
  it is relative) with logic name `ident` to the search path of the compiler.
  The same operation can be performed using the environment variable
  `JASMINPATH`. The syntax is `JASMINPATH="ident1=path1:ident2=path2"`.
  Then one can use `from ident require "file.jazz"` to refer to file
  `path/file.jazz`. The error messages of the compiler contain the list of
  transitively included files if needed, so locating the problematic line should
  be easier than with manual includes.

- **A new operator, `#copy` to copy register arrays.** It is used like an
  assembly operator, `a = #copy(b);` or `a = #copy_128(b);` if the word size
  needs to be specified. It is added automatically to assignments of the form
  `a1 = a2;` where `a1` and `a2` are arrays and at least one of them is a
  register array.

- **Easier flag manipulation.** Boolean flags can now be referred to by their
  names. For instance, `?{cf=b} = #CMP(x,y);` assigns the carry flag to variable
  `b`. The `cf=` part is not needed if the variable already has the name of a
  flag (this is case-insensitive), e.g. `?{CF} = #CMP(x, y);` assigns the carry
  flag to variable `CF`. One can even use names for boolean expressions that are
  computed based on a combination of flags. For instance,
  `?{"==" = b, "<s" = c} = #CMP(x, y);` assigns the result of the equality test
  to variable `b` and the result of the signed comparison to variable `c`.
  Jasmin knows how to translate that into the right combination of flags.

- **A type system for cryptographic constant time.** Function arguments and
  return types, as well as local declarations, can be annotated (using the
  aforementionned annotation system) with a security level. This can either be
  `#public`, `#secret`, `#poly=l` or `#poly={l1,...,ln}`, where `l1`, ..., `ln`
  are security level variables that allow to express the security level of one
  variable depending on the security levels of other variables. Then option
  `-checkCTon f` calls a type-checker on function `f` that checks that `f` can
  be given a security type compatible with the annotations given by the user.
  Option `-checkCT` checks the whole program. If the annotations are partial,
  the type-checker tries to infer the missing parts, except for the signature of
  export functions since that part is expected to be specified by the user. The
  analysis is flow-sensitive, meaning that one variable can have two different
  security levels at two different points in the program. This is the default
  when a variable is not annotated. When a variable is annotated, it is expected
  to have the given level at all points where it appears. If the user wants to
  change the default behaviour, it can use `#flex` or `#strict` to choose
  whether the security level of a variable can vary or not over its lifetime.
  Jasmin already supported some way of reasoning about constant-time in the form
  of an alternative extraction to EasyCrypt making leakages explicit. This
  extraction is more flexible, but in general the type system should be easier
  to use.

- **No export of global variables anymore.** Global variables are no longer
  visible outside of the Jasmin compilation unit, so they cannot be referred to
  by other compilation units at link time.

- **New tunneling pass.** At the end of the compilation, the compiler tries to
  replace a jump pointing to another jump by a single jump pointing to the
  target of the second jump.

- **New heuristic for register allocation.** The old one can be called with
  option `-lazy-regalloc`. If the compilation fails with the default one, it may
  succeed with `-lazy-regalloc`. The old heuristic appears to give in some cases
  more intuitive results.

- **Support of Intel syntax.** Jasmin used to print assembly programs only in
  AT&T syntax. This remains the default, but there is a new option `-intel` to
  print it in Intel syntax.

- **Declarations anywhere in the function body.** Before, the declarations had
  to be at the start of the function body. This was relaxed, they can now appear
  anywhere in the body.

- **Printing in Jasmin syntax.** The compiler used to print programs in a syntax
  that was different from the Jasmin syntax, in general for no good reason. It
  now tries to use Jasmin syntax. In particular, the output of option `-ptyping`
  should always be syntactically valid. Please report an issue if it is not the
  case!

- **Nicer errors.** The error system was rewritten. This should give more
  uniform and a bit nicer error messages.

# Jasmin 21.0

This is the initial release of Jasmin.
