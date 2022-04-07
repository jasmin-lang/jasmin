# Jasmin 22.0

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
  internal. As such, they do not need to respect the calling conventions of C
  and are therefore a bit more flexible.

- **New storage modifiers `reg ptr` and `stack ptr`** to declare arrays.
  `reg ptr` is used to store the address of a stack array in a register. The
   main use of `reg ptr` arrays is to pass stack arrays as arguments to
   subroutines, since the latter do not accept stack arrays as arguments
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

- **A flexible annotation system**. It allows to attach annotations to most of
  the constructs of the language (e.g. functions and instructions). The concrete
  syntax is the following: `#[annotation]` or `#[annotation=value]`.

- **Writing the lower bits of a register.** Instead of computing a small value
  and writing it afterwards in a larger register, one can write to the lower
  bits of a register and zero the higher bits in one go. Here is an example
  illustrating the feature.
        reg u64 x; reg u256 y;
        y = (256u)#VMOV(x); // writes x in the lower bits of y
                            // and zeroes the other bits of y

- **An include system.** Including a Jasmin file in another one is now a native
  feature of Jasmin. The concrete syntax is `require "file.jazz"`. If the path
  is relative, it is interpreted relatively to the location of the Jasmin file.
  To deal with more complex cases, an option `-I ident:path` was added to the
  compiler. It adds `path` (interpreted relatively to the current directory if
  it is relative) with logic name `ident` to the search path of the compiler.
  Then one can use `from ident require "file.jazz"` to refer to file
  `path/file.jazz`. The error messages of the compiler contain the list of
  transitively included files if needed, so locating the problematic line should
  be easier than with manual includes.

- **A new operator, `#copy` to copy register arrays.** It is used like an
  assembly operator, `a = #copy(b);` or `a = #copy_128(b);` if the word size
  needs to be specified.

- **Easier flag manipulation.** Boolean flags can now be referred to by their
  names. For instance, `?{cf=b} = #CMP(x,y);` assigns the carry flag to variable
  `b`. The `cf=` part is not needed if the variable already has the name of a
  flag (this is case-insensitive), e.g. `?{cF} = #CMP(x, y);` assigns the carry
  flag to variable `cF`. One can even use names for boolean expressions that are
  computed based on a combination of flags. For instance,
  `?{"==" = b, "<s" = c} = #CMP(x, y);` assigns the result of the equality test
  to variable `b` and the result of the signed comparison to variable `c`.
  Jasmin knows how to translate that into the right combination of flags.

- **Nicer errors.** The error system was rewritten. This should give more
  uniform and a bit nicer error messages.

# Jasmin 21.0

This is the initial release of Jasmin.
