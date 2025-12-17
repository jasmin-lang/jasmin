# FAQ

## How to debug compilation errors?

### Register allocation

> register allocation: no more register to allocate “ ra.357”

This message says that there are no free registers for storing the return address of some function
(its name is a white space followed by `ra`).
Which function? With the command-line flag `-debug` on, the compiler will output the required information
(`grep` for the actual name of the variable to filter the too verbose output).

There are two possible kinds of fix to this kind of issue: either spill some registers to ensure there is at least one register that is free at *all* call sites; or change the calling-convention of the function so that return address is passed on the stack
(this can be achieved through the `#returnaddress=stack` annotation before the function declaration).

### Stack allocation

> no region associated to variable p

Here is a minimal program triggering this error:

~~~
export fn dangling_reference() -> reg u32 {
  reg ptr u32[1] p;
  p[0] = 0;
  reg u32 r;
  r = p[0];
  return r;
}
~~~

The problem comes from the fact that there is no memory allocated to the array: variable `p` is tagged as `ptr` so that after compilation the register that corresponds to `p` only contains a reference (aka a pointer) to the array. One way to solve this issue is to link `p` to an other array for which there is some allocated memory, for instance with: `stack u32[2] s; p = s[1:1];`.


### Linearization

> assignment remains

Assignments (instructions of the form `d = e;`) are processed by the various compilation passes,
removed (when they become dead) or replaced by target operations (i.e., assembly-level instructions, such as `rax = #MOV(rbx);`).
When everything goes well, all assignments are gone before the [linearization pass](../compiler/passes/linearization).

This error message arises when one of the earlier passes could not handle the assignment.
Often, the [instruction selection pass](../compiler/passes/inst_select) could not find in the target instruction set (ISA) an operation matching said assignment.
A common work-around is to decompose the assignment into several simpler steps.

## How do I set a register to zero?

For setting variables to zero, Jasmin has the special `#set0()` intrinsic.
For example:

```jazz
reg u64 i;

i = #set0();
while (i < 256) {
    // ...
    i += 1;
}
```

## How to achieve code reuse?

If you want to share some function, global or parameter
across several files, then this is exactly
the role of `require` directives (described [here](../language/syntax/structure.md#require)).
Just write the code to be reused in a dedicated file, typically with the extension `.jinc`,
and require it in the files where you need it.

If you want more advanced code reuse,
there is ongoing work to develop a proper module system in Jasmin,
but for the time being one solution is to abuse `require` directives.

Indeed, since the require system is purely syntactic,
it can enable some kind of template-like mechanism in Jasmin.
Instead of writing correct Jasmin code in the dedicated file,
one can write incorrect code, typically code that makes use
of undefined symbols, either variables or functions.
Taken in isolation, this is of course not valid code,
but if it is required in a file where
the symbols are defined, it becomes valid.

It may prove particularly useful in cryptography.
Indeed, it often happens that cryptographic algorithms depend on some
parameters and that several sets of parameters are possible.
One can write a Jasmin implementation that depends
on undefined parameters, and require it in different files that define
the parameters appropriately.

Here is an example.
In the file `hash.jinc`, the function `hash` takes as an argument an array `in`
of bytes of length `N`, hashes it, and returns the result in an array `out`
of length `M`.

```
// in file hash.jinc
fn hash (reg ptr u8[M] out, reg ptr u8[N] in) -> reg ptr u8[M] {
  ...
  return out;
}
```
Notice that this is not a well-defined Jasmin function, since `M` and `N` are not defined.

Files `hash_128_16.jazz` and `hash_256_32.jazz` instantiate the function
`hash` with the appropriate parameters.

```
// in file hash_128_16.jazz
param int N = 128;
param int M = 16;

require "hash.jinc"
```

```
// in file hash_256_32.jazz
param int N = 256;
param int M = 32;

require "hash.jinc"
```

If multiple instantiations of the same function
need to be made in the same file
(or in files that are transitively required by the same file),
this approach does not work directly, since there would be
several functions with the same name, hence a name clash.

The trick, in this case, is to take advantage of namespaces.
Indeed, if the template is instantiated in different namespaces,
there is no longer a name clash.

Reusing our `hash` example, we could write
the following file `hash.jazz`.

```
// in file hash.jazz

namespace Short {
  param int N = 128;
  param int M = 16;

  require "hash.jinc"
}

namespace Long {
  param int N = 256;
  param int M = 32;

  require "hash.jinc"
}

// we have two functions: Short::hash and Long::hash
```

:::{caution}
Both requires and namespaces
are purely syntactic constructs.
This is code reuse for the programmer,
who writes a function once and instantiates it several times,
but not for the Jasmin compiler,
for which each instantation is a different function.
In particular, this means that the assembly produced by the
compiler will contain one function per instantiation,
increasing code size.
More generally, all Jasmin tools will see the instantiations
as distinct functions.
This may imply doing the same work several times,
in particular if you start playing with the extraction
into EasyCrypt.
:::
