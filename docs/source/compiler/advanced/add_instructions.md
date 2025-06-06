# How to add new instructions

This is a brief overview of the process of adding support for new “intrinsics” into the Jasmin language and compiler.

## Write unit tests

This clarifies the concrete syntax and what are the possible variants of the new instruction.
For instance, the `VPMULHRS` intrinsic can operate on 128-bit vectors or 256-bit vectors;
in both cases, it treats them as vectors of 16-bit values;
it therefore supports two suffixes, `_8u16` and `_16u16`.

## Update the abstract syntax

The `asm_op` datatype (in file `proof/compiler/x86_instr_decl.v`) lists all supported instructions.
Add a variant to this datatype for each intrinsic.
Values in this type are often parameterized by a `wsize` argument (the size of the values it manipulates);
vector instructions are often additionally parameterized by a `velem` argument (the size of the elements in the vectors).

## Define the semantics

Define the semantics for the instruction when applied to well-typed value, as a total function.
This usually relies on machine-word operations that must be additionally defined in the `proof/lang/word.v` file.

## Write the descriptor

The instruction descriptor gathers information about the intrinsics: syntax (to
parse and pretty-print), semantics, calling-convention, valid ranges for
immediate arguments (if any), etc. There are a few notations available to ease
the definitions of such descriptors. The usual way to define a new descriptor is
to copy and adapt the descriptor for an instruction that has similar
constraints.

Add this descriptor to the `instr_desc` function that maps instructions from the
abstract syntax to their descriptor (for semantics and compilation) and to the
`prim_string` association list that maps mnemonics to abstract syntax (for
parsing and type-checking).

## Optionally add EasyCrypt support

The semantics of the added instruction can be defined or axiomatized in the
EasyCrypt theory found in the `eclib/` directory.
