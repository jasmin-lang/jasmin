# Syntax reference

Jasmin is a low-level language: it is essentially assembly with variables and
structured control flow.
It should be thought of as a tool to help you write assembly: programmers use
Jasmin to produce specific assembly code in a convenient, safe, and secure
manner.

This section documents the surface syntax of the language. For the operational
meaning of each construct, see the [semantics reference](../semantics/index.md).
For annotations that customize compiler behavior and declare security properties,
see the [annotations reference](../annotations/index.md).

## Notation conventions

The grammar notation used throughout this reference is an informal BNF:

- `<name>` -- a nonterminal (a syntactic category)
- `"keyword"` -- a literal keyword or symbol
- `|` -- alternatives
- `?` -- optional (zero or one)
- `*` -- zero or more repetitions
- `+` -- one or more repetitions
- `(` `)` -- grouping

Concrete examples always precede the grammar rules.

## Architecture considerations

The core Jasmin syntax is architecture-neutral. Architecture-specific features
(intrinsic names, available register widths, alignment requirements) are noted
inline where relevant. See the architecture-specific documentation for full
details on each target.

:::{toctree}
:maxdepth: 2

structure.md
types.md
code.md
expressions.md
lvalues.md
:::
