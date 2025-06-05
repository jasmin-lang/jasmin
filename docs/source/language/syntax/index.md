# Syntax reference

Jasmin is a low-level language: it is essentially assembly with variables and
structured control flow.
It should be thought of as a tool to help you write assembly: programmers use
Jasmin to produce specific assembly code in a convenient, safe and secure
manner.
This means that there are special considerations for each architecture.
You can read these for the [[x86-64|x86-64]] and the [[ARMv7-M|ARMv7-M]] target
architectures.

:::{toctree}
:maxdepth: 2

structure.md
code.md
expressions.md
lvalues.md
:::
