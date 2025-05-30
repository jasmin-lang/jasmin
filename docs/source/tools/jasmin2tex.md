# How to pretty-print a Jasmin program

The `jasmin2tex` tool (distributed with the Jasmin compiler; named `jazz2tex` before release 2023.06.4) can write LATEX representations of Jasmin programs:


    jasmin2tex -o output.tex input.jazz

The produced LATEX snippet is meant to be included in a `jasmincode` environment provided by the `jasmin` package defined in the following file: [jasmin.sty](./resources/jasmin.sty).
