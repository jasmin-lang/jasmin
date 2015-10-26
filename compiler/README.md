Installing with OPAM
====================

1. Switch to the dmasm directory.

2. Create a new opam switch for dmasm and activate it:

```
opam switch dmasm --alias-of 4.02.3
eval `opam config env`
```

3. Install all dependecies using opam:

```
opam pin add dmasm `pwd` -n
opam install dmasm --deps-only
```

4. Compile dmasm and test:

```
make dmasm
make test-dmasm-square # output assembly file
make unit-tests
```