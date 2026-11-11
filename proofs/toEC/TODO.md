# Extraction to EasyCrypt: what remains to do

Points left for later on the extraction (`jasmin2ec`) and on its safety
variant (`jasmin2ec --safety`).

## Passes to add

- **Explicit size extension of operator outputs.** An operator that extends
  the size of its outputs, `BaseOp (Some ws, o)`, for instance
  `?{}, b = (64u)#ADD_32(a, 1)`, has `b : u64` as output type (`instr_desc`
  gives the extended type to the word outputs), while the EasyCrypt operator
  `ADD_32` returns the outputs at their base size. The printer bridges the
  gap with an auxiliary variable, `(oF, cF, sF, pF, zF, aux) <- (ADD_32 a
  (W32.of_int 1)); b <- (zeroextu64 aux);`, the only auxiliary variable it
  still creates (`ec_dests` in `toEC.ml`). A proved pass should produce this
  shape in the Jasmin program: the operator at its base size writes a
  variable of the base type, followed by an assignment that zero-extends it
  into the destination. `normalize_calls` does not cover this case: every
  destination already fits the output type, the mismatch only exists between
  the Jasmin type and the result type of the EasyCrypt operator.
- **Explicit casts in expressions.** An operator applied to an argument of a
  larger word type truncates it implicitly, `x_32 +32 y_64`. A proved pass
  should write the truncation in the source, `x_32 +32 (32u)y_64`, so that
  the printer prints expressions as they stand instead of inserting the
  casts itself (`ec_cast`, `truncateu*` in `toEC.ml`).

Both passes are needed by the plain extraction and by the safety extraction.

## Printer

- **`witness` only where needed.** `toec_fun` initialises every local array
  to `witness`, sorted by name. Compute instead the variables live at the
  entry of the function (the liveness of `dead_code`, with the results and
  the memory live at exit), and initialise only the local arrays of that set
  that are not parameters. Writing a cell (`Laset`, `Lasub`) reads the array,
  so the stack arrays filled cell by cell stay initialised; the `reg ptr`
  locals assigned from a stack array, the results of `#copy` and of calls,
  and the `_` destinations lose their initialisation. Many extracted files
  change: a printer change of its own, with the corpus replayed before and
  after. Open question: the non-array locals live at entry are never
  initialised (reading one is a safety error in Jasmin).
- **Name of the output file.** The file of `--safety-specs` requires the
  theory of the extracted file, named after the file given by `-o`; a name
  that is not an EasyCrypt identifier (`-o call-export.ec` gives
  `require import Call-export.`) makes the specification file unusable.
  `jasmin2ec` should reject such a name with a message when
  `--safety-specs` is given.

## Safety: contracts

- **Copies around the calls.** `contracts_to_asserts` copies every argument
  of a call to a function with a contract into a fresh variable (`ip := es`),
  and the parameters into the contract variables in the callee
  (`iparams := params`), because the postcondition may read them. With the
  default contract the postcondition reads only the results, so these copies
  (`a_0 <- a; xx <- x; b_xx <- b_x;` before `g (a_0, xx, b_xx)`, and
  `b_x_0 <- b_x` before the requires test) are dead weight. Copy only what
  the postcondition reads, or nothing when it reads no parameter: a change of
  the pass and of its proof.

## Safety: simplification of the assertions

- **Bounds of the array accesses.** The condition of an access `x[i]` with
  `i : u64` is `0 <= to_uint i * 8 /\ to_uint i * 8 + 8 <= 32`.
  - The lower half needs only a context-free interval evaluation of the
    integer expressions: `to_uint` of a word is in `[0, 2^n)`, a literal has
    its value, sums and products of intervals are computed; `lo <= e` is
    `true` when the lower bound of `e` is at least `lo`, symmetrically for
    the upper bound. The proof is a lemma on the evaluation of an
    expression: the interval contains the value, and the operations covered
    do not fail in the total mode, so the rewriting drops nothing that could
    fail.
  - The upper half needs the guard `i \ult 4`. The guard of a `while` holds
    in its body and that of an `if` in its branches: a new fact `Aival lo hi`
    on the scalar variables the guard compares to constants, killed at the
    writes as the other facts are, and not part of the fixpoint at the head
    of the loop (it comes from the guard of the current iteration). The
    interval evaluation then reads the facts of the variables. Heavier
    proof: the soundness of the facts a guard gives.
- **Export the facts.** The facts the pass computes are lost: the
  postcondition it proves is removed from the code, but the EasyCrypt
  specification still states it and the EasyCrypt proof redoes the work (the
  loop invariant `is_init b_x 0 32` of `double_safe` in
  `compiler/examples/extraction-safety-unit-tests/proofs.ec` is exactly the
  fact of the pass at the head of the loop). Keep an assertion that the pass
  reduces to `true` with a label `proved`, and insert at the head of each
  loop body an assertion `invariant` translating the state of the fixpoint
  (`Afull x` gives `is_barr_init x 0 len`, `Ainit l` a conjunction on its
  intervals, `Aconst c` gives `x == c`): a true assertion can be added
  without changing the theorem, and its truth is the soundness of the
  abstract state the pass already proves. The printer prints these labels as
  comments, not as `raise`, and writes in the specification file a proof
  skeleton, `proc; wp; while (inv); auto => />; smt()`.
