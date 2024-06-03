
# [unreleased]

## New features

- ARM now compiles `x = imm;` smartly: for small immediates, a single `MOV`; for
  immediates whose negation is small, a single `MVN`; and for large immediates
  a pair of `MOV` and `MOVT`.

- Export functions can have `ptr` arrays as arguments and results.
  The compiler assumes that writable `ptr` are disjoint from the other
  `ptr` arguments and from the global data. This is the responsibility of
  the caller to ensure that this holds.
  For now, writable `ptr` must come first in the list of arguments and be
  returned first and in the same order in the list of results.
  ([PR #707](https://github.com/jasmin-lang/jasmin/pull/707)).

- Add spill/unspill primitives allowing to spill/unspill reg and reg ptr
  to/from the stack without need to declare the corresponding stack variable.
  If the annotation #spill_to_mmx is used at the variable declaration the variable
  is spilled into a mmx variable (this works only for x86)
  See `compiler/tests/success/common/spill.jazz`.
  and `compiler/tests/success/X86-64/spill_mmx.jazz`.
  ([PR #687](https://github.com/jasmin-lang/jasmin/pull/687)) and
  ([PR #692](https://github.com/jasmin-lang/jasmin/pull/692)).

- Add a swap primitive,
    `x, y = #swap(x, y)`
  to allow swapping the contents of two operands.
  The x and y can be reg or reg ptr.
  The swap is performed without the need of extra register or memory access.
  On arm-m4, this is compiled using 3 xor instructions.
  See `compiler/tests/success/common/swap.jazz` and
      `compiler/tests/success/common/swap_word.jazz` for usage.
  ([PR #691](https://github.com/jasmin-lang/jasmin/pull/691),
   [PR #816](https://github.com/jasmin-lang/jasmin/pull/816)).

- Support Selective Speculative Load Hardening.
  We now support operators SLH operators as in [Typing High-Speed Cryptography
  against Spectre v1](https://ia.cr/2022/1270).
  The compilation of these is proven to preserve functional semantics.
  We also provide a speculative CCT checker, via the `jazzct` flag `--sct`.
  ([PR #447](https://github.com/jasmin-lang/jasmin/pull/447),
   [PR #723](https://github.com/jasmin-lang/jasmin/pull/723),
   [PR #814](https://github.com/jasmin-lang/jasmin/pull/814))

- Register arrays and sub-arrays can appear as arguments and return values of
  local functions;
  the “make-reference-arguments” pass is now run before expansion of register
  arrays
  ([PR #452](https://github.com/jasmin-lang/jasmin/pull/452),
  [PR #720](https://github.com/jasmin-lang/jasmin/pull/720)).

- Add the instruction `MULX_hi`,
     `hi = #MULX_hi(x, y);` is equivalent to `hi, _ = #MULX(x, y);`
  but no extra register is used for the low half of the result.

- Definition of parameters can now use arbritrary expressions and depend on
  other parameters. See `tests/success/common/test_globals.jazz`.
  ([PR #595](https://github.com/jasmin-lang/jasmin/pull/595)).

- The generated code for allocating and freeing stack frames in ARM has been
  slightly optimized: small constants are used as immediates, 16-bit or
  Thumb-expandable constants loaded with `MOV`, and bigger ones constructed
  with `MOV` and `MOVT`.
  ([PR #597](https://github.com/jasmin-lang/jasmin/pull/597)).

- Support stack zeroization.
  The compiler can introduce code that zeroizes the stack at the end of export
  functions. The user can enable this feature using either annotations
  (`stackzero` and `stackzerosize`), or compiler flags (`-stack-zero` and
  `-stack-zero-size`). Three strategies are currently supported: `unrolled`
  (the code is a sequence of writes as long as needed), `loop` (the code is
  a loop) and `loopSCT` (same as `loop` but with a `LFENCE` at the end to defend
  against Spectre).
  ([PR #631](https://github.com/jasmin-lang/jasmin/pull/631)).

- Interleave references to source-code positions within the assembly listings
  when the `-g` command-line flag is given (off by default).
  ([PR #684](https://github.com/jasmin-lang/jasmin/pull/684)).

- The Constant-Time security checker also accepts annotations for the
  *Speculative*-Constant-Time checker (`transient` and `msf` are interpreted as
  `public`; information relative to pointers or to mis-speculated executions is
  ignored)
  ([PR #773](https://github.com/jasmin-lang/jasmin/pull/773)).

- The Constant-Time security checker optionally runs the first compilation
  passes before checking; the last pass to run is configured through the
  `--compile` command line argument
  ([PR #788](https://github.com/jasmin-lang/jasmin/pull/788)).

- Global data in assembly listing now shows the names of all global variables
  ([PR #793](https://github.com/jasmin-lang/jasmin/pull/793)).

## Bug fixes

- The compiler rejects ARM intrincics with the `S` suffix if the instruction
  does not set flags
  ([PR #809](https://github.com/jasmin-lang/jasmin/pull/809);
  fixes [#808](https://github.com/jasmin-lang/jasmin/issues/808)).

- Type-checking rejects invalid variants of primitive operators
  ([PR #490](https://github.com/jasmin-lang/jasmin/pull/490);
  fixes [#488](https://github.com/jasmin-lang/jasmin/pull/488)).

- Constant propagation handles global variables assigned to inline variables
  ([PR #541](https://github.com/jasmin-lang/jasmin/pull/541);
  fixes [#540](https://github.com/jasmin-lang/jasmin/issues/540)).

- More precise detection of speculative safe loads in the SCT checker
  ([PR #556](https://github.com/jasmin-lang/jasmin/pull/556)).

- Fix expansion of `#copy` operators when target is marked as `ptr`
  ([PR #550](https://github.com/jasmin-lang/jasmin/pull/550);
  fixes [#499](https://github.com/jasmin-lang/jasmin/pull/499)).

- Improve the safety checking for `(I)DIV` x86 instructions
  ([PR #574](https://github.com/jasmin-lang/jasmin/pull/574);
  fixes [#561](https://github.com/jasmin-lang/jasmin/issues/561)).

- Remove dead functions after loop unrolling
  ([PR 611](https://github.com/jasmin-lang/jasmin/pull/611);
  fixes [#607](https://github.com/jasmin-lang/jasmin/issues/607)).

- Fix code generation for ARMv7 when stack frames are large
  ([PR 677](https://github.com/jasmin-lang/jasmin/pull/677)
  [PR 712](https://github.com/jasmin-lang/jasmin/pull/697);
  fixes [#696](https://github.com/jasmin-lang/jasmin/issues/696)).

- Fix code generation for ARMv7 when export function have large stack frames
  ([PR #710](https://github.com/jasmin-lang/jasmin/pull/710);
   fixes [#709](https://github.com/jasmin-lang/jasmin/issues/709)).

- Type-checking warns about calls to export functions that are not explicitly
  inlined; export functions called from Jasmin code are inlined at call sites
  ([PR #731](https://github.com/jasmin-lang/jasmin/pull/731);
  fixes [#729](https://github.com/jasmin-lang/jasmin/issues/729)).

- Attach more precise meta-data to variables introduced at compile-time
  ([PR #753](https://github.com/jasmin-lang/jasmin/pull/753);
  fixes [#718](https://github.com/jasmin-lang/jasmin/issues/718)).

- Correctly parse ARMv7 intrinsics whose name ends in `-S`
  ([PR #791](https://github.com/jasmin-lang/jasmin/pull/791);
  fixes [#546](https://github.com/jasmin-lang/jasmin/issues/546)).

## Other changes

- Pretty-printing of Jasmin programs is more precise
  ([PR #491](https://github.com/jasmin-lang/jasmin/pull/491)).

- Fix semantics of the `MULX` instruction
  ([PR #531](https://github.com/jasmin-lang/jasmin/pull/531);
  fixes [#525](https://github.com/jasmin-lang/jasmin/issues/525)).

- The deprecated legacy interface to the CT checker has been removed
  ([PR #769](https://github.com/jasmin-lang/jasmin/pull/769)).

- In x86 assembly, 8-bit immediate operands are printed unsigned,
  i.e., in the range [0; 255]
  ([PR #821](https://github.com/jasmin-lang/jasmin/pull/821);
  fixes [#803](https://github.com/jasmin-lang/jasmin/issues/803)).

# Jasmin 2023.06.3 — 2024-04-10

## New features

- The type system for constant time now ensures that division and modulo
  operators may only be used with public arguments.
  This ensures that problems like KyberSlash (https://kyberslash.cr.yp.to/) do
  not occur.
  ([PR #722](https://github.com/jasmin-lang/jasmin/pull/722)).

- Add the x86_64 instruction `XCHG`,
    `a, b = #XCHG(a, b);` to allow swapping the contents of two operands.
  ([PR #678](https://github.com/jasmin-lang/jasmin/pull/678)).

- The Constant-Time security checker is now available as a separate `jazzct`
  tool; the `-checkCT`, `-checkCTon`, and `-infer` command line options are
  deprecated
  ([PR #766](https://github.com/jasmin-lang/jasmin/pull/766)).

- Register allocation can print liveness information (enable with `-pliveness`)
  ([PR #749](https://github.com/jasmin-lang/jasmin/pull/749),
  [PR #776](https://github.com/jasmin-lang/jasmin/pull/776)).

- Relaxed alignment constraints for memory and array accesses
  ([PR #748](https://github.com/jasmin-lang/jasmin/pull/748),
  [PR #772](https://github.com/jasmin-lang/jasmin/pull/772)).

- Namespaces can be used to structure source code and require the same file
  more than once (in different contexts)
  ([PR #734](https://github.com/jasmin-lang/jasmin/pull/734),
  [PR #780](https://github.com/jasmin-lang/jasmin/pull/780)).

- Extraction as EasyCrypt code targets version 2024.01
  ([PR #690](https://github.com/jasmin-lang/jasmin/pull/690)).

## Bug fixes

- The compiler no longer throws an exception when a required file does not exist
  ([PR #733](https://github.com/jasmin-lang/jasmin/pull/733);
  fixes [#383](https://github.com/jasmin-lang/jasmin/issues/383)).

- When slicing, export functions that are called from kept functions are no
  longer spuriously kept
  ([PR #751](https://github.com/jasmin-lang/jasmin/pull/751);
  fixes [#750](https://github.com/jasmin-lang/jasmin/issues/750)).

## Other changes

- Instruction selection for x86-64, when storing a large immediate value in
  memory, introduces a copy through an intermediate register rather that
  emitting invalid code
  ([PR #730](https://github.com/jasmin-lang/jasmin/pull/730)).

- Expansion of `#copy` operators uses an intermediate register when needed
  ([PR #735](https://github.com/jasmin-lang/jasmin/pull/735)).

- Add more warning options:
    - `-wduplicatevar`: warns when two variables share the same name;
    - `-wunusedvar`: warns when a declared variable is not used.

  ([PR #605](https://github.com/jasmin-lang/jasmin/pull/605)).
  Warning this is a **breaking change**.

# Jasmin 2023.06.2 — 2023-12-22

## New features

- Instruction selection for arm-m4 turns `x = (y << n) - z` into
  `x = #RSB(z, y << n)` and `x = n - y` into `x = #RSB(y, n)` where `n` is a constant.
  ([PR #585](https://github.com/jasmin-lang/jasmin/pull/585),
  [PR #589](https://github.com/jasmin-lang/jasmin/pull/589)).

- Add instructions `REV`, `REV16`, and `REVSH` to arm-m4;
  ([PR #620](https://github.com/jasmin-lang/jasmin/pull/620);
  fixes [#618](https://github.com/jasmin-lang/jasmin/issues/618)).

- Add instructions `CLZ`, `CMN`, `BFC`, and `BFI` to arm-m4:
  ([PR #641](https://github.com/jasmin-lang/jasmin/pull/641),
  [PR #642](https://github.com/jasmin-lang/jasmin/pull/642),
  [PR #643](https://github.com/jasmin-lang/jasmin/pull/643)).

- Add signed multiply halfwords instructions `SMULBB`, `SMULBT`, `SMULTB`,
  `SMULTT`, `SMLABB`, `SMLABT`, `SMLATB`, `SMLATT`, `SMULWB`, and `SMULWT`
  ([PR #644](https://github.com/jasmin-lang/jasmin/pull/644)).

- Array indexing expressions are automatically and silently casted from word to
  int during pretyping
  ([PR #673](https://github.com/jasmin-lang/jasmin/pull/673);
  fixes [#672](https://github.com/jasmin-lang/jasmin/issues/672)).

## Bug fixes

- Fix printing to EasyCrypt of ARMv7 instruction `bic`
  ([PR #554](https://github.com/jasmin-lang/jasmin/pull/554)).

- Add alignment during global datas for arm-m4
  ([PR #590](https://github.com/jasmin-lang/jasmin/pull/590);
  fixes [#587](https://github.com/jasmin-lang/jasmin/issues/587)).

- Type-checking rejects wrongly casted primitive operators
  ([PR #489](https://github.com/jasmin-lang/jasmin/pull/488);
  fixes [#69](https://github.com/jasmin-lang/jasmin/issues/69)).

- Fix combine flag notation for arm
  ([PR 594](https://github.com/jasmin-lang/jasmin/pull/594);
  fixes [#593](https://github.com/jasmin-lang/jasmin/issues/593)).

- Flag combination support `"!="` as the negation of `"=="`
  ([PR 600](https://github.com/jasmin-lang/jasmin/pull/600);
  fixes [#599](https://github.com/jasmin-lang/jasmin/issues/599)).

- Fix extraction to easycrypt of for loops that modify the loop counter
  ([PR 616](https://github.com/jasmin-lang/jasmin/pull/616)).

- Fix instruction selection for stack-allocation on ARM
  ([PR 623](https://github.com/jasmin-lang/jasmin/pull/623);
  fixes [#622](https://github.com/jasmin-lang/jasmin/issues/622)).

## Other changes

- Unsigned division on x86 emits a xor instead of “mov 0“
  ([PR #582](https://github.com/jasmin-lang/jasmin/pull/582)).

- The safety checker uses less list concatenations
  ([PR #669](https://github.com/jasmin-lang/jasmin/pull/669)).

# Jasmin 2023.06.1 — 2023-07-31

## New features

- More arm instructions are available:
  `MLA`, `MLS`
  ([PR #480](https://github.com/jasmin-lang/jasmin/pull/480)),
  `UMAAL`
  ([PR #543](https://github.com/jasmin-lang/jasmin/pull/543)),
  `UMLAL`, `SMULL`, `SMLAL`, `SMMUL`, `SMMULR`
  ([PR #481](https://github.com/jasmin-lang/jasmin/pull/481),
   [PR #492](https://github.com/jasmin-lang/jasmin/pull/492),
   [PR #514](https://github.com/jasmin-lang/jasmin/pull/514),
   [PR #545](https://github.com/jasmin-lang/jasmin/pull/545)).

- Notation for string literals; there is no implicit zero terminator;
  escaping follows the lexical conventions of OCaml
  ([PR #517](https://github.com/jasmin-lang/jasmin/pull/517),
   [PR #532](https://github.com/jasmin-lang/jasmin/pull/532)).

## Bug fixes

- Fix semantics of the `IMUL`, `IMULr`, and `IMULri` instructions
  ([PR #528](https://github.com/jasmin-lang/jasmin/pull/528);
  fixes [#524](https://github.com/jasmin-lang/jasmin/issues/524)).

- Fix semantics of the `SHLD_16`, `SHRD_16`, `VPSLLV`, and `VPSRLV` instructions
  ([PR #520](https://github.com/jasmin-lang/jasmin/pull/520)).

- Handle the size parameter in LZCNT semantic
  ([PR #516](https://github.com/jasmin-lang/jasmin/pull/516);
  fixes [#515](https://github.com/jasmin-lang/jasmin/issues/515)).

## Other changes

- Various improvements related to ARMv7
  ([PR #476](https://github.com/jasmin-lang/jasmin/pull/476),
   [PR #477](https://github.com/jasmin-lang/jasmin/pull/477),
   [PR #479](https://github.com/jasmin-lang/jasmin/pull/479)).

# Jasmin 2023.06.0 — Villers-lès-Nancy, 2023-06-09

## New features

- Support ARMv7 (Cortex-M4) as target architecture
  ([PR #242](https://github.com/jasmin-lang/jasmin/pull/242)).

- Compute the maximal call depth for each function; a function annotation
  `#[calldepth=n]` can be used to check that the maximal call depth is exactly
  `n`
  ([PR #282](https://github.com/jasmin-lang/jasmin/pull/282)).

- Add bit rotation operators for expressions: `<<r` and `>>r`
  ([PR #290](https://github.com/jasmin-lang/jasmin/pull/290)).
  These get extracted to `|<<|` and `|>>|` in EasyCrypt.

- Local functions with return address on the stack use usual `CALL`
  and `RET` x86 instructions instead of (direct & computed) `JMP`
  ([PR #194](https://github.com/jasmin-lang/jasmin/pull/194)).

- The pretty-printer of Jasmin programs to LATEX is now available as a separate
  `jazz2tex` tool; the `-latex` command line flag is deprecated
  ([PR #372](https://github.com/jasmin-lang/jasmin/pull/372)).

- The safety checker fully unrolls `while` loops annotated as `#bounded`
  and does not attempt at proving termination of `while` loops annotated
  with `#no_termination_check`
  ([PR #362](https://github.com/jasmin-lang/jasmin/pull/362),
  [PR #384](https://github.com/jasmin-lang/jasmin/pull/384)).

- The safety checker warns about possible alignment issues rather than failing,
  when the `-nocheckalignment` command-line flag is given
  ([PR #401](https://github.com/jasmin-lang/jasmin/pull/401)).

- The `jasminc` tool may process only a slice of the input program, when one or
  more `-slice f` arguments are given on the command line; slicing occurs after
  expansion of parameters and its result can be observed with `-pcstexp`
  ([PR #414](https://github.com/jasmin-lang/jasmin/pull/414)).

## Bug fixes

- Various fixes to the LATEX printer
  ([PR #406](https://github.com/jasmin-lang/jasmin/pull/406)).

- Fix the semantics of shift and rotation operators: the second
  argument (the shift amount) is no longer truncated
  ([PR #413](https://github.com/jasmin-lang/jasmin/pull/413)).

- Improve liveness analysis for register allocation
  ([PR #469](https://github.com/jasmin-lang/jasmin/pull/469);
  fixes [#455](https://github.com/jasmin-lang/jasmin/issues/455)).

## Other changes

- Explicit if-then-else in flag combinations is no longer supported
  in x86 assembly generation; conditions that used to be supported
  can be expressed using equality and disequality tests
  ([PR #270](https://github.com/jasmin-lang/jasmin/pull/270)).

- When the `-timings` command-line flag is given, timestamps are
  written to the standard error after each compilation pass and during
  safety analysis when entering a local function; the elapsed time since
  previous timestamp is also displayed
  ([PR #403](https://github.com/jasmin-lang/jasmin/pull/403)).

- Local functions that are never called are removed from the program during the
  “remove unused function” pass
  ([PR #427](https://github.com/jasmin-lang/jasmin/pull/427)).

# Jasmin 2022.09.3 — Villers-lès-Nancy, 2023-05-31

## New features

- x86 instructions `PCLMULQDQ`, `VPCLMULQDQ` are available
  ([PR #396](https://github.com/jasmin-lang/jasmin/pull/396)).

- x86 intrinsics that accept a size suffix (e.g., `_128`) also accept, with a
  warning, a vector suffix (e.g., `_4u32`)
  ([PR #303](https://github.com/jasmin-lang/jasmin/pull/303)).

## Bug fixes

- The x86 instructions `VMOVSHDUP` and `VMOVSLDUP` accept a size suffix (`_128`
  or `_256`) instead of a vector description suffix (`4u32` or `8u32`)
  ([PR #303](https://github.com/jasmin-lang/jasmin/pull/303);
  fixes [#301](https://github.com/jasmin-lang/jasmin/issues/301)).

- Fixes for x86 instruction `BT`
  ([PR #420](https://github.com/jasmin-lang/jasmin/pull/420)).

- Register allocation checks that forced register are from the expected bank
  ([PR #422](https://github.com/jasmin-lang/jasmin/pull/422);
  fixes [#421](https://github.com/jasmin-lang/jasmin/issues/421)).

- Fix semantics of the `VPERMD`, `VPMADDWD`, and `VPMADDUBSW` instructions
  ([PR #442](https://github.com/jasmin-lang/jasmin/pull/442)).

- Fix semantics of the `VPMOVSX` and `VPMOVZX` instructions
  ([PR #446](https://github.com/jasmin-lang/jasmin/pull/446)).

- Fix semantics of the `VPSHUFB` and `VPCMPGT` instructions
  ([PR #449](https://github.com/jasmin-lang/jasmin/pull/449)).

- Fix semantics of the `SHR`, `RCL`, and `RCR` instructions
  ([PR #451](https://github.com/jasmin-lang/jasmin/pull/451)).

## Other changes

- Instruction selection for `x86_64` recognizes shifts (rotations, etc.) by
  an amount that is explicitly truncated (e.g., `x >>= y & 63`)
  ([PR #412](https://github.com/jasmin-lang/jasmin/pull/412)).

# Jasmin 2022.09.2

This release fixes the AUTHORS file which was not up-to-date.

# Jasmin 2022.09.1

## New features

- More x86 instructions are available:
  `VPMUL`
  ([PR #276](https://github.com/jasmin-lang/jasmin/pull/276)),
  `VPAVG`
  ([PR #285](https://github.com/jasmin-lang/jasmin/pull/285)),
  `CLFLUSH`, `LFENCE`, `MFENCE`, `SFENCE`
  ([PR #334](https://github.com/jasmin-lang/jasmin/pull/334)),
  `PDEP`
  ([PR #328](https://github.com/jasmin-lang/jasmin/pull/328)),
  `VMOVDQA`
  ([PR #279](https://github.com/jasmin-lang/jasmin/pull/279)).

- Division and modulo operators can be used in compound assignments
  (e.g., `x /= y`)
  ([PR #324](https://github.com/jasmin-lang/jasmin/pull/324)).

## Bug fixes

- Safety checker handles the `#copy` and `#randombytes` operators
  ([PR #312](https://github.com/jasmin-lang/jasmin/pull/312),
  [PR #317](https://github.com/jasmin-lang/jasmin/pull/317);
  fixes [#308](https://github.com/jasmin-lang/jasmin/issues/308)).

- Register allocation takes into account conflicts between flag registers
  ([PR #311](https://github.com/jasmin-lang/jasmin/pull/311);
  fixes [#309](https://github.com/jasmin-lang/jasmin/issues/309)).

- Register allocation fails when some `reg bool` variables remain unallocated
  ([PR #313](https://github.com/jasmin-lang/jasmin/pull/313);
  fixes [#310](https://github.com/jasmin-lang/jasmin/issues/310)).

- Fixes to the safety checker
  ([PR #315](https://github.com/jasmin-lang/jasmin/pull/315),
  [PR #343](https://github.com/jasmin-lang/jasmin/pull/343),
  [PR #365](https://github.com/jasmin-lang/jasmin/pull/365);
  fixes [#314](https://github.com/jasmin-lang/jasmin/issues/314)).

- Safety checker better handles integer shift operators
  ([PR #322](https://github.com/jasmin-lang/jasmin/pull/322);
  fixes [#319](https://github.com/jasmin-lang/jasmin/issues/319)).

- Improved error message in array expansion
  ([PR #331](https://github.com/jasmin-lang/jasmin/pull/331);
  fixes [#333](https://github.com/jasmin-lang/jasmin/issues/333)).

- The `randombytes` system-call is better handled by the constant-time checker
  ([PR #326](https://github.com/jasmin-lang/jasmin/pull/326);
  fixes [#325](https://github.com/jasmin-lang/jasmin/issues/325)).

- Stack-allocation ensures that array slices are in bounds
  ([PR #363](https://github.com/jasmin-lang/jasmin/pull/363);
  fixes [#54](https://github.com/jasmin-lang/jasmin/issues/54)).

- Safety checker folds constant expressions during linearization
  ([PR #387](https://github.com/jasmin-lang/jasmin/pull/387);
  fixes [#385](https://github.com/jasmin-lang/jasmin/issues/385),
  [#386](https://github.com/jasmin-lang/jasmin/issues/386)).

- Fix compilation and semantics of the `VPEXTR` and `VPINSR` instructions
  ([PR #394](https://github.com/jasmin-lang/jasmin/pull/394);
  fixes [#395](https://github.com/jasmin-lang/jasmin/issues/395)).

## Other changes

- The live-range-splitting transformation is run a second time after
  expansion of register arrays
  ([PR #341](https://github.com/jasmin-lang/jasmin/pull/341)).

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
