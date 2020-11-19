- To use the cost analyser, simply run:

     - `$ ./jasminc -pipeline -branchpredictor FILE.jazz`

- To use the naive cost analyser mentioned in the paper, simply run:

     - `$ ./jasminc -pipeline -branchpredictor -naivepipeline FILE.jazz`
  Note that for the naive cost analysis, only the maximal cost is
  meaningful (the minimal cost inferred is to be ignored).

- For programs with input-dependent cost, the name of the register
  holding the input (of which the cost depends) must be provided as an
  additional information to the analyser using the

     - `-safetyparam`

  option. We describe how to use this option in more details at the end
  of this README.

- There are additional information on how to use and interpret the
  cost analysis results at the end of this file.

Jasmin Examples Files
--------------------------------------------------------------------
- The simple (non-crypto) Jasmin examples can be found in the
      - `simple-examples/`
  sub-folder.
  These were mostly taken from the Jasmin examples, except for the
  opti.jazz and nonopti.jazz files, which we wrote (these correspond
  to the optimized and non-optimized scalar_product program of the
  paper).

- The implementations of poly1305 and chacha20 are in the
      - `ref/`
  sub-folder for the scalar versions, and
      - `avx2/`
  sub-folders for the vectorized versions.
  These are Jasmin implementations obtained starting from the (now
  old version of) the libjc library at:
  https://github.com/tfaoliveira/libjc

- The AES implementation was written by us, and is in the
       - `aes/`
  sub-folder.

- The expected results for the simple and crypto examples can be found
  in the following files:
     - `expected_results.txt`
     - `expected_results_crypto.txt`


Running the Experiments
--------------------------------------------------------------------
- To compute the cost of the simple (non-crypto) Jasmin examples, run:
     - `$ ./run-analysis`
  The results for the file 'FILE.jazz' are stored in 'FILE.jazz.cost',
  and the results for the naive cost analysis in
  'FILE.jazz.cost_naive'.


- To compute the cost of the crypto Jasmin examples, run:
     - `$ ./run-analysis-crypto`
  Again, the results are stored alongside the Jasmin source code, with
  '.cost' or a '.cost_naive' extension.
  Note that the analysis of some implementations can take a very long
  time (from a few minutes for the Poly1305 and Chacha/ref
  implementations, almost and hour for the Chacha20/avx2
  implementations, to a few hours for the AES implementations).

- By default, 3 analyses are run in parallel (if you have more cores,
  simply set the `MAXJOBS` variable at the beginning of either the
  script to a higher value).

- The final results of an analysis comprises the maximal and minimal
  cost bounds obtained, as well as projection of these bounds on a
  fixed value of the input to help quickly assessing the cost (by
  default, the value 10 is used).
  As an example, we give below the (end of) the results we obtained
	when analyzing poly1305/ref. We explain how to interpret them below
	(jump to Explanation)
  We also make a few important remarks at the end of the README.



Example of cost analysis results on poly1305/ref
--------------------------------------------------------------------

*** No Safety Violation

Memory and cost ranges:
  mem_RDX: [0; 0]
  mem_RCX: [0; 32]
  
Cost Max:
* Rel:
{16·v_costMax ≥ 113·inv_RDX + 592, 7232·inv_RDX ≤ 127·v_costMax +
116861276628454616316182, inv_RDX ≤ 18446744073709551615, v_costMax ≤
120·inv_RDX + 37, 16·v_costMax ≤ 113·inv_RDX + 2399, v_costMax ≤
130280130020573708430}
v_costMax ∊ [37; 130280130020573708430]

Cost Min:
* Rel:
{16·v_costMin ≥ 113·inv_RDX + 400, 6328·inv_RDX ≤ 127·v_costMin +
100185419985821181658762, inv_RDX ≤ 18446744073709551615, v_costMin ≤
112·inv_RDX + 25, 16·v_costMin ≤ 113·inv_RDX + 2079, v_costMin ≤
130280130020573708410}
v_costMin ∊ [25; 130280130020573708410]


Cost Min projected:
* Rel:
{16·v_costMin ≤ 3209, 8·v_costMin ≥ 765, inv_RDX = 10}
v_costMin ∊ [765/8; 3209/16]


Cost Max projected:
* Rel:
{16·v_costMax ≤ 3529, 8·v_costMax ≥ 861, inv_RDX = 10}
v_costMax ∊ [861/8; 3529/16]



Explanation
--------------------------------------------------------------------
- The "Cost Min projected" and "Cost Max projected" entries gives
  projection of the minimal and maximal cost on an input of 10 for
  inlen (which is stored in RDX).

- The important results are the "Cost Max" and "Cost Min" entries.
  Note that the ranges for costMax (resp. costMin) are given using a
  conjunction of linear equalities and inequalities, and are also
  projected on an interval below.
  For programs whose cost depends on the program input, the projected
  value is of no use, e.g.:
  
     v_costMax ∊ [37; 130280130020573708430]

  is too imprecise. Only the relational (i.e. inequalities)
  information are useful:

    {16·v_costMax ≥ 113·inv_RDX + 592, 7232·inv_RDX ≤ 127·v_costMax +
     116861276628454616316182, inv_RDX ≤ 18446744073709551615,
     v_costMax ≤ 120·inv_RDX + 37, 16·v_costMax ≤ 113·inv_RDX + 2399,
     v_costMax ≤ 130280130020573708430}

  This entry states that the costMax value must satisfy the invariant
  above, where inv_RDX is the initial value of the inlen variable.
  Here, we have to manually select the best bounds among the relations
  obtained. In the paper, when we add several incomparable bounds, we
  selected the best asymptotic bound. Here, for example, the best
  bound is:

     16·v_costMax ≤ 113·inv_RDX + 2399

  which, by dividing by 16 and rounding (upward since this is the
  maximal cost), gives us:

     costMax ≤ 7.1·inv_RDX + 150

- Note that, since input values are always upper-bound by (2^ws - 1)
  (where ws is the number of bits used to represent the input), our
  relational results always contain an upper-bound of the form.

     costMax <= SomeLargeInteger

  We ignore this upper-bound, which is of little value.


		
A few remarks
--------------------------------------------------------------------
- The branch predictor option approximates a processor branch predictor

- You can see what the analyser is doing using the '-debug'
  option. Note there can be hundred of thousands of line of
  logs. Simply jump to the end of the file for the final results.

- Each implementation is analysed twice, once to get overlaps
  information using an aliasing analysis, and once to compute the
  bounds on the execution cost (using the aliasing analysis results).

- For programs with input-dependent cost, or with input pointers
  pointing to arbitrarily large memory regions (e.g. a message of
  arbitrary length to be encrypted), it is necessary to provide
  additional information to the analyser using the

     - `-safetyparam "pointerList;inputDependentList"`

  option. Here, 'pointerList' and 'inputDependentList' are the comma
  separated list or registers holding the, respectively, pointers to
  arbitrarily large memory region and inputs of which the cost
  depends.  We explain how to obtain these on an example
  (poly1305/ref).  Consider the exported (i.e. main) function
  signature:

    `export fn
     poly1305_ref3(reg u64 out, reg u64 in, reg u64 inlen, reg u64 k)`

  Here, 'out' and 'in' are pointers, and 'inlen' an input dependency for
  the cost.
  When running the analyser first without parameters, it will print
  (at the beginning of the analyses) the function signature after most
  compilation pass, where input variables have been replaced by
  registers. Here, we get:
     `fn
      poly1305_ref3(Reg U64 RDI, Reg U64 RSI, Reg U64 RDX, Reg U64 RCX)`

  Hence we use the parameters:
  
      - `-safetyparam  "RSI,RDI;RDX"`

  for "in,out;inlen".
  
