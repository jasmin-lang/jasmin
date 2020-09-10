Safety analysis
--------------------------------------------------------------------

- The implementations of poly1305 and chacha20 are in the ref/ sub-folder for
  the scalar versions, and avx2/ sub-folders
  for the vectorized versions.

- To check the safety of the implementations, simply run:
     - `$ ./std-check`
  Note that the analysis of some implementations can take a very long time
  (from a few minutes for the ref/Poly1305 implementations to several hours
  for the avx2/Chacha20 implementations).

- By default, 3 analyses are run in parallel (if you have more cores,
  simply set the `MAXJOBS` variable at the beginning of the script to
  a higher value).

- The intermediate state of the analysis and the final results of the
  analysis of implem.jazz are written into implem.jazz.res in the same
  directory.

  The final results of an analysis comprise a summary of all safety
	violations encountered during the analysis (if any), plus an
	over-approximation of all memory ranges where stores and writes
  took place. The user must then check that the inferred memory
	ranges are indeed the intended one. These inferred memory
	ranges can serve as a memory calling contract for the function.

  As an example, we give below the final results we obtained when
	analyzing ref/Poly1305_movcc. We explain how to interpret them below.
	(We also make a few important remarks at the end of the README).


Example of analysis results
--------------------------------------------------------------------

*** No Safety Violation

Memory ranges:
  mem_out: [0; 16]
  mem_inlen: [0; 0]
  mem_k: [0; 32]
    
* Rel:
{inv_in ≥ 0, mem_in ≥ 0, inv_inlen ≥ mem_in,
 inv_inlen ≤ 18446744073709551615, inv_in ≤ 18446744073709551615}
mem_in ∊ [0; 18446744073709551615]


Explanation
--------------------------------------------------------------------

- the ranges below [* Standard semantics *] are an over-approximation of
 the memory accesses done at the end of the program execution.

- Note that some ranges are given using intervals:
    - e.g. `mem_k: [0; 32]` states that the pointer `k` (which points to the key)
		is 32 bytes long (the interval is misprinted, it inclusive on the left and
		exclusive on the right).

- Other ranges are given through conjunctions of linear inequalities.
    - e.g. the entry:
		* Rel:
    {inv_in ≥ 0,
		 mem_in ≥ 0,
		 inv_inlen ≥ mem_in,
		 inv_inlen ≤ 18446744073709551615,
		 inv_in ≤ 18446744073709551615}
    mem_in ∊ [0; 18446744073709551615]

    states that the memory accesses to the input pointer are done anywhere
		between 0 and `inv_inlen` (which is the initial value of the inlen variable).
		This can be rewritten as `0 ≤ mem_in ≤ inv_inlen`, which is exactly what we
		wanted.
		
A few remarks
--------------------------------------------------------------------

- There can be hundred of thousands of line of logs. Simply jump to
  the end of the `.res` file for the final results.

- The Chacha20 implementations are analysed twice, once to get bounds
  on memory access for the plaintext pointer `plain`, and once for the
	cipher-text pointer `output`.


