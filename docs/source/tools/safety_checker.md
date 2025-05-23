# Safety checker

The Jasmin compiler comes with a static analyser that attempts to automatically prove the safety of the program to be compiled.

To use it, just call the compiler with the `-checksafety` flag on the command line:
it will check the safety of the *export* functions rather than compiling them.

Safety is formally defined as “to have a well defined semantics”, according to the Coq specification that is given in the `proofs/lang/psem.v` file:
a function is safe to call from an initial memory with some arguments whenever there exist a final memory and result values such that running this function from that initial state terminates in that final state.

Broadly speaking, safety entails:

  - termination;
  - array accesses are in bounds;
  - memory accesses are valid, i.e., are properly aligned and target allocated memory;
  - arithmetic operations are applied to valid arguments.

Jasmin functions are usually not *absolutely* safe: it may be possible to find initial states from which the execution is not properly defined. For instance, if a function accesses memory by dereferencing a pointer given as argument, said pointer must target allocated memory.

Therefore, the safety checker outputs a *safety precondition*: a property of the initial state
(initial memory and arguments) that, when satisfied, ensures that the execution is safe.

As an example, we give below the final results we obtained when
analysing `compiler/examples/loop_add.jazz` and `compiler/examples/memcmp.jazz`, and explain how to interpret them.


## Example: `loop_add.jazz`
Assuming we are in the `compiler/` directory, running `./jasminc -checksafety examples/loop_add.jazz` should yield:

```
Default checker parameters.

Analysing function add16

*** No Safety Violation

Memory ranges:
  mem_in: [0; 128]
  
* Rel:
{mem_in ≥ 0, inv_in ≥ 0, mem_in ≤ 128, inv_in ≤ 18446744073709551615}
mem_in ∊ [0; 128]

* Alignment: in 64;
```
This states that the function is memory safe, assuming that:
- the input `in` points to an allocated memory region of at least 128 bytes;
- the `Rel` part can be ignored here (we detail it in the next example);
- the input `in` must be aligned to 64 bits. 


## Example: `memcmp.jazz`
The `memcmp` export function has the signature:
```
export fn memcmp(reg u64 p, reg u64 q, reg u64 n) -> reg u64
```
Essentially, it takes two pointers `p` and `q` of length `n`, and compare them.  To help the analyser, we can declare which inputs are pointers and which inputs are lengths, which is done through the `safetyparam` option as follows:
```
./jasminc -checksafety examples/memcmp.jazz -safetyparam "memcmp>p,q;n"
```
(pointers and lengths are comma `,` separated lists of input variables).

Running the checker should yield:
```
Default checker parameters.

Analyzing function memcmp

*** No Safety Violation

Memory ranges:
  mem_n: [0; 0]
  
* Rel:
{inv_n ≤ 18446744073709551615, 8·inv_n ≥ mem_q, 8·inv_n ≥ mem_p, mem_q ≥ 0, mem_p ≥ 0}
mem_p ∊ [0; 147573952589676412920]
mem_q ∊ [0; 147573952589676412920]

* Alignment: p 64; q 64; 
```
Here, because the allocated memory regions pointed by `p` and `q` are of size depending on the initial value of `n`, we must check the `Rel` entry. This entry gives the allocated memory region safety pre-condition through a conjunctions of linear inequalities. 

For example, we see that `mem_q` (the memory region corresponding to input pointer `q`) is such that:
```
0 ≤ mem_q ≤ 8·inv_n
```
Where `inv_n` is the initial value of input `n`. That is, `q` must point to an allocated memory region of length `8·n`.
