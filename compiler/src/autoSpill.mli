(** Naive automatic spilling. The transformation implemented in this module
    automatically inserts spill and unspill operators in a systematic way:
    “spillable” variables are spilled after every definition (including
    arguments on function entry) and unspilled before every use (including
    returning results at the end of functions).

    Which program variables are considered “spillable” (and therefore subject to
    this transformation) depend on the “strategy”. There are two possible
    strategies:
    - either all reg variables are considered spillable, unless their
      declaration are annotated with [#[nospill]];
    - or only reg variables that are explicitly annotated with [#[spill]] are
      considered spillable.

    When a function is annotated [nospill], then it is preserved: no spill or
    unspill operator are introduced in its body.

    Note that an [msf] annotation implies [nospill].

    This transformation is experimental (i.e., subject to change) and trusted
    (i.e., not proved). *)

(** The [strategy] controls which variables are subject to the spill/unspill
    operators introduced by this transformation. *)
type strategy =
  | OptIn  (** reg variables explicitly annotated with [spill] *)
  | OptOut  (** all reg variables, except the ones annotated with [nospill] *)

val doit : strategy -> ('info, 'asm) Prog.prog -> ('info, 'asm) Prog.prog
(** Insert spill and unspill operators in a program, according to the chosen
    strategy. *)
