open Prog

type ty_fun

val pp_funty : Format.formatter -> Name.t * ty_fun -> unit

val ty_prog :
  ('asm -> bool) -> ('info, 'asm) prog -> Name.t list -> (Name.t * ty_fun) list
(** Type-check a program.

    A call [ty_prog is_ct_asm p f] type-checks (for Speculative Constant-Time)
    the functions of the program [p] whose names are given in the list [f]
    (defaults to all functions if [f] is the empty list).

    Argument [is_ct_asm] classifies which assembly operators are assumed to be
    constant time (i.e., assumed to be safe to apply to sensitive data).

    The program must not contain any #spill or #unspill pseudo-operation. *)

val compile_infer_msf :
  ('info, 'asm) prog -> (Slh_lowering.slh_t list * Slh_lowering.slh_t list) Hf.t
