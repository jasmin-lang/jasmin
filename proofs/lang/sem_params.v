(* Parameters of the semantics of Jasmin.

We need to balance granularity not to introduce unnecessary dependencies while
packing parameters that always go together.

Another concern is that some of these definitions are extracted and used in
OCaml.
Having record fields of type [Type] is inconvenient in OCaml, so we have them
as parameters.
*)

Require Import
  flag_combination
  sopn
  syscall
  wsize.


(* Parameters needed to build states.
   This gets extracted and used in OCaml (in the evaluator), so we have
   [syscall_state] as a parameter instead of a record field. *)
Class EstateParams (syscall_state : Type) := mk_ep
  {
    _pd :> PointerData | 1000;
  }.

Arguments mk_ep {_ _}.

(* Parameters needed to evaluate expressions. *)
Class SemPexprParams := mk_spp
  {
    _fcp :> FlagCombinationParams | 1000;
  }.

Arguments mk_spp {_}.


(* Parameters needed to execute programs.
   This gets extracted and used in OCaml (in the evaluator), so [asm_op] and
   [syscall_state] are parameters instead of record fields. *)
Class SemInstrParams (asm_op syscall_state : Type) := mk_sip
  {
    _asmop :> asmOp asm_op | 1000;
    _sc_sem :> syscall_sem syscall_state | 1000;
  }.

Arguments mk_sip {_ _ _ _}.
