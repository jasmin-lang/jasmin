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
  type
  syscall
  wsize.


(* Parameters needed to build states. *)
Class EstateParams := mk_ep
  {
    _pd : PointerData;
    _msf_size : MSFsize;
  }.

#[global]
Existing Instances _pd _msf_size | 1000.

Arguments mk_ep {_}.

(* Parameters needed to evaluate expressions. *)
Class SemPexprParams := mk_spp
  {
    _fcp : FlagCombinationParams;
  }.

#[global]
Existing Instance _fcp | 1000.

Arguments mk_spp {_}.


(* Parameters needed to execute programs.
   This gets extracted and used in OCaml (in the evaluator), so [asm_op] is a
   parameter instead of a record field. *)
Class SemInstrParams (asm_op : Type) := mk_sip
  {
    _asmop : asmOp asm_op;
  }.

#[global]
Existing Instances _asmop | 1000.

Arguments mk_sip {_ _}.

Class WithAssert := { assert_allowed : bool }.
Definition noassert : WithAssert := {| assert_allowed := false |}.
Definition withassert : WithAssert := {| assert_allowed := true |}.

#[global] Existing Instances noassert | 1000.
