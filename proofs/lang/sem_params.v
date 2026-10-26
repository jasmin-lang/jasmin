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
  utils
  wsize.


(* Parameters needed to build states.
   This gets extracted and used in OCaml (in the evaluator), so we have
   [syscall_state] as a parameter instead of a record field. *)
Class EstateParams (syscall_state : Type) := mk_ep
  {
    _pd : PointerData;
    _msf_size : MSFsize;
  }.

#[global]
Existing Instances _pd _msf_size | 1000.

Arguments mk_ep {_ _}.

(* Parameters needed to evaluate expressions. *)
Class SemPexprParams := mk_spp
  {
    _fcp : FlagCombinationParams;
  }.

#[global]
Existing Instance _fcp | 1000.

Arguments mk_spp {_}.


(* Parameters needed to execute programs.
   This gets extracted and used in OCaml (in the evaluator), so [asm_op] and
   [syscall_state] are parameters instead of record fields. *)
Class SemInstrParams (asm_op syscall_state : Type) := mk_sip
  {
    _asmop : asmOp asm_op;
    _sc_sem : syscall_sem syscall_state;
  }.

#[global]
Existing Instances _asmop _sc_sem | 1000.

Arguments mk_sip {_ _ _ _}.

(* How the semantics treats specifications:
   - [NoAssert]: an assertion is an error, contracts are ignored;
   - [AssertOnly]: assertions are evaluated, contracts are ignored (this is
     the semantics of the extraction to EasyCrypt, where contracts become
     specifications, not checks);
   - [AssertContracts]: assertions are evaluated, and so are the pre- and
     postconditions of a function at each call. *)
Variant assert_mode := NoAssert | AssertOnly | AssertContracts.

Class WithAssert := { wa_mode : assert_mode }.

Definition assert_allowed {wa : WithAssert} : bool :=
  match wa_mode with NoAssert => false | _ => true end.

Definition contracts_checked {wa : WithAssert} : bool :=
  match wa_mode with AssertContracts => true | _ => false end.

Definition noassert : WithAssert := {| wa_mode := NoAssert |}.
Definition withassert : WithAssert := {| wa_mode := AssertContracts |}.
Definition withassert_nocontract : WithAssert := {| wa_mode := AssertOnly |}.

#[global] Existing Instances noassert | 1000.

(* The relational rules whose two sides must run the *same* semantic function,
   typically those about [exec_sopn], only hold when the two modes agree: in the
   total mode a failing operation returns the result of its total version, which
   is unrelated to what the other mode computes.  Stating the agreement as a
   class keeps it inferable in silence in the mono-mode case, which is every
   compiler pass. *)
Class SameMode (sm1 sm2 : SemMode) := { same_mode : sm1 = sm2 }.
#[global] Instance same_mode_refl (sm : SemMode) : SameMode sm sm :=
  {| same_mode := eq_refl |}.

(* Stronger still: the monotonicity theory ([value_uincl]) is false in the total
   mode, where an operation that fails in the partial mode returns a value
   unrelated to the one the more defined side computes.  The rules that rely on
   it are therefore available in the partial mode only. *)
Class IsPartial (sm : SemMode) := { is_partial : sm = partial }.
#[global] Instance is_partial_partial : IsPartial partial :=
  {| is_partial := eq_refl |}.
