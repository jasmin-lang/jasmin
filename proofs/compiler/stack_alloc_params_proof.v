From mathcomp Require Import ssreflect seq ssralg.
From Coq Require Import Utf8.
Require Import psem.
Require Export stack_alloc_params.

(* TODO : move elsewhere *)
(* but not clear where
   Uptr is defined in memory_model, no stype there
   stype is defined in type, no Uptr there
*)
Notation spointer := (sword Uptr) (only parsing).

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Definition mov_ofs_correct (mov_ofs : lval → assgn_tag → mov_kind → pexpr → pexpr → option instr_r) :=
  forall (P' : sprog) ev s1 e w ofs pofs x tag mk ins s2,
    p_globs P' = [::]
    -> sem_pexpr true [::] s1 e >>= to_pointer = ok w
    -> sem_pexpr true [::] s1 ofs >>= to_pointer = ok pofs
    -> mov_ofs x tag mk e ofs = Some ins
    -> write_lval true [::] x (Vword (w + pofs)) s1 = ok s2
    -> exists2 vm2, sem_i P' ev s1 ins (with_vm s2 vm2) & evm s2 =1 vm2.

Definition immediate_correct (immediate : var_i → Z → instr_r) :=
  forall (P' : sprog) w s (x: var_i) z,
    vtype x = sword Uptr ->
    sem_i P' w s (immediate x z)
      (with_vm s (evm s).[x <- Vword (wrepr Uptr z)]).

Definition swap_correct (swap : assgn_tag → var_i → var_i → var_i → var_i → instr_r) :=
  forall (P' : sprog) rip s tag (x y z w : var_i) (pz pw: pointer),
    vtype x = spointer -> vtype y = spointer -> 
    vtype z = spointer -> vtype w = spointer -> 
    (evm s).[z] = Vword pz ->
    (evm s).[w] = Vword pw -> 
    sem_i P' rip s (swap tag x y z w)
      (with_vm s ((evm s).[x <- Vword pw]).[y <- Vword pz]).

Record h_stack_alloc_params (saparams : stack_alloc_params) :=
  {
    (* [mov_ofs] must behave as described in stack_alloc_params.v. *)
    mov_ofsP : mov_ofs_correct saparams.(sap_mov_ofs);
    (* specification of sap_immediate *)
    sap_immediateP : immediate_correct saparams.(sap_immediate);
    sap_swapP : swap_correct saparams.(sap_swap)
  }.

End WITH_PARAMS.
