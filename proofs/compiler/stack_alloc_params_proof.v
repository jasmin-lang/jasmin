From mathcomp Require Import ssreflect ssrbool seq ssralg.
From Coq Require Import Utf8.
Require Import psem.
Require Export stack_alloc_params.

(* TODO : move elsewhere *)
(* but not clear where
   Uptr is defined in memory_model, no atype there
   atype is defined in type, no Uptr there
*)
Notation spointer := (aword Uptr) (only parsing).

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Definition mov_ofs_correct (mov_ofs : lval → assgn_tag → mov_kind → pexpr → pexpr → option instr_r) :=
  forall (P' : sprog) ev s1 e w ofs pofs x tag mk ii ins s2,
    p_globs P' = [::]
    -> sem_pexpr true [::] s1 e >>= to_pointer = ok w
    -> sem_pexpr true [::] s1 ofs >>= to_pointer = ok pofs
    -> mov_ofs x tag mk e ofs = Some ins
    -> write_lval true [::] x (Vword (w + pofs)) s1 = ok s2
    -> exists2 vm2, esem_i P' ev (MkI ii ins) s1 = ok (with_vm s2 vm2) & evm s2 =1 vm2.

Definition immediate_correct (immediate : var_i → Z → instr_r) :=
  forall (P' : sprog) w s ii (x: var_i) z,
    vtype x = aword Uptr ->
    esem_i P' w (MkI ii (immediate x z)) s = ok
      (with_vm s (evm s).[x <- Vword (wrepr Uptr z)]).

Definition swap_correct (swap : assgn_tag → var_i → var_i → var_i → var_i → instr_r) :=
  forall (P' : sprog) rip s ii tag (x y z w : var_i) (pz pw: pointer),
    convertible (vtype x) spointer -> convertible (vtype y) spointer -> 
    convertible (vtype z) spointer -> convertible (vtype w) spointer -> 
    (evm s).[z] = Vword pz ->
    (evm s).[w] = Vword pw -> 
    esem_i P' rip (MkI ii (swap tag x y z w)) s = ok
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
