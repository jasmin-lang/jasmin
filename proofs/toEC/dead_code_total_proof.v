(* * The pass dead_code in the modes of the extraction to EasyCrypt.

   The extraction for safety runs [dead_code] on programs whose assertions
   are evaluated, in the total mode. Its correctness there is needed in both
   directions; [dead_code_proof] proves the direction from the source to the
   transformed program, with [values_uincl] on the results, for the
   semantics of the compiler.

   [dead_code] keeps the assertions, the system calls and the calls, and
   removes assignments and operators whose results are dead. The direction
   from the transformed program to the source therefore needs these removed
   instructions not to fail. In the total mode an instruction whose
   expressions are well typed does not fail: the memory accesses, the array
   accesses and the operators are total, a variable never written reads a
   default value. [total_ok] states it for every assignment and operator of
   the program. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import dead_code.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Section DEFS.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}.

(* In the total mode, on every state, the assignments and the operators of [p]
   run. *)
Fixpoint total_ok_i (p : uprog) (i : instr) : Prop :=
  let total_ok_c :=
    fix total_ok_c (c : cmd) : Prop :=
      if c is i :: c then total_ok_i p i /\ total_ok_c c else True in
  let 'MkI _ ir := i in
  match ir with
  | Cassgn x tg ty e => forall s, is_ok (sem_assgn (sm := total) p x tg ty e s)
  | Copn xs tg o es => forall s, is_ok (sem_sopn (sm := total) (p_globs p) o s xs es)
  | Ccall _ _ _ | Csyscall _ _ _ | Cassert _ => True
  | Cif _ c1 c2 | Cwhile _ c1 _ _ c2 => total_ok_c c1 /\ total_ok_c c2
  | Cfor _ _ c => total_ok_c c
  end.

Definition total_ok (p : uprog) : Prop :=
  forall fn fd i, get_fundef (p_funcs p) fn = Some fd -> List.In i fd.(f_body) -> total_ok_i p i.

(* The results of [fn] that [onfun] keeps. *)
Definition dc_keep_res (onfun : funname -> option (seq bool)) (fn : funname) (fr : fstate) :=
  {| fscs := fscs fr; fmem := fmem fr; fvals := fn_keep_only onfun fn (fvals fr) |}.

(* Same arguments; the results of the transformed program are those of the
   source that [onfun] keeps. *)
Definition dc_src_tgt_spec onfun : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 => fn1 = fn2 /\ fs1 = fs2;
     rpostF_ := fun fn1 _ _ _ fr1 fr2 => fr2 = dc_keep_res onfun fn1 fr1 |}.

Definition dc_tgt_src_spec onfun : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 => fn1 = fn2 /\ fs1 = fs2;
     rpostF_ := fun fn1 _ _ _ fr1 fr2 => fr1 = dc_keep_res onfun fn1 fr2 |}.

End DEFS.

(* When the source runs without failure, its assertions evaluated, the
   transformed program runs with the same results, but those removed. The
   contracts are not evaluated: they read the results that are removed. *)
Axiom dead_code_src_tgt :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {sm : SemMode} {LC : LoopCounter}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (onfun : funname -> option (seq bool)) (p p' : uprog) (ev : extra_val_t),
  dead_code_prog_tokeep (fun _ => false) (fun _ fi => fi) false onfun p = ok p' ->
  forall fn,
  wiequiv_f (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    p p' ev ev (rpreF (eS := dc_src_tgt_spec onfun)) fn fn
    (rpostF (eS := dc_src_tgt_spec onfun)).

(* When the transformed program runs without failure, in the total mode with
   its assertions evaluated, the source runs with the same results, but those
   removed. *)
Axiom dead_code_tgt_src :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {LC : LoopCounter}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (onfun : funname -> option (seq bool)) (p p' : uprog) (ev : extra_val_t),
  total_ok p ->
  dead_code_prog_tokeep (fun _ => false) (fun _ fi => fi) false onfun p = ok p' ->
  forall fn,
  wiequiv_f (sm1 := total) (sm2 := total)
    (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    p' p ev ev (rpreF (eS := dc_tgt_src_spec onfun)) fn fn
    (rpostF (eS := dc_tgt_src_spec onfun)).
