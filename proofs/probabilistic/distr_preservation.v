From Coq Require Import Lia JMeq.
From HB Require Import structures.

From mathcomp Require Import
  ssreflect
  ssralg
  ssrfun
  ssrbool
  ssrnum
  ssrnat
  choice
  distr
  eqtype
  fintype
  matrix
  order
  reals
  seq
  word
  word_ssrZ
.
From mathcomp Require boolp.

From ITree Require Import
  Basics
  ITree
  ITreeDefinition
  ITreeFacts
  Rutt
  RuttFacts
  Exception
.
Import ITree.

Require Import
  equiv_extras
  rutt_extras
  xrutt
  xrutt_facts
  it_exec
.
Require Import
  it_sems_core
  psem
  psem_facts
  relational_logic
  hoare_logic
.
Require Import
  compiler
  core_logics
  distr_extra
  utils
  values
  word
  syscall
.
Require Import
  arch_decl
  arch_extra
  arch_sem
  arch_params
  sem_params_of_arch_extra
.
Require Import
  arch_params_proof
  stack_alloc_proof_1
  stack_alloc_proof_2
  it_compiler_proof
  asm_gen_proof
.
Require Import
  dinterp lutt_extras
.
From Stdlib Require Import Program.Equality.

Require allocation.

Import Order.TTheory.

#[local] Open Scope ring_scope.
#[local] Open Scope Z.
#[local] Open Scope order_scope.

#[local] Coercion Pos.to_nat : positive >-> nat.

#[local] Notation "'let*' p ':=' c1 'in' c2" :=
  (@ITree.bind _ _ _ c1 (fun p => c2))
    (at level 61, p as pattern, c1 at next level, right associativity).

Section MOVE.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}
  {vregs : veneer_regs_info} {avs : asm_veneer_sem}
  {lowering_options : Type}
  (aparams : architecture_params)
  (haparams : h_architecture_params aparams)
  (cparams : compiler_params) 
  (print_uprogP : forall s p, cparams.(print_uprog) s p = p)
  (print_sprogP : forall s p, cparams.(print_sprog) s p = p)
  (print_linearP : forall s p, cparams.(print_linear) s p = p)
.

Definition safe_uprog (p : uprog) (fn : funname) (fs : fstate) : Prop :=
  safe (is_error wE) (isem_unit p fn fs).

Let REeq {E : Type -> Type} A1 A2 (e1: E A1) (e2: E A2) :=
  exists h : A2 = A1, e1 = eq_rect A2 E e2 A1 h.

Let RAeq {E : Type -> Type} A1 A2 (e1: E A1) (a1: A1) (e2: E A2) (a2: A2) :=
  JMeq a1 a2.

(* specializes compiler correctness to safe source programs *)
Lemma correct_comp entries p q fn fd :
  compile_prog_to_asm aparams cparams entries p = ok q ->
  fn \in entries ->
  get_fundef p.(p_funcs) fn = Some fd ->
  exists2 xfd,
    get_fundef q.(asm_funcs) fn = Some xfd
    & forall s t,
        safe_uprog p fn s ->
        full_pre p q fn xfd s t ->
        eutt
          (full_post cparams p q fn xfd s t)
          (isem_unit p fn s) (isem_asm q fn t).
Proof using print_uprogP print_sprogP print_linearP haparams.
move=> hcomp hfn hfd.
have [xfd [hxfd MY heq]] := [elaborate
  it_compile_prog_to_asmP
    haparams print_uprogP print_sprogP print_linearP hcomp hfn ].
exists xfd; first exact: hxfd.
move=> s t hsafe hpre.
apply/simple_rutt_eutt/(EPreRel_safe_xrutt_rutt hsafe).
apply: (lutt_xrutt_trans_l
  (REv := EPreRel_safe (is_error wE) REeq)
  (RAns := RAeq)
  (RR := full_post cparams p q fn xfd s t));
  cycle -2.

- exact:
    (isem_fun_finalize (wa := withassert) (scP := sCP_unit) (wE := wE)) hfd.
- apply: lutt_xrutt_trans_l; cycle -2.
  + exact: lutt_true.
  + exact: heq hpre.
  + move=> T1 T2 [|[n1]]; first by left. 
    move=> [|[n2]]; first by left.
    move=> _ [p1 p2] //; rewrite p2; right; exists erefl.
    simpl; f_equal.
    dependent destruction p1; auto.    
  + move=> T1 T2. move => [//|[n1]] r1 [//|[n2]] r2 _ _ _ [p1 p2].
    dependent destruction p1.
    dependent destruction p2; simpl.
    move=> /(JMeq_eq (x := r1)) <-.
    split; auto.
    move => h1; dependent destruction h1; auto.
  done.
- done.
- done.
- by [].
Qed.

End MOVE.


Section CHOICEOF.

  Context (T : Type).

  Definition choiceof : Type := T.

  (** We require 'choiceof T' to be classical, i.e. to satisfy the
      excluded middle *)  
  Lemma choiceof_comparable : comparable choiceof.
  Proof. by move=> ??; apply/boolp.pselect. Qed.

  #[export] HB.instance Definition choiceof_eqType :=
    hasDecEq.Build choiceof (compareP choiceof_comparable).

  #[export] HB.instance Definition choiceof_choiceType :=
    boolp.gen_choiceMixin choiceof.

End CHOICEOF.


Section MAIN.

Context {R : realType}.

Notation distr := (distr R).
Notation RndE := (dinterp.RndE (R := R)).
Notation ER := (ErrEvent +' RndEvent).

#[local] Existing Instance wE.
#[local] Existing Instance rndE.

Definition wvec (n : nat) : Type := 'rV[u8]_n.

Definition wseq_of_wvec (n : nat) (v : wvec n) : seq u8 :=
  [seq v ord0 i | i <- enum 'I_n ].

Definition handleRE : Handler RndEvent RndE :=
  fun _ '(syscall.Rnd len) =>
    let* bs := unif_rV (Z.to_nat len) in
    Ret (wseq_of_wvec bs).

Definition interp_Rnd : itree RndEvent ~> itree RndE :=
  fun _ t => interp handleRE t.


Section RND_CORRECT.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {it_asm_scsem : asm_syscall_sem}
.  
Context
  {asm_scsem : asm_syscall_sem}
  {vregs : veneer_regs_info} {avs : asm_veneer_sem}
  {lowering_options : Type}
  (aparams : architecture_params)
  (haparams : h_architecture_params aparams)
  (cparams : compiler_params) 
  (print_uprogP : forall s p, cparams.(print_uprog) s p = p)
  (print_sprogP : forall s p, cparams.(print_sprog) s p = p)
  (print_linearP : forall s p, cparams.(print_linear) s p = p)
.

Definition choice_rel (V1 V2: Type) (r: V1 -> V2 -> Prop) :
  choiceof V1 -> choiceof V2 -> Prop := fun x y => r x y.

Definition flattenER (V : choiceType) (e: V) (t: itree ER V) :
  itree RndE V :=
  interp_Rnd (let* x := interp_Err t in Ret (exec_dflt e x)).
  
Definition prob_sim (V1 V2 : choiceType) (Rel: V1 -> V2 -> Prop)
  (t1: itree ER V1) (t2: itree ER V2) :=
  forall  (v1: V1) (v2: V2),
    deqX Rel (dinterp (flattenER v1 t1)) (dinterp (flattenER v2 t2)).

(* probabilistc correctness in general *)
Lemma probabilistic_correctness (V1 V2 : choiceType) (Rel: V1 -> V2 -> Prop)
  (t1: itree ER V1) (t2: itree ER V2) :
  safe lutt_extras.is_inlB t1 ->
  eutt Rel t1 t2 -> prob_sim Rel t1 t2.
Proof.
  intros H H0 v1 v2.
  eapply eutt_deqX.
  eapply eutt_interp_RR.  
  eapply rutt2eutt.
  eapply simple_rutt_eutt in H0.
  eapply safe_default_ok; auto.
Qed.  

(* Probabilistic correcteness spec: given a source program p and a
   target program q with random events, a target function xfd for a
   function name fn satisfying the full_post spec with respect to a
   source state s and a target state t, the probabilistic
   interpretations of fn as source function of p starting from s and
   as target function of q starting from t give the same
   distribution. *)
Notation prob_equivalence p q fn xfd s t :=
  (prob_sim (choice_rel (full_post cparams p q fn xfd s t))
          (isem_unit p fn s) (isem_asm q fn t)).

(* compilation of programs with random events preserves probabilities
*)
Lemma rnd_correct_comp entries p q fn fd :
  compile_prog_to_asm aparams cparams entries p = ok q ->
  fn \in entries ->
  get_fundef p.(p_funcs) fn = Some fd ->
  exists2 xfd,
    get_fundef q.(asm_funcs) fn = Some xfd
    & forall s t,
        safe_uprog p fn s ->
        full_pre p q fn xfd s t ->
        prob_equivalence p q fn xfd s t. 
Proof using R aparams asm_e asm_op asm_scsem call_conv cond cparams extra_op
haparams print_linearP print_sprogP print_uprogP reg regx rflag xreg.
  intros H H0 H1.
  have [xfd H2 H3] := [elaborate correct_comp haparams
               print_uprogP print_sprogP print_linearP H H0 H1]. 
  exists xfd; auto.
  intros s t X1 X3.
  specialize (H3 s t X1 X3).
  eapply probabilistic_correctness; auto.
Qed.

End RND_CORRECT.

End MAIN.


