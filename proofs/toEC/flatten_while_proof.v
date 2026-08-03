From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import Paco.paco.
From ITree Require Import ITree ITreeFacts.

Require Import psem.
Require Export flatten_while.

Import MonadNotation.
Local Open Scope monad_scope.

Section FLATTEN_WHILE_PROOF.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.

Context
  (p p' : uprog)
  (ev : extra_val_t)
  (flatten_while_ok : flatten_while_prog p = p')
.

(* Iter dinaturality, specialized to plain [ITree.iter] (the library's own
   [iter_dinatural_ktree] is stated for the [ktree] category, one
   [unfold_ktree] away from what is needed here; it is simpler to replay its
   proof directly against [ITree.iter]). Purely about [itree]/[bind]/[iter],
   so it is generic in the event type [Ei], independent of this file's
   ambient [E]. *)
Lemma iter_dinatural_plain {Ei : Type -> Type} {A B C : Type}
    (f : A -> itree Ei (C + B)) (g : C -> itree Ei (A + B)) (a0 : A) :
  ITree.iter (fun a => ITree.bind (f a) (fun cb =>
      match cb with
      | inl c => Tau (g c)
      | inr b => Ret (inr b)
      end)) a0
  ≅ ITree.bind (f a0) (fun cb =>
     match cb with
     | inl c0 => Tau (ITree.iter (fun c =>
         ITree.bind (g c) (fun ab =>
         match ab with
         | inl a => Tau (f a)
         | inr b => Ret (inr b)
         end)) c0)
     | inr b => Ret b
     end).
Proof.
revert f g a0.
ginit. gcofix CIH. intros.
rewrite unfold_iter.
rewrite bind_bind.
guclo eqit_clo_bind. econstructor. try reflexivity.
intros [] ? [].
{ rewrite bind_tau.
  rewrite unfold_iter.
  gstep; econstructor.
  rewrite bind_bind.
  guclo eqit_clo_bind; econstructor; try reflexivity.
  intros [] ? [].
  * rewrite bind_tau.
    gstep; constructor.
    eauto with paco.
  * rewrite bind_ret_l. gstep; econstructor; auto.
}
{ rewrite bind_ret_l. gstep; constructor; auto. }
Qed.

(* The crux "loop rotation" equation, proved via the iter dinaturality above:
   on a single program [p], executing a [Cwhile] with a non-empty pre-block
   [c1] is the same as executing [c1] once, then an equivalent [Cwhile] with
   empty pre-block whose body ends by replaying [c1]. Both sides run under
   the same program [p], so this is a fact about [p] alone, independent of
   [flatten_while].

   [wequiv_rec] fixes the function-call semantics to [sem_fun_rec] at event
   type [recCall +' E] (not this file's ambient [E]/[sem_F] instance, picked
   independently by typeclass search), so the whole development below is
   generic in a fresh event type [Ei] and semantics [sem_Fi], to be
   instantiated at [recCall +' E] / [sem_fun_rec] where it is used, inside
   [flatten_while_cP]'s [Cwhile] case.

   [rotate_f]/[rotate_g] split one round of the [c1]-headed loop into "run
   c1, always continue" (f) and "test the condition, maybe run c2" (g);
   [rotate_step]/[rotate_step'] are the "f;g" / "g;f" composites that
   [iter_dinatural_plain] relates. [rotate_step_roundP]/[rotate_step'_roundP]
   show these composites reproduce the two rounds up to one harmless [Tau],
   bridged to the full [iter]s by the library's [eutt_iter] properness. *)
Section ROTATE.

Context
  {Ei Ei0 : Type -> Type}
  {wEi : with_Error Ei Ei0}
  {sem_Fi : sem_Fun Ei}
.

(* Strong (≅) helper fact: composes freely with rewriting inside a
   coinductive [ecofix] proof, unlike the weaker (≈) [isem_cmd_cat] /
   [isem_cmd_while]. *)
Lemma isem_foldr_cat c1 c2 s :
  isem_foldr isem_i_body p ev (c1 ++ c2) s ≅
  (s1 <- isem_foldr isem_i_body p ev c1 s;;
   isem_foldr isem_i_body p ev c2 s1).
Proof.
elim: c1 s => [ | i c1 hc1] /= s.
- by rewrite bind_ret_l; reflexivity.
rewrite bind_bind.
apply: eq_itree_clo_bind; first reflexivity.
by move=> ?? <-; apply: hc1.
Qed.

Definition rotate_f (c1 : cmd) (a : estate) : itree Ei (estate + estate) :=
  s1 <- isem_foldr isem_i_body p ev c1 a;; Ret (inl s1).

Definition rotate_g (e : pexpr) (c2 : cmd) (c : estate) :
    itree Ei (estate + estate) :=
  b <- isem_cond p e c;;
  if b then s2 <- isem_foldr isem_i_body p ev c2 c;; Ret (inl s2)
  else Ret (inr c).

Definition rotate_step (c1 : cmd) (e : pexpr) (c2 : cmd) (a : estate) :
    itree Ei (estate + estate) :=
  cb <- rotate_f c1 a;;
  match cb with
  | inl c => Tau (rotate_g e c2 c)
  | inr b => Ret (inr b)
  end.

Definition rotate_step' (c1 : cmd) (e : pexpr) (c2 : cmd) (c : estate) :
    itree Ei (estate + estate) :=
  ab <- rotate_g e c2 c;;
  match ab with
  | inl a => Tau (rotate_f c1 a)
  | inr b => Ret (inr b)
  end.

Lemma rotate_step_roundP c1 e c2 a :
  rotate_step c1 e c2 a ≈ isem_while_round isem_i_body p ev c1 e c2 a.
Proof.
rewrite /rotate_step /rotate_f /isem_while_round.
setoid_rewrite bind_bind.
apply eutt_eq_bind => s1.
rewrite bind_ret_l.
apply tau_eutt.
Qed.

Lemma rotate_step'_roundP c1 e c2 c :
  rotate_step' c1 e c2 c ≈
    isem_while_round isem_i_body p ev [::] e (c2 ++ c1) c.
Proof.
rewrite /rotate_step' /rotate_g /isem_while_round /=.
rewrite bind_ret_l.
setoid_rewrite bind_bind.
apply eutt_eq_bind => b.
case: b.
- rewrite bind_bind.
  setoid_rewrite isem_foldr_cat.
  setoid_rewrite bind_bind.
  apply eutt_eq_bind => s2.
  rewrite bind_ret_l.
  apply tau_eutt.
rewrite bind_ret_l.
reflexivity.
Qed.

Lemma rotate_iter_stepP c1 e c2 a :
  ITree.iter (rotate_step c1 e c2) a ≈
  ITree.iter (isem_while_round isem_i_body p ev c1 e c2) a.
Proof. apply eutt_iter => s; apply rotate_step_roundP. Qed.

Lemma rotate_iter_step'P c1 e c2 c :
  ITree.iter (rotate_step' c1 e c2) c ≈
  ITree.iter (isem_while_round isem_i_body p ev [::] e (c2 ++ c1)) c.
Proof. apply eutt_iter => s; apply rotate_step'_roundP. Qed.

Lemma flatten_while_rotate_auxP c1 e c2 s :
  (s1 <- isem_foldr isem_i_body p ev c1 s;;
   ITree.iter (isem_while_round isem_i_body p ev [::] e (c2 ++ c1)) s1) ≈
  ITree.iter (isem_while_round isem_i_body p ev c1 e c2) s.
Proof.
rewrite -(rotate_iter_stepP c1 e c2 s).
setoid_rewrite <- (rotate_iter_step'P c1 e c2).
rewrite /rotate_step.
rewrite (iter_dinatural_plain (rotate_f c1) (rotate_g e c2)).
rewrite /rotate_f bind_bind.
apply eutt_eq_bind => s1.
rewrite bind_ret_l.
rewrite -/(rotate_f c1) -/(rotate_step' c1 e c2).
symmetry.
apply tau_eutt.
Qed.

Lemma flatten_while_rotateP ii al c1 e inf c2 s :
  isem_cmd_ p ev (c1 ++ [:: MkI ii (Cwhile al [::] e inf (c2 ++ c1))]) s ≈
  isem_cmd_ p ev [:: MkI ii (Cwhile al c1 e inf c2)] s.
Proof.
rewrite /isem_cmd_ isem_foldr_cat /=.
rewrite /isem_while_loop.
setoid_rewrite bind_ret_r.
exact: flatten_while_rotate_auxP.
Qed.

End ROTATE.

Lemma flatten_while_eq_globs : p_globs p = p_globs p'.
Proof using flatten_while_ok. by rewrite -flatten_while_ok. Qed.

#[local] Instance flatten_while_checker_st_eqP : Checker_eq p p' checker_st_eq :=
  checker_st_eqP flatten_while_eq_globs.

#[local] Instance flatten_while_checker_a_st_eqP : Checker_a_eq p p' checker_a_st_eq :=
  checker_a_st_eqP flatten_while_eq_globs.

#[local] Hint Resolve flatten_while_checker_st_eqP flatten_while_checker_a_st_eqP : core.

Let Pi (i : instr) :=
  wequiv_rec p p' ev ev eq_spec (st_eq tt) [:: i] (flatten_while_i i) (st_eq tt).

Let Pi_r (i : instr_r) := forall ii, Pi (MkI ii i).

Let Pc (c : cmd) :=
  wequiv_rec p p' ev ev eq_spec (st_eq tt) c (flatten_while_c flatten_while_i c) (st_eq tt).

Lemma flatten_while_cP c : Pc c.
Proof using E Pc Pi Pi_r asm_op dc ep ev flatten_while_ok p p' rE0 sip spp
  syscall_state wE wsw.
apply: (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => // {c}.
- by apply wequiv_nil.
- move=> i c hi hc /=.
  rewrite -cat1s.
  by apply wequiv_cat with (st_eq tt); [exact hi | exact hc].
- by move=> >; apply wequiv_assgn_rel_eq with checker_st_eq tt.
- by move=> >; apply wequiv_opn_rel_eq with checker_st_eq tt.
- by move=> >; apply wequiv_syscall_rel_eq with checker_st_eq tt.
- by move=> a ii /=; apply wequiv_assert_rel_eq with checker_a_st_eq.
- by move=> e c1 c2 hc1 hc2 ii /=; apply wequiv_if_rel_eq with checker_st_eq tt tt tt.
- by move=> v dir lo hi c hc ii /=; apply wequiv_for_rel_eq with checker_st_eq tt tt.
- move=> al c1 e inf c2 hc1 hc2 ii.
  rewrite /Pi /=.
  case: c1 hc1 => [ | i1 c1] hc1 /=.
  + apply wequiv_while_rel_eq with checker_st_eq tt.
    * exact: flatten_while_checker_st_eqP.
    * done.
    * apply wequiv_nil; done.
    exact: hc2.
  rewrite /wequiv_rec /wequiv.
  apply (wkequiv_eutt_l
    (F1 := fun s => isem_cmd_ (sem_F := sem_fun_rec E) p ev
      ((i1 :: c1) ++
       [:: MkI ii (Cwhile al [::] e inf (c2 ++ (i1 :: c1)))]) s)).
  + move=> s1 s2 _.
    exact: (flatten_while_rotateP ii al (i1 :: c1) e inf c2 s1).
  rewrite -/wequiv -/wequiv_rec.
  apply wequiv_cat with (st_eq tt).
  + exact: hc1.
  apply wequiv_while_rel_eq with checker_st_eq tt.
  + exact: flatten_while_checker_st_eqP.
  + done.
  + apply wequiv_nil; done.
  apply wequiv_cat with (st_eq tt).
  + exact: hc2.
  exact: hc1.
move=> xs f es ii /=.
apply wequiv_call_rel_eq with checker_st_eq tt => //.
move=> ?? <-; exact/wequiv_fun_rec.
Qed.

Lemma get_fundef_flatten_while fn :
  get_fundef (p_funcs (flatten_while_prog p)) fn =
    omap flatten_while_fd (get_fundef (p_funcs p) fn).
Proof.
rewrite /get_fundef /flatten_while_prog /=.
by elim: (p_funcs p) => [|[fn' fd'] pfuns ih] //=; case: eqP.
Qed.

Lemma flatten_while_proof fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using flatten_while_ok.
apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hget.
exists (flatten_while_fd fd).
- by rewrite -flatten_while_ok get_fundef_flatten_while hget.
move=> s11 hinit.
exists s11.
- by apply: (eq_initialize _ _ _ _ hinit) => //; rewrite -flatten_while_ok.
exists (st_eq tt), (st_eq tt); split=> //.
apply flatten_while_cP.
exact: (st_eq_finalize erefl erefl erefl).
Qed.

End FLATTEN_WHILE_PROOF.
