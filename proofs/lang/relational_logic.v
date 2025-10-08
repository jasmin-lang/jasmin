From Coq Require Import
  Program
  Setoid
  Morphisms
  RelationClasses
  List.

From ITree Require Import
  ITree
  ITreeFacts
  Basics.HeterogeneousRelations
  Interp.Recursion
  Eq.Rutt
  Eq.RuttFacts.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Require Import xrutt xrutt_facts.
Require Import expr psem_defs psem_core oseq compiler_util.
Require Import it_sems_core core_logics hoare_logic.
Import Utf8.

Definition rel (I1 I2 : Type) := I1 -> I2 -> Prop.

Definition rel_io (I1 I2 O1 O2 : Type) := I1 -> I2 -> O1 -> O2 -> Prop.

Notation relT := (fun _ _ => True).

Notation eq_init i1 i2 := (fun i1' i2' => i1' = i1 /\ i2' = i2).

Section WREQUIV.

Context {Err1 Err2 : Set}.

(* generic, (independent of itrees), error-sensitive and
   input-sensitive (by fresult), fully relational Hoare triples.
   meant to represent a similarity, not really an equivalence *)
Definition wrequiv_io {I1 I2 O1 O2}
   (P : rel I1 I2) (F1 : fresult Err1 I1 O1) (F2 : fresult Err2 I2 O2) (Q : rel_io I1 I2 O1 O2) :=
  forall i1 i2 o1, P i1 i2 -> F1 i1 = ok o1 -> exists2 o2, F2 i2 = ok o2 & Q i1 i2 o1 o2.

(* similar, with input-independent post-conditions *)
Definition wrequiv {I1 I2 O1 O2}
   (P : rel I1 I2) (F1 : fresult Err1 I1 O1) (F2 : fresult Err2 I2 O2) (Q : rel O1 O2) :=
  wrequiv_io P F1 F2 (fun _ _ => Q).

Lemma wrequiv_ioP {I1 I2 O1 O2} (P : rel I1 I2) F1 F2 (Q : rel_io I1 I2 O1 O2) :
  wrequiv_io P F1 F2 Q <->
  (forall i1_ i2_, P i1_ i2_ -> wrequiv (fun i1 i2 => i1 = i1_ /\ i2 = i2_) F1 F2 (Q i1_ i2_)).
Proof.
  split.
  + by move=> h i1_ i2_ hP i1 i2 ? [??]; subst i1 i2; apply: h hP.
  by move=> h i1 i2 o1 /h; apply.
Qed.

Lemma wrequiv_io_weaken {I1 I2 O1 O2} (P P' : rel I1 I2) (Q Q' : rel_io I1 I2 O1 O2) F1 F2 :
  (forall i1 i2, P' i1 i2 -> P i1 i2) ->
  (forall i1 i2 o1 o2, P' i1 i2 -> Q i1 i2 o1 o2 -> Q' i1 i2 o1 o2) ->
  wrequiv_io P F1 F2 Q ->
  wrequiv_io P' F1 F2 Q'.
Proof.
  move=> hP'P hQQ' h i1 i2 o1 hP' hF1.
  have [o2 -> hQ]:= h _ _ _ (hP'P _ _ hP') hF1; eauto.
Qed.

Lemma wrequiv_weaken {I1 I2 O1 O2} (P P' : rel I1 I2) (Q Q' : rel O1 O2) F1 F2 :
  (forall i1 i2, P' i1 i2 -> P i1 i2) ->
  (forall o1 o2, Q o1 o2 -> Q' o1 o2) ->
  wrequiv P F1 F2 Q ->
  wrequiv P' F1 F2 Q'.
Proof. move=> hP'P hQQ'; apply wrequiv_io_weaken => //; auto. Qed.

Lemma wrequiv_io_ok {I1 I2} (P : rel I1 I2) (Q : rel_io I1 I2 I1 I2):
  (forall i1 i2, P i1 i2 -> Q i1 i2 i1 i2) ->
  wrequiv_io P (@Ok _ _) (@Ok _ _) Q.
Proof. by move=> hPQ i1 i2 o1 hQ [<-]; exists i2 => //; apply hPQ. Qed.

Lemma wrequiv_ok {I1 I2} (Q : rel I1 I2) : wrequiv Q (@Ok _ _) (@Ok _ _) Q.
Proof. by apply wrequiv_io_ok. Qed.

Lemma wrequiv_io_err {I1 I2 O1 O2} (P : rel I1 I2) (Q : rel_io I1 I2 O1 O2) (e : Err1) F :
  wrequiv_io P (fun i1 => Error e) F Q.
Proof. by move=> ?. Qed.

Lemma wrequiv_err {I1 I2 O1 O2} (P : rel I1 I2) (Q : rel O1 O2) (e : Err1) F :
  wrequiv P (fun i1 => Error e) F Q.
Proof. apply wrequiv_io_err. Qed.

Lemma wrequiv_false {I1 I2 O1 O2} (F1 : fresult Err1 I1 O1) (F2 : fresult Err2 I2 O2) (Q : rel O1 O2):
  wrequiv (fun _ _ => False) F1 F2 Q.
Proof. done. Qed.

Lemma wrequiv_io_bind {I1 I2 T1 T2 O1 O2}
  (R : rel_io I1 I2 T1 T2)
  (P : rel I1 I2)
  (Q : rel_io I1 I2 O1 O2) F1 F1' F2 F2' :
  wrequiv_io P F1 F2 R ->
  (forall i1 i2, P i1 i2 -> wrequiv (R i1 i2) F1' F2' (Q i1 i2)) ->
  wrequiv_io P (fun i => F1 i >>= F1') (fun i => F2 i >>= F2') Q.
Proof.
  move=> h h' i1 i2 o1 hP; t_xrbindP => t1 /(h _ _ _ hP) [t2 -> /= hR].
  by apply: h'.
Qed.

Lemma wrequiv_bind {I1 I2 T1 T2 O1 O2}
  (R : rel T1 T2)
  (P : rel I1 I2)
  (Q : rel O1 O2) F1 F1' F2 F2' :
  wrequiv P F1 F2 R ->
  wrequiv R F1' F2' Q ->
  wrequiv P (fun i => F1 i >>= F1') (fun i => F2 i >>= F2') Q.
Proof. by move=> h h'; apply wrequiv_io_bind with (R:= fun _ _ => R). Qed.

Lemma wrequiv_read {S1 S2 T1 T2 O1 O2} F1 F1' F2 F2' (P : rel S1 S2) (R : rel T1 T2) (Q : rel O1 O2) :
  wrequiv P F1 F2 R ->
  (forall t1 t2, R t1 t2 -> wrequiv P (F1' t1) (F2' t2) Q) ->
  wrequiv P (fun s => Let r := F1 s in F1' r s) (fun s => Let r := F2 s in F2' r s) Q.
Proof.
  by move=> hF hF' s1 s2 o1 hP; t_xrbindP => t1 /hF -/(_ _ hP) [t2 -> /=] /hF'; apply.
Qed.

Lemma wrequiv_bind_eval {S1 S2 I1 I2 T1 T2 O1 O2} F1 F1' F2 F2'
  (P : rel S1 S2) (R : rel T1 T2) (Q : rel O1 O2) (i1 : I1) (i2 : I2) :
  (forall s1 s2, P s1 s2 -> wrequiv (eq_init i1 i2) F1 F2 R) ->
  (forall t1 t2, R t1 t2 -> wrequiv P (F1' t1) (F2' t2) Q) ->
  wrequiv P (fun s => Let r := F1 i1 in F1' r s)  (fun s => Let r := F2 i2 in F2' r s) Q.
Proof.
  move=> hF hF' s1 s2 o1 hP; t_xrbindP => t1 /(hF _ _ hP) -/(_ i2) [] // t2 -> /=.
  by move=> /hF'; apply.
Qed.

Lemma wrequiv_eval {S1 S2 I1 I2 O1 O2} F1 F2
  (P : rel S1 S2) (Q : rel O1 O2) (i1 : I1) (i2 : I2) :
  (forall s1 s2, P s1 s2 -> wrequiv (eq_init i1 i2) F1 F2 Q) ->
  wrequiv P (fun s => F1 i1) (fun s => F2 i2) Q.
Proof. by move=> hF s1 s2 o1 hP /(hF _ _ hP) -/(_ i2); apply. Qed.

Lemma wrequiv_id {I1 I2 O1 O2} (F1 : fresult Err1 I1 O1) (F2 : fresult Err2 I2 O2) P i1 i2:
   wrequiv (eq_init i1 i2) F1 F2 P ->
   wrequiv (eq_init i1 i2) F1 F2 (fun o1 o2 => [/\ P o1 o2, F1 i1 = ok o1 & F2 i2 = ok o2]).
Proof.
  move=> h _ _ o1 [-> ->] hF1.
  by case: (h i1 i2 _ _ hF1) => // => o2 ??; exists o2.
Qed.

Lemma wrequiv_eq_pred {I1 I2 O1 O2} F1 F2 (P : rel I1 I2) (Q : rel O1 O2) :
  (forall i1 i2, P i1 i2 -> wrequiv (eq_init i1 i2) F1 F2 Q) ->
  wrequiv P F1 F2 Q.
Proof. by move=> h i1 i2 hP /h{}h; apply (h i1 i2). Qed.

End WREQUIV.

Section SOPN.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {asm_op}  {sip : SemInstrParams asm_op syscall_state}.

Lemma wrequiv_exec_sopn o :
  wrequiv (Forall2 value_uincl) (exec_sopn o) (exec_sopn o) (Forall2 value_uincl).
Proof. move=> vs1 vs2 vs1'; apply vuincl_exec_opn. Qed.

End SOPN.

Lemma wrequiv_eq {I O Err} (F: fresult Err I O) : wrequiv eq F F eq.
Proof. move=> i _ o <-; eauto. Qed.

Lemma wrequiv_to_bool : wrequiv value_uincl to_bool to_bool eq.
Proof.
  move=> v1 v2 b1 hu hb1.
  have [b2 /= -> /value_uinclE /= [->]] := val_uincl_of_val (ty:= sbool) hu hb1; eauto.
Qed.

Lemma wrequiv_to_int : wrequiv value_uincl to_int to_int eq.
Proof.
  move=> v1 v2 i1 hu hi1.
  have [b2 /= -> /value_uinclE /= [->]] := val_uincl_of_val (ty:= sint) hu hi1; eauto.
Qed.

Lemma wrequiv_truncate_val ty :
  wrequiv value_uincl (truncate_val ty) (truncate_val ty) value_uincl.
Proof. move=> v1 v2 v1'; apply value_uincl_truncate. Qed.

(* ------------------------------------------------- *)

(* pre-relation and postrelation associated with an event type *)
Class EventRels (E0 : Type -> Type) :=
  { EPreRel0_  : prerel E0 E0
  ; EPostRel0_ : postrel E0 E0 }.

Definition EPreRel0 {E0} {rE0 : EventRels E0} := EPreRel0_.
Definition EPostRel0 {E0} {rE0 : EventRels E0} := EPostRel0_.

(* pre-relation associated with an event type extended with errors *)
Definition EPreRel {E E0 : Type -> Type} {wE : with_Error E E0}
  {rE0 : EventRels E0} : prerel E E :=
  fun T1 T2 (e1 : E T1) (e2 : E T2) =>
    sum_prerelF (fun _ _ _ _ => True) EPreRel0 (mfun1 e1) (mfun1 e2).

(* post-relation associated with an event type extended with errors *)
Definition EPostRel {E E0 : Type -> Type} {wE : with_Error E E0}
  {rE0 : EventRels E0} : postrel E E :=
  fun T1 T2 (e1 : E T1) (t1 : T1) (e2 : E T2) (t2 : T2) =>
    sum_postrelF (fun _ _ _ _ _ _ => True) EPostRel0
      (mfun1 e1) t1 (mfun1 e2) t2.

Section WKEQUIV.

Context {E E0: Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

(* alternative version of wrequiv, directly specialized to itrees and
   based on xrutt *)
Definition wkequiv_io {I1 I2 O1 O2}
   (P : rel I1 I2) (F1 : ktree E I1 O1) (F2 : ktree E I2 O2) (Q : rel_io I1 I2 O1 O2) :=
  forall i1 i2, P i1 i2 ->
    xrutt (errcutoff (is_error wE)) nocutoff EPreRel EPostRel (Q i1 i2)
          (F1 i1) (F2 i2).

(* similar, with input-independent post-conditions *)
Definition wkequiv {I1 I2 O1 O2}
  (P : rel I1 I2) (F1 : ktree E I1 O1) (F2 : ktree E I2 O2) (Q : rel O1 O2) :=
  wkequiv_io P F1 F2 (fun i1 i2 => Q).

Lemma wkequiv_ioP {I1 I2 O1 O2} (P : rel I1 I2) F1 F2 (Q : rel_io I1 I2 O1 O2) :
  wkequiv_io P F1 F2 Q <->
  (forall i1 i2, P i1 i2 -> wkequiv (eq_init i1 i2) F1 F2 (Q i1 i2)).
Proof.
  split.
  + by move=> h i1 i2 hP _ _ [-> ->]; apply h.
  by move=> h i1 i2 hP; apply h.
Qed.

Lemma wkequiv_io_ret {I1 I2 O1 O2} (P : rel I1 I2) f1 f2 (Q : rel_io I1 I2 O1 O2) :
  (forall i1 i2, P i1 i2 -> Q i1 i2 (f1 i1) (f2 i2)) ->
  wkequiv_io P (fun i => ret (f1 i)) (fun i => ret (f2 i)) Q.
Proof. by move=> hPQ i1 i2 hP; apply xrutt_Ret; apply hPQ. Qed.

Lemma wkequiv_ret {I1 I2 O1 O2} (P : rel I1 I2) f1 f2 (Q : rel O1 O2) :
  (forall i1 i2, P i1 i2 -> Q (f1 i1) (f2 i2)) ->
  wkequiv P (fun i => ret (f1 i)) (fun i => ret (f2 i)) Q.
Proof. by apply wkequiv_io_ret. Qed.

Lemma wkequiv_io_bind {I1 I2 T1 T2 O1 O2}
  (R : rel_io I1 I2 T1 T2)
  (P : rel I1 I2)
  (Q : rel_io I1 I2 O1 O2) F1 F2 F1' F2' :
  wkequiv_io P F1 F2 R ->
  (forall i1 i2, P i1 i2 -> wkequiv (R i1 i2) F1' F2' (Q i1 i2)) ->
  wkequiv_io P (fun i => t <- F1 i;; F1' t) (fun i => t <- F2 i;; F2' t) Q.
Proof.
  move=> h h' i1 i2 hP.
  apply xrutt_bind with (R i1 i2).
  + by apply h.
  by move=> r1 r2; apply h'.
Qed.

Lemma wkequiv_bind {I1 I2 T1 T2 O1 O2}
  (R : rel T1 T2)
  (P : rel I1 I2)
  (Q : rel O1 O2) F1 F2 F1' F2' :
  wkequiv P F1 F2 R ->
  wkequiv R F1' F2' Q ->
  wkequiv P (fun i => t <- F1 i;; F1' t) (fun i => t <- F2 i;; F2' t) Q.
Proof. by move=> h h'; apply wkequiv_io_bind with (R := fun _ _ => R). Qed.

Lemma wkequiv_bind_ret_left {I1 I2 O1 O2}
  (P : rel I1 I2)
  (Q : rel O1 O2) F1 F2 :
  wkequiv P F1 F2 Q ->
  wkequiv P (fun i => t <- F1 i;; Ret t) F2 Q.
Proof. move=> h s t; setoid_rewrite bind_ret_r; apply h. Qed.

Lemma wkequiv_bind_ret_right {I1 I2 O1 O2}
  (P : rel I1 I2)
  (Q : rel O1 O2) F1 F2 :
  wkequiv P F1 F2 Q ->
  wkequiv P F1 (fun i => t <- F2 i;; Ret t) Q.
Proof. move=> h s t; setoid_rewrite bind_ret_r; apply h. Qed.

Lemma wkequiv_read {S1 S2 T1 T2 O1 O2} F1 F2 F1' F2'
  (P : rel S1 S2) (R : rel T1 T2) (Q : rel O1 O2) :
  wkequiv P F1 F2 R ->
  (forall t1 t2, R t1 t2 -> wkequiv P (F1' t1) (F2' t2) Q) ->
  wkequiv P (fun s => r <- F1 s ;; F1' r s) (fun s => r <- F2 s ;; F2' r s) Q.
Proof.
  move=> hF hF' s1 s2 hP.
  apply xrutt_bind with R; eauto.
  by move=> r1 r2 hR; apply hF'.
Qed.

Lemma wkequiv_eval {S1 S2 I1 I2 T1 T2 O1 O2} F1 F2 F1' F2'
  (P : rel S1 S2) (R : rel T1 T2) (Q : rel O1 O2) (i1 : I1) (i2 : I2) :
  (forall s1 s2, P s1 s2 -> wkequiv (eq_init i1 i2) F1 F2 R) ->
  (forall t1 t2, R t1 t2 -> wkequiv P (F1' t1) (F2' t2) Q) ->
  wkequiv P (fun s => r <- F1 i1 ;; F1' r s) (fun s => r <- F2 i2 ;; F2' r s) Q.
Proof.
  move=> hF hF' s1 s2 hP.
  apply xrutt_bind with R.
  + by apply (hF _ _ hP).
  by move=> r1 r2 hR; apply hF'.
Qed.

Lemma wkequiv_eq_pred {I1 I2 O1 O2} F1 F2 (P : rel I1 I2) (Q : rel O1 O2) :
  (forall i1 i2, P i1 i2 -> wkequiv (eq_init i1 i2) F1 F2 Q) ->
  wkequiv P F1 F2 Q.
Proof. by move=> h i1 i2 hP; apply (h i1 i2 hP). Qed.

Lemma wkequivP' {I1 I2 O1 O2} F1 F2 (P : rel I1 I2) (Q : rel O1 O2) :
  (forall i1 i2, wkequiv (fun i1' i2' => eq_init i1 i2 i1' i2' /\ P i1' i2') F1 F2 Q) <->
  wkequiv P F1 F2 Q.
Proof.
  rewrite /wkequiv wkequiv_ioP; split.
  + by move=> h i1 i2 hP i1' i2' [??]; subst i1' i2'; apply (h i1 i2).
  by move=> h i1 i2 i1' i2' [[??] hP]; subst i1' i2'; apply (h i1 i2).
Qed.

Lemma wkequiv_iter (IT1 IT2 T1 T2 : Type) (I : rel IT1 IT2) (Q : rel T1 T2) body1 body2 :
  wkequiv I body1 body2 (sum_rel I Q) ->
  wkequiv I (ITree.iter body1) (ITree.iter body2) Q.
Proof. by move=> hbody i1 i2 hI; apply xrutt_iter with I. Qed.

(* TODO: it will be nicer to be able to rewrite under wkequiv, i.e we need morphisms *)
Lemma wkequiv_eutt_l {I1 I2 O1 O2}
  (P : rel I1 I2)
  (Q : rel O1 O2) F1 F2 F1':
  (forall s1 s2, P s1 s2 -> F1 s1 ≈ F1' s1) ->
  wkequiv P F1 F2 Q ->
  wkequiv P F1' F2 Q.
Proof.
  by move=> heq h s1 s2 hP; rewrite <-(heq _ _ hP); apply h.
Qed.

Lemma wkequiv_eutt_r {I1 I2 O1 O2}
  (P : rel I1 I2)
  (Q : rel O1 O2) F1 F2 F2':
  (forall s1 s2, P s1 s2 -> F2 s2 ≈ F2' s2) ->
  wkequiv P F1 F2 Q ->
  wkequiv P F1 F2' Q.
Proof.
  by move=> heq h s1 s2 hP; rewrite <-(heq _ _ hP); apply h.
Qed.

End WKEQUIV.

Section WKEQUIV_WEAKEN.

Context {E E0: Type -> Type} {wE: with_Error E E0} {rE0 rE0': EventRels E0}.

Lemma wkequiv_io_weaken {I1 I2 O1 O2} (P P' : rel I1 I2)
  (Q Q' : rel_io I1 I2 O1 O2) F1 F2 :
  (forall T1 T2 (e1 : E0 T1) (e2 : E0 T2),
    EPreRel0 (rE0:=rE0) e1 e2 -> EPreRel0 (rE0:=rE0') e1 e2) ->
  (forall T1 T2 (e1 : E0 T1) (t1 : T1) (e2 : E0 T2) (t2 : T2),
    EPreRel0 (rE0:=rE0) e1 e2 ->
    EPostRel0 (rE0:=rE0') e1 t1 e2 t2 -> EPostRel0 (rE0:=rE0) e1 t1 e2 t2) ->
  (forall i1 i2, P' i1 i2 -> P i1 i2) ->
  (forall i1 i2 o1 o2, P' i1 i2 -> Q i1 i2 o1 o2 -> Q' i1 i2 o1 o2) ->
  wkequiv_io (rE0:=rE0)  P F1 F2 Q ->
  wkequiv_io (rE0:=rE0') P' F1 F2 Q'.
Proof.
  move=> hpreI hpostI hP'P hQQ' heqv i1 i2 hP'.
  have := heqv _ _ (hP'P _ _ hP').
  apply xrutt_weaken => //.
  + move=> T1 T2 e1 e2; rewrite /EPreRel.
    by rewrite -sum_prerelP; case.
  + move=> T1 T2 e1 t1 e2 t2 _ _; rewrite /EPreRel /EPostRel => h1 /sum_postrelP h2.
    by case: h2 h1 => //=; eauto.
  by move=> o1 o2; apply hQQ'.
Qed.

Lemma wkequiv_weaken {I1 I2 O1 O2} (P P' : rel I1 I2) (Q Q' : rel O1 O2) F1 F2 :
  (forall T1 T2 (e1 : E0 T1) (e2 : E0 T2),
    EPreRel0 (rE0:=rE0) e1 e2 -> EPreRel0 (rE0:=rE0') e1 e2) ->
  (forall T1 T2 (e1 : E0 T1) (t1 : T1) (e2 : E0 T2) (t2 : T2),
    EPreRel0 (rE0:=rE0) e1 e2 ->
    EPostRel0 (rE0:=rE0') e1 t1 e2 t2 -> EPostRel0 (rE0:=rE0) e1 t1 e2 t2) ->
  (forall i1 i2, P' i1 i2 -> P i1 i2) ->
  (forall i1 i2 o1 o2, P' i1 i2 -> Q o1 o2 -> Q' o1 o2) ->
  wkequiv (rE0:=rE0)  P F1 F2 Q ->
  wkequiv (rE0:=rE0') P' F1 F2 Q'.
Proof. apply wkequiv_io_weaken. Qed.

End WKEQUIV_WEAKEN.

(* Definition of a relational logic over program *)

Section RELATIONAL.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {asm_op: Type}
  {sip : SemInstrParams asm_op syscall_state}
  {pT1 pT2 : progT}
  {wsw1 wsw2: WithSubWord}
  {scP1 : semCallParams (wsw:= wsw1) (pT := pT1)}
  {scP2 : semCallParams (wsw:= wsw2) (pT := pT2)}
  {dc1 dc2: DirectCall}.

Notation prog1 := (prog (pT := pT1)).
Notation prog2 := (prog (pT := pT2)).

Notation extra_val_t1 := (@extra_val_t pT1).
Notation extra_val_t2 := (@extra_val_t pT2).

Notation vm1_t := (Vm.t (wsw:=wsw1)).
Notation vm2_t := (Vm.t (wsw:=wsw2)).

Notation estate1 := (estate (wsw:=wsw1) (ep:=ep)).
Notation estate2 := (estate (wsw:=wsw2) (ep:=ep)).


Notation sem_Fun1 := (sem_Fun (pT:=pT1)).
Notation sem_Fun2 := (sem_Fun (pT:=pT2)).

Definition relPreF := funname -> funname -> fstate -> fstate -> Prop.
Definition relPostF := funname -> funname -> fstate -> fstate -> fstate -> fstate -> Prop.

Definition rel_e := rel pexpr pexpr.
Definition rel_v := rel value value.
Definition rel_vs := rel values values.
Definition rel_c := rel estate1 estate2.

Section TR_MutualRec.

Class EquivSpec :=
  { rpreF_  : relPreF
  ; rpostF_ : relPostF }.

Definition rpreF {eS : EquivSpec} := rpreF_.
Definition rpostF {eS : EquivSpec} := rpostF_.

Definition eq_spec : EquivSpec :=
  {| rpreF_ := fun (fn1 fn2 : funname) (fs1 fs2 : fstate) => fn1 = fn2 /\ fs1 = fs2
   ; rpostF_ := fun (fn1 fn2 : funname) (fs1 fs2 fr1 fr2: fstate) => fr1 = fr2 |}.

Context (spec : EquivSpec) {E0: Type -> Type}.

Definition RPreD {T1 T2} (d1 : recCall T1)
                         (d2 : recCall T2) : Prop :=
  match d1, d2 with
  | RecCall _ fn1 fs1, RecCall _ fn2 fs2 => rpreF fn1 fn2 fs1 fs2
  end.

Definition RPostD {T1 T2} (d1 : recCall T1) (t1: T1) (d2 : recCall T2) (t2: T2) : Prop :=
  match d1 in recCall T1_ return T1_ -> T2 -> Prop with
  | RecCall _ fn1 fs1 =>
    match d2 in recCall T2_ return fstate -> T2_ -> Prop with
    | RecCall _ fn2 fs2 => rpostF fn1 fn2 fs1 fs2
    end
  end t1 t2.

Instance relEvent_recCall {rE0 : EventRels E0} : EventRels (recCall +' E0) :=
  {| EPreRel0_  := sum_prerelF (@RPreD) EPreRel0
   ; EPostRel0_ := sum_postrelF (@RPostD) EPostRel0
  |}.

End TR_MutualRec.

Section IRESULT.

Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Lemma rutt_iresult (T1 T2:Type) (s1 : estate1) (s2 : estate2) (x1 : exec T1) (x2 : exec T2) (R : T1 -> T2 -> Prop) :
  (forall v1, x1 = ok v1 -> exists2 v2, x2 = ok v2 & R v1 v2) ->
  xrutt (errcutoff (is_error wE)) nocutoff EPreRel EPostRel R (iresult s1 x1) (iresult s2 x2).
Proof.
  case: x1 => [ v1 | e1] hok.
  + have [v2 -> /=] := hok _ erefl.
    by apply: xrutt_Ret.
  apply xrutt_CutL => //.
  by rewrite /errcutoff /is_error /subevent /resum /fromErr mid12.
Qed.

Lemma wkequiv_iresult {I1 I2 O1 O2} (P : rel I1 I2) (Q : rel O1 O2) (f1 : I1 -> estate1) (f2 : I2 -> estate2) F1 F2 :
  wrequiv P F1 F2 Q ->
  wkequiv P (fun i => iresult (f1 i) (F1 i)) (fun i => iresult (f2 i) (F2 i)) Q.
Proof. by move=> h i1 i2 hP; apply rutt_iresult => s1'; apply: h. Qed.

Lemma wkequiv_iresult_right (P : rel estate1 estate2) (Q : rel estate1 estate2) (f2 : estate2 -> estate2) F2 :
  (forall s t, P s t -> exists2 t', F2 t = ok t' & Q s t') ->
  wkequiv P (fun s => Ret s) (fun t => iresult (f2 t) (F2 t)) Q.
Proof.
  by move=> h s t /h [t'] hF2 hQ; rewrite /iresult hF2 /=; apply xrutt_Ret.
Qed.

Lemma wkequiv_iresult_left (P : rel estate1 estate2) (Q : rel estate1 estate2) (f1 : estate1 -> estate1) F1 :
  (forall s s' t, P s t -> F1 s = ok s' -> Q s' t) ->
  wkequiv P (fun s => iresult (f1 s) (F1 s)) (fun t => Ret t) Q.
Proof.
  move=> h s t /h{}h; rewrite /iresult.
  case heq: (F1 s) => [s' | e] /=.
  + by apply/xrutt_Ret/h.
  apply xrutt_CutL.
  by rewrite /errcutoff /is_error /subevent /= /resum /fromErr mid12.
Qed.

End IRESULT.

Section WITHASSERT.

Context {wc1 wc2: WithCatch} {wa1 wa2 : WithAssert}.
Notation isem_fun1 := (isem_fun (wsw:=wsw1) (dc:=dc1) (ep:=ep) (spp:=spp) (wc:=wc1) (wa:=wa1) (sip:=sip) (pT:=pT1) (scP:= scP1)).
Notation isem_fun2 := (isem_fun (wsw:=wsw2) (dc:=dc2) (ep:=ep) (spp:=spp) (wc:=wc2) (wa:=wa2)(sip:=sip) (pT:=pT2) (scP:= scP2)).

Section WEQUIV_CORE.

Context {E E0 : Type -> Type} {sem_F1 : sem_Fun1 E} {sem_F2 : sem_Fun2 E}
    {wE: with_Error E E0} {rE0 : EventRels E0}.

Context (p1 : prog1) (p2 : prog2) (ev1: extra_val_t1) (ev2 : extra_val_t2).

Notation sem_fun1 := (sem_fun (pT := pT1) (sem_Fun := sem_F1)).
Notation sem_fun2 := (sem_fun (pT := pT2) (sem_Fun := sem_F2)).

(* fully relational Hoare triples on itree semantics, based on
   wkequiv_io (i.e. basically on xrutt) *)

Definition wequiv_f_ii (P : relPreF) ii1 ii2 (fn1 fn2 : funname) (Q:relPostF) :=
  wkequiv_io
    (P fn1 fn2)
      (sem_fun1 p1 ev1 ii1 fn1)
      (sem_fun2 p2 ev2 ii2 fn2)
    (Q fn1 fn2).

Definition wequiv_f_body (P : relPreF) (fn1 fn2 : funname) (Q:relPostF) :=
  wkequiv_io
    (P fn1 fn2)
      (isem_fun_body (dc:=dc1) (wc:=wc1) (wa:=wa1) (sem_F:=sem_F1) p1 ev1 fn1)
      (isem_fun_body (dc:=dc2) (wc:=wc2) (wa:=wa2) (sem_F:=sem_F2) p2 ev2 fn2)
    (Q fn1 fn2).

Definition wequiv (pre:rel_c) (c1 c2 : cmd) (post : rel_c) :=
  wkequiv
    pre
     (isem_cmd_ (dc:=dc1) (wc:=wc1) (wa:=wa1) (sem_F:=sem_F1) p1 ev1 c1)
     (isem_cmd_ (dc:=dc2) (wc:=wc2) (wa:=wa2) (sem_F:=sem_F2) p2 ev2 c2)
    post.

Notation sem_pexpr1 := (sem_pexpr (wc:=wc1) (wa:=wa1)).
Notation sem_pexpr2 := (sem_pexpr (wc:=wc2) (wa:=wa2)).
Notation sem_pexprs1 := (sem_pexprs (wc:=wc1) (wa:=wa1)).
Notation sem_pexprs2 := (sem_pexprs (wc:=wc2) (wa:=wa2)).
Notation sem_cond1 := (sem_cond (wc:=wc1) (wa:=wa1)).
Notation sem_cond2 := (sem_cond (wc:=wc2) (wa:=wa2)).
Notation sem_bound1 := (sem_bound (wc:=wc1) (wa:=wa1)).
Notation sem_bound2 := (sem_bound (wc:=wc2) (wa:=wa2)).

Notation write_lval1 := (write_lval (wc:=wc1) (wa:=wa1)).
Notation write_lval2 := (write_lval (wc:=wc2) (wa:=wa2)).
Notation write_lvals1 := (write_lvals (wc:=wc1) (wa:=wa1)).
Notation write_lvals2 := (write_lvals (wc:=wc2) (wa:=wa2)).

Notation upd_estate1 := (upd_estate (wc:=wc1) (wa:=wa1)).
Notation upd_estate2 := (upd_estate (wc:=wc2) (wa:=wa2)).

Notation sem_pre1 := (sem_pre (wsw:=wsw1) (wc:=wc1) (wa:=wa1) (dc:=dc1) (pT:=pT1)).
Notation sem_pre2 := (sem_pre (wsw:=wsw2) (wc:=wc2) (wa:=wa2) (dc:=dc2) (pT:=pT2)).
Notation sem_post1 := (sem_post (wsw:=wsw1) (wc:=wc1) (wa:=wa1) (dc:=dc1) (pT:=pT1)).
Notation sem_post2 := (sem_post (wsw:=wsw2) (wc:=wc2) (wa:=wa2) (dc:=dc2) (pT:=pT2)).

Lemma wequiv_weaken P1 P2 Q1 Q2 c1 c2 :
  (forall s1 s2, P1 s1 s2 -> P2 s1 s2) ->
  (forall s1 s2, Q2 s1 s2 -> Q1 s1 s2) ->
  wequiv P2 c1 c2 Q2 ->
  wequiv P1 c1 c2 Q1.
Proof. move=> h1 h2; apply wkequiv_weaken => //; auto. Qed.

Lemma wequiv_cat (R P Q : rel_c) (c1 c1' c2 c2' : cmd) :
  wequiv P c1 c2 R ->
  wequiv R c1' c2' Q ->
  wequiv P (c1 ++ c1') (c2 ++ c2') Q.
Proof.
  move=> h h' s1 s2 hP; rewrite !isem_cmd_cat.
  apply xrutt_bind with R; first by apply h.
  apply h'.
Qed.

Lemma wequiv_nil P Q : (forall i1 i2, P i1 i2 -> Q i1 i2) -> wequiv P [::] [::] Q.
Proof. apply wkequiv_ret. Qed.

Lemma wequiv_cons (R P Q : rel_c) (i1 i2 : instr) (c1 c2 : cmd) :
  wequiv P [::i1] [::i2] R ->
  wequiv R c1 c2 Q ->
  wequiv P (i1 :: c1) (i2 :: c2) Q.
Proof. rewrite -(cat1s i1 c1) -(cat1s i2 c2); apply wequiv_cat. Qed.

Lemma wequiv_assgn_core (P Q : rel_c) ii1 x1 tg1 ty1 e1 ii2 x2 tg2 ty2 e2 :
  wrequiv P (sem_assgn (wc:=wc1) (wa:=wa1) p1 x1 tg1 ty1 e1) (sem_assgn (wc:=wc2) (wa:=wa2) p2 x2 tg2 ty2 e2) Q ->
  wequiv P [:: MkI ii1 (Cassgn x1 tg1 ty1 e1)] [:: MkI ii2 (Cassgn x2 tg2 ty2 e2)] Q.
Proof.
  move=> h; rewrite /wequiv /isem_cmd_ /=.
  apply wkequiv_bind with Q; last by apply wkequiv_ret.
  by apply wkequiv_iresult.
Qed.

Lemma wequiv_assgn (Rv Rtr: rel_v) (P Q : rel_c) ii1 x1 tg1 ty1 e1 ii2 x2 tg2 ty2 e2 :
  wrequiv P (fun s => sem_pexpr1 true (p_globs p1) s e1)
           (fun s => sem_pexpr2 true (p_globs p2) s e2) Rv ->
  (forall s1 s2, P s1 s2 -> wrequiv Rv (truncate_val ty1) (truncate_val ty2) Rtr) ->
  (forall v1 v2, Rtr v1 v2 ->
    wrequiv P (write_lval1 true (p_globs p1) x1 v1) (write_lval2 true (p_globs p2) x2 v2) Q) ->
  wequiv P [:: MkI ii1 (Cassgn x1 tg1 ty1 e1)] [:: MkI ii2 (Cassgn x2 tg2 ty2 e2)] Q.
Proof.
  move=> he htr hwr; apply wequiv_assgn_core; rewrite /sem_assgn.
  apply: (wrequiv_read he) => v1 v2 hv.
  apply wrequiv_bind_eval with Rtr.
  + by move=> s1 s2 /htr; apply wrequiv_weaken => // > [-> ->].
  by apply hwr.
Qed.

Lemma wequiv_assgn_eq (P Q : rel_c) ii1 x1 tg1 ty e1 ii2 x2 tg2 e2 :
  wrequiv P (fun s => sem_pexpr1 true (p_globs p1) s e1)
            (fun s => sem_pexpr2 true (p_globs p2) s e2) eq ->
  (forall v, wrequiv P (write_lval1 true (p_globs p1) x1 v) (write_lval2 true (p_globs p2) x2 v) Q) ->
  wequiv P [:: MkI ii1 (Cassgn x1 tg1 ty e1)] [:: MkI ii2 (Cassgn x2 tg2 ty e2)] Q.
Proof.
  move=> he hx; apply wequiv_assgn with eq eq => //.
  + by move=> *; apply wrequiv_eq.
  by move=> > <-; apply hx.
Qed.

Lemma wequiv_assgn_uincl (P Q : rel_c) ii1 x1 tg1 ty e1 ii2 x2 tg2 e2 :
  wrequiv P (fun s => sem_pexpr1 true (p_globs p1) s e1)
            (fun s => sem_pexpr2 true (p_globs p2) s e2) value_uincl ->
  (forall v1 v2, value_uincl v1 v2 ->
    wrequiv P (write_lval1 true (p_globs p1) x1 v1) (write_lval2 true (p_globs p2) x2 v2) Q) ->
  wequiv P [:: MkI ii1 (Cassgn x1 tg1 ty e1)] [:: MkI ii2 (Cassgn x2 tg2 ty e2)] Q.
Proof. move=> he; apply wequiv_assgn with value_uincl => // *; apply wrequiv_truncate_val. Qed.

Lemma wequiv_assgn_esem (P Q : rel_c) ii1 x1 tg1 ty e1 c2 :
  wrequiv P (sem_assgn (wc:=wc1) (wa:=wa1) p1 x1 tg1 ty e1)
            (esem (wc:=wc2) (wa:=wa2) p2 ev2 c2) Q ->
  wequiv P [:: MkI ii1 (Cassgn x1 tg1 ty e1)] c2 Q.
Proof.
  move=> h s t hP /=.
  case heq: sem_assgn => [s' | e] /=.
  + rewrite bind_ret_r.
    have [t' /esem_i_bodyP -> hQ /=] := h s t s' hP heq.
    by apply xrutt.xrutt_Ret.
  rewrite bind_ret_r; apply xrutt_CutL => //.
  by rewrite /errcutoff /is_error /subevent /resum /fromErr mid12.
Qed.

Lemma wequiv_opn (Rve Rvo : rel_vs) P Q ii1 xs1 at1 o1 es1 ii2 xs2 at2 o2 es2 :
  wrequiv P (fun s => sem_pexprs1 true (p_globs p1) s es1)
            (fun s => sem_pexprs2 true (p_globs p2) s es2) Rve ->
  (forall s1 s2, P s1 s2 -> wrequiv Rve (exec_sopn (wc:=wc1) o1) (exec_sopn (wc:=wc2) o2) Rvo) ->
  (forall vs1 vs2,
    Rvo vs1 vs2 -> wrequiv P (fun s1 => write_lvals1 true (p_globs p1) s1 xs1 vs1)
                             (fun s2 => write_lvals2 true (p_globs p2) s2 xs2 vs2) Q) ->
  wequiv P [:: MkI ii1 (Copn xs1 at1 o1 es1)] [:: MkI ii2 (Copn xs2 at2 o2 es2)] Q.
Proof.
  move=> he ho hwr; rewrite /wequiv /isem_cmd_ /=.
  apply wkequiv_bind with Q; last by apply wkequiv_ret.
  apply wkequiv_iresult; rewrite /sem_sopn.
  eapply wrequiv_read; last by apply hwr.
  eapply wrequiv_read; first apply he.
  move=> t1 t2 ht; eapply wrequiv_eval.
  by move=> s1 s2 /ho; apply wrequiv_weaken => // > [-> ->].
Qed.

Lemma wequiv_opn_esem (P Q : rel_c) ii1 xs1 tg1 o1 es1 c2 :
  wrequiv P (fun s => sem_sopn (wc:=wc1) (wa:=wa1) (p_globs p1) o1 s xs1 es1)
            (esem (wc:=wc2) (wa:=wa2) p2 ev2 c2) Q ->
  wequiv P [:: MkI ii1 (Copn xs1 tg1 o1 es1)] c2 Q.
Proof.
  move=> h s t hP /=.
  case heq: sem_sopn => [s' | e] /=.
  + rewrite bind_ret_r.
    have [t' /esem_i_bodyP -> hQ /=] := h s t s' hP heq.
    by apply xrutt.xrutt_Ret.
  rewrite bind_ret_r; apply xrutt_CutL => //.
  by rewrite /errcutoff /is_error /subevent /resum /fromErr mid12.
Qed.

Lemma wequiv_syscall Rv Ro P Q ii1 xs1 sc1 es1 ii2 xs2 sc2 es2 :
  wrequiv P (fun s => sem_pexprs1 true (p_globs p1) s es1)
            (fun s => sem_pexprs2 true (p_globs p2) s es2) Rv ->
  (forall s1 s2, P s1 s2 ->
     wrequiv Rv (fun vs1 => fexec_syscall (scP:=scP1) sc1 (mk_fstate vs1 s1))
                (fun vs2 => fexec_syscall sc2 (mk_fstate vs2 s2)) Ro)->
  (forall fs1 fs2,
    Ro fs1 fs2 ->
    wrequiv P (upd_estate1 true (p_globs p1) xs1 fs1)
              (upd_estate2 true (p_globs p2) xs2 fs2) Q) ->
  wequiv P [:: MkI ii1 (Csyscall xs1 sc1 es1)] [:: MkI ii2 (Csyscall xs2 sc2 es2)] Q.
Proof.
  move=> he ho hwr; rewrite /equiv /isem_cmd_ /=.
  apply wkequiv_bind with Q; last by apply wkequiv_ret.
  apply wkequiv_iresult.
  apply (wrequiv_read he).
  move=> vs1 vs2 hvs; eapply wrequiv_read; last by apply hwr.
  by move=> s1 s2 fr1 hP; apply (ho s1 s2 hP).
Qed.

Lemma wequiv_syscall_eq P Q ii1 xs1 sc1 es1 ii2 sc2 xs2 es2 :
  (forall s1 s2, P s1 s2 -> escs s1 = escs s2 /\ emem s1 = emem s2) ->
  wrequiv P (fun s => sem_pexprs1 true (p_globs p1) s es1)
            (fun s => sem_pexprs2 true (p_globs p2) s es2) eq ->
  wrequiv eq (fexec_syscall (scP:=scP1) sc1)
             (fexec_syscall (scP:=scP2) sc2) eq ->
  (forall fs,
    wrequiv P (upd_estate1 true (p_globs p1) xs1 fs)
              (upd_estate2 true (p_globs p2) xs2 fs) Q) ->
  wequiv P [:: MkI ii1 (Csyscall xs1 sc1 es1)] [:: MkI ii2 (Csyscall xs2 sc2 es2)] Q.
Proof.
  move=> heq he hsc hx.
  apply wequiv_syscall with eq eq => //.
  + by rewrite /mk_fstate => s1 s2 /heq [<- <-] ?? fs1 <-; apply hsc.
  move=> > <-; apply hx.
Qed.

Lemma wequiv_syscall_esem (P Q : rel_c) ii1 xs1 sc1 es1 c2 :
  wrequiv P (sem_syscall (wc:=wc1) (wa:=wa1) p1 xs1 sc1 es1)
            (esem (wc:=wc2) (wa:=wa2) p2 ev2 c2) Q ->
  wequiv P [:: MkI ii1 (Csyscall xs1 sc1 es1)] c2 Q.
Proof.
  move=> h s t hP /=.
  case heq: sem_syscall => [s' | e] /=.
  + rewrite bind_ret_r.
    have [t' /esem_i_bodyP -> hQ /=] := h s t s' hP heq.
    by apply xrutt.xrutt_Ret.
  rewrite bind_ret_r; apply xrutt_CutL => //.
  by rewrite /errcutoff /is_error /subevent /resum /fromErr mid12.
Qed.

Lemma wequiv_assert_esem (P Q : rel_c) ii1 a1 c2 :
  wrequiv P (fun (s:estate1) => Let _ := sem_assert (wsw:=wsw1) (wc:=wc1) (wa:=wa1) (p_globs p1) s a1 in ok s)
            (esem (wc:=wc2) (wa:=wa2) p2 ev2 c2) Q ->
  wequiv P [:: MkI ii1 (Cassert a1)] c2 Q.
Proof.
  move=> h s t hP /=; rewrite /isem_assert.
  case heq: sem_assert => [s' | e] /=.
  + rewrite bind_ret_r.
    have [|t' /esem_i_bodyP -> hQ /=] := h s t s hP.
    + by rewrite heq.
    by rewrite bind_ret_l; apply xrutt.xrutt_Ret.
  rewrite bind_ret_r bind_vis; apply xrutt_CutL => //.
  by rewrite /errcutoff /is_error /subevent /resum /fromErr mid12.
Qed.

Lemma wequiv_assert (P Q : rel_c) ii1 a1 ii2 a2 :
  (assert_allowed (WithAssert:=wa1) ->
   assert_allowed (WithAssert:=wa2) /\
   forall s1 s2,
     P s1 s2 ->
     sem_cond1 (p_globs p1) a1.2 s1 = ok true ->
     sem_cond2 (p_globs p2) a2.2 s2 = ok true /\ Q s1 s2) ->
  wequiv P [:: MkI ii1 (Cassert a1)] [:: MkI ii2 (Cassert a2)] Q.
Proof.
  move=> hcond; apply wequiv_assert_esem => s t s' hP /=.
  rewrite /sem_assert; t_xrbindP.
  move=> /hcond [-> {}hcond] b1 hsem1 hb1 _ <-; rewrite hb1 in hsem1 => {hb1 b1}.
  by have [-> hQ /=] := hcond _ _ hP hsem1; exists t.
Qed.

Lemma sem_cond_uincl P e1 e2 :
  wrequiv P (fun (s:estate1) => sem_pexpr1 true (p_globs p1) s e1)
            (fun (s:estate2) => sem_pexpr2 true (p_globs p2) s e2) value_uincl ->
  wrequiv P (sem_cond1 (p_globs p1) e1) (sem_cond2 (p_globs p2) e2) eq.
Proof.
  move=> he; apply: wrequiv_bind wrequiv_to_bool; apply he.
Qed.

Lemma wequiv_assert_uincl (P Q : rel_c) ii1 a1 ii2 a2 :
  (assert_allowed (WithAssert:=wa1) ->
     assert_allowed (WithAssert:=wa2) /\
     wrequiv P (fun s => sem_pexpr1 true (p_globs p1) s a1.2)
               (fun s => sem_pexpr2 true (p_globs p2) s a2.2) value_uincl) ->
  (assert_allowed (WithAssert:=wa1) ->
   assert_allowed (WithAssert:=wa2) ->
   forall s1 s2,
     P s1 s2 ->
     sem_pexpr1 true (p_globs p1) s1 a1.2 = ok (Vbool true) ->
     sem_pexpr2 true (p_globs p2) s2 a2.2 = ok (Vbool true) ->
     Q s1 s2) ->
  wequiv P [:: MkI ii1 (Cassert a1)] [:: MkI ii2 (Cassert a2)] Q.
Proof.
  move=> hcond hweak; apply wequiv_assert => haa1.
  have [haa2 h] := hcond haa1; split => //.
  move=> s1 s2 hP hsem1.
  have [o2 hsem2 ?]:= sem_cond_uincl h hP hsem1; subst o2; split => //.
  by apply hweak => //;[ move: hsem1 | move: hsem2]; rewrite /sem_cond; t_xrbindP => ? -> /to_boolI ->.
Qed.

Lemma wequiv_assert_eq (P Q : rel_c) ii1 a1 ii2 a2 :
  (assert_allowed (WithAssert:=wa1) ->
     assert_allowed (WithAssert:=wa2) /\
     wrequiv P (fun s => sem_pexpr1 true (p_globs p1) s a1.2)
               (fun s => sem_pexpr2 true (p_globs p2) s a2.2) eq) ->
  (assert_allowed (WithAssert:=wa1) ->
   assert_allowed (WithAssert:=wa2) ->
   forall s1 s2,
     P s1 s2 ->
     sem_pexpr1 true (p_globs p1) s1 a1.2 = ok (Vbool true) ->
     sem_pexpr2 true (p_globs p2) s2 a2.2 = ok (Vbool true) ->
     Q s1 s2) ->
  wequiv P [:: MkI ii1 (Cassert a1)] [:: MkI ii2 (Cassert a2)] Q.
Proof.
  move=> hcond; apply wequiv_assert_uincl => /hcond [? he]; split => //.
  by apply: wrequiv_weaken he => // > ->.
Qed.

Section ST_REL.

Context (D:Type).
Context (R : D -> vm1_t -> vm2_t -> Prop).

Definition st_rel (d : D) (s : estate1) (t : estate2) :=
  [/\ escs s = escs t, emem s = emem t & R d (evm s) (evm t)%vm].

Lemma st_rel_weaken d d' :
  (forall vm1 vm2, R d vm1 vm2 -> R d' vm1 vm2) ->
  forall s1 s2, st_rel d s1 s2 -> st_rel d' s1 s2.
Proof. by move => h s1 s2 [???]; split => //; apply h. Qed.

Context (Rv : values -> values -> Prop).

Definition fs_rel (fs1 fs2 : fstate) :=
  [/\ fscs fs1 = fscs fs2, fmem fs1 = fmem fs2 & Rv (fvals fs1) (fvals fs2)].

Lemma upd_st_rel wdb1 wdb2 gd1 gd2 d d' xs1 xs2 :
  (forall vs1 vs2, Rv vs1 vs2 ->
     wrequiv
       (st_rel d)
       (λ s1, write_lvals wdb1 gd1 s1 xs1 vs1) (λ s2, write_lvals wdb2 gd2 s2 xs2 vs2)
       (st_rel d')) ->
  (forall fs1 fs2, fs_rel fs1 fs2 ->
     wrequiv
       (st_rel d)
       (upd_estate wdb1 gd1 xs1 fs1) (upd_estate wdb2 gd2 xs2 fs2)
       (st_rel d')).
Proof. by move=> h fs1 fs2 [h1 h2 /h{}h]; rewrite /upd_estate h1 h2 => s t s' [?? hvm]; apply h. Qed.

Lemma upd_st_eq wdb1 wdb2 gd1 gd2 d d' xs1 xs2 :
  (forall vs,
     wrequiv
       (st_rel d)
       (λ s1, write_lvals wdb1 gd1 s1 xs1 vs) (λ s2, write_lvals wdb2 gd2 s2 xs2 vs)
       (st_rel d')) ->
  (forall fs,
     wrequiv
       (st_rel d)
       (upd_estate wdb1 gd1 xs1 fs) (upd_estate wdb2 gd2 xs2 fs)
       (st_rel d')).
Proof. by move=> h fs; rewrite /upd_estate => s t s' [?? hvm]; apply h. Qed.

End ST_REL.

Definition fs_uincl := fs_rel (List.Forall2 value_uincl).

Lemma fs_uinclR fs : fs_uincl fs fs.
Proof. split=> //; exact: values_uincl_refl. Qed.

Lemma wequiv_syscall_uincl P Q ii1 xs1 sc1 es1 ii2 sc2 xs2 es2 :
  (forall s1 s2, P s1 s2 -> escs s1 = escs s2 /\ emem s1 = emem s2) ->
  wrequiv P (fun s => sem_pexprs1 true (p_globs p1) s es1)
           (fun s => sem_pexprs2 true (p_globs p2) s es2) (Forall2 value_uincl) ->
  wrequiv fs_uincl (fexec_syscall (scP:=scP1) sc1)
                  (fexec_syscall (scP:=scP2) sc2) fs_uincl ->
  (forall fs1 fs2,
    fs_uincl fs1 fs2 ->
    wrequiv P (upd_estate1 true (p_globs p1) xs1 fs1)
              (upd_estate2 true (p_globs p2) xs2 fs2) Q) ->
  wequiv P [:: MkI ii1 (Csyscall xs1 sc1 es1)] [:: MkI ii2 (Csyscall xs2 sc2 es2)] Q.
Proof.
  move=> heq he hsc.
  apply wequiv_syscall with (Forall2 value_uincl) => //.
  by rewrite /mk_fstate => s1 s2 /heq [<- <-] vs1 vs2 fr1 huincl;apply hsc.
Qed.

Lemma wequiv_if_full P Q ii1 e1 c1 c1' ii2 e2 c2 c2' :
  wrequiv P (sem_cond1 (p_globs p1) e1) (sem_cond2 (p_globs p2) e2) eq ->
  (forall b, wequiv
        (fun s1 s2 => [/\ P s1 s2, sem_cond1 (p_globs p1) e1 s1 = ok b & sem_cond2 (p_globs p2) e2 s2 = ok b])
        (if b then c1 else c1')
        (if b then c2 else c2') Q) ->
  wequiv P [:: MkI ii1 (Cif e1 c1 c1')] [:: MkI ii2 (Cif e2 c2 c2')] Q.
Proof.
  move=> he hc; rewrite /wequiv /isem_cmd_ /=.
  apply wkequiv_bind with Q; last by apply wkequiv_ret.
  apply wkequiv_eq_pred => s1 s2 hP.
  eapply wkequiv_read with (fun b1 b2 =>
     [/\ b1 = b2, sem_cond1 (p_globs p1) e1 s1 = ok b1 & sem_cond2 (p_globs p2) e2 s2 = ok b2]).
  + apply wkequiv_iresult.
    apply wrequiv_id; apply: wrequiv_weaken he => //.
    by move=> > [-> ->].
  by move=> b b2 [???]; subst b2; apply: wkequiv_weaken (hc b) => // _ _ [-> ->].
Qed.

Lemma wequiv_if P Q ii1 e1 c1 c1' ii2 e2 c2 c2' :
  wrequiv P (sem_cond1 (p_globs p1) e1) (sem_cond2 (p_globs p2) e2) eq ->
  (forall b, wequiv P (if b then c1 else c1') (if b then c2 else c2') Q) ->
  wequiv P [:: MkI ii1 (Cif e1 c1 c1')] [:: MkI ii2 (Cif e2 c2 c2')] Q.
Proof.
  move=> hcond hc hc'; apply wequiv_if_full => // b.
  by apply: wequiv_weaken (hc b) => // > [].
Qed.

(* Usefull for lowering *)
Lemma wequiv_if_esem P P' Q ii1 e1 c1 c1' c ii2 e2 c2 c2':
  (forall s t v, P s t -> sem_pexpr1 true (p_globs p1) s e1 = ok v ->
     exists t', [/\ esem p2 ev2 c t = ok t', P' s t' & sem_pexpr2 true (p_globs p2) t' e2 = ok v]) ->
  (forall b, wequiv P' (if b then c1 else c1') (if b then c2 else c2') Q) ->
  wequiv P [::MkI ii1 (Cif e1 c1 c1')] (c ++ [::MkI ii2 (Cif e2 c2 c2')]) Q.
Proof.
  move=> he hc s t hP /=.
  rewrite isem_cmd_cat !bind_ret_r/=.
  rewrite /isem_cond.
  case heq: sem_cond => [b | e] /=; last first.
  + rewrite bind_vis; apply xrutt_CutL.
    by rewrite /errcutoff /is_error /subevent /= /resum /fromErr mid12.
  move: heq; rewrite /sem_cond; t_xrbindP => v hse1 hto.
  have [t' [hsemc hP' hse2]] := he s t v hP hse1.
  rewrite bind_ret_l (esem_i_bodyP hsemc) /= bind_ret_l hse2 /= hto /= bind_ret_l bind_ret_r.
  by case: (b) (hc b _ _ hP').
Qed.

Lemma wequiv_if_uincl P Q ii1 e1 c1 c1' ii2 e2 c2 c2' :
  wrequiv P (fun (s:estate1) => sem_pexpr1 true (p_globs p1) s e1)
            (fun (s:estate2) => sem_pexpr2 true (p_globs p2) s e2) value_uincl ->
  (forall b, wequiv P (if b then c1 else c1') (if b then c2 else c2') Q) ->
  wequiv P [:: MkI ii1 (Cif e1 c1 c1')] [:: MkI ii2 (Cif e2 c2 c2')] Q.
Proof. move=> /sem_cond_uincl; apply wequiv_if. Qed.

Lemma wequiv_if_eq P Q ii1 e1 c1 c1' ii2 e2 c2 c2' :
  wrequiv P (fun (s:estate1) => sem_pexpr1 true (p_globs p1) s e1)
           (fun (s:estate2) => sem_pexpr2 true (p_globs p2) s e2) eq ->
  (forall b, wequiv P (if b then c1 else c1') (if b then c2 else c2') Q) ->
  wequiv P [:: MkI ii1 (Cif e1 c1 c1')] [:: MkI ii2 (Cif e2 c2 c2')] Q.
Proof. by move=> he; apply wequiv_if_uincl; apply: wrequiv_weaken he => // > <-. Qed.

Lemma wequiv_if_rcond P Q ii1 e1 c1 c1' c2 b :
  (forall s1 s2 v, P s1 s2 -> sem_cond1 (p_globs p1) e1 s1 = ok v -> v = b) ->
  wequiv P (if b then c1 else c1') c2 Q ->
  wequiv P [:: MkI ii1 (Cif e1 c1 c1')] c2 Q.
Proof.
  move=> he1 hc2 s1 s2 hP /=.
  rewrite /isem_cond.
  case heq: (sem_cond1 (p_globs p1) e1 s1) => [b' | err] /=.
  + rewrite bind_ret_r bind_ret_l.
    rewrite (he1 _ _ _ hP heq); apply: hc2 hP.
  rewrite bind_bind bind_vis.
  apply xrutt_CutL => //.
  by rewrite /errcutoff /is_error /subevent /resum /fromErr mid12.
Qed.

Lemma wequiv_for P0 P Pi ii1 i1 d lo1 hi1 c1 ii2 i2 lo2 hi2 c2 :
  (forall s1 s2, P0 s1 s2 -> P s1 s2) ->
  wrequiv P0 (sem_bound1 (p_globs p1) lo1 hi1) (sem_bound2 (p_globs p2) lo2 hi2) eq ->
  (forall i : Z, wrequiv P (write_var true i1 (Vint i)) (write_var true i2 (Vint i)) Pi) ->
  wequiv Pi c1 c2 P ->
  wequiv P0 [:: MkI ii1 (Cfor i1 (d, lo1, hi1) c1)] [:: MkI ii2 (Cfor i2 (d, lo2, hi2) c2)] P.
Proof.
  move=> hP0P hbound hwi hc; rewrite /wequiv /isem_cmd_ /=.
  apply wkequiv_bind with P; last by apply wkequiv_ret.
  apply wkequiv_read with eq.
  + by apply wkequiv_iresult.
  move=> bounds _ <-.
  apply wkequiv_weaken with P P => //.
  elim: wrange => /= [| j js hrec].
  + by apply wkequiv_ret.
  apply wkequiv_bind with Pi.
  + by apply wkequiv_iresult.
  by apply: wkequiv_bind hrec.
Qed.

Lemma wrequiv_sem_bound (P : rel_c) lo1 hi1 lo2 hi2 :
  wrequiv P (fun s => sem_pexprs1 true (p_globs p1) s [::lo1; hi1])
            (fun s => sem_pexprs2 true (p_globs p2) s [::lo2; hi2]) (List.Forall2 value_uincl) ->
  wrequiv P (sem_bound1 (p_globs p1) lo1 hi1) (sem_bound2 (p_globs p2) lo2 hi2) eq.
Proof.
  move=> hbound; rewrite /sem_bound.
  move=> s1 s2 lh1 hP; t_xrbindP => ilo1 vlo1 hlo1 hvlo1 ihi1 vhi1 hhi1 hvhi1 <-.
  have [] /= := hbound s1 s2 [::vlo1; vhi1] hP.
  + by rewrite hlo1 /= hhi1.
  t_xrbindP => _ vlo2 -> _ hvhi2 -> <- <-.
  move=> /List_Forall2_inv [hulo /List_Forall2_inv [huhi _]] /=.
  have [_ -> <-] := wrequiv_to_int hulo hvlo1.
  have [_ -> <- /=] := wrequiv_to_int huhi hvhi1.
  eexists; eauto.
Qed.

Lemma wequiv_for_uincl P0 P Pi ii1 i1 d lo1 hi1 c1 ii2 i2 lo2 hi2 c2 :
  (forall s1 s2, P0 s1 s2 -> P s1 s2) ->
  wrequiv P0 (fun s => sem_pexprs1 true (p_globs p1) s [::lo1; hi1])
            (fun s => sem_pexprs2 true (p_globs p2) s [::lo2; hi2]) (List.Forall2 value_uincl) ->
  (forall i : Z, wrequiv P (write_var true i1 (Vint i)) (write_var true i2 (Vint i)) Pi) ->
  wequiv Pi c1 c2 P ->
  wequiv P0 [:: MkI ii1 (Cfor i1 (d, lo1, hi1) c1)] [:: MkI ii2 (Cfor i2 (d, lo2, hi2) c2)] P.
Proof. by move=> hP0P hbound; apply/wequiv_for/wrequiv_sem_bound. Qed.

Lemma wequiv_for_eq P0 P Pi ii1 i1 d lo1 hi1 c1 ii2 i2 lo2 hi2 c2 :
  (forall s1 s2, P0 s1 s2 -> P s1 s2) ->
  wrequiv P0 (fun s => sem_pexprs1 true (p_globs p1) s [::lo1; hi1])
            (fun s => sem_pexprs2 true (p_globs p2) s [::lo2; hi2]) eq ->
  (forall i : Z, wrequiv P (write_var true i1 (Vint i)) (write_var true i2 (Vint i)) Pi) ->
  wequiv Pi c1 c2 P ->
  wequiv P0 [:: MkI ii1 (Cfor i1 (d, lo1, hi1) c1)] [:: MkI ii2 (Cfor i2 (d, lo2, hi2) c2)] P.
Proof.
  move=> hP0P hbound; apply wequiv_for_uincl => //.
  by apply: wrequiv_weaken hbound => // > <-; apply List_Forall2_refl.
Qed.

Lemma wequiv_while_full I I' ii1 al1 e1 inf1 c1 c1' ii2 al2 e2 inf2 c2 c2' :
  wequiv I c1 c2 I' ->
  wrequiv I' (sem_cond1 (p_globs p1) e1) (sem_cond2 (p_globs p2) e2) eq ->
  wequiv (fun s1 s2 =>
    [/\ I' s1 s2, sem_cond1 (p_globs p1) e1 s1 = ok true & sem_cond2 (p_globs p2) e2 s2 = ok true]) c1' c2' I ->
  wequiv I [:: MkI ii1 (Cwhile al1 c1 e1 inf1 c1')] [:: MkI ii2 (Cwhile al2 c2 e2 inf2 c2')]
     (fun s1 s2 => [/\ I' s1 s2, sem_cond1 (p_globs p1) e1 s1 = ok false & sem_cond2 (p_globs p2) e2 s2 = ok false]).
Proof.
  move=> hc hcond hc'; rewrite /wequiv /isem_cmd_ /=.
  set Q := (Q in wkequiv _ _ _ Q).
  apply wkequiv_bind with Q; last by apply wkequiv_ret.
  apply wkequiv_iter with (I := I) => //; rewrite /isem_while_loop.
  apply (wkequiv_bind hc).
  apply wkequiv_eq_pred => s1 s2 hP.
  eapply wkequiv_read with (fun b1 b2 =>
     [/\ b1 = b2, sem_cond1 (p_globs p1) e1 s1 = ok b1 & sem_cond2 (p_globs p2) e2 s2 = ok b2]).
  + apply wkequiv_iresult.
    apply wrequiv_id; apply: wrequiv_weaken hcond => //.
    by move=> > [-> ->].
  move=> b b2 [<-]; case: b => ??.
  + apply wkequiv_bind with I.
    + by apply: wkequiv_weaken hc' => // ?? [-> ->].
    by apply wkequiv_ret => *; constructor.
  by apply wkequiv_ret => ?? [-> ->]; constructor.
Qed.

Lemma wequiv_while I I' ii1 al1 e1 inf1 c1 c1' ii2 al2 e2 inf2 c2 c2' :
  wrequiv I' (sem_cond1 (p_globs p1) e1) (sem_cond2 (p_globs p2) e2) eq ->
  wequiv I c1 c2 I' ->
  wequiv I' c1' c2' I ->
  wequiv I [:: MkI ii1 (Cwhile al1 c1 e1 inf1 c1')] [:: MkI ii2 (Cwhile al2 c2 e2 inf2 c2')] I'.
Proof.
  move=> hcond hc hc'.
  apply wequiv_weaken with (P2 := I)
    (Q2 := fun s1 s2 =>
      [/\ I' s1 s2, sem_cond1 (p_globs p1) e1 s1 = ok false & sem_cond2 (p_globs p2) e2 s2 = ok false]) => //.
  + by move=> > [].
  apply wequiv_while_full => //.
  by apply: wequiv_weaken hc' => // > [].
Qed.

(* Usefull for lowering *)
Lemma wequiv_while_esem I I1 I' ii1 al1 e1 inf1 c1 c1' c ii2 al2 e2 inf2 c2 c2':
  wequiv I c1 c2 I1 ->
  (forall s t v, I1 s t -> sem_pexpr1 true (p_globs p1) s e1 = ok v ->
     exists t', [/\ esem p2 ev2 c t = ok t', I' s t' & sem_pexpr2 true (p_globs p2) t' e2 = ok v]) ->
  wequiv I' c1' c2' I ->
  wequiv I [::MkI ii1 (Cwhile al1 c1 e1 inf1 c1')] [::MkI ii2 (Cwhile al2 (c2 ++ c) e2 inf2 c2')] I'.
Proof.
  move=> hc hcond hc'; rewrite /wequiv /isem_cmd_ /=.
  apply wkequiv_bind with I'; last by apply wkequiv_ret.
  apply wkequiv_iter with (I := I) => //; rewrite /isem_while_loop.
  rewrite /isem_while_round.
  apply wkequiv_eutt_r with (F2 :=
    (λ s : estate2,
      s0' <- isem_foldr isem_i_body p2 ev2 c2 s;;
      s0 <- isem_foldr isem_i_body p2 ev2 c s0';;
      b <- isem_cond p2 e2 s0;; (if b then s1 <- isem_foldr isem_i_body p2 ev2 c2' s0;; ret (inl s1) else ret (inr s0)))).
  + move=> > _. rewrite -/(isem_cmd_ p2 ev2 (c2 ++ c)) isem_cmd_cat.
    rewrite Monad.bind_bind; reflexivity.
  apply (wkequiv_bind hc).
  move=> s t hI1 /=.
  rewrite /isem_cond.
  case heq: sem_cond => [b | e] /=; last first.
  + rewrite bind_vis; apply xrutt_CutL.
    by rewrite /errcutoff /is_error /subevent /= /resum /fromErr mid12.
  move: heq; rewrite /sem_cond; t_xrbindP => v hse1 hto.
  have [t' [hsemc hI' hse2]] := hcond s t v hI1 hse1.
  rewrite bind_ret_l -/(isem_cmd_ p2 ev2 c) (esem_i_bodyP hsemc) /=.
  rewrite bind_ret_l hse2 /= hto /= bind_ret_l.
  case: (b).
  + apply (wkequiv_bind hc') => //.
    by apply wkequiv_ret => *; constructor.
  by apply xrutt_Ret; constructor.
Qed.

Lemma wequiv_while_uincl I I' ii1 al1 e1 inf1 c1 c1' ii2 al2 e2 inf2 c2 c2' :
  wrequiv I' (fun (s:estate1) => sem_pexpr1 true (p_globs p1) s e1)
             (fun (s:estate2) => sem_pexpr2 true (p_globs p2) s e2) value_uincl ->
  wequiv I c1 c2 I' ->
  wequiv I' c1' c2' I ->
  wequiv I [:: MkI ii1 (Cwhile al1 c1 e1 inf1 c1')] [:: MkI ii2 (Cwhile al2 c2 e2 inf2 c2')] I'.
Proof. move=> /sem_cond_uincl; apply wequiv_while. Qed.

Lemma wequiv_while_eq I I' ii1 al1 e1 inf1 c1 c1' ii2 al2 e2 inf2 c2 c2' :
  wrequiv I' (fun (s:estate1) => sem_pexpr1 true (p_globs p1) s e1)
             (fun (s:estate2) => sem_pexpr2 true (p_globs p2) s e2) eq ->
  wequiv I c1 c2 I' ->
  wequiv I' c1' c2' I ->
  wequiv I [:: MkI ii1 (Cwhile al1 c1 e1 inf1 c1')] [:: MkI ii2 (Cwhile al2 c2 e2 inf2 c2')] I'.
Proof. by move=> he; apply wequiv_while_uincl; apply: wrequiv_weaken he => // > <-. Qed.

Lemma wequiv_while_unroll P Q ii1 al e1 inf1 c1 c1' c2 :
  let: w := [:: MkI ii1 (Cwhile al c1 e1 inf1 c1') ] in
  wequiv P (c1 ++ [:: MkI ii1 (Cif e1 (c1' ++ w) [::])]) c2 Q ->
  wequiv P w c2 Q.
Proof.
  by move=> /= h s1 s2 hP; rewrite isem_cmd_while; apply h.
Qed.

Lemma wequiv_call_core_wa (Pf : relPreF) (Qf : relPostF) Rv P Q ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  wrequiv P (fun s => sem_pexprs1 (~~ (@direct_call dc1)) (p_globs p1) s es1)
            (fun s => sem_pexprs2 (~~ (@direct_call dc2)) (p_globs p2) s es2) Rv ->
  (forall s1 s2 vs1 vs2, P s1 s2 -> Rv vs1 vs2 ->
     sem_pre1 p1 fn1 (mk_fstate vs1 s1) = ok tt ->
     sem_pre2 p2 fn2 (mk_fstate vs2 s2) = ok tt) ->
  (forall s1 s2 vs1 vs2,
     P s1 s2 -> Rv vs1 vs2 -> Pf fn1 fn2 (mk_fstate vs1 s1) (mk_fstate vs2 s2)) ->
  wequiv_f_ii Pf ii1 ii2 fn1 fn2 Qf ->
  (forall fs1 fs2 fr1 fr2,
     Pf fn1 fn2 fs1 fs2 -> Qf fn1 fn2 fs1 fs2 fr1 fr2 ->
    sem_post1 p1 fn1 fs1.(fvals) fr1 = ok () ->
    sem_post2 p2 fn2 fs2.(fvals) fr2 = ok ()) ->
  (forall fs1 fs2 fr1 fr2,
    Pf fn1 fn2 fs1 fs2 -> Qf fn1 fn2 fs1 fs2 fr1 fr2 ->
    wrequiv
      (fun s1 s2 => [/\ P s1 s2, escs s1 = fscs fs1, escs s2 = fscs fs2
                      , emem s1 = fmem fs1, emem s2 = fmem fs2
                      & Rv (fvals fs1) (fvals fs2)])
        (upd_estate1 (~~ (@direct_call dc1)) (p_globs p1) xs1 fr1)
        (upd_estate2 (~~ (@direct_call dc2)) (p_globs p2) xs2 fr2)
      Q) ->
  wequiv P [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] Q.
Proof.
  move=> hes hpre hPPf hCall hpost hPQf; rewrite /wequiv /isem_cmd_ /=.
  apply wkequiv_bind with Q; last by apply wkequiv_ret.
  apply wkequiv_read with Rv.
  + by apply wkequiv_iresult.
  move=> vs1 vs2 hvs.
  apply wkequiv_eq_pred => s1 s2 hP.
  set fs1 := mk_fstate vs1 s1; set fs2 := mk_fstate vs2 s2.
  apply wkequiv_read with (fun u1 u2 => sem_pre1 p1 fn1 fs1 = ok tt /\ sem_pre2 p2 fn2 fs2 = ok tt).
  + by apply wkequiv_iresult => _ _ [] [-> ->] he; have ?:= hpre _ _ _ _ hP hvs he; exists tt.
  move=> _ _ [hpre1 hpre2].
  apply wkequiv_read with (Qf fn1 fn2 fs1 fs2).
  + by move=> _ _ [-> ->]; apply/hCall/hPPf.
  move=> fr1 fr2 hQf.
  apply wkequiv_read with (fun u1 u2 => sem_post1 p1 fn1 fs1.(fvals) fr1 = ok tt /\ sem_post2 p2 fn2 fs2.(fvals) fr2 = ok tt).
  + apply wkequiv_iresult => _ _ [] _ hpost1.
    have hpost2 := hpost _ _ _ _ (hPPf _ _ _ _ hP hvs) hQf hpost1.
    by exists tt.
  move=> _ _ _; apply wkequiv_iresult.
  eapply wrequiv_weaken; last apply (hPQf fs1 fs2); eauto.
  by move=> ?? [-> ->].
Qed.

Lemma wequiv_call_wa (Pf : relPreF) (Qf : relPostF) Rv P Q ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  wrequiv P (fun s => sem_pexprs1 (~~ (@direct_call dc1)) (p_globs p1) s es1)
            (fun s => sem_pexprs2 (~~ (@direct_call dc2)) (p_globs p2) s es2) Rv ->
  (forall s1 s2 vs1 vs2, P s1 s2 -> Rv vs1 vs2 ->
     sem_pre1 p1 fn1 (mk_fstate vs1 s1) = ok tt ->
     sem_pre2 p2 fn2 (mk_fstate vs2 s2) = ok tt) ->
  (forall s1 s2 vs1 vs2,
     P s1 s2 -> Rv vs1 vs2 -> Pf fn1 fn2 (mk_fstate vs1 s1) (mk_fstate vs2 s2)) ->
  (forall fs1 fs2 fr1 fr2,
     Pf fn1 fn2 fs1 fs2 -> Qf fn1 fn2 fs1 fs2 fr1 fr2 ->
    sem_post1 p1 fn1 fs1.(fvals) fr1 = ok () ->
    sem_post2 p2 fn2 fs2.(fvals) fr2 = ok ()) ->
  wequiv_f_ii Pf ii1 ii2 fn1 fn2 Qf ->
  (forall fs1 fs2 fr1 fr2,
    Pf fn1 fn2 fs1 fs2 -> Qf fn1 fn2 fs1 fs2 fr1 fr2 ->
    wrequiv P (upd_estate1 (~~ (@direct_call dc1)) (p_globs p1) xs1 fr1)
              (upd_estate2 (~~ (@direct_call dc2)) (p_globs p2) xs2 fr2) Q) ->
  wequiv P [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] Q.
Proof.
  move=> hes hpre hPPf hpost hCall hPQf.
  apply wequiv_call_core_wa with Pf Qf Rv => //.
  move=> > hPf hQf; apply wrequiv_weaken with P Q => //.
  + by move=> > [].
  apply: hPQf hPf hQf.
Qed.

Lemma wequiv_call_eq_wa P Q ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  wrequiv P (fun s => sem_pexprs1 (~~ (@direct_call dc1)) (p_globs p1) s es1)
            (fun s => sem_pexprs2 (~~ (@direct_call dc2)) (p_globs p2) s es2) eq ->
  (forall s1 s2 vs, P s1 s2 ->
     sem_pre1 p1 fn1 (mk_fstate vs s1) = ok tt ->
     sem_pre2 p2 fn2 (mk_fstate vs s2) = ok tt) ->
  (forall s1 s2 vs,
     P s1 s2 -> rpreF (eS:=eq_spec) fn1 fn2 (mk_fstate vs s1) (mk_fstate vs s2)) ->
  wequiv_f_ii (rpreF (eS:=eq_spec)) ii1 ii2 fn1 fn2 (rpostF (eS:=eq_spec)) ->
  (forall vs fr,
    sem_post1 p1 fn1 vs fr = ok () ->
    sem_post2 p2 fn1 vs fr = ok ()) ->
  (forall fs,
    wrequiv P (upd_estate1 (~~ (@direct_call dc1)) (p_globs p1) xs1 fs)
              (upd_estate2 (~~ (@direct_call dc2)) (p_globs p2) xs2 fs) Q) ->
  wequiv P [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] Q.
Proof.
  move=> he hpre hfs hfn hpost hupd.
  apply wequiv_call_wa with (Pf:=rpreF (eS:=eq_spec)) (Qf:= rpostF (eS:=eq_spec)) (Rv:=eq) => //.
  + by move=> s1 s2 vs1 vs2 hP ->; apply hpre.
  + by move=> s1 s2 vs1 _ hP <-; apply hfs.
  + by move=> fs1 fs2 fr1 fr2 [<- <-] <-; apply hpost.
  move=> fs1 fs2 ft1 ft2 [<- <-] /= <-; apply hupd.
Qed.

Definition wequiv_fun_body_hyp_wa (RPreF:relPreF) fn1 fn2 (RPostF:relPostF) :=
  forall fs1 fs2,
  RPreF fn1 fn2 fs1 fs2 ->
  forall fd1, get_fundef (p_funcs p1) fn1 = Some fd1 ->
  exists2 fd2, get_fundef (p_funcs p2) fn2 = Some fd2 &
    sem_pre1 p1 fn1 fs1 = ok tt ->
    sem_pre2 p2 fn2 fs2 = ok tt /\
    forall s11, initialize_funcall (dc:=dc1) p1 ev1 fd1 fs1 = ok s11 ->
    exists2 s21,
      initialize_funcall (dc:=dc2) p2 ev2 fd2 fs2 = ok s21 &
      exists (P Q : rel_c),
       [/\ P s11 s21
          , wequiv P fd1.(f_body) fd2.(f_body) Q
          , wrequiv Q (finalize_funcall (dc:=dc1) fd1) (finalize_funcall (dc:=dc2) fd2) (RPostF fn1 fn2 fs1 fs2)
          & (forall fr1 fr2, RPostF fn1 fn2 fs1 fs2 fr1 fr2 ->
                             sem_post1 p1 fn1 fs1.(fvals) fr1 = ok () -> sem_post2 p2 fn2 fs2.(fvals) fr2 = ok ())
        ].

Lemma wequiv_fun_body_wa RPreF fn1 fn2 RPostF :
  wequiv_fun_body_hyp_wa RPreF fn1 fn2 RPostF ->
  wequiv_f_body RPreF fn1 fn2 RPostF.
Proof.
  move=> hf; rewrite /wequiv_f_body /isem_fun_body.
  apply wkequiv_ioP => fs1 fs2 hPf.
  have {}hf:= hf _ _ hPf.
  apply wkequiv_read with (fun fd1 fd2 => get_fundef (p_funcs p1) fn1 = Some fd1 /\
                                          get_fundef (p_funcs p2) fn2 = Some fd2).
  + rewrite /kget_fundef => ??.
    case: get_fundef hf => /= [fd1 |].
    + by move=> /(_ _ erefl) [fd2 ] -> _ _; apply xrutt_Ret.
    move=> _ _; apply xrutt_CutL.
    by rewrite /errcutoff /is_error /subevent /resum /fromErr mid12.
  move=> fd1 fd2 [+ hfd2].
  move=> {}/hf [fd2']; rewrite hfd2 => -[?];  subst fd2' => hf.
  apply wkequiv_read with (fun _ _ => sem_pre1 p1 fn1 fs1 = ok ()).
  + by apply wkequiv_iresult => ?? [] [-> ->] h; have [-> ?] := hf h; eauto.
  move=> _ _ hpre1; have [hpre2 {}hf] := hf hpre1.
  move=> _ _ [-> ->].
  apply xrutt_bind with (fun s1 s2 =>
     [/\ initialize_funcall (dc:=dc1) p1 ev1 fd1 fs1 = ok s1 &
         initialize_funcall (dc:=dc2) p2 ev2 fd2 fs2 = ok s2]).
  + apply (wkequiv_iresult (P:= eq_init fs1 fs2)) => //.
    by move=> ?? s1 [-> ->] /[dup] hinit1 /hf [s2]  hinit2 _; exists s2.
  move=> s1 s2 [hs1 hs2].
  have [s2' {hf}] := hf _ hs1.
  rewrite hs2 => -[?] [P] [Q] [hP hbody hfin hpost]; subst s2'.
  apply wkequiv_bind with Q P => // s1' s2' hQ.
  apply xrutt_bind with (RPostF fn1 fn2 fs1 fs2).
  + by apply: (wkequiv_iresult _ _ hfin).
  move=> fr1 fr2 hPostF.
  apply xrutt_bind with (fun _ _ => true).
  + by apply rutt_iresult => -[] /(hpost _ _ hPostF) ->; exists tt.
  by move=> _ _ _; apply xrutt_Ret.
Qed.

(* One sided rules *)

Lemma wequiv_assign_right P Q ii x tg ty e :
  (forall s t, P s t -> exists2 t', sem_assgn p2 x tg ty e t = ok t' & Q s t') ->
  wequiv P [::] [::MkI ii (Cassgn x tg ty e)] Q.
Proof.
  move=> h; rewrite /wequiv /=.
  by apply/wkequiv_bind_ret_right/wkequiv_iresult_right.
Qed.

Lemma wequiv_assign_left P Q ii x tg ty e :
  (forall s s' t, P s t -> sem_assgn (wc:=wc1) (wa:=wa1) p1 x tg ty e s = ok s' ->  Q s' t) ->
  wequiv P [::MkI ii (Cassgn x tg ty e)] [::] Q.
Proof.
  move=> h; rewrite /wequiv /=.
  by apply/wkequiv_bind_ret_left/wkequiv_iresult_left.
Qed.

Lemma wequiv_assert_left P Q ii a :
  (assert_allowed (WithAssert:=wa1) ->
   forall s t, P s t -> sem_pexpr1 true (p_globs p1) s a.2 = ok (Vbool true) -> Q s t) ->
  wequiv P [::MkI ii (Cassert a)] [::] Q.
Proof.
  move=> h; rewrite /wequiv /=.
  apply/wkequiv_bind_ret_left.
  move=> s1 s2 hP; rewrite /isem_assert.
  case heq: sem_assert => [ []| e] /=.
  + rewrite bind_ret_l.
    move: heq; rewrite /sem_assert /sem_cond; t_xrbindP => hwa [] // v he /to_boolI ? _ _; subst v.
    by apply/xrutt_Ret/h.
  rewrite /Exception.throw bind_vis.
  apply xrutt_CutL => //.
  by rewrite /errcutoff /is_error /subevent /resum /fromErr mid12.
Qed.

Lemma wequiv_asserts_left P Q ii (a_s : list assertion) :
  assert_allowed (WithAssert:=wa1) ->
  (forall s t, P s t -> (forall a, List.In a a_s -> sem_pexpr1 true (p_globs p1) s a.2 = ok (Vbool true)) -> Q s t) ->
  wequiv P [seq MkI ii (Cassert a) | a <- a_s] [::] Q.
Proof.
  rewrite -{1}(app_nil_l a_s) => hwa1 hPQ.
  apply wequiv_weaken with
    (fun s t => P s t /\
       (forall a, List.In a (@nil assertion) -> sem_pexpr1 true (p_globs p1) s a.2 = ok (Vbool true)))
    Q => //.
  elim: a_s (@nil assertion) hPQ => [ | a0 a_s hrec] /= a_s0 hPQ.
  + by apply wequiv_nil => s t [hP ha_s0]; apply hPQ => //; rewrite app_nil_r.
  rewrite -(cat0s [::]) -cat1s.
  apply wequiv_cat with
    (fun s t => P s t /\
       (forall a, List.In a (a0::a_s0) -> sem_pexpr1 true (p_globs p1) s a.2 = ok (Vbool true))).
  + by apply wequiv_assert_left => _ s t [hP ha_s0] ha0; split => //= a [<- // | hin]; apply ha_s0.
  apply hrec => s t hP h; apply hPQ => // a /in_app_iff /= [hin|[<-|hin]]; apply h; rewrite in_app_iff /=; auto.
Qed.

Section REL.

Context {D:Type}.
Context (R : D -> estate1 -> estate2 -> Prop).

Class Checker_e :=
 { check_es    : D -> pexprs -> pexprs -> D -> Prop
 ; check_lvals : D -> lvals -> lvals -> D -> Prop
 ; check_esP_rel :
   forall d es1 es2 d', check_es d es1 es2 d' -> forall s1 s2, R d s1 s2 -> R d' s1 s2
 }.

Context {ce : Checker_e}.

Definition wdb_ok (wdb1 wdb2 : bool) :=
  wdb1 /\ wdb2 \/ wdb1 = ~~@direct_call dc1 /\ wdb2 = ~~@direct_call dc2.

Lemma wdb_ok_true : wdb_ok true true.
Proof. by left. Qed.

Lemma wdb_ok_direct : wdb_ok (~~@direct_call dc1) (~~@direct_call dc2).
Proof. by right. Qed.
#[local]Hint Resolve wdb_ok_true wdb_ok_direct : core.

Class Checker_uincl :=
 { ucheck_esP   :
   forall wdb1 wdb2 d es1 es2 d',
     wdb_ok wdb1 wdb2 ->
     check_es d es1 es2 d' ->
     wrequiv (R d) ((sem_pexprs1 wdb1 (p_globs p1))^~ es1) ((sem_pexprs2 wdb2 (p_globs p2))^~ es2)
       (List.Forall2 value_uincl)
 ; ucheck_lvalsP :
   forall wdb1 wdb2 d xs1 xs2 d',
     wdb_ok wdb1 wdb2 ->
     check_lvals d xs1 xs2 d' ->
     forall vs1 vs2, List.Forall2 value_uincl vs1 vs2 ->
     wrequiv (R d) (λ s1 : estate, write_lvals1 wdb1 (p_globs p1) s1 xs1 vs1)
                          (λ s2 : estate, write_lvals2 wdb2 (p_globs p2) s2 xs2 vs2) ( R d')
 }.

Class Checker_eq :=
 { echeck_esP   :
   forall (wdb1 wdb2 : bool) d es1 es2 d',
     wdb_ok wdb1 wdb2 ->
     check_es d es1 es2 d' ->
     wrequiv (R d) ((sem_pexprs1 wdb1 (p_globs p1))^~ es1) ((sem_pexprs2 wdb2 (p_globs p2))^~ es2) eq
 ; echeck_lvalsP :
   forall (wdb1 wdb2 : bool) d xs1 xs2 d',
     wdb_ok wdb1 wdb2 ->
     check_lvals d xs1 xs2 d' ->
     forall vs,
     wrequiv (R d) (λ s1 : estate, write_lvals1 wdb1 (p_globs p1) s1 xs1 vs)
                          (λ s2 : estate, write_lvals2 wdb2 (p_globs p2) s2 xs2 vs) (R d')
 }.

Section UINCL.

Context {cu:Checker_uincl}.

Lemma ucheck_eP d e1 e2 d' :
  check_es d [::e1] [::e2] d' ->
  wrequiv (R d) ((sem_pexpr1 true (p_globs p1))^~ e1) ((sem_pexpr2 true (p_globs p2))^~ e2) value_uincl.
Proof.
  move=> /ucheck_esP -/(_ _ _ wdb_ok_true) h s t v hst he.
  have [|vs]:= h s t [::v] hst.
  + by rewrite /= he.
  by rewrite /=; t_xrbindP => v' -> <- /List_Forall2_inv [??]; exists v'.
Qed.

Lemma ucheck_lvalP d x1 x2 d' :
  check_lvals d [::x1] [::x2] d' ->
  forall v1 v2, value_uincl v1 v2 ->
   wrequiv (R d) (λ s1 : estate, write_lval1 true (p_globs p1) x1 v1 s1)
                        (λ s2 : estate, write_lval2 true (p_globs p2) x2 v2 s2) (R d').
Proof.
  move=> /ucheck_lvalsP  -/(_ _ _ wdb_ok_true) h v1 v2 hu s t s' hst hx.
  have [||/=]:= h [::v1] [::v2] _ s t s' hst.
  + by apply List.Forall2_cons => //; apply List.Forall2_nil.
  + by rewrite /= hx.
  t_xrbindP => t' _ -> -> ?; eexists; eauto.
Qed.

Lemma wequiv_assgn_rel_uincl d de d' ii1 x1 tg1 ty e1 ii2 x2 tg2 e2 :
  check_es d [::e1] [::e2] de ->
  check_lvals de [::x1] [::x2] d' ->
  wequiv (R d) [:: MkI ii1 (Cassgn x1 tg1 ty e1)] [:: MkI ii2 (Cassgn x2 tg2 ty e2)] (R d').
Proof.
  move=> hes hxs.
  apply wequiv_assgn_uincl.
  + by apply: ucheck_eP hes.
  move=> v1 v2 hu; apply wrequiv_weaken with (R de) (R d') => //.
  + by apply: check_esP_rel hes.
  apply: ucheck_lvalP hxs v1 v2 hu.
Qed.

Lemma wequiv_assert_rel_uincl d de ii1 a1 ii2 a2 :
  (assert_allowed (WithAssert:=wa1) → assert_allowed (WithAssert:=wa2)) ->
  check_es d [::a1.2] [::a2.2] de ->
  wequiv (R d) [:: MkI ii1 (Cassert a1)] [:: MkI ii2 (Cassert a2)] (R de).
Proof.
  move=> hassert hes; apply wequiv_assert_uincl.
  + move=> /hassert ?; split => //; apply: ucheck_eP hes.
  by move=> _ _ + + + _ _; apply: check_esP_rel hes.
Qed.

Lemma wequiv_if_rel_uincl_R d de d1 d2 d' ii e c1 c2 ii' e' c1' c2' :
  check_es d [::e] [::e'] de ->
  (forall s1 s2, R d1 s1 s2 -> R d' s1 s2) ->
  (forall s1 s2, R d2 s1 s2 -> R d' s1 s2) ->
  wequiv (R de) c1 c1' (R d1) ->
  wequiv (R de) c2 c2' (R d2) ->
  wequiv (R d) [:: MkI ii (Cif e c1 c2)] [:: MkI ii' (Cif e' c1' c2')] (R d').
Proof.
  move=> hes hd1 hd2 hc1 hc2.
  apply wequiv_if_uincl.
  + by apply: ucheck_eP hes.
  move=> b; apply wequiv_weaken with  (R de) (R d') => //.
  + by apply: check_esP_rel hes.
  by case: b; [apply: wequiv_weaken hc1 | apply: wequiv_weaken hc2] => //; apply st_rel_weaken.
Qed.

Lemma wequiv_for_rel_uincl_R d0 d dhi di ii i dir lo hi c ii' i' lo' hi' c':
  check_es d0 [::lo; hi] [::lo'; hi'] dhi ->
  (∀ s1 s2, R dhi s1 s2 → R d s1 s2) ->
  check_lvals d [::Lvar i] [::Lvar i'] di ->
  wequiv (R di) c c' (R d) ->
  wequiv (R d0) [:: MkI ii (Cfor i (dir, lo, hi) c)] [:: MkI ii' (Cfor i' (dir, lo', hi') c')] (R d).
Proof.
  move=> hes hdhi hx hc.
  apply wequiv_for_uincl with (R di) => //.
  + by move=> s1 s2 /(check_esP_rel hes) /hdhi.
  + by apply: ucheck_esP hes.
  by move=> j; have /(_ j j (value_uincl_refl j)) := ucheck_lvalP hx.
Qed.

Lemma wequiv_while_rel_uincl d d' de ii1 al1 c1 e1 inf1 c1' ii2 al2 c2 e2 inf2 c2' :
  check_es d' [::e1] [::e2] de ->
  wequiv (R d) c1 c2 (R d') →
  wequiv (R de) c1' c2' (R d) →
  wequiv (R d) [:: MkI ii1 (Cwhile al1 c1 e1 inf1 c1')] [:: MkI ii2 (Cwhile al2 c2 e2 inf2 c2')] (R de).
Proof.
  move=> he hc hc'.
  apply wequiv_weaken with (R d) (R d') => //.
  + by apply: check_esP_rel he.
  apply wequiv_while_uincl => //.
  + by apply: ucheck_eP he.
  apply wequiv_weaken with (R de) (R d) => //.
  by apply: check_esP_rel he.
Qed.

Lemma wequiv_syscall_rel_uincl_core_R d de de' d' ii1 xs1 sc1 es1 ii2 xs2 sc2 es2 :
  (∀ d s1 s2, R d s1 s2 → escs s1 = escs s2 ∧ emem s1 = emem s2) →
  (forall scs mem s1 s2, R de s1 s2 ->
     R de' (with_scs (with_mem s1 mem) scs) (with_scs (with_mem s2 mem) scs)) →
  check_es d es1 es2 de →
  check_lvals de' xs1 xs2 d' →
  wrequiv fs_uincl (fexec_syscall (scP:=scP1) sc1) (fexec_syscall (scP:=scP2) sc2) fs_uincl →
  wequiv (R d) [:: MkI ii1 (Csyscall xs1 sc1 es1)] [:: MkI ii2 (Csyscall xs2 sc2 es2)] (R d').
Proof.
  move=> hsm hwith hes hxs hsc.
  apply wequiv_syscall_uincl.
  + by apply hsm.
  + by apply: ucheck_esP hes.
  + by apply hsc.
  move=> fs1 fs2 [hscs hmem hu]; rewrite /upd_estate.
  move=> s1 s2 s1' hR.
  apply ucheck_lvalsP with de' => //.
  rewrite hscs hmem; apply hwith.
  apply: check_esP_rel hes s1 s2 hR.
Qed.

Lemma wequiv_call_rel_uincl_R_wa d de de' d' ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  (∀ d s1 s2, R d s1 s2 → escs s1 = escs s2 ∧ emem s1 = emem s2) →
  (forall scs mem s1 s2, R de s1 s2 ->
     R de' (with_scs (with_mem s1 mem) scs) (with_scs (with_mem s2 mem) scs)) →
  check_es d es1 es2 de →
  check_lvals de' xs1 xs2 d' →
  (∀ s1 s2 vs1 vs2, R d s1 s2 → List.Forall2 value_uincl vs1 vs2 →
     sem_pre1 p1 fn1 (mk_fstate vs1 s1) = ok () → sem_pre2 p2 fn2 (mk_fstate vs2 s2) = ok ()) →
  wequiv_f_ii (fun _ _ => fs_uincl) ii1 ii2 fn1 fn2 (fun _ _ _ _ => fs_uincl) →
  (∀ vs1 vs2 fr1 fr2,
    List.Forall2 value_uincl vs1 vs2 → fs_uincl fr1 fr2 →
    sem_post1 p1 fn1 vs1 fr1 = ok () → sem_post2 p2 fn2 vs2 fr2 = ok ()) →
  wequiv (R d) [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] (R d').
Proof.
  move=> hsm hwith hes hxs hpre hf hpost.
  apply wequiv_call_wa with (fun _ _ => fs_uincl) (fun _ _ _ _ => fs_uincl) (List.Forall2 value_uincl).
  + by apply: ucheck_esP hes.
  + by apply hpre.
  + by rewrite /mk_fstate; move=> > /hsm [-> ->] ?.
  + by move=> > [_ _]; apply hpost.
  + by apply hf.
  move=> fs1 fs2 fr1 fr2 _ [hscs hmem hu]; rewrite /upd_estate.
  move=> s1 s2 s1' hR.
  apply ucheck_lvalsP with de' => //.
  rewrite hscs hmem; apply hwith.
  apply: check_esP_rel hes s1 s2 hR.
Qed.

End UINCL.

Section EQ.

Context {cu:Checker_eq}.

Lemma echeck_eP d e1 e2 d' :
  check_es d [::e1] [::e2] d' ->
  wrequiv (R d) ((sem_pexpr1 true (p_globs p1))^~ e1) ((sem_pexpr2 true (p_globs p2))^~ e2) eq.
Proof.
  move=> /echeck_esP -/(_ _ _ wdb_ok_true) h s t v hst he.
  have [|vs]:= h s t [::v] hst.
  + by rewrite /= he.
  by rewrite /=; t_xrbindP => v' -> <- [?]; exists v'.
Qed.

Lemma echeck_lvalP d x1 x2 d' :
  check_lvals d [::x1] [::x2] d' ->
  forall v,
  wrequiv (R d) (λ s1 : estate, write_lval1 true (p_globs p1) x1 v s1)
                        (λ s2 : estate, write_lval2 true (p_globs p2) x2 v s2) (R d').
Proof.
  move=> /echeck_lvalsP  -/(_ _ _ wdb_ok_true) h v s t s' hst hx.
  have [|/=]:= h [::v] s t s' hst.
  + by rewrite /= hx.
  t_xrbindP => t' _ -> -> ?; eexists; eauto.
Qed.

Lemma wequiv_assgn_rel_eq d de d' ii1 x1 tg1 ty e1 ii2 x2 tg2 e2 :
  check_es d [::e1] [::e2] de ->
  check_lvals de [::x1] [::x2] d' ->
  wequiv (R d) [:: MkI ii1 (Cassgn x1 tg1 ty e1)] [:: MkI ii2 (Cassgn x2 tg2 ty e2)] (R d').
Proof.
  move=> hes hxs.
  apply wequiv_assgn_eq.
  + by apply: echeck_eP hes.
  move=> v; apply wrequiv_weaken with (R de) (R d') => //.
  + by apply: check_esP_rel hes.
  apply: echeck_lvalP hxs v.
Qed.

Lemma wequiv_assert_rel_eq d de ii1 a1 ii2 a2 :
  (assert_allowed (WithAssert:=wa1) → assert_allowed (WithAssert:=wa2)) ->
  check_es d [::a1.2] [::a2.2] de ->
  wequiv (R d) [:: MkI ii1 (Cassert a1)] [:: MkI ii2 (Cassert a2)] (R de).
Proof.
  move=> hassert hes.
  apply wequiv_assert_eq.
  + by move=> /hassert ?; split => //; apply: echeck_eP hes.
  by move=> _ _ + + + _ _; apply: check_esP_rel hes.
Qed.

Lemma wequiv_if_rel_eq_R d de d1 d2 d' ii e c1 c2 ii' e' c1' c2' :
  check_es d [::e] [::e'] de ->
  (forall s1 s2, R d1 s1 s2 -> R d' s1 s2) ->
  (forall s1 s2, R d2 s1 s2 -> R d' s1 s2) ->
  wequiv (R de) c1 c1' (R d1) ->
  wequiv (R de) c2 c2' (R d2) ->
  wequiv (R d) [:: MkI ii (Cif e c1 c2)] [:: MkI ii' (Cif e' c1' c2')] (R d').
Proof.
  move=> hes hd1 hd2 hc1 hc2.
  apply wequiv_if_eq.
  + by apply: echeck_eP hes.
  move=> b; apply wequiv_weaken with  (R de) (R d') => //.
  + by apply: check_esP_rel hes.
  by case: b; [apply: wequiv_weaken hc1 | apply: wequiv_weaken hc2] => //; apply st_rel_weaken.
Qed.

Lemma wequiv_for_rel_eq_R d0 d dhi di ii i dir lo hi c ii' i' lo' hi' c':
  check_es d0 [::lo; hi] [::lo'; hi'] dhi ->
  (∀ s1 s2, R dhi s1 s2 → R d s1 s2) ->
  check_lvals d [::Lvar i] [::Lvar i'] di ->
  wequiv (R di) c c' (R d) ->
  wequiv (R d0) [:: MkI ii (Cfor i (dir, lo, hi) c)] [:: MkI ii' (Cfor i' (dir, lo', hi') c')] (R d).
Proof.
  move=> hes hdhi hx hc.
  apply wequiv_for_eq with (R di) => //.
  + by move=> s1 s2 /(check_esP_rel hes) /hdhi.
  + by apply: echeck_esP hes.
  by move=> j; have /(_ j) := echeck_lvalP hx.
Qed.

Lemma wequiv_while_rel_eq d d' de ii1 al1 c1 e1 inf1 c1' ii2 al2 c2 e2 inf2 c2' :
  check_es d' [::e1] [::e2] de ->
  wequiv (R d) c1 c2 (R d') →
  wequiv (R de) c1' c2' (R d) →
  wequiv (R d) [:: MkI ii1 (Cwhile al1 c1 e1 inf1 c1')] [:: MkI ii2 (Cwhile al2 c2 e2 inf2 c2')] (R de).
Proof.
  move=> he hc hc'.
  apply wequiv_weaken with (R d) (R d') => //.
  + by apply: check_esP_rel he.
  apply wequiv_while_eq => //.
  + by apply: echeck_eP he.
  apply wequiv_weaken with (R de) (R d) => //.
  by apply: check_esP_rel he.
Qed.

Lemma wequiv_syscall_rel_eq_core_R d de de' d' ii1 xs1 sc1 es1 ii2 xs2 sc2 es2 :
  (∀ d s1 s2, R d s1 s2 → escs s1 = escs s2 ∧ emem s1 = emem s2) →
  (forall scs mem s1 s2, R de s1 s2 ->
     R de' (with_scs (with_mem s1 mem) scs) (with_scs (with_mem s2 mem) scs)) →
  check_es d es1 es2 de →
  check_lvals de' xs1 xs2 d' →
  wrequiv eq (fexec_syscall (scP:=scP1) sc1) (fexec_syscall (scP:=scP2) sc2) eq →
  wequiv (R d) [:: MkI ii1 (Csyscall xs1 sc1 es1)] [:: MkI ii2 (Csyscall xs2 sc2 es2)] (R d').
Proof.
  move=> hsm hwith hes hxs hsc.
  apply wequiv_syscall_eq.
  + by apply hsm.
  + by apply: echeck_esP hes.
  + by apply hsc.
  move=> fs; rewrite /upd_estate.
  move=> s1 s2 s1' hR.
  apply echeck_lvalsP with de' => //.
  apply hwith.
  apply: check_esP_rel hes s1 s2 hR.
Qed.

Lemma wequiv_call_rel_eq_R_wa d de de' d' ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  (∀ d s1 s2, R d s1 s2 → escs s1 = escs s2 ∧ emem s1 = emem s2) →
  (forall scs mem s1 s2, R de s1 s2 ->
     R de' (with_scs (with_mem s1 mem) scs) (with_scs (with_mem s2 mem) scs)) →
  check_es d es1 es2 de →
  check_lvals de' xs1 xs2 d' →
  (∀ s1 s2 vs, R d s1 s2 →
     sem_pre1 p1 fn1 (mk_fstate vs s1) = ok () → sem_pre2 p2 fn2 (mk_fstate vs s2) = ok ()) →
  wequiv_f_ii (fun _ _ => eq) ii1 ii2 fn1 fn2 (fun _ _ _ _ => eq) →
  (∀ vs fr,
    sem_post1 p1 fn1 vs fr = ok () → sem_post2 p2 fn2 vs fr = ok ()) →
  wequiv (R d) [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] (R d').
Proof.
  move=> hsm hwith hes hxs hpre hf hpost.
  apply wequiv_call_wa with (fun _ _ => eq) (fun _ _ _ _ => eq) eq.
  + by apply: echeck_esP hes.
  + by move=> > hR <-; apply hpre.
  + by rewrite /mk_fstate; move=> > /hsm [-> ->] ->.
  + by move=> > <- <-; apply hpost.
  + by apply hf.
  move=> > h1 <-; rewrite /upd_estate.
  move=> s1 s2 s1' hR.
  apply echeck_lvalsP with de' => //.
  apply hwith.
  apply: check_esP_rel hes s1 s2 hR.
Qed.

End EQ.

End REL.

Section ST_REL.

Context {D:Type}.
Context (R : D -> vm1_t -> vm2_t -> Prop).

Context {ce : Checker_e (st_rel R)}.

Section UINCL.

Context {cu:Checker_uincl (R:=st_rel R)}.

Lemma wequiv_if_rel_uincl d de d1 d2 d' ii e c1 c2 ii' e' c1' c2' :
  check_es d [::e] [::e'] de ->
  (forall vm1 vm2, R d1 vm1 vm2 -> R d' vm1 vm2) ->
  (forall vm1 vm2, R d2 vm1 vm2 -> R d' vm1 vm2) ->
  wequiv (st_rel R de) c1 c1' (st_rel R d1) ->
  wequiv (st_rel R de) c2 c2' (st_rel R d2) ->
  wequiv (st_rel R d) [:: MkI ii (Cif e c1 c2)] [:: MkI ii' (Cif e' c1' c2')] (st_rel R d').
Proof.
  move=> hes hd1 hd2.
  by apply wequiv_if_rel_uincl_R with ce => //; apply st_rel_weaken.
Qed.

Lemma wequiv_for_rel_uincl d0 d dhi di ii i dir lo hi c ii' i' lo' hi' c':
  check_es d0 [::lo; hi] [::lo'; hi'] dhi ->
  (∀ s1 s2, R dhi s1 s2 → R d s1 s2) ->
  check_lvals d [::Lvar i] [::Lvar i'] di ->
  wequiv (st_rel R di) c c' (st_rel R d) ->
  wequiv (st_rel R d0) [:: MkI ii (Cfor i (dir, lo, hi) c)] [:: MkI ii' (Cfor i' (dir, lo', hi') c')] (st_rel R d).
Proof.
  move=> hes hdhi hx hc.
  apply wequiv_for_rel_uincl_R with ce dhi di => //.
  by apply st_rel_weaken.
Qed.

Lemma wequiv_syscall_rel_uincl_core d de d' ii1 xs1 sc1 es1 ii2 xs2 sc2 es2 :
  check_es d es1 es2 de →
  check_lvals de xs1 xs2 d' →
  wrequiv fs_uincl (fexec_syscall (scP:=scP1) sc1) (fexec_syscall (scP:=scP2) sc2) fs_uincl →
  wequiv (st_rel R d) [:: MkI ii1 (Csyscall xs1 sc1 es1)] [:: MkI ii2 (Csyscall xs2 sc2 es2)] (st_rel R d').
Proof.
  apply wequiv_syscall_rel_uincl_core_R => //.
  + by move=> > [-> ->].
  by move=> scs mem s1 s2 [???].
Qed.

Lemma wequiv_call_rel_uincl_wa d de d' ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  check_es d es1 es2 de →
  check_lvals de xs1 xs2 d' →
  (∀ s1 s2 vs1 vs2,
     st_rel R d s1 s2 → Forall2 value_uincl vs1 vs2 →
     sem_pre1 p1 fn1 (mk_fstate vs1 s1) = ok () → sem_pre2 p2 fn2 (mk_fstate vs2 s2) = ok ()) →
  wequiv_f_ii (fun _ _ => fs_uincl) ii1 ii2 fn1 fn2 (fun _ _ _ _ => fs_uincl) →
  (∀ vs1 vs2 fr1 fr2,
     List.Forall2 value_uincl vs1 vs2 → fs_uincl fr1 fr2 →
     sem_post1 p1 fn1 vs1 fr1 = ok () → sem_post2 p2 fn2 vs2 fr2 = ok ()) →
  wequiv (st_rel R d) [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] (st_rel R d').
Proof.
  apply wequiv_call_rel_uincl_R_wa => //.
  + by move=> > [-> ->].
  by move=> scs mem s1 s2 [???].
Qed.

End UINCL.

Section EQ.

Context {cu:Checker_eq (R:=st_rel R)}.

Lemma wequiv_if_rel_eq d de d1 d2 d' ii e c1 c2 ii' e' c1' c2' :
  check_es d [::e] [::e'] de ->
  (forall vm1 vm2, R d1 vm1 vm2 -> R d' vm1 vm2) ->
  (forall vm1 vm2, R d2 vm1 vm2 -> R d' vm1 vm2) ->
  wequiv (st_rel R de) c1 c1' (st_rel R d1) ->
  wequiv (st_rel R de) c2 c2' (st_rel R d2) ->
  wequiv (st_rel R d) [:: MkI ii (Cif e c1 c2)] [:: MkI ii' (Cif e' c1' c2')] (st_rel R d').
Proof.
  move=> hes hd1 hd2.
  by apply wequiv_if_rel_eq_R with ce => //; apply st_rel_weaken.
Qed.

Lemma wequiv_for_rel_eq d0 d dhi di ii i dir lo hi c ii' i' lo' hi' c':
  check_es d0 [::lo; hi] [::lo'; hi'] dhi ->
  (∀ s1 s2, R dhi s1 s2 → R d s1 s2) ->
  check_lvals d [::Lvar i] [::Lvar i'] di ->
  wequiv (st_rel R di) c c' (st_rel R d) ->
  wequiv (st_rel R d0) [:: MkI ii (Cfor i (dir, lo, hi) c)] [:: MkI ii' (Cfor i' (dir, lo', hi') c')] (st_rel R d).
Proof.
  move=> hes hdhi hx hc.
  apply wequiv_for_rel_eq_R with ce dhi di => //.
  by apply st_rel_weaken.
Qed.

Lemma wequiv_syscall_rel_eq_core d de d' ii1 xs1 sc1 es1 ii2 xs2 sc2 es2 :
  check_es d es1 es2 de →
  check_lvals de xs1 xs2 d' →
  wrequiv eq (fexec_syscall (scP:=scP1) sc1) (fexec_syscall (scP:=scP2) sc2) eq →
  wequiv (st_rel R d) [:: MkI ii1 (Csyscall xs1 sc1 es1)] [:: MkI ii2 (Csyscall xs2 sc2 es2)] (st_rel R d').
Proof.
  apply wequiv_syscall_rel_eq_core_R => //.
  + by move=> > [-> ->].
  by move=> scs mem s1 s2 [???].
Qed.

Lemma wequiv_call_rel_eq_wa d de d' ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  check_es d es1 es2 de →
  check_lvals de xs1 xs2 d' →
  (∀ s1 s2 vs,
     st_rel R d s1 s2 →
     sem_pre1 p1 fn1 (mk_fstate vs s1) = ok () → sem_pre2 p2 fn2 (mk_fstate vs s2) = ok ()) →
  wequiv_f_ii (fun _ _ => eq) ii1 ii2 fn1 fn2 (fun _ _ _ _ => eq) →
  (∀ vs fr,
     sem_post1 p1 fn1 vs fr = ok () → sem_post2 p2 fn2 vs fr = ok ()) →
  wequiv (st_rel R d) [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] (st_rel R d').
Proof.
  apply wequiv_call_rel_eq_R_wa => //.
  + by move=> > [-> ->].
  by move=> scs mem s1 s2 [???].
Qed.

End EQ.

End ST_REL.

Notation _vm_eq := (fun (_:unit) => vm_eq (wsw1:=wsw1) (wsw2:=wsw2)).
Definition st_eq := st_rel _vm_eq.

Definition check_es_st_eq (_:unit) (es1 es2 : pexprs) (_:unit) := es1 = es2.
Definition check_lvals_st_eq (_:unit) (xs1 xs2 : lvals) (_:unit) := xs1 = xs2.

Lemma check_esP_R_st_eq (d : unit) (es1 es2 : pexprs) (d' : unit) :
  check_es_st_eq d es1 es2 d' → ∀ s1 s2, st_rel _vm_eq d s1 s2 → st_rel _vm_eq d' s1 s2.
Proof. by move=> ?; apply st_rel_weaken. Qed.

Definition checker_st_eq : Checker_e (st_rel _vm_eq) :=
  {| check_es := check_es_st_eq;
     check_lvals := check_lvals_st_eq;
     check_esP_rel := check_esP_R_st_eq |}.

Notation _vm_uincl := (fun (_:unit) => vm_uincl (wsw1:=wsw1) (wsw2:=wsw2)).
Definition st_uincl := st_rel _vm_uincl.

Lemma check_esP_R_st_uincl (d : unit) (es1 es2 : pexprs) (d' : unit) :
  check_es_st_eq d es1 es2 d' → ∀ s1 s2, st_rel _vm_uincl d s1 s2 → st_rel _vm_uincl d' s1 s2.
Proof. by move=> ?; apply st_rel_weaken. Qed.

Definition checker_st_uincl : Checker_e (st_rel _vm_uincl) :=
  {| check_es := check_es_st_eq;
     check_lvals := check_lvals_st_eq;
     check_esP_rel := check_esP_R_st_uincl |}.

End WEQUIV_CORE.

Section WEQUIV_WHOARE.

Context {E E0 : Type -> Type} {sem_F1 : sem_Fun1 E} {sem_F2 : sem_Fun2 E}
    {wE: with_Error E E0} {iE0 : InvEvent E0} {rE0 : EventRels E0}.

Context (p1 : prog1) (p2 : prog2) (ev1: extra_val_t1) (ev2 : extra_val_t2).

Definition EventRels_and1 : EventRels E0 :=
  {| EPreRel0_ := fun T1 T2 (e1 : E0 T1) (e2 : E0 T2) => preInv0 e1 /\ EPreRel0 e1 e2
   ; EPostRel0_ := fun T1 T2 (e1 : E0 T1) t1 (e2 : E0 T2) t2 => postInv0 e1 t1 /\ EPostRel0 e1 t1 e2 t2 |}.

Definition EventRels_and2 : EventRels E0 :=
  {| EPreRel0_ := fun T1 T2 (e1 : E0 T1) (e2 : E0 T2) => preInv0 e2 /\ EPreRel0 e1 e2
   ; EPostRel0_ := fun T1 T2 (e1 : E0 T1) t1 (e2 : E0 T2) t2 => postInv0 e2 t2 /\ EPostRel0 e1 t1 e2 t2 |}.

Lemma whoare_wequiv1 (P Q : rel_c) (P1 Q1 : Pred_c (wsw:=wsw1)) c1 c2:
  (forall s1 s2, P s1 s2 -> P1 s1) ->
  hoare (wc:=wc1) (wa:=wa1) (wsw:=wsw1) (dc:=dc1) (iEr := invErrT) p1 ev1 P1 c1 Q1 ->
  wequiv p1 p2 ev1 ev2 P c1 c2 Q ->
  wequiv (rE0 := EventRels_and1) p1 p2 ev1 ev2 P c1 c2 (fun s1 s2 => Q1 s1 /\ Q s1 s2).
Proof.
  move=> hPP1 hh he s1 s2 hP.
  have {}hh := hh s1 (hPP1 _ _ hP).
  have {}he := he _ _ hP.
  have := lutt_xrutt_trans_l hh he.
  apply xrutt_weaken => //.
  + move=> T1 T2 e1 e2 []; rewrite /preInv /EPreRel /=.
    by case: (mfun1 e1); case: (mfun1 e2).
  move=> T1 T2 e1 t1 e2 t2 + _ [].
  rewrite /errcutoff /is_error /preInv /EPreRel /EPostRel /postInv /=.
  case: (mfun1 e1); case: (mfun1 e2) => //=.
Qed.

Lemma whoare_wequiv2 (P Q : rel_c) (P2 Q2 : Pred_c (wsw:=wsw2)) c1 c2:
  (forall s1 s2, P s1 s2 -> P2 s2) ->
  hoare (wsw:=wsw2) (dc:=dc2) (iEr := invErrT) p2 ev2 P2 c2 Q2 ->
  wequiv p1 p2 ev1 ev2 P c1 c2 Q ->
  wequiv (rE0 := EventRels_and2) p1 p2 ev1 ev2 P c1 c2 (fun s1 s2 => Q2 s2 /\ Q s1 s2).
Proof.
  move=> hPP2 hh he s1 s2 hP.
  have {}hh := hh s2 (hPP2 _ _ hP).
  have {}he := he _ _ hP.
  have := lutt_xrutt_trans_r hh he.
  apply xrutt_weaken => //.
  + move=> T1 T2 e1 e2 []; rewrite /preInv /EPreRel /=.
    by case: (mfun1 e1); case: (mfun1 e2).
  move=> T1 T2 e1 t1 e2 t2 + _ [].
  rewrite /errcutoff /is_error /preInv /EPreRel /EPostRel /postInv /=.
  case: (mfun1 e1); case: (mfun1 e2) => //=.
Qed.

End WEQUIV_WHOARE.

Section WEQUIV_WRITE.
Context {E E0 : Type -> Type} {sem_F1 : sem_Fun1 E} {sem_F2 : sem_Fun2 E}
    {wE: with_Error E E0} {rE0 : EventRels E0}.

Context (p1 : prog1) (p2 : prog2) (ev1: extra_val_t1) (ev2 : extra_val_t2).

Lemma wequiv_write1 (P Q : rel_c) c1 c2:
  wequiv p1 p2 ev1 ev2 P c1 c2 Q ->
  (forall s1_,
    wequiv p1 p2 ev1 ev2
     (fun s1 s2 => s1 = s1_ /\ P s1 s2)
     c1 c2
     (fun s1 s2 => s1_.(evm) =[\ write_c c1] s1.(evm) /\ Q s1 s2)).
Proof.
  move=> /wkequivP' h s1_; apply/wkequivP' => s1__ s2_.
  have /(_ s1_) hw := [elaborate it_writeP (wc:=wc1) (wa:=wa1) (dc:=dc1) p1 ev1 c1 ].
  have h_ : forall s1 s2, (s1 = s1_ /\ s2 = s2_) /\ P s1 s2 -> s1 = s1_.
  + by move=> ?? [] [].
  have {h_ h}:= whoare_wequiv1 h_ hw (h s1_ s2_).
  apply wkequiv_weaken => //.
  + by move=> > [].
  by move=> ?? [] [] ?? [].
Qed.

Lemma wequiv_write2 (P Q : rel_c) c1 c2:
  wequiv p1 p2 ev1 ev2 P c1 c2 Q ->
  (forall s2_,
    wequiv p1 p2 ev1 ev2
     (fun s1 s2 => s2 = s2_ /\ P s1 s2)
     c1 c2
     (fun s1 s2 => s2_.(evm) =[\ write_c c2] s2.(evm) /\ Q s1 s2)).
Proof.
  move=> /wkequivP' h s2_; apply/wkequivP' => s1_ s2__.
  have /(_ s2_) hw := [elaborate it_writeP (dc:=dc2) p2 ev2 c2 ].
  have h_ : forall s1 s2, (s1 = s1_ /\ s2 = s2_) /\ P s1 s2 -> s2 = s2_.
  + by move=> ?? [] [].
  have {h_ h}:= whoare_wequiv2 h_ hw (h s1_ s2_).
  apply wkequiv_weaken => //.
  + by move=> > [].
  by move=> ?? [] [] ?? [].
Qed.

End WEQUIV_WRITE.

Notation sem_fun_full1 := (sem_fun_full (wsw:=wsw1) (dc:=dc1) (ep:=ep) (spp:=spp) (wc:=wc1) (wa:=wa1) (sip:=sip) (pT:=pT1) (scP:= scP1)).
Notation sem_fun_full2 := (sem_fun_full (wsw:=wsw2) (dc:=dc2) (ep:=ep) (spp:=spp) (wc:=wc2) (wa:=wa2) (sip:=sip) (pT:=pT2) (scP:= scP2)).

Section WEQUIV_FUN.

Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Context (p1 : prog1) (p2 : prog2) (ev1: extra_val_t1) (ev2 : extra_val_t2)  (spec : EquivSpec).

Definition wequiv_f_rec RPreF ii1 ii2 fn1 fn2 RPostF :=
  wequiv_f_ii (rE0:=relEvent_recCall spec) p1 p2 ev1 ev2 RPreF ii1 ii2 fn1 fn2 RPostF.

Section REC.

Context (sem_F1 : funname -> sem_Fun1 (recCall +' E)).
Context (sem_F2 : funname -> sem_Fun2 (recCall +' E)).

Definition wequiv_fun_body_hyp_rec_wa (RPreF:relPreF) fn1 fn2 (RPostF:relPostF) :=
  forall fs1 fs2,
  RPreF fn1 fn2 fs1 fs2 ->
  forall fd1, get_fundef (p_funcs p1) fn1 = Some fd1 ->
  exists2 fd2, get_fundef (p_funcs p2) fn2 = Some fd2 &
    sem_pre (wsw:=wsw1) (wc:=wc1) (wa:=wa1) (dc:=dc1) (pT:=pT1) p1 fn1 fs1 = ok tt ->
    sem_pre (wsw:=wsw2) (wc:=wc2) (wa:=wa2) (dc:=dc2) (pT:=pT2) p2 fn2 fs2 = ok tt /\
    forall s11, initialize_funcall (dc:=dc1) p1 ev1 fd1 fs1 = ok s11 ->
      exists2 s21,
        initialize_funcall (dc:=dc2) p2 ev2 fd2 fs2 = ok s21 &
        exists (P Q : rel_c),
          [/\ P s11 s21
            , wequiv (sem_F1 := sem_F1 fn1) (sem_F2 := sem_F2 fn2) (rE0:=relEvent_recCall spec) p1 p2 ev1 ev2 P fd1.(f_body) fd2.(f_body) Q
            , wrequiv Q (finalize_funcall (dc:=dc1) fd1) (finalize_funcall (dc:=dc2) fd2) (RPostF fn1 fn2 fs1 fs2)
            & (forall fr1 fr2, RPostF fn1 fn2 fs1 fs2 fr1 fr2 ->
               sem_post (wsw:=wsw1) (wc:=wc1) (wa:=wa1) (dc:=dc1) (pT:=pT1) p1 fn1 fs1.(fvals) fr1 = ok () ->
               sem_post (wsw:=wsw2) (wc:=wc2) (wa:=wa2) (dc:=dc2) (pT:=pT2) p2 fn2 fs2.(fvals) fr2 = ok ())].

#[local]
Lemma xrutt_weaken_aux post (sem1 : itree (recCall +' E) fstate) (sem2 : itree (recCall +' E) fstate) :
  xrutt (errcutoff (is_error (FIso_suml recCall (Err:=ErrEvent)))) nocutoff
    (EPreRel (rE0 := relEvent_recCall spec)) (EPostRel (rE0 := relEvent_recCall spec))
   post sem1 sem2 ->
  xrutt (@EE_MR _ (@errcutoff _ (is_error wE)) recCall) (@EE_MR _ nocutoff recCall)
      (sum_prerel (@RPreD spec) EPreRel) (sum_postrel (@RPostD spec) EPostRel)
      post sem1 sem2.
Proof.
  apply xrutt_weaken => //.
  + move=> T1 e1; rewrite /errcutoff /= /EE_MR.
    by case: e1 => //= e; rewrite /is_error /=; case: mfun1.
  + move=> T1 T2 e1 e2; rewrite /EPreRel sum_prerelP.
    case: e1 e2 => [ [ii1 fn1 fs1] | e1] [ [ii2 fn2 fs2] | e2] //=.
    + by case : mfun1. + by case : mfun1.
    by case: mfun1 => // ?; case: mfun1.
  move=> T1 T2 e1 t1 e2 t2; rewrite /EPostRel sum_postrelP.
  case: e1 t1 e2 t2 => [ [ii1 fn1 fs1] | e1] t1 [ [ii2 fn2 fs2] | e2] t2 //=.
  by case: mfun1 => // ?; case: mfun1.
Qed.

Notation isem_fun_def1 := (isem_fun_def (wsw:=wsw1) (dc:=dc1) (wc:=wc1) (wa:=wa1) (ep:=ep) (spp:=spp) (sip:=sip) (pT:=pT1) (scP:= scP1) (sem_F:=sem_F1)).

Notation isem_fun_def2 := (isem_fun_def (wsw:=wsw2) (dc:=dc2) (wc:=wc2) (wa:=wa2) (ep:=ep) (spp:=spp) (sip:=sip) (pT:=pT2) (scP:= scP2) (sem_F:=sem_F2)).

Notation wiequiv_f rpreF fn1 fn2 rpostF :=
   (wkequiv_io (rpreF fn1 fn2) (isem_fun_def1 p1 ev1 fn1) (isem_fun_def2 p2 ev2 fn2) (rpostF fn1 fn2)).

Lemma wequiv_fun_ind_wa :
  ((forall ii1 ii2 fn1 fn2, wequiv_f_rec rpreF ii1 ii2 fn1 fn2 rpostF) ->
   (forall fn1 fn2, wequiv_fun_body_hyp_rec_wa rpreF fn1 fn2 rpostF)) ->
  forall fn1 fn2,
  wiequiv_f rpreF fn1 fn2 rpostF.
Proof.
  have hrec : (forall ii1 ii2 fn1 fn2, wequiv_f_rec rpreF ii1 ii2 fn1 fn2 rpostF).
  + by move=> ii1 ii2 fn1' fn2' fs1' fs2' hpre'; apply xrutt_trigger.
  move=> /(_ hrec) hbody fn1 fn2 fs1 fs2 hpre.
  apply interp_mrec_xrutt with (RPreInv := (@RPreD spec))
                               (RPostInv := (@RPostD spec)).
  + move=> {hpre fn1 fn2 fs1 fs2}.
    move=> _ _ [ii1 fn1 fs1] [ii2 fn2 fs2] hpre.
    have := wequiv_fun_body_wa (hbody fn1 fn2) hpre.
    by apply xrutt_weaken_aux.
  have := wequiv_fun_body_wa (hbody fn1 fn2) hpre.
  apply xrutt_weaken_aux.
Qed.

End REC.

Definition wequiv_rec P c1 c2 Q :=
  wequiv (rE0:=relEvent_recCall spec) p1 p2 ev1 ev2 P c1 c2 Q.

Definition wequiv_rec_i P i1 i2 Q := wequiv_rec P [:: i1 ] [:: i2 ] Q.

Definition wequiv_rec_ir P i1 ii1 i2 ii2 Q :=
  wequiv_rec_i P (MkI ii1 i1) (MkI ii2 i2) Q.

Definition wiequiv_f rpreF fn1 fn2 rpostF :=
   (wkequiv_io (rpreF fn1 fn2)
      (isem_fun (wsw:=wsw1) (dc:=dc1) (wc:=wc1) (wa:=wa1) (ep:=ep) (spp:=spp) (sip:=sip) (pT:=pT1) (scP:= scP1) p1 ev1 fn1)
      (isem_fun (wsw:=wsw2) (dc:=dc2) (wc:=wc2) (wa:=wa2) (ep:=ep) (spp:=spp) (sip:=sip) (pT:=pT2) (scP:= scP2) p2 ev2 fn2)
     (rpostF fn1 fn2)).

Lemma wequiv_fun_get_wa fn1 fn2 Pf Qf :
  (forall fd1, get_fundef (p_funcs p1) fn1 = Some fd1 ->
    wiequiv_f (fun fn1 fn2 fs1 fs2 =>
      [/\ Pf fn1 fn2 fs1 fs2
        , sem_pre (dc:=dc1) (wsw:=wsw1) (wc:=wc1) (wa:=wa1) p1 fn1 fs1 = ok tt
        & exists s1, initialize_funcall (dc:=dc1) p1 ev1 fd1 fs1 = ok s1])
      fn1 fn2 Qf) ->
  wiequiv_f Pf fn1 fn2 Qf.
Proof.
  move=> hfd fs1 fs2 hpre /=.
  rewrite !isem_call_unfold /isem_fun_body /kget_fundef.
  case heq : get_fundef => [fd1 | ].
  + rewrite /= bind_ret_l /isem_pre.
    case heq0 : (sem_pre p1 fn1 fs1) => [ [] | ].
    + case heq1 : initialize_funcall => [s1 | e].
      + have hpre' :
          [/\ Pf fn1 fn2 fs1 fs2, sem_pre (dc:=dc1) (wsw:=wsw1) (wc:=wc1) (wa:=wa1) p1 fn1 fs1 = ok tt
            & exists s1, initialize_funcall (dc:=dc1) p1 ev1 fd1 fs1 = ok s1].
        + by split => //; exists s1.
        have /= := hfd _ heq _ _ hpre'.
        by rewrite !isem_call_unfold /isem_fun_body /kget_fundef heq /= bind_ret_l /isem_pre heq0 heq1.
      rewrite bind_ret_l /= bind_vis; apply xrutt_CutL.
      by rewrite /errcutoff /is_error /subevent /resum /fromErr mid12.
    rewrite /= bind_vis; apply xrutt_CutL.
    by rewrite /errcutoff /is_error /subevent /resum /fromErr mid12.
  rewrite /= bind_vis; apply xrutt_CutL.
  by rewrite /errcutoff /is_error /subevent /resum /fromErr mid12.
Qed.

End WEQUIV_FUN.

End WITHASSERT.

Section CONTEXT.
Context {wa1 wa2: WithAssert}.
Context {E E0 : Type -> Type} {sem_F1 : sem_Fun1 E} {sem_F2 : sem_Fun2 E}
    {wE: with_Error E E0} {rE0 : EventRels E0}.
Context (p1 : prog1) (p2 : prog2) (ev1: extra_val_t1) (ev2 : extra_val_t2).

Notation sem_pexprs1 := (sem_pexprs (wa:=wa1)).
Notation sem_pexprs2 := (sem_pexprs (wa:=wa2)).
Notation write_lvals1 := (write_lvals (wa:=wa1)).
Notation write_lvals2 := (write_lvals (wa:=wa2)).

Lemma wequiv_opn_eq {wc:WithCatch} P Q ii1 xs1 at1 o es1 ii2 xs2 at2 es2 :
  wrequiv P (fun s => sem_pexprs1 true (p_globs p1) s es1)
           (fun s => sem_pexprs2 true (p_globs p2) s es2) eq ->
  (forall vs,
    wrequiv P (fun s1 => write_lvals1 true (p_globs p1) s1 xs1 vs)
             (fun s2 => write_lvals2 true (p_globs p2) s2 xs2 vs) Q) ->
  wequiv (wa1:=wa1) p1 p2 ev1 ev2 P [:: MkI ii1 (Copn xs1 at1 o es1)] [:: MkI ii2 (Copn xs2 at2 o es2)] Q.
Proof.
  move=> he hx; apply wequiv_opn with eq eq => //.
  + by move=> *; apply wrequiv_eq.
  by move=> > <-; apply hx.
Qed.

Lemma wequiv_opn_uincl P Q ii1 xs1 at1 o es1 ii2 xs2 at2 es2 :
  wrequiv P (fun s => sem_pexprs1 true (p_globs p1) s es1)
           (fun s => sem_pexprs2 true (p_globs p2) s es2) (Forall2 value_uincl) ->
  (forall vs1 vs2,
    Forall2 value_uincl vs1 vs2 ->
    wrequiv P (fun s1 => write_lvals1 true (p_globs p1) s1 xs1 vs1)
             (fun s2 => write_lvals2 true (p_globs p2) s2 xs2 vs2) Q) ->
  wequiv (wa1:=wa1) p1 p2 ev1 ev2 P [:: MkI ii1 (Copn xs1 at1 o es1)] [:: MkI ii2 (Copn xs2 at2 o es2)] Q.
Proof.
  move=> he; apply wequiv_opn with (Forall2 value_uincl) => //.
  move=> *; apply wrequiv_exec_sopn.
Qed.

Section UINCL.
Context {D:Type}.
Context (R : D -> estate1 -> estate2 -> Prop).
Context {ce : Checker_e R}.
Context {cu: (Checker_uincl p1 p2 (wa1:=wa1)) R ce }.

Lemma wequiv_opn_rel_uincl d de d' ii1 xs1 tg1 o es1  ii2 xs2 tg2 es2 :
  check_es d es1 es2 de →
  check_lvals de xs1 xs2 d' →
  wequiv (wa1:=wa1) p1 p2 ev1 ev2 (R d) [:: MkI ii1 (Copn xs1 tg1 o es1)] [:: MkI ii2 (Copn xs2 tg2 o es2)] (R d').
Proof.
  move=> hes hxs.
  apply wequiv_opn_uincl.
  + apply: ucheck_esP hes; apply wdb_ok_true.
  move=> v1 v2 hu; apply wrequiv_weaken with (R de) (R d') => //.
  + by apply: check_esP_rel hes.
  apply: ucheck_lvalsP hxs v1 v2 hu; apply wdb_ok_true.
Qed.
End UINCL.

Section EQ.
Context {D:Type} {wc: WithCatch}.
Context (R : D -> estate1 -> estate2 -> Prop).
Context {ce : Checker_e R}.
Context {cu: (Checker_eq p1 p2 (wa1:=wa1)) R ce}.

Lemma wequiv_opn_rel_eq d de d' ii1 xs1 tg1 o es1 ii2 xs2 tg2 es2 :
  check_es d es1 es2 de →
  check_lvals de xs1 xs2 d' →
  wequiv (wa1:=wa1) p1 p2 ev1 ev2 (R d) [:: MkI ii1 (Copn xs1 tg1 o es1)] [:: MkI ii2 (Copn xs2 tg2 o es2)] (R d').
Proof.
  move=> hes hxs.
  apply wequiv_opn_eq.
  + by apply: echeck_esP hes; apply wdb_ok_true.
  move=> v; apply wrequiv_weaken with (R de) (R d') => //.
  + by apply: check_esP_rel hes.
  by apply: echeck_lvalsP hxs v; apply wdb_ok_true.
Qed.

End EQ.

End CONTEXT.

Section NOASSERT.

Notation isem_fun1 := (isem_fun (wsw:=wsw1) (dc:=dc1) (ep:=ep) (spp:=spp) (sip:=sip) (pT:=pT1) (scP:= scP1)).
Notation isem_fun2 := (isem_fun (wsw:=wsw2) (dc:=dc2) (ep:=ep) (spp:=spp) (sip:=sip) (pT:=pT2) (scP:= scP2)).

Section WEQUIV_CORE.

Context {E E0 : Type -> Type} {sem_F1 : sem_Fun1 E} {sem_F2 : sem_Fun2 E}
    {wE: with_Error E E0} {rE0 : EventRels E0}.

Context (p1 : prog1) (p2 : prog2) (ev1: extra_val_t1) (ev2 : extra_val_t2).

Notation sem_fun1 := (sem_fun (pT := pT1) (sem_Fun := sem_F1)).
Notation sem_fun2 := (sem_fun (pT := pT2) (sem_Fun := sem_F2)).

Lemma wequiv_noassert ii a c P Q :
  wequiv p1 p2 ev1 ev2 P [:: MkI ii (Cassert a)] c Q.
Proof.
  move=> s1 s2 _ /=.
  rewrite bind_ret_r /isem_assert /= /Exception.throw bind_vis; apply xrutt_CutL => //.
  by rewrite /errcutoff /is_error /subevent /resum /fromErr mid12.
Qed.

Lemma wequiv_call (Pf : relPreF) (Qf : relPostF) Rv P Q ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  wrequiv P (fun s => sem_pexprs (~~ (@direct_call dc1)) (p_globs p1) s es1)
            (fun s => sem_pexprs (~~ (@direct_call dc2)) (p_globs p2) s es2) Rv ->
  (forall s1 s2 vs1 vs2,
     P s1 s2 -> Rv vs1 vs2 -> Pf fn1 fn2 (mk_fstate vs1 s1) (mk_fstate vs2 s2)) ->
  wequiv_f_ii p1 p2 ev1 ev2 Pf ii1 ii2 fn1 fn2 Qf ->
  (forall fs1 fs2 fr1 fr2,
    Pf fn1 fn2 fs1 fs2 -> Qf fn1 fn2 fs1 fs2 fr1 fr2 ->
    wrequiv P (upd_estate (~~ (@direct_call dc1)) (p_globs p1) xs1 fr1)
              (upd_estate (~~ (@direct_call dc2)) (p_globs p2) xs2 fr2) Q) ->
  wequiv p1 p2 ev1 ev2 P [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] Q.
Proof.
  by move=> hes hPf hf; apply: (wequiv_call_wa hes _ hPf _ hf).
Qed.

Lemma wequiv_call_eq P Q ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  wrequiv P (fun s => sem_pexprs (~~ (@direct_call dc1)) (p_globs p1) s es1)
            (fun s => sem_pexprs (~~ (@direct_call dc2)) (p_globs p2) s es2) eq ->
  (forall s1 s2 vs,
     P s1 s2 -> rpreF (eS:=eq_spec) fn1 fn2 (mk_fstate vs s1) (mk_fstate vs s2)) ->
  wequiv_f_ii p1 p2 ev1 ev2 (rpreF (eS:=eq_spec)) ii1 ii2 fn1 fn2 (rpostF (eS:=eq_spec)) ->
  (forall fs,
    wrequiv P (upd_estate (~~ (@direct_call dc1)) (p_globs p1) xs1 fs)
              (upd_estate (~~ (@direct_call dc2)) (p_globs p2) xs2 fs) Q) ->
  wequiv p1 p2 ev1 ev2 P [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] Q.
Proof.
  by move=> hes hPf hf; apply: (wequiv_call_eq_wa hes _ hPf hf).
Qed.

Definition wequiv_fun_body_hyp (RPreF:relPreF) fn1 fn2 (RPostF:relPostF) :=
  forall fs1 fs2,
  RPreF fn1 fn2 fs1 fs2 ->
  forall fd1, get_fundef (p_funcs p1) fn1 = Some fd1 ->
  exists2 fd2, get_fundef (p_funcs p2) fn2 = Some fd2 &
    exists (P Q : rel_c),
      forall s11, initialize_funcall (dc:=dc1) p1 ev1 fd1 fs1 = ok s11 ->
      exists s21,
        [/\ initialize_funcall (dc:=dc2) p2 ev2 fd2 fs2 = ok s21
          , P s11 s21
          , wequiv p1 p2 ev1 ev2 P fd1.(f_body) fd2.(f_body) Q
          & wrequiv Q (finalize_funcall (dc:=dc1) fd1) (finalize_funcall (dc:=dc2) fd2) (RPostF fn1 fn2 fs1 fs2)
        ].

Lemma wequiv_fun_body RPreF fn1 fn2 RPostF :
  wequiv_fun_body_hyp RPreF fn1 fn2 RPostF ->
  wequiv_f_body p1 p2 ev1 ev2 RPreF fn1 fn2 RPostF.
Proof.
  move=> h; apply wequiv_fun_body_wa => fs1 fs2 hpre fd1 hfd1.
  have [fd2 hfd2 [P] [Q] {}h]:= h fs1 fs2 hpre fd1 hfd1.
  rewrite /sem_pre /sem_post /=; exists fd2 => // _; split => //.
  by move=> s1 /h [s2] [*]; exists s2 => //; exists P, Q.
Qed.

Lemma wequiv_call_rel_uincl_R
  {D : Type} [R : D → estate1 → estate2 → Prop] {ce : Checker_e R} {cu : Checker_uincl p1 p2 (R:=R)}
  d de de' d' ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  (∀ d s1 s2, R d s1 s2 → escs s1 = escs s2 ∧ emem s1 = emem s2) →
  (forall scs mem s1 s2, R de s1 s2 ->
     R de' (with_scs (with_mem s1 mem) scs) (with_scs (with_mem s2 mem) scs)) →
  check_es d es1 es2 de →
  check_lvals de' xs1 xs2 d' →
  wequiv_f_ii p1 p2 ev1 ev2 (fun _ _ => fs_uincl) ii1 ii2 fn1 fn2 (fun _ _ _ _ => fs_uincl) →
  wequiv p1 p2 ev1 ev2 (R d) [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] (R d').
Proof.
  move=> hscm hde' hes hxs hf.
  by apply: (wequiv_call_rel_uincl_R_wa (cu:=cu) hscm hde' hes hxs _ hf).
Qed.

Lemma wequiv_call_rel_eq_R
  {D : Type} [R : D → estate1 → estate2 → Prop] {ce : Checker_e R} {cu : Checker_eq p1 p2 (R:=R)}
  d de de' d' ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  (∀ d s1 s2, R d s1 s2 → escs s1 = escs s2 ∧ emem s1 = emem s2) →
  (forall scs mem s1 s2, R de s1 s2 ->
     R de' (with_scs (with_mem s1 mem) scs) (with_scs (with_mem s2 mem) scs)) →
  check_es d es1 es2 de →
  check_lvals de' xs1 xs2 d' →
  wequiv_f_ii p1 p2 ev1 ev2 (fun _ _ => eq) ii1 ii2 fn1 fn2 (fun _ _ _ _ => eq) →
  wequiv p1 p2 ev1 ev2 (R d) [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] (R d').
Proof.
  move=> hscm hde' hes hxs hf.
  by apply: (wequiv_call_rel_eq_R_wa (cu:=cu) hscm hde' hes hxs _ hf).
Qed.

Lemma wequiv_call_rel_uincl
  {D : Type} [R : D → vm1_t → vm2_t → Prop] {ce : Checker_e (st_rel R)} {cu : Checker_uincl p1 p2 (R:=st_rel R)}
  d de d' ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  check_es d es1 es2 de →
  check_lvals de xs1 xs2 d' →
  wequiv_f_ii p1 p2 ev1 ev2 (fun _ _ => fs_uincl) ii1 ii2 fn1 fn2 (fun _ _ _ _ => fs_uincl) →
  wequiv p1 p2 ev1 ev2 (st_rel R d) [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] (st_rel R d').
Proof.
  move=> hes hxs hf.
  by apply: (wequiv_call_rel_uincl_wa (cu:=cu) hes hxs _ hf).
Qed.

Lemma wequiv_call_rel_eq
  {D : Type} [R : D → vm1_t → vm2_t → Prop] {ce : Checker_e (st_rel R)} {cu : Checker_eq p1 p2 (R:=st_rel R)}
  d de d' ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  check_es d es1 es2 de →
  check_lvals de xs1 xs2 d' →
  wequiv_f_ii p1 p2 ev1 ev2 (fun _ _ => eq) ii1 ii2 fn1 fn2 (fun _ _ _ _ => eq) →
  wequiv p1 p2 ev1 ev2 (st_rel R d) [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] (st_rel R d').
Proof.
  move=> hes hxs hf.
  by apply: (wequiv_call_rel_eq_wa (cu:=cu) hes hxs _ hf).
Qed.

End WEQUIV_CORE.

Notation sem_fun_full1 := (sem_fun_full (wsw:=wsw1) (dc:=dc1) (ep:=ep) (spp:=spp) (sip:=sip) (pT:=pT1) (scP:= scP1)).
Notation sem_fun_full2 := (sem_fun_full (wsw:=wsw2) (dc:=dc2) (ep:=ep) (spp:=spp) (sip:=sip) (pT:=pT2) (scP:= scP2)).

Notation wiequiv_f_ii := (wequiv_f_ii (sem_F1 := sem_fun_full1) (sem_F2 := sem_fun_full2)).
Notation wiequiv   := (wequiv (sem_F1 := sem_fun_full1) (sem_F2 := sem_fun_full2)).

Section WEQUIV_FUN.

Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Context (p1 : prog1) (p2 : prog2) (ev1: extra_val_t1) (ev2 : extra_val_t2)  (spec : EquivSpec).

Definition wequiv_fun_body_hyp_rec (RPreF:relPreF) fn1 fn2 (RPostF:relPostF) :=
  forall fs1 fs2,
  RPreF fn1 fn2 fs1 fs2 ->
  forall fd1, get_fundef (p_funcs p1) fn1 = Some fd1 ->
  exists2 fd2, get_fundef (p_funcs p2) fn2 = Some fd2 &
    forall s11, initialize_funcall (dc:=dc1) p1 ev1 fd1 fs1 = ok s11 ->
      exists2 s21,
        initialize_funcall (dc:=dc2) p2 ev2 fd2 fs2 = ok s21 &
        exists (P Q : rel_c),
        [/\ P s11 s21
          , wequiv_rec p1 p2 ev1 ev2 spec P fd1.(f_body) fd2.(f_body) Q
          & wrequiv Q (finalize_funcall (dc:=dc1) fd1) (finalize_funcall (dc:=dc2) fd2) (RPostF fn1 fn2 fs1 fs2)].

Lemma wequiv_fun_ind :
  ((forall ii1 ii2 fn1 fn2, wequiv_f_rec p1 p2 ev1 ev2 spec rpreF ii1 ii2 fn1 fn2 rpostF) ->
   (forall fn1 fn2, wequiv_fun_body_hyp_rec rpreF fn1 fn2 rpostF)) ->
  forall fn1 fn2,
  wiequiv_f p1 p2 ev1 ev2 rpreF fn1 fn2 rpostF.
Proof.
  move=> hrec.
  apply wequiv_fun_ind_wa => {}/hrec h fn1 fn2 fs1 fs2 /h{}h fd1 {}/h [fd2 hfd2 h].
  exists fd2 => // _; split => // s1 {}/h [s2 ? [P] [Q] [*]]; exists s2 => //.
  by exists P, Q.
Qed.

End WEQUIV_FUN.

End NOASSERT.

End RELATIONAL.

Notation wiequiv_f_wa wc1 wc2 wa1 wa2 :=
  (wiequiv_f (wc1 := wc1) (wc2 := wc2) (wa1 := wa1) (wa2 := wa2) ).

Notation wiequiv_wa wc1 wc2 wa1 wa2 :=
  (wequiv (sem_F1 := sem_fun_full (wc:=wc1) (wa:=wa1)) (sem_F2 := sem_fun_full (wc:=wc2) (wa:=wa2))).

(* Notation wiequiv_f := (wequiv_f_ii (sem_F1 := sem_fun_full) (sem_F2 := sem_fun_full)). *)
Notation wiequiv   := (wequiv (sem_F1 := sem_fun_full) (sem_F2 := sem_fun_full)).

Lemma st_relP {syscall_state : Type} {ep : EstateParams syscall_state} {wsw : WithSubWord}
  D (R : D -> Vm.t -> Vm.t -> Prop) d s t :
  st_rel R d s t <-> t = with_vm s (evm t) /\ R d (evm s) (evm t).
Proof.
  rewrite (surj_estate s) (surj_estate t) /=.
  by split => [ [/= <- <-] | [[<- <-] ?]].
Qed.

Section SYSCALL.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {wc : WithCatch }
  {wa : WithAssert}
  {asm_op: Type}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {wsw : WithSubWord}
  {scP : semCallParams (wsw:= wsw) (pT := pT)}
  {dc: DirectCall}.

Lemma fs_uincl_syscall o : wrequiv fs_uincl (fexec_syscall o) (fexec_syscall o) fs_uincl.
Proof.
  rewrite /fexec_syscall => fs1 fs2 fr1 [<- <- hu1].
  t_xrbindP => -[[rscs m] vs1] hex.
  have [vs2 -> hu2] := exec_syscallP hex hu1.
  by move=> [<-] /=; eexists.
Qed.

Context {E E0 : Type -> Type} {sem_F1 sem_F2 : sem_Fun E} {wE: with_Error E E0} {rE0 : EventRels E0}.

Context (p1 p2 : prog) (ev1 ev2: extra_val_t).

Context {D : Type}
        {R : D -> Vm.t -> Vm.t -> Prop}
        {ce : Checker_e (st_rel R)}.

Lemma wequiv_syscall_rel_uincl {cu: Checker_uincl p1 p2 (ce:=ce)} d de d' ii1 xs1 sc es1 ii2 xs2 es2 :
  check_es d es1 es2 de →
  check_lvals de xs1 xs2 d' →
  wequiv (sem_F1:=sem_F1) (sem_F2:=sem_F2)
    p1 p2 ev1 ev2 (st_rel R d) [:: MkI ii1 (Csyscall xs1 sc es1)] [:: MkI ii2 (Csyscall xs2 sc es2)] (st_rel R d').
Proof.
  move=> hes hxs.
  eapply wequiv_syscall_rel_uincl_core; eauto.
  apply fs_uincl_syscall.
Qed.

Lemma wequiv_syscall_rel_eq {cu: Checker_eq p1 p2 (ce:=ce)} d de d' ii1 xs1 sc es1 ii2 xs2 es2 :
  check_es d es1 es2 de →
  check_lvals de xs1 xs2 d' →
  wequiv (sem_F1:=sem_F1) (sem_F2:=sem_F2)
    p1 p2 ev1 ev2 (st_rel R d) [:: MkI ii1 (Csyscall xs1 sc es1)] [:: MkI ii2 (Csyscall xs2 sc es2)] (st_rel R d').
Proof.
  move=> hes hxs.
  eapply wequiv_syscall_rel_eq_core; eauto.
  apply wrequiv_eq.
Qed.

End SYSCALL.

Arguments Checker_eq {syscall_state} {ep spp} {asm_op} {sip pT1 pT2 wsw1 wsw2 dc1 dc2 wc1 wc2 wa1 wa2}
  _ _ {D} [R] ce.

Arguments Checker_uincl {syscall_state} {ep spp} {asm_op} {sip pT1 pT2 wsw1 wsw2 dc1 dc2 wc1 wc2 wa1 wa2}
  _ _ {D} [R] ce.

Class EventRels_trans {E0 : Type -> Type} (rE12 rE23 rE13 : EventRels E0) :=
  { ERpre_trans : forall T1 T2 T3 (e1 : E0 T1) (e2 : E0 T2) (e3 : E0 T3),
       EPreRel0 (rE0:=rE12) e1 e2 → EPreRel0 (rE0:=rE23) e2 e3 → EPreRel0 (rE0:=rE13) e1 e3;
    ERpost_trans : forall T1 T2 T3 (e1 : E0 T1) (e2 : E0 T2) (e3 : E0 T3) t1 t3,
     EPreRel0 (rE0:=rE12) e1 e2 → EPreRel0 (rE0:=rE23) e2 e3 → EPostRel0 (rE0:=rE13) e1 t1 e3 t3 →
     exists2 t2 : T2, EPostRel0 (rE0:=rE12) e1 t1 e2 t2 & EPostRel0 (rE0:=rE23) e2 t2 e3 t3; }.

Section TRANSITIVITY.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {asm_op : Type}
  {sip : SemInstrParams asm_op syscall_state}
  {pT1 pT2 pT3 : progT}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {wsw1 wsw2 wsw3 : WithSubWord}
  {wc1 wc2 wc3 : WithCatch }
  {wa1 wa2 wa3 : WithAssert}
  {scP1 : semCallParams (wsw := wsw1) (pT := pT1)}
  {scP2 : semCallParams (wsw := wsw2) (pT := pT2)}
  {scP3 : semCallParams (wsw := wsw3) (pT := pT3)}
  {dc1 dc2 dc3 : DirectCall}
  {rE12 : EventRels E0} {rE23 : EventRels E0} {rE13 : EventRels E0}
  {sem_F1 : sem_Fun (sip := sip) (pT := pT1) E}
  {sem_F2 : sem_Fun (sip := sip) (pT := pT2) E}
  {sem_F3 : sem_Fun (sip := sip) (pT := pT3) E}
  {rE_trans : EventRels_trans rE12 rE23 rE13}
.

Notation prog1 := (prog (pT := pT1)).
Notation prog2 := (prog (pT := pT2)).
Notation prog3 := (prog (pT := pT3)).

Notation EPre12 := (EPreRel (rE0 := rE12)).
Notation EPre23 := (EPreRel (rE0 := rE23)).
Notation EPre13 := (EPreRel (rE0 := rE13)).
Notation EPost12 := (EPostRel (rE0 := rE12)).
Notation EPost23 := (EPostRel (rE0 := rE23)).
Notation EPost13 := (EPostRel (rE0 := rE13)).

Notation wiequiv_f12 :=
  (wiequiv_f
     (scP1 := scP1) (scP2 := scP2)
     (wc1 := wc1) (wc2:= wc2)
     (wa1 := wa1) (wa2 := wa2)
     (dc1 := dc1) (dc2 := dc2)
     (rE0 := rE12)).
Notation wiequiv_f23 :=
  (wiequiv_f
     (scP1 := scP2) (scP2 := scP3)
     (wc1 := wc2) (wc2:= wc3)
     (wa1 := wa2) (wa2 := wa3)
     (dc1 := dc2) (dc2 := dc3)
     (rE0 := rE23)).
Notation wiequiv_f13 :=
  (wiequiv_f
     (scP1 := scP1) (scP2 := scP3)
     (wc1 := wc1) (wc2:= wc3)
     (wa1 := wa1) (wa2 := wa3)
     (dc1 := dc1) (dc2 := dc3)
     (rE0 := rE13)).

Lemma wiequiv_f_trans p1 p2 p3 ev1 ev2 ev3 fn1 fn2 fn3 rpreF12 rpreF23 rpreF13
  rpostF12 rpostF23 rpostF13 :
  (forall fs1 fs3,
      rpreF13 fn1 fn3 fs1 fs3 ->
      exists2 fs2, rpreF12 fn1 fn2 fs1 fs2 & rpreF23 fn2 fn3 fs2 fs3) ->
  (forall fs1 fs2 fs3 r1 r3,
      rpreF12 fn1 fn2 fs1 fs2 ->
      rpreF23 fn2 fn3 fs2 fs3 ->
      rcompose (rpostF12 fn1 fn2 fs1 fs2) (rpostF23 fn2 fn3 fs2 fs3) r1 r3 ->
      rpostF13 fn1 fn3 fs1 fs3 r1 r3) ->
  wiequiv_f12 p1 p2 ev1 ev2 rpreF12 fn1 fn2 rpostF12 ->
  wiequiv_f23 p2 p3 ev2 ev3 rpreF23 fn2 fn3 rpostF23 ->
  wiequiv_f13 p1 p3 ev1 ev3 rpreF13 fn1 fn3 rpostF13.
Proof.
  move=> hpre hpost h1 h2 fs1 fs3 hpre13.
  have [fs2 hpre12 hpre23] := hpre _ _ hpre13.
  apply xrutt_weaken with
    (errcutoff (is_error wE)) nocutoff (prcompose EPre12 EPre23)
    (pocompose EPre12 EPre23 EPost12 EPost23)
    (rcompose (rpostF12 fn1 fn2 fs1 fs2) (rpostF23 fn2 fn3 fs2 fs3)) => //.
  + move=> T1 T3 e1 e3 [T2 e2]; rewrite /EPreRel.
    case: (mfun1 e1) (mfun1 e2) (mfun1 e3) => [err1 | e0_1] /= [err2 | e0_2] //= [err3 | e0_3] //.
    apply ERpre_trans.
  + move=> T1 T3 e1 t1 e3 t3. rewrite /errcutoff /nocutoff /is_error => herr _ _ hh.
    move=> T2 e2; move: hh; rewrite /EPreRel /EPostRel.
    case: (mfun1 e1) herr => //.
    move=> e0_1 _. case: (mfun1 e2) => //= e0_2.
    case: (mfun1 e3) => //= e0_3.
    by move=> ???; apply ERpost_trans.
  + by move=> r1 r2; apply hpost.
  have := h2 _ _ hpre23; have := h1 _ _ hpre12.
  apply xrutt_facts.xrutt_trans.
  move=> T1 T2 e1 e2 /sum_prerelP h.
  dependent destruction h => /=.
  + by rewrite /errcutoff /= /is_error -x0.
  by rewrite /errcutoff /is_error -x.
Qed.

End TRANSITIVITY.

Notation pre_eq := (rpreF (eS := eq_spec)).
Notation post_eq := (rpostF (eS := eq_spec)).
