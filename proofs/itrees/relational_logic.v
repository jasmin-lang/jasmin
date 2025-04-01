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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import xrutt xrutt_facts.
Require Import expr psem_defs psem oseq compiler_util.
Require Import it_sems_core core_logics hoare_logic.

Definition rel (I1 I2 : Type) := I1 -> I2 -> Prop.

Definition rel_io (I1 I2 O1 O2 : Type) := I1 -> I2 -> O1 -> O2 -> Prop.

Notation relT := (fun _ _ => True).

Notation eq_init i1 i2 := (fun i1' i2' => i1' = i1 /\ i2' = i2).

Section WREQUIV.

Context {Err1 Err2 : Set}.

Definition wrequiv_io {I1 I2 O1 O2}
   (P : rel I1 I2) (F1 : fresult Err1 I1 O1) (F2 : fresult Err2 I2 O2) (Q : rel_io I1 I2 O1 O2) :=
  forall i1 i2 o1, P i1 i2 -> F1 i1 = ok o1 -> exists2 o2, F2 i2 = ok o2 & Q i1 i2 o1 o2.

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

End WREQUIV.

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

Class RelEvent (E0 : Type -> Type) :=
  { RPreInv0_  : prerel E0 E0
  ; RPostInv0_ : postrel E0 E0 }.

Definition RPreInv0 {E0} {rE0 : RelEvent E0} := RPreInv0_.
Definition RPostInv0 {E0} {rE0 : RelEvent E0} := RPostInv0_.

Definition RPreInv {E E0 : Type -> Type} {wE : with_Error E E0} {rE0 : RelEvent E0} : prerel E E :=
  fun T1 T2 (e1 : E T1) (e2 : E T2) =>
    sum_prerel (fun _ _ _ _ => True) RPreInv0 _ _ (mfun1 e1) (mfun1 e2).

Definition RPostInv {E E0 : Type -> Type} {wE : with_Error E E0} {rE0 : RelEvent E0} : postrel E E :=
  fun T1 T2 (e1 : E T1) (t1 : T1) (e2 : E T2) (t2 : T2) =>
    sum_postrel (fun _ _ _ _ _ _ => True) RPostInv0 _ _ (mfun1 e1) t1 (mfun1 e2) t2.

Section WKEQUIV.

Context {E E0: Type -> Type} {wE: with_Error E E0} {rE0 : RelEvent E0}.

Definition wkequiv_io {I1 I2 O1 O2}
   (P : rel I1 I2) (F1 : ktree E I1 O1) (F2 : ktree E I2 O2) (Q : rel_io I1 I2 O1 O2) :=
  forall i1 i2, P i1 i2 ->
  xrutt (errcutoff (is_error wE)) nocutoff RPreInv RPostInv (Q i1 i2) (F1 i1) (F2 i2).

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

Lemma wkequiv_iter (IT1 IT2 T1 T2 : Type) (I : rel IT1 IT2) (Q : rel T1 T2) body1 body2 :
  wkequiv I body1 body2 (sum_rel I Q) ->
  wkequiv I (ITree.iter body1) (ITree.iter body2) Q.
Proof. by move=> hbody i1 i2 hI; apply xrutt_iter with I. Qed.

End WKEQUIV.

Section WKEQUIV_WEAKEN.

Context {E E0: Type -> Type} {wE: with_Error E E0} {rE0 rE0': RelEvent E0}.

Lemma wkequiv_io_weaken {I1 I2 O1 O2} (P P' : rel I1 I2) (Q Q' : rel_io I1 I2 O1 O2) F1 F2 :
  (forall T1 T2 (e1 : E0 T1) (e2 : E0 T2),
    RPreInv0 (rE0:=rE0) e1 e2 -> RPreInv0 (rE0:=rE0') e1 e2) ->
  (forall T1 T2 (e1 : E0 T1) (t1 : T1) (e2 : E0 T2) (t2 : T2),
    RPreInv0 (rE0:=rE0) e1 e2 ->
    RPostInv0 (rE0:=rE0') e1 t1 e2 t2 -> RPostInv0 (rE0:=rE0) e1 t1 e2 t2) ->
  (forall i1 i2, P' i1 i2 -> P i1 i2) ->
  (forall i1 i2 o1 o2, P' i1 i2 -> Q i1 i2 o1 o2 -> Q' i1 i2 o1 o2) ->
  wkequiv_io (rE0:=rE0)  P F1 F2 Q ->
  wkequiv_io (rE0:=rE0') P' F1 F2 Q'.
Proof.
  move=> hpreI hpostI hP'P hQQ' heqv i1 i2 hP'.
  have := heqv _ _ (hP'P _ _ hP').
  apply xrutt_weaken_v2 => //.
  + move=> T1 T2 e1 e2; rewrite /RPreInv.
    by case => {}T1 {}T2 {}e1 {}e2 ?; constructor; auto.
  + move=> T1 T2 e1 t1 e2 t2 _ _; rewrite /RPreInv /RPostInv => h1 h2.
    case: h2 h1 => {}T1 {}T2 {}e1 {}t1 {}e2 {}t2 ?; constructor => //.
    by dependent destruction h1; eauto.
  by move=> o1 o2; apply hQQ'.
Qed.

Lemma wkequiv_weaken {I1 I2 O1 O2} (P P' : rel I1 I2) (Q Q' : rel O1 O2) F1 F2 :
  (forall T1 T2 (e1 : E0 T1) (e2 : E0 T2),
    RPreInv0 (rE0:=rE0) e1 e2 -> RPreInv0 (rE0:=rE0') e1 e2) ->
  (forall T1 T2 (e1 : E0 T1) (t1 : T1) (e2 : E0 T2) (t2 : T2),
    RPreInv0 (rE0:=rE0) e1 e2 ->
    RPostInv0 (rE0:=rE0') e1 t1 e2 t2 -> RPostInv0 (rE0:=rE0) e1 t1 e2 t2) ->
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

Notation estate1 := (estate (wsw:=wsw1) (ep:=ep)).
Notation estate2 := (estate (wsw:=wsw2) (ep:=ep)).

Notation isem_fun1 := (isem_fun (wsw:=wsw1) (dc:=dc1) (ep:=ep) (spp:=spp) (sip:=sip) (pT:=pT1) (scP:= scP1)).
Notation isem_fun2 := (isem_fun (wsw:=wsw2) (dc:=dc2) (ep:=ep) (spp:=spp) (sip:=sip) (pT:=pT2) (scP:= scP2)).

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

Context (spec : EquivSpec) {E0: Type -> Type}.

Definition RPreD {T1 T2} (d1 : recCall T1)
                         (d2 : recCall T2) : Prop :=
  match d1, d2 with
  | RecCall fn1 fs1, RecCall fn2 fs2 => rpreF fn1 fn2 fs1 fs2
  end.

Definition RPostD {T1 T2} (d1 : recCall T1) (t1: T1) (d2 : recCall T2) (t2: T2) : Prop :=
  match d1 in recCall T1_ return T1_ -> T2 -> Prop with
  | RecCall fn1 fs1 =>
    match d2 in recCall T2_ return fstate -> T2_ -> Prop with
    | RecCall fn2 fs2 => rpostF fn1 fn2 fs1 fs2
    end
  end t1 t2.

Instance relEvent_recCall {rE0 : RelEvent E0} : RelEvent (recCall +' E0) :=
  {| RPreInv0_  := sum_prerel (@RPreD) RPreInv0
   ; RPostInv0_ := sum_postrel (@RPostD) RPostInv0
  |}.

End TR_MutualRec.

Section IRESULT.

Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : RelEvent E0}.

Lemma rutt_iresult (T1 T2:Type) (s1 : estate1) (s2 : estate2) (x1 : exec T1) (x2 : exec T2) (R : T1 -> T2 -> Prop) :
  (forall v1, x1 = ok v1 -> exists2 v2, x2 = ok v2 & R v1 v2) ->
  xrutt (errcutoff (is_error wE)) nocutoff RPreInv RPostInv R (iresult s1 x1) (iresult s2 x2).
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

End IRESULT.

Section WEQUIV_CORE.

Context {E E0 : Type -> Type} {sem_F1 : sem_Fun1 E} {sem_F2 : sem_Fun2 E}
    {wE: with_Error E E0} {rE0 : RelEvent E0}.

Context (p1 : prog1) (p2 : prog2) (ev1: extra_val_t1) (ev2 : extra_val_t2).

Notation sem_fun1 := (sem_fun (pT := pT1) (sem_Fun := sem_F1)).
Notation sem_fun2 := (sem_fun (pT := pT2) (sem_Fun := sem_F2)).

Definition wequiv_f (P : relPreF) (fn1 fn2 : funname) (Q:relPostF) :=
  wkequiv_io
    (P fn1 fn2)
      (sem_fun1 p1 ev1 fn1)
      (sem_fun2 p2 ev2 fn2)
    (Q fn1 fn2).

Definition wequiv_f_body (P : relPreF) (fn1 fn2 : funname) (Q:relPostF) :=
  wkequiv_io
    (P fn1 fn2)
      (isem_fun_body (dc:=dc1) (sem_F:=sem_F1) p1 ev1 fn1)
      (isem_fun_body (dc:=dc2) (sem_F:=sem_F2) p2 ev2 fn2)
    (Q fn1 fn2).

Definition wequiv (pre:rel_c) (c1 c2 : cmd) (post : rel_c) :=
  wkequiv
    pre
     (isem_cmd_ (dc:=dc1) (sem_F:=sem_F1) p1 ev1 c1)
     (isem_cmd_ (dc:=dc2) (sem_F:=sem_F2) p2 ev2 c2)
    post.

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

Lemma wequiv_assgn (Rv Rtr: rel_v) (P Q : rel_c) ii1 x1 tg1 ty1 e1 ii2 x2 tg2 ty2 e2 :
  wrequiv P (fun s => sem_pexpr true (p_globs p1) s e1)
           (fun s => sem_pexpr true (p_globs p2) s e2) Rv ->
  (forall s1 s2, P s1 s2 -> wrequiv Rv (truncate_val ty1) (truncate_val ty2) Rtr) ->
  (forall v1 v2, Rtr v1 v2 ->
    wrequiv P (write_lval true (p_globs p1) x1 v1) (write_lval true (p_globs p2) x2 v2) Q) ->
  wequiv P [:: MkI ii1 (Cassgn x1 tg1 ty1 e1)] [:: MkI ii2 (Cassgn x2 tg2 ty2 e2)] Q.
Proof.
  move=> he htr hwr; rewrite /wequiv /isem_cmd_ /=.
  apply wkequiv_bind with Q; last by apply wkequiv_ret.
  apply wkequiv_iresult; rewrite /sem_assgn.
  apply: (wrequiv_read he) => v1 v2 hv.
  apply wrequiv_bind_eval with Rtr.
  + by move=> s1 s2 /htr; apply wrequiv_weaken => // > [-> ->].
  by apply hwr.
Qed.

Lemma wequiv_assgn_eq (P Q : rel_c) ii1 x1 tg1 ty e1 ii2 x2 tg2 e2 :
  wrequiv P (fun s => sem_pexpr true (p_globs p1) s e1)
            (fun s => sem_pexpr true (p_globs p2) s e2) eq ->
  (forall v, wrequiv P (write_lval true (p_globs p1) x1 v) (write_lval true (p_globs p2) x2 v) Q) ->
  wequiv P [:: MkI ii1 (Cassgn x1 tg1 ty e1)] [:: MkI ii2 (Cassgn x2 tg2 ty e2)] Q.
Proof.
  move=> he hx; apply wequiv_assgn with eq eq => //.
  + by move=> *; apply wrequiv_eq.
  by move=> > <-; apply hx.
Qed.

Lemma wequiv_assgn_uincl (P Q : rel_c) ii1 x1 tg1 ty e1 ii2 x2 tg2 e2 :
  wrequiv P (fun s => sem_pexpr true (p_globs p1) s e1)
            (fun s => sem_pexpr true (p_globs p2) s e2) value_uincl ->
  (forall v1 v2, value_uincl v1 v2 ->
    wrequiv P (write_lval true (p_globs p1) x1 v1) (write_lval true (p_globs p2) x2 v2) Q) ->
  wequiv P [:: MkI ii1 (Cassgn x1 tg1 ty e1)] [:: MkI ii2 (Cassgn x2 tg2 ty e2)] Q.
Proof. move=> he; apply wequiv_assgn with value_uincl => // *; apply wrequiv_truncate_val. Qed.

Lemma wequiv_opn (Rve Rvo : rel_vs) P Q ii1 xs1 at1 o1 es1 ii2 xs2 at2 o2 es2 :
  wrequiv P (fun s => sem_pexprs true (p_globs p1) s es1)
            (fun s => sem_pexprs true (p_globs p2) s es2) Rve ->
  (forall s1 s2, P s1 s2 -> wrequiv Rve (exec_sopn o1) (exec_sopn o2) Rvo) ->
  (forall vs1 vs2,
    Rvo vs1 vs2 -> wrequiv P (fun s1 => write_lvals true (p_globs p1) s1 xs1 vs1)
                             (fun s2 => write_lvals true (p_globs p2) s2 xs2 vs2) Q) ->
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

Lemma wequiv_opn_eq P Q ii1 xs1 at1 o es1 ii2 xs2 at2 es2 :
  wrequiv P (fun s => sem_pexprs true (p_globs p1) s es1)
           (fun s => sem_pexprs true (p_globs p2) s es2) eq ->
  (forall vs,
    wrequiv P (fun s1 => write_lvals true (p_globs p1) s1 xs1 vs)
             (fun s2 => write_lvals true (p_globs p2) s2 xs2 vs) Q) ->
  wequiv P [:: MkI ii1 (Copn xs1 at1 o es1)] [:: MkI ii2 (Copn xs2 at2 o es2)] Q.
Proof.
  move=> he hx; apply wequiv_opn with eq eq => //.
  + by move=> *; apply wrequiv_eq.
  by move=> > <-; apply hx.
Qed.

(* FIXME: move this (depends on psem.v) *)
Lemma wrequiv_exec_sopn o :
  wrequiv (Forall2 value_uincl) (exec_sopn o) (exec_sopn o) (Forall2 value_uincl).
Proof. move=> vs1 vs2 vs1'; apply vuincl_exec_opn. Qed.

Lemma wequiv_opn_uincl P Q ii1 xs1 at1 o es1 ii2 xs2 at2 es2 :
  wrequiv P (fun s => sem_pexprs true (p_globs p1) s es1)
           (fun s => sem_pexprs true (p_globs p2) s es2) (Forall2 value_uincl) ->
  (forall vs1 vs2,
    Forall2 value_uincl vs1 vs2 ->
    wrequiv P (fun s1 => write_lvals true (p_globs p1) s1 xs1 vs1)
             (fun s2 => write_lvals true (p_globs p2) s2 xs2 vs2) Q) ->
  wequiv P [:: MkI ii1 (Copn xs1 at1 o es1)] [:: MkI ii2 (Copn xs2 at2 o es2)] Q.
Proof.
  move=> he; apply wequiv_opn with (Forall2 value_uincl) => //.
  move=> *; apply wrequiv_exec_sopn.
Qed.

Lemma wequiv_syscall Rv Ro P Q ii1 xs1 sc1 es1 ii2 xs2 sc2 es2 :
  wrequiv P (fun s => sem_pexprs true (p_globs p1) s es1)
            (fun s => sem_pexprs true (p_globs p2) s es2) Rv ->
  (forall s1 s2, P s1 s2 ->
     wrequiv Rv (fun vs1 => fexec_syscall (scP:=scP1) sc1 (mk_fstate vs1 s1))
                (fun vs2 => fexec_syscall sc2 (mk_fstate vs2 s2)) Ro)->
  (forall fs1 fs2,
    Ro fs1 fs2 ->
    wrequiv P (upd_estate true (p_globs p1) xs1 fs1)
              (upd_estate true (p_globs p2) xs2 fs2) Q) ->
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
  wrequiv P (fun s => sem_pexprs true (p_globs p1) s es1)
            (fun s => sem_pexprs true (p_globs p2) s es2) eq ->
  wrequiv eq (fexec_syscall (scP:=scP1) sc1)
             (fexec_syscall (scP:=scP2) sc2) eq ->
  (forall fs,
    wrequiv P (upd_estate true (p_globs p1) xs1 fs)
              (upd_estate true (p_globs p2) xs2 fs) Q) ->
  wequiv P [:: MkI ii1 (Csyscall xs1 sc1 es1)] [:: MkI ii2 (Csyscall xs2 sc2 es2)] Q.
Proof.
  move=> heq he hsc hx.
  apply wequiv_syscall with eq eq => //.
  + by rewrite /mk_fstate => s1 s2 /heq [<- <-] ?? fs1 <-; apply hsc.
  move=> > <-; apply hx.
Qed.

Definition fs_uincl (fs1 fs2: fstate) :=
  [/\ fs1.(fscs) = fs2.(fscs)
    , fs1.(fmem) = fs2.(fmem)
    & Forall2 value_uincl fs1.(fvals) fs2.(fvals)].

Lemma wequiv_syscall_uincl P Q ii1 xs1 sc1 es1 ii2 sc2 xs2 es2 :
  (forall s1 s2, P s1 s2 -> escs s1 = escs s2 /\ emem s1 = emem s2) ->
  wrequiv P (fun s => sem_pexprs true (p_globs p1) s es1)
           (fun s => sem_pexprs true (p_globs p2) s es2) (Forall2 value_uincl) ->
  wrequiv fs_uincl (fexec_syscall (scP:=scP1) sc1)
                  (fexec_syscall (scP:=scP2) sc2) fs_uincl ->
  (forall fs1 fs2,
    fs_uincl fs1 fs2 ->
    wrequiv P (upd_estate true (p_globs p1) xs1 fs1)
              (upd_estate true (p_globs p2) xs2 fs2) Q) ->
  wequiv P [:: MkI ii1 (Csyscall xs1 sc1 es1)] [:: MkI ii2 (Csyscall xs2 sc2 es2)] Q.
Proof.
  move=> heq he hsc.
  apply wequiv_syscall with (Forall2 value_uincl) => //.
  by rewrite /mk_fstate => s1 s2 /heq [<- <-] vs1 vs2 fr1 huincl;apply hsc.
Qed.

Lemma wequiv_if_full P Q ii1 e1 c1 c1' ii2 e2 c2 c2' :
  wrequiv P (sem_cond (p_globs p1) e1) (sem_cond (p_globs p2) e2) eq ->
  (forall b, wequiv
        (fun s1 s2 => [/\ P s1 s2, sem_cond (p_globs p1) e1 s1 = ok b & sem_cond (p_globs p2) e2 s2 = ok b])
        (if b then c1 else c1')
        (if b then c2 else c2') Q) ->
  wequiv P [:: MkI ii1 (Cif e1 c1 c1')] [:: MkI ii2 (Cif e2 c2 c2')] Q.
Proof.
  move=> he hc; rewrite /wequiv /isem_cmd_ /=.
  apply wkequiv_bind with Q; last by apply wkequiv_ret.
  apply wkequiv_eq_pred => s1 s2 hP.
  eapply wkequiv_read with (fun b1 b2 =>
     [/\ b1 = b2, sem_cond (p_globs p1) e1 s1 = ok b1 & sem_cond (p_globs p2) e2 s2 = ok b2]).
  + apply wkequiv_iresult.
    apply wrequiv_id; apply: wrequiv_weaken he => //.
    by move=> > [-> ->].
  by move=> b b2 [???]; subst b2; apply: wkequiv_weaken (hc b) => // _ _ [-> ->].
Qed.

Lemma wequiv_if P Q ii1 e1 c1 c1' ii2 e2 c2 c2' :
  wrequiv P (sem_cond (p_globs p1) e1) (sem_cond (p_globs p2) e2) eq ->
  (forall b, wequiv P (if b then c1 else c1') (if b then c2 else c2') Q) ->
  wequiv P [:: MkI ii1 (Cif e1 c1 c1')] [:: MkI ii2 (Cif e2 c2 c2')] Q.
Proof.
  move=> hcond hc hc'; apply wequiv_if_full => // b.
  by apply: wequiv_weaken (hc b) => // > [].
Qed.

Lemma sem_cond_uincl P e1 e2 :
  wrequiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s e1)
            (fun (s:estate2) => sem_pexpr true (p_globs p2) s e2) value_uincl ->
  wrequiv P (sem_cond (p_globs p1) e1) (sem_cond (p_globs p2) e2) eq.
Proof.
  move=> he; rewrite /sem_cond.
  apply: wrequiv_bind wrequiv_to_bool; apply he.
Qed.

Lemma wequiv_if_uincl P Q ii1 e1 c1 c1' ii2 e2 c2 c2' :
  wrequiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s e1)
            (fun (s:estate2) => sem_pexpr true (p_globs p2) s e2) value_uincl ->
  (forall b, wequiv P (if b then c1 else c1') (if b then c2 else c2') Q) ->
  wequiv P [:: MkI ii1 (Cif e1 c1 c1')] [:: MkI ii2 (Cif e2 c2 c2')] Q.
Proof. move=> /sem_cond_uincl; apply wequiv_if. Qed.

Lemma wequiv_if_eq P Q ii1 e1 c1 c1' ii2 e2 c2 c2' :
  wrequiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s e1)
           (fun (s:estate2) => sem_pexpr true (p_globs p2) s e2) eq ->
  (forall b, wequiv P (if b then c1 else c1') (if b then c2 else c2') Q) ->
  wequiv P [:: MkI ii1 (Cif e1 c1 c1')] [:: MkI ii2 (Cif e2 c2 c2')] Q.
Proof. by move=> he; apply wequiv_if_uincl; apply: wrequiv_weaken he => // > <-. Qed.

Lemma wequiv_for P Pi ii1 i1 d lo1 hi1 c1 ii2 i2 lo2 hi2 c2 :
  wrequiv P (sem_bound (p_globs p1) lo1 hi1) (sem_bound (p_globs p2) lo2 hi2) eq ->
  (forall i : Z, wrequiv P (write_var true i1 (Vint i)) (write_var true i2 (Vint i)) Pi) ->
  wequiv Pi c1 c2 P ->
  wequiv P [:: MkI ii1 (Cfor i1 (d, lo1, hi1) c1)] [:: MkI ii2 (Cfor i2 (d, lo2, hi2) c2)] P.
Proof.
  move=> hbound hwi hc; rewrite /wequiv /isem_cmd_ /=.
  apply wkequiv_bind with P; last by apply wkequiv_ret.
  apply wkequiv_read with eq.
  + by apply wkequiv_iresult.
  move=> bounds _ <-; elim: wrange => /= [| j js hrec].
  + by apply wkequiv_ret.
  apply wkequiv_bind with Pi.
  + by apply wkequiv_iresult.
  by apply: wkequiv_bind hrec.
Qed.

Lemma wrequiv_sem_bound (P : rel_c) lo1 hi1 lo2 hi2 :
  wrequiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s lo1)
            (fun (s:estate2) => sem_pexpr true (p_globs p2) s lo2) value_uincl ->
  wrequiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s hi1)
            (fun (s:estate2) => sem_pexpr true (p_globs p2) s hi2) value_uincl ->
  wrequiv P (sem_bound (p_globs p1) lo1 hi1) (sem_bound (p_globs p2) lo2 hi2) eq.
Proof.
  move=> hlo hhi; rewrite /sem_bound.
  have h : forall e1 e2,
    wrequiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s e1)
             (fun (s:estate2) => sem_pexpr true (p_globs p2) s e2) value_uincl ->
    wrequiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s e1 >>= to_int)
             (fun (s:estate2) => sem_pexpr true (p_globs p2) s e2 >>= to_int) eq.
  + by move=> e1 e2 he; apply: wrequiv_bind wrequiv_to_int; apply he.
  move=> s1 s2 lh1 hP.
  apply rbindP => vlo /(h _ _ hlo _ _ _ hP) [_ -> <-].
  apply rbindP => vhi /(h _ _ hhi _ _ _ hP) [_ -> <-] [<-] /=; eauto.
Qed.

Lemma wequiv_for_uincl P Pi ii1 i1 d lo1 hi1 c1 ii2 i2 lo2 hi2 c2 :
  wrequiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s lo1)
           (fun (s:estate2) => sem_pexpr true (p_globs p2) s lo2) value_uincl ->
  wrequiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s hi1)
           (fun (s:estate2) => sem_pexpr true (p_globs p2) s hi2) value_uincl ->
  (forall i : Z, wrequiv P (write_var true i1 (Vint i)) (write_var true i2 (Vint i)) Pi) ->
  wequiv Pi c1 c2 P ->
  wequiv P [:: MkI ii1 (Cfor i1 (d, lo1, hi1) c1)] [:: MkI ii2 (Cfor i2 (d, lo2, hi2) c2)] P.
Proof. by move=> hlo hhi; apply/wequiv_for/wrequiv_sem_bound. Qed.

Lemma wequiv_for_eq P Pi ii1 i1 d lo1 hi1 c1 ii2 i2 lo2 hi2 c2 :
  wrequiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s lo1)
           (fun (s:estate2) => sem_pexpr true (p_globs p2) s lo2) eq ->
  wrequiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s hi1)
           (fun (s:estate2) => sem_pexpr true (p_globs p2) s hi2) eq ->
  (forall i : Z, wrequiv P (write_var true i1 (Vint i)) (write_var true i2 (Vint i)) Pi) ->
  wequiv Pi c1 c2 P ->
  wequiv P [:: MkI ii1 (Cfor i1 (d, lo1, hi1) c1)] [:: MkI ii2 (Cfor i2 (d, lo2, hi2) c2)] P.
Proof.
  move=> hlo hhi; apply wequiv_for_uincl.
  + by apply: wrequiv_weaken hlo => // > <-.
  by apply: wrequiv_weaken hhi => // > <-.
Qed.

Lemma wequiv_while_full I I' ii1 al1 e1 inf1 c1 c1' ii2 al2 e2 inf2 c2 c2' :
  wequiv I c1 c2 I' ->
  wrequiv I' (sem_cond (p_globs p1) e1) (sem_cond (p_globs p2) e2) eq ->
  wequiv (fun s1 s2 =>
    [/\ I' s1 s2, sem_cond (p_globs p1) e1 s1 = ok true & sem_cond (p_globs p2) e2 s2 = ok true]) c1' c2' I ->
  wequiv I [:: MkI ii1 (Cwhile al1 c1 e1 inf1 c1')] [:: MkI ii2 (Cwhile al2 c2 e2 inf2 c2')]
     (fun s1 s2 => [/\ I' s1 s2, sem_cond (p_globs p1) e1 s1 = ok false & sem_cond (p_globs p2) e2 s2 = ok false]).
Proof.
  move=> hc hcond hc'; rewrite /wequiv /isem_cmd_ /=.
  set Q := (Q in wkequiv _ _ _ Q).
  apply wkequiv_bind with Q; last by apply wkequiv_ret.
  apply wkequiv_iter with (I := I) => //; rewrite /isem_while_loop.
  apply (wkequiv_bind hc).
  apply wkequiv_eq_pred => s1 s2 hP.
  eapply wkequiv_read with (fun b1 b2 =>
     [/\ b1 = b2, sem_cond (p_globs p1) e1 s1 = ok b1 & sem_cond (p_globs p2) e2 s2 = ok b2]).
  + apply wkequiv_iresult.
    apply wrequiv_id; apply: wrequiv_weaken hcond => //.
    by move=> > [-> ->].
  move=> b b2 [<-]; case: b => ??.
  + apply wkequiv_bind with I.
    + by apply: wkequiv_weaken hc' => // ?? [-> ->].
    by apply wkequiv_ret => *; constructor.
  by apply wkequiv_ret => ?? [-> ->]; constructor.
Qed.

Lemma wequiv_while I I' ii1 al1 e1 c1 inf1 c1' ii2 al2 e2 c2 inf2 c2' :
  wrequiv I' (sem_cond (p_globs p1) e1) (sem_cond (p_globs p2) e2) eq ->
  wequiv I c1 c2 I' ->
  wequiv I' c1' c2' I ->
  wequiv I [:: MkI ii1 (Cwhile al1 c1 e1 inf1 c1')] [:: MkI ii2 (Cwhile al2 c2 e2 inf2 c2')] I'.
Proof.
  move=> hcond hc hc'.
  apply wequiv_weaken with (P2 := I)
    (Q2 := fun s1 s2 =>
      [/\ I' s1 s2, sem_cond (p_globs p1) e1 s1 = ok false & sem_cond (p_globs p2) e2 s2 = ok false]) => //.
  + by move=> > [].
  apply wequiv_while_full => //.
  by apply: wequiv_weaken hc' => // > [].
Qed.

Lemma wequiv_while_uincl I I' ii1 al1 e1 c1 inf1 c1' ii2 al2 e2 c2 inf2 c2' :
  wrequiv I' (fun (s:estate1) => sem_pexpr true (p_globs p1) s e1)
             (fun (s:estate2) => sem_pexpr true (p_globs p2) s e2) value_uincl ->
  wequiv I c1 c2 I' ->
  wequiv I' c1' c2' I ->
  wequiv I [:: MkI ii1 (Cwhile al1 c1 e1 inf1 c1')] [:: MkI ii2 (Cwhile al2 c2 e2 inf2 c2')] I'.
Proof. move=> /sem_cond_uincl; apply wequiv_while. Qed.

Lemma wequiv_while_eq I I' ii1 al1 e1 c1 inf1 c1' ii2 al2 e2 c2 inf2 c2' :
  wrequiv I' (fun (s:estate1) => sem_pexpr true (p_globs p1) s e1)
             (fun (s:estate2) => sem_pexpr true (p_globs p2) s e2) eq ->
  wequiv I c1 c2 I' ->
  wequiv I' c1' c2' I ->
  wequiv I [:: MkI ii1 (Cwhile al1 c1 e1 inf1 c1')] [:: MkI ii2 (Cwhile al2 c2 e2 inf2 c2')] I'.
Proof. by move=> he; apply wequiv_while_uincl; apply: wrequiv_weaken he => // > <-. Qed.

Lemma wequiv_call (Pf : relPreF) (Qf : relPostF) Rv P Q ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  wrequiv P (fun s => sem_pexprs (~~ (@direct_call dc1)) (p_globs p1) s es1)
            (fun s => sem_pexprs (~~ (@direct_call dc2)) (p_globs p2) s es2) Rv ->
  (forall s1 s2 vs1 vs2,
     P s1 s2 -> Rv vs1 vs2 -> Pf fn1 fn2 (mk_fstate vs1 s1) (mk_fstate vs2 s2)) ->
  wequiv_f Pf fn1 fn2 Qf ->
  (forall fs1 fs2 fr1 fr2,
    Pf fn1 fn2 fs1 fs2 -> Qf fn1 fn2 fs1 fs2 fr1 fr2 ->
    wrequiv P (upd_estate (~~ (@direct_call dc1)) (p_globs p1) xs1 fr1)
              (upd_estate (~~ (@direct_call dc2)) (p_globs p2) xs2 fr2) Q) ->
  wequiv P [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] Q.
Proof.
  move=> hes hPPf hCall hPQf; rewrite /wequiv /isem_cmd_ /=.
  apply wkequiv_bind with Q; last by apply wkequiv_ret.
  apply wkequiv_read with Rv.
  + by apply wkequiv_iresult.
  move=> vs1 vs2 hvs.
  apply wkequiv_eq_pred => s1 s2 hP.
  set fs1 := mk_fstate vs1 s1; set fs2 := mk_fstate vs2 s2.
  apply wkequiv_read with (Qf fn1 fn2 fs1 fs2).
  + by move=> _ _ [-> ->]; apply/hCall/hPPf.
  move=> fr1 fr2 hQf; apply wkequiv_iresult.
  eapply wrequiv_weaken; last apply (hPQf fs1 fs2); eauto.
  by move=> ?? [-> ->].
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
          , wequiv P fd1.(f_body) fd2.(f_body) Q
          & wrequiv Q (finalize_funcall (dc:=dc1) fd1) (finalize_funcall (dc:=dc2) fd2) (RPostF fn1 fn2 fs1 fs2)].

Lemma wequiv_fun_body RPreF fn1 fn2 RPostF :
  wequiv_fun_body_hyp RPreF fn1 fn2 RPostF ->
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
  move=> {}/hf [fd2']; rewrite hfd2 => -[?] [P] [Q] hf; subst fd2'.
  apply wkequiv_bind with (fun s1 s2 => [/\ P s1 s2, initialize_funcall (dc:=dc1) p1 ev1 fd1 fs1 = ok s1 &
                                                     initialize_funcall (dc:=dc2) p2 ev2 fd2 fs2 = ok s2]).
  + by apply wkequiv_iresult; apply wrequiv_id => ?? s1 [-> ->] /hf [s2] [*]; exists s2.
  apply wkequiv_eq_pred => s1 s2 [_ + hs2] => {}/hf [s2']; rewrite hs2 => -[] [?] hP hbody hfin; subst s2'.
  apply wkequiv_bind with Q.
  + by apply: wequiv_weaken hbody => // > [-> ->].
  by apply wkequiv_iresult.
Qed.

End WEQUIV_CORE.

Notation sem_fun_full1 := (sem_fun_full (wsw:=wsw1) (dc:=dc1) (ep:=ep) (spp:=spp) (sip:=sip) (pT:=pT1) (scP:= scP1)).
Notation sem_fun_full2 := (sem_fun_full (wsw:=wsw2) (dc:=dc2) (ep:=ep) (spp:=spp) (sip:=sip) (pT:=pT2) (scP:= scP2)).

Notation wiequiv_f := (wequiv_f (sem_F1 := sem_fun_full1) (sem_F2 := sem_fun_full2)).
Notation wiequiv   := (wequiv (sem_F1 := sem_fun_full1) (sem_F2 := sem_fun_full2)).

Section WEQUIV_FUN.

Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : RelEvent E0}.

Context (p1 : prog1) (p2 : prog2) (ev1: extra_val_t1) (ev2 : extra_val_t2)  (spec : EquivSpec).

Definition wequiv_f_rec RPreF fn1 fn2 RPostF :=
  wequiv_f (rE0:=relEvent_recCall spec) p1 p2 ev1 ev2 RPreF fn1 fn2 RPostF.

Definition wequiv_rec P c1 c2 Q :=
  wequiv (rE0:=relEvent_recCall spec) p1 p2 ev1 ev2 P c1 c2 Q.

Definition wequiv_fun_body_hyp_rec (RPreF:relPreF) fn1 fn2 (RPostF:relPostF) :=
  forall fs1 fs2,
  RPreF fn1 fn2 fs1 fs2 ->
  forall fd1, get_fundef (p_funcs p1) fn1 = Some fd1 ->
  exists2 fd2, get_fundef (p_funcs p2) fn2 = Some fd2 &
    exists (P Q : rel_c),
      forall s11, initialize_funcall (dc:=dc1) p1 ev1 fd1 fs1 = ok s11 ->
      exists s21,
        [/\ initialize_funcall (dc:=dc2) p2 ev2 fd2 fs2 = ok s21
          , P s11 s21
          , wequiv_rec P fd1.(f_body) fd2.(f_body) Q
          & wrequiv Q (finalize_funcall (dc:=dc1) fd1) (finalize_funcall (dc:=dc2) fd2) (RPostF fn1 fn2 fs1 fs2)].

Lemma sum_prerelP (E1 E2 D1 D2 : Type -> Type) (PR1 : prerel E1 D1) (PR2 : prerel E2 D2) T1 T2 e1 e2 :
  sum_prerel PR1 PR2 T1 T2 e1 e2 <->
  match e1, e2 with
  | inl1 e1, inl1 e2 => PR1 T1 T2 e1 e2
  | inr1 e1, inr1 e2 => PR2 T1 T2 e1 e2
  | _, _ => False
  end.
Proof.
  split; first by case.
  by case: e1 e2 => // e1 [] e2 //; constructor.
Qed.

Lemma sum_postrelP (E1 E2 D1 D2 : Type -> Type) (PR1 : postrel E1 D1) (PR2 : postrel E2 D2) T1 T2 e1 t1 e2 t2 :
  sum_postrel PR1 PR2 T1 T2 e1 t1 e2 t2 <->
  match e1, e2 with
  | inl1 e1, inl1 e2 => PR1 T1 T2 e1 t1 e2 t2
  | inr1 e1, inr1 e2 => PR2 T1 T2 e1 t1 e2 t2
  | _, _ => False
  end.
Proof.
  split; first by case.
  by case: e1 e2 => // e1 [] e2 //; constructor.
Qed.

#[local]
Lemma xrutt_weaken_aux post (sem1 : itree (recCall +' E) fstate) (sem2 : itree (recCall +' E) fstate) :
  xrutt (errcutoff (is_error (FIso_suml recCall (Err:=ErrEvent)))) nocutoff
    (RPreInv (rE0 := relEvent_recCall spec)) (RPostInv (rE0 := relEvent_recCall spec))
   post sem1 sem2 ->
  xrutt (@EE_MR _ (@errcutoff _ (is_error wE)) recCall)
        (@EE_MR _ nocutoff recCall)
        (sum_prerel (@RPreD spec) RPreInv)
        (sum_postrel (@RPostD spec) RPostInv)
        post sem1 sem2.
Proof.
  apply xrutt_weaken => //.
  + move=> T1 e1; rewrite /errcutoff /= /EE_MR.
    by case: e1 => //= e; rewrite /is_error /=; case: mfun1.
  + move=> T1 T2 e1 e2; rewrite /RPreInv !sum_prerelP.
    case: e1 e2 => [ [fn1 fs1] | e1] [ [fn2 fs2] | e2] //=.
    + by rewrite sum_prerelP.
    + by case : mfun1 => // ?; rewrite sum_prerelP.
    + by case : mfun1 => // ?; rewrite sum_prerelP.
    by case: mfun1 => // ?; case: mfun1 => // ?; rewrite !sum_prerelP.
  move=> T1 T2 e1 t1 e2 t2.
  rewrite /RPostInv !sum_postrelP.
  case: e1 t1 e2 t2 => [ [fn1 fs1] | e1] t1 [ [fn2 fs2] | e2] t2 //=.
  + by rewrite sum_postrelP.
  by case: mfun1 => // ?; case: mfun1 => // ?; rewrite !sum_postrelP.
Qed.

Lemma wequiv_fun_ind :
  ((forall fn1 fn2, wequiv_f_rec rpreF fn1 fn2 rpostF) ->
   (forall fn1 fn2, wequiv_fun_body_hyp_rec rpreF fn1 fn2 rpostF)) ->
  forall fn1 fn2,
  wiequiv_f p1 p2 ev1 ev2 rpreF fn1 fn2 rpostF.
Proof.
  have hrec : (forall fn1 fn2, wequiv_f_rec rpreF fn1 fn2 rpostF).
  + move=> fn1' fn2' fs1' fs2' hpre'; apply xrutt_trigger => //.
    + by constructor; constructor.
    rewrite /RPostInv /= => fr1 fr2 h; dependent destruction h.
    by dependent destruction H.
  move=> /(_ hrec) hbody fn1 fn2 fs1 fs2 hpre.
  apply interp_mrec_xrutt with (RPreInv := (@RPreD spec))
                                         (RPostInv := (@RPostD spec)).
  + move=> {hpre fn1 fn2 fs1 fs2}.
    move=> _ _ [fn1 fs1] [fn2 fs2] hpre.
    have := wequiv_fun_body (hbody fn1 fn2) hpre.
    by apply xrutt_weaken_aux.
  have := wequiv_fun_body (hbody fn1 fn2) hpre.
  apply xrutt_weaken_aux.
Qed.

End WEQUIV_FUN.

Definition eq_spec : EquivSpec :=
  {| rpreF_ := fun (fn1 fn2 : funname) (fs1 fs2 : fstate) => fn1 = fn2 /\ fs1 = fs2
   ; rpostF_ := fun (fn1 fn2 : funname) (fs1 fs2 fr1 fr2: fstate) => fr1 = fr2 |}.

End RELATIONAL.

Notation wiequiv_f := (wequiv_f (sem_F1 := sem_fun_full) (sem_F2 := sem_fun_full)).
Notation wiequiv   := (wequiv (sem_F1 := sem_fun_full) (sem_F2 := sem_fun_full)).


