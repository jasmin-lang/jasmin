From Coq Require Import
  Program 
  Setoid
  Morphisms
  RelationClasses.

From Paco Require Import paco.

From ITree Require Import
  ITree
  ITreeFacts 
  Basics.HeterogeneousRelations 
  Interp.Recursion
  Eq.Paco2
  Events.Exception
  Events.FailFacts
  Eq.Rutt
  Eq.RuttFacts.
 
From mathcomp Require Import ssreflect ssrfun ssrbool.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import expr psem_defs oseq compiler_util.
(* needed for the last lemma *)
Require Import psem. 

Require Import it_sems_core core_logics.


Notation PredT := (fun=>True).

(* Definition of a relational logic over program *)

Class InvEvent (E0 : Type -> Type) :=
  { preInv0_  : prepred E0
  ; postInv0_ : postpred E0 }.

Definition preInv0 {E0} {iE0 : InvEvent E0} := preInv0_.
Definition postInv0 {E0} {iE0 : InvEvent E0} := postInv0_.

Class InvErr :=
  { invErr_ : it_exec.error_data -> Prop }.

Definition invErr {iEr : InvErr} := invErr_.

Definition get_error T (e : ErrEvent T) :=
  match e with
  | Throw e => e
  end.

Definition preInvErr {iEr : InvErr} : prepred ErrEvent :=
  fun T (e : ErrEvent T) => invErr (get_error e).

Definition preInv {E E0: Type -> Type} {wE : with_Error E E0} {iE0 : InvEvent E0} {iEr : InvErr} : prepred E :=
  fun T (e : E T) =>
    match mfun1 e with
    | inl1 err => preInvErr err
    | inr1 e0 => preInv0 e0
    end.

Definition postInv {E E0: Type -> Type} {wE : with_Error E E0} {iE0 : InvEvent E0} : postpred E :=
  fun T (e : E T) (t : T) =>
    match mfun1 e with
    | inl1 err => False (* Errors are void type ... *)
    | inr1 e0 => postInv0 e0 t
    end.


Section TRIVIAL.

Context {E E0: Type -> Type} {wE : with_Error E E0}.

Definition trivial_invEvent (E0 : Type -> Type) : InvEvent E0 :=
  {| preInv0_ := fun _ _ => True
   ; postInv0_ := fun _ _ _ => True |}.

Definition trivial_invErr : InvErr :=
  {| invErr_ := fun _ => True |}.

Lemma preInv_trivial T (e : E T) :
  preInv (iE0:= trivial_invEvent E0) (iEr := trivial_invErr) e.
Proof. by rewrite /preInv; case: mfun1. Qed.

End TRIVIAL.

Section Section.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {asm_op: Type}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {wsw : WithSubWord}
  {scP : semCallParams}
  {dc : DirectCall}.

Definition Pred (T : Type) := T -> Prop.
Definition Pred_io (T1 T2 : Type) := T1 -> T2 -> Prop.

Definition PreF := funname -> Pred fstate.
Definition PostF := funname -> Pred_io fstate fstate.

Definition Pred_e  := Pred pexpr.
Definition Pred_v  := Pred value.
Definition Pred_vs := Pred values.
Definition Pred_c  := Pred estate.
Definition Pred_err := Pred error.

Section TR_MutualRec.

Class HoareSpec :=
  { preF_  : PreF
  ; postF_ : PostF }.

Definition preF {hS : HoareSpec} := preF_.
Definition postF {hS : HoareSpec} := postF_.

Context (spec : HoareSpec) {E0: Type -> Type}.

Definition preD T (d : recCall T) : Prop :=
  match d with
  | RecCall fn fs => preF fn fs
  end.

Definition postD T (d : recCall T) (t: T) : Prop :=
  match d in recCall T_ return T_ -> Prop with
  | RecCall fn fs => postF fn fs
  end t.

Definition invEvent_recCall {iE0 : InvEvent E0} : InvEvent (recCall +' E0) :=
  {| preInv0_  := sum_prepred (@preD) preInv0
   ; postInv0_ := sum_postpred (@postD) postInv0
  |}.

End TR_MutualRec.

Section RHOARE.

Definition fresult (Err : Set) T1 T2 := T1 -> result Err T2.

Context {Err : Set}.

(* P : precondition
   Q : postcondition
   QE : postcondition for error *)

Definition rhoare_io {I O}
   (P : Pred I) (F : fresult Err I O) (Q : Pred_io I O) (QE : I -> Pred Err) :=
  forall i, P i ->
    match F i with
    | Ok o => Q i o
    | Error e => QE i e
    end.

Definition rhoare {I O} (P : Pred I) (F : fresult Err I O) (Q : Pred O) (QE : Pred Err) :=
  rhoare_io P F (fun _ => Q) (fun _ => QE).

Lemma rhoare_ioP {I O} (P : Pred I) (F : fresult Err I O) (Q : Pred_io I O) (QE : I -> Pred Err) :
  rhoare_io P F Q QE <-> (forall i0, P i0 -> rhoare (fun i => i = i0) F (Q i0) (QE i0)).
Proof.
  split.
  + by move=> h i0 hP i ?; subst i0; have := h _ hP.
  by move=> h i hP; apply (h i hP i).
Qed.

Lemma rhoare_io_weaken {I O} (F : fresult Err I O)
  (P P' : Pred I) (Q Q': Pred_io I O) (QE QE' : I -> Pred Err) :
  (forall i, P' i -> P i) ->
  (forall i o, P' i -> Q i o -> Q' i o) ->
  (forall i e, P' i -> QE i e -> QE' i e) ->
  rhoare_io P F Q QE ->
  rhoare_io P' F Q' QE'.
Proof.
  move=> hP'P hQQ' hEE' hhoare i hP'.
  case: (F i) (hhoare i (hP'P i hP')).
  + by move=> o; apply hQQ'.
  by move=> e; apply hEE'.
Qed.

Lemma rhoare_weaken {I O} (F : fresult Err I O) (P P' : Pred I) (Q Q': Pred O) (QE QE' : Pred Err) :
  (forall i, P' i -> P i) ->
  (forall o, Q o -> Q' o) ->
  (forall e, QE e -> QE' e) ->
  rhoare P F Q QE ->
  rhoare P' F Q' QE'.
Proof. move=> hP hQQ' hEE'; apply rhoare_io_weaken => // > ?; auto. Qed.

Lemma rhoare_true {I O} P (F : fresult Err I O) : rhoare P F PredT PredT.
Proof. by move=> ??; case: F. Qed.

Lemma rhoare_false {I O} (F : fresult Err I O) Q Qerr : rhoare (fun=>False) F Q Qerr.
Proof. by move=> ?. Qed.

Lemma wrhoareP {I O} P (F : fresult Err I O) Q :
  rhoare P F Q PredT <->
  (forall i o, P i -> F i = ok o -> Q o).
Proof.
  rewrite /rhoare /rhoare_io; split => h i; have {h}:= h i; case : (F i) => //.
  + by move=> ? h ?? [<-]; auto.
  by move=> ? h /h -/(_ _ erefl).
Qed.

Lemma rhoare_ok {T} (P Q : Pred T) (QE : Pred Err) :
  (forall t, P t -> Q t) ->
  rhoare P (fun t => ok t) Q QE.
Proof. done. Qed.

Lemma rhoare_err {T} (P Q : Pred T) (QE : Pred Err) e:
  (forall i, P i -> QE e) <-> rhoare P (fun i => Error e) Q QE.
Proof. done. Qed.

Lemma rhoare_bind {I T O} (F1 : fresult Err I T) (F2 : fresult Err T O)
  (P : Pred I) (R : Pred T) (Q : Pred O) (QE : Pred Err) (QET : Pred Err) :
  (forall i t e , P i -> R t -> QET e -> QE e) ->
  rhoare P F1 R QE ->
  rhoare R F2 Q QET ->
  rhoare P (fun i => Let r := F1 i in F2 r) Q QE.
Proof.
  move=> hQE hF1 hF2 i hP.
  case: (F1 i) (hF1 i hP) => //=.
  move=> t hR; case: (F2 t) (hF2 t hR) => //=.
  by move=> e; apply: hQE hP hR.
Qed.

Lemma rhoare_read {S T O} (F1 : fresult Err S T) (F2 : T -> fresult Err S O)
  (P : Pred S) (R : Pred T) (Q : Pred O) (QE : Pred Err) :
  rhoare P F1 R QE ->
  (forall t, R t -> rhoare P (F2 t) Q QE) ->
  rhoare P (fun s => Let r := F1 s in F2 r s) Q QE.
Proof.
  move=> hF1 hF2 s hP.
  case: (F1 s) (hF1 s hP) => //=.
  move=> t hR; case: (F2 t s) (hF2 t hR s hP) => //=.
Qed.

Lemma rhoare_bind_eval {S I T O} (F1 : fresult Err I T) (F2 : T -> fresult Err S O)
  (P : Pred S) (R : Pred T) (Q : Pred O) (QE : Pred Err) i :
  (forall s, P s -> rhoare (fun i' => i' = i) F1 R QE) ->
  (forall t, R t -> rhoare P (F2 t) Q QE) ->
  rhoare P (fun s => Let r := F1 i in F2 r s) Q QE.
Proof.
  move=> hF1 hF2 s hP.
  case: (F1 i) (hF1 s hP i erefl) => //=.
  move=> t hR; case: (F2 t s) (hF2 t hR s hP) => //=.
Qed.

Lemma rhoare_eval {S I O} (F : fresult Err I O)
  (P : Pred S) (Q : Pred O) (QE : Pred Err) i :
  (forall s, P s -> rhoare (fun i' => i' = i) F Q QE) ->
  rhoare P (fun s => F i) Q QE.
Proof. by move=> hF s hP; case: (F i) (hF s hP i erefl). Qed.

Lemma rhoare_write {S O} (F1 : fresult Err S S) (F2 : fresult Err S O)
  (P R : Pred S) (Q : Pred O) (QE : Pred Err) :
  rhoare P F1 R QE ->
  rhoare R F2 Q QE ->
  rhoare P (fun s => Let s := F1 s in F2 s) Q QE.
Proof. by move=> hF1 hF2 s hP; case: (F1 s) (hF1 s hP). Qed.

Lemma rhoare_id {I O} (F : fresult Err I O) i0 (P : Pred I) (QE : Pred Err):
  rhoare (fun i => i = i0 /\ P i) F (fun=> True) QE ->
  rhoare (fun i => i = i0 /\ P i) F (fun o => F i0 = ok o) QE.
Proof. by move=> h i hP; have := h i hP; case: hP => ? _; subst i0; case: (F i). Qed.

End RHOARE.

Section KHOARE.

Context {E E0: Type -> Type} {wE: with_Error E E0} {iE0 : InvEvent E0} {iEr : InvErr}.

Definition khoare_io {I O}
   (P : Pred I) (F : ktree E I O) (Q : Pred_io I O) :=
  forall i, P i -> lutt preInv postInv (Q i) (F i).

Definition khoare {I O} (P : Pred I) (F : ktree E I O) (Q : Pred O) :=
  khoare_io P F (fun i => Q).

(* Remark: in pratice khoare_io and khoare are equivalent *)
Lemma khoare_ioP {I O} (P : Pred I) (F : ktree E I O) (Q : Pred_io I O) :
  khoare_io P F Q <-> (forall i0, P i0 -> khoare (fun i => i = i0) F (Q i0)).
Proof.
  split.
  + by move=> h i0 hP i ?; subst i0; have := h _ hP.
  by move=> h i hP; apply (h i hP i).
Qed.

Lemma khoare_io_ret {I O} (P: Pred I) (f : I -> O) (Q : Pred_io I O) :
  (forall i, P i -> Q i (f i)) ->
  khoare_io P (fun i => ret (f i)) Q.
Proof. by move=> hPQ i hP; rewrite -lutt_Ret; apply hPQ. Qed.

Lemma khoare_ret {I O} (P : Pred I) (f : I -> O) (Q : Pred O) :
  (forall i, P i -> Q (f i)) ->
  khoare P (fun i => ret (f i)) Q.
Proof. by apply khoare_io_ret. Qed.

Lemma khoare_io_bind {I T O}
  (R : Pred_io I T)
  (P : Pred I)
  (Q : Pred_io I O) F F' :
  khoare_io P F R ->
  (forall i, P i -> khoare (R i) F' (Q i)) ->
  khoare_io P (fun i => t <- F i;; F' t) Q.
Proof.
  move=> h h' i hP.
  apply lutt_bind with (R i); first by apply h.
  by move=> t hR; apply h'.
Qed.

Lemma khoare_bind {I T O}
  (R : Pred T)
  (P : Pred I)
  (Q : Pred O) F F' :
  khoare P F R ->
  khoare R F' Q ->
  khoare P (fun i => t <- F i;; F' t) Q.
Proof. by move=> h h'; apply khoare_io_bind with (R := fun t => R). Qed.

Definition rInvErr := fun s e => invErr (mk_error_data s e).

Lemma khoare_io_iresult (T : Type) F (P : Pred_c) (Q: Pred_io estate T) :
  rhoare_io P F Q rInvErr ->
  khoare_io P (fun s => iresult s (F s)) Q.
Proof.
  move=> hr s hP; have := hr s hP.
  case: (F s) => [v | e] hQ.
  + by apply lutt_Ret.
  apply lutt_Vis => //=.
  by rewrite /preInv /= /subevent /= /resum /= /fromErr mid12.
Qed.

Lemma khoare_iresult (T : Type) F (P : Pred_c) (Q: Pred T) (Qerr: Pred error) :
  (forall s e, P s -> Qerr e -> rInvErr s e) ->
  rhoare P F Q Qerr ->
  khoare P (fun s => iresult s (F s)) Q.
Proof.
  move=> herr hF; apply khoare_io_iresult.
  apply rhoare_io_weaken with P (fun=> Q) (fun _ e => Qerr e) => //.
Qed.

Lemma khoare_read {S T O} (F1 : ktree E S T) (F2 : T -> ktree E S O)
  (P : Pred S) (R : Pred T) (Q : Pred O) :
  khoare P F1 R ->
  (forall t, R t -> khoare P (F2 t) Q) ->
  khoare P (fun s => r <- F1 s ;; F2 r s) Q.
Proof.
  move=> hF1 hF2 s hP.
  eapply lutt_bind; eauto.
  by move=> t hR; apply hF2.
Qed.

Lemma khoare_eval {S I T O} (F1 : ktree E I T) (F2 : T -> ktree E S O)
  (P : Pred S) (R : Pred T) (Q : Pred O) i :
  (forall s, P s -> khoare (fun i' => i' = i) F1 R) ->
  (forall t, R t -> khoare P (F2 t) Q) ->
  khoare P (fun s => r <- F1 i ;; F2 r s) Q.
Proof.
  move=> hF1 hF2 s hP.
  eapply lutt_bind.
  + by apply (hF1 _ hP i erefl).
  by move=> t hR; apply hF2.
Qed.

(* Dead we really want this? or
   (forall i0, P i0 -> khoare (fun i => i = i0) F Q) *)
Lemma khoare_eq_pred {I O} (F : ktree E I O) (P : Pred I) (Q : Pred O) :
  (forall i0, khoare (fun i => i = i0 /\ P i) F Q) ->
  khoare P F Q.
Proof. by move=> h i0 hP; apply (h i0 i0). Qed.

Lemma khoare_iter (IT T : Type) (I : Pred IT) (Q : Pred T) (body : ktree E IT (IT + T)) :
  khoare I body (sum_pred I Q) ->
  khoare I (ITree.iter body) Q.
Proof. move=> hbody i hI; apply: lutt_iter hI => {}i; apply hbody. Qed.

End KHOARE.

Lemma khoare_io_true {E E0: Type -> Type} {wE: with_Error E E0} {I O} (P: Pred I) (F : ktree E I O) :
  khoare_io (iE0 := trivial_invEvent E0) (iEr := trivial_invErr) P F (fun _ _ => True).
Proof.
  move=> i _; apply: lutt_weaken (lutt_true (F i)) => //.
  move=> ?? _; apply preInv_trivial.
Qed.

Section KHOARE_WEAKEN.

Context {E E0: Type -> Type} {wE: with_Error E E0} {iE0 iE0': InvEvent E0} {iEr iEr': InvErr}.

Lemma khoare_io_weaken {I O} (P P' : Pred I) (Q Q': Pred_io I O) F :
  (forall (T : Type) (e : E0 T), preInv0 (iE0:=iE0) e -> preInv0 (iE0:=iE0') e) ->
  (forall (T : Type) (e : E0 T) (t : T), preInv0 (iE0:=iE0) e -> postInv0 (iE0:=iE0') e t -> postInv0 (iE0:=iE0) e t) ->
  (forall e, invErr (iEr:=iEr) e -> invErr (iEr:=iEr') e) ->
  (forall i, P' i -> P i) ->
  (forall i o, P' i -> Q i o -> Q' i o) ->
  khoare_io (iE0:=iE0) (iEr:=iEr) P F Q ->
  khoare_io (iE0:=iE0') (iEr:=iEr') P' F Q'.
Proof.
  move=> hpreI hpostI heI hP'P hQQ' heqv i hP'.
  apply lutt_weaken with (preInv (iE0:=iE0) (iEr:=iEr)) (postInv (iE0:=iE0)) (Q i); auto.
  + by move=> T e; rewrite /preInv; case: mfun1; rewrite /preInvErr; auto.
  by move=> T e; rewrite /preInv /postInv; case: mfun1; auto.
Qed.

Lemma khoare_weaken {I O} (P P' : Pred I) (Q Q': Pred O) F :
  (forall (T : Type) (e : E0 T), preInv0 (iE0:=iE0) e -> preInv0 (iE0:=iE0') e) ->
  (forall (T : Type) (e : E0 T) (t : T), preInv0 (iE0:=iE0) e -> postInv0 (iE0:=iE0') e t -> postInv0 (iE0:=iE0) e t) ->
  (forall e, invErr (iEr:=iEr) e -> invErr (iEr:=iEr') e) ->
  (forall i, P' i -> P i) ->
  (forall o, Q o -> Q' o) ->
  khoare (iE0:=iE0) (iEr:=iEr) P F Q ->
  khoare (iE0:=iE0') (iEr:=iEr') P' F Q'.
Proof. move=> ??? hP hQ; apply khoare_io_weaken => // > _; apply hQ. Qed.

End KHOARE_WEAKEN.

Section HOARE_CORE.

Context {E E0: Type -> Type}  {sem_F : sem_Fun E} {wE: with_Error E E0} {iE0 : InvEvent E0} {iEr : InvErr}.

Context (p : prog) (ev: extra_val_t).

Definition hoare_f (P : PreF) (fn : funname) (Q: PostF) :=
  khoare_io (P fn) (sem_fun p ev fn) (Q fn).

Definition hoare_f_body (P : PreF) (fn : funname) (Q:PostF) :=
  khoare_io (P fn) (isem_fun_body p ev fn) (Q fn).

Definition hoare_io (P : Pred_c) (c : cmd) (Q : Pred_io estate estate) :=
  khoare_io P (isem_cmd_ p ev c) Q.

Definition hoare (P : Pred_c) (c : cmd) (Q : Pred_c) :=
  khoare P (isem_cmd_ p ev c) Q.

(* Since hoare_io and hoare are equivalent we will only focus on hoare *)
Lemma hoare_ioP P c Q :
  hoare_io P c Q <-> (forall s0, P s0 -> hoare (fun s => s = s0) c (Q s0)).
Proof. apply khoare_ioP. Qed.

Lemma hoareP P c Q :
  hoare P c Q <-> (forall s0, P s0 -> hoare (fun s => s = s0) c Q).
Proof. apply hoare_ioP. Qed.

(* FIXME allow to weaken the inv *)
Lemma hoare_weaken1 P1 P2 Q1 Q2 c :
  (forall s, P1 s -> P2 s) ->
  (forall s, Q2 s -> Q1 s) ->
  hoare P2 c Q2 ->
  hoare P1 c Q1.
Proof. by apply khoare_weaken. Qed.

Lemma hoare_cat (R P Q : Pred_c) (c c' : cmd) :
  hoare P c R ->
  hoare R c' Q ->
  hoare P (c ++ c') Q.
Proof.
  move=> h h' s hP ; rewrite isem_cmd_cat.
  apply lutt_bind with R => //.
  by apply h.
Qed.

Lemma hoare_skip P Q : (forall s, P s -> Q s) -> hoare P [::] Q.
Proof. apply khoare_ret. Qed.

Lemma hoare_cons (R P Q : Pred_c) (i : instr) (c : cmd) :
  hoare P [::i] R ->
  hoare R c Q ->
  hoare P (i :: c) Q.
Proof. rewrite -(cat1s i c); apply hoare_cat. Qed.

Lemma hoare_assgn (Rv Rtr: Pred_v) (P Q : Pred_c) (Qerr : Pred_err) ii x tg ty e :
  (forall s e, P s -> Qerr e -> rInvErr s e) ->
  rhoare P (fun s => sem_pexpr true (p_globs p) s e) Rv Qerr ->
  (forall s, P s -> rhoare Rv (truncate_val ty) Rtr Qerr) ->
  (forall v, Rtr v -> rhoare P (write_lval true (p_globs p) x v) Q Qerr) ->
  hoare P [:: MkI ii (Cassgn x tg ty e)] Q.
Proof.
  move=> herr he htr hwr; rewrite /hoare /isem_cmd_ /=.
  apply khoare_bind with Q; last by apply khoare_ret.
  apply (khoare_iresult herr); rewrite /sem_assgn.
  apply: (rhoare_read he) => v hv.
  apply rhoare_bind_eval with Rtr.
  + by move=> s /htr; apply rhoare_weaken => // > ->.
  apply hwr.
Qed.

Lemma hoare_opn (Rve Rvo : Pred_vs) P Q Qerr ii xs tag o es :
  (forall s e, P s -> Qerr e -> rInvErr s e) ->
  rhoare P (fun s => sem_pexprs true (p_globs p) s es) Rve Qerr ->
  (forall s, P s -> rhoare Rve (exec_sopn o) Rvo Qerr) ->
  (forall vs, Rvo vs -> rhoare P (fun s => write_lvals true (p_globs p) s xs vs) Q Qerr) ->
  hoare P [:: MkI ii (Copn xs tag o es)] Q.
Proof.
  move=> herr he ho hwr; rewrite /hoare /isem_cmd_ /=.
  apply khoare_bind with Q; last by apply khoare_ret.
  apply: (khoare_iresult herr); rewrite /sem_sopn.
  eapply rhoare_read.
  + eapply rhoare_read; first apply he.
    move=> t ht; eapply rhoare_eval.
    move=> s /ho; apply rhoare_weaken; last done.
    + by move=> > ->.
    by move=> > h; apply h.
  by apply hwr.
Qed.

Lemma hoare_syscall Rv Ro P Q Qerr ii xs sc es :
  (forall s e, P s -> Qerr e -> rInvErr s e) ->
  rhoare P (fun s => sem_pexprs true (p_globs p) s es) Rv Qerr ->
  (forall s, P s ->
     rhoare Rv (fun vs => fexec_syscall sc (mk_fstate vs s)) Ro Qerr) ->
  (forall fs, Ro fs ->
     rhoare P (upd_estate true (p_globs p) xs fs) Q Qerr) ->
  hoare P [:: MkI ii (Csyscall xs sc es)] Q.
Proof.
  move=> herr he ho hwr; rewrite /hoare /isem_cmd_ /=.
  apply khoare_bind with Q; last by apply khoare_ret.
  apply: (khoare_iresult herr); rewrite /sem_syscall.
  apply (rhoare_read he).
  move=> t ht; eapply rhoare_read; last by apply hwr.
  move=> s hP; apply (ho s hP _ ht).
Qed.

Lemma hoare_if_full P Q Qerr ii e c c' :
  (forall s e, P s -> Qerr e -> rInvErr s e) ->
  rhoare P (sem_cond (p_globs p) e) (fun _ => True) Qerr ->
  (forall b,
     hoare (fun s => P s /\ sem_cond (p_globs p) e s = ok b) (if b then c else c') Q) ->
  hoare P [:: MkI ii (Cif e c c')] Q.
Proof.
  move=> herr he hc; rewrite /hoare /isem_cmd_ /=.
  apply khoare_bind with Q; last by apply khoare_ret.
  apply khoare_eq_pred => s0.
  apply khoare_read with (fun b => sem_cond (p_globs p) e s0 = ok b).
  + rewrite /isem_cond; apply khoare_iresult with Qerr.
    + by move=> ?? []; auto.
    by apply rhoare_id; apply: rhoare_weaken he => // > [].
  by move=> b hb; apply: khoare_weaken (hc b) => // s [->].
Qed.

Lemma hoare_if P Q Qerr ii e c c' :
  (forall s e, P s -> Qerr e -> rInvErr s e) ->
  rhoare P (sem_cond (p_globs p) e) (fun _ => True) Qerr ->
  (forall b, hoare P (if b then c else c') Q) ->
  hoare P [:: MkI ii (Cif e c c')] Q.
Proof.
  move=> herr he hc; apply (hoare_if_full (Qerr:=Qerr)) => //.
  by move=> b; apply: hoare_weaken1 (hc b) => // s [].
Qed.

Lemma hoare_for_full P Pb Pi Qerr ii i d lo hi c :
  (forall s e, P s -> Qerr e -> rInvErr s e) ->
  rhoare P (sem_bound (p_globs p) lo hi) Pb Qerr ->
  (forall bounds (j:Z),
    Pb bounds ->
    (* FIXME : j \in (wrange d bounds.1 bounds.2) *)
    List.In j (wrange d bounds.1 bounds.2) ->
    rhoare P (write_var true i (Vint j)) Pi Qerr) ->
  hoare Pi c P ->
  hoare P [:: MkI ii (Cfor i (d, lo, hi) c)] P.
Proof.
  move=> herr hbound hwi hc; rewrite /hoare /isem_cmd_ /=.
  apply khoare_bind with P; last by apply khoare_ret.
  apply khoare_read with Pb.
  + by apply (khoare_iresult herr).
  move=> bounds {}/hwi; elim (wrange _ _) => /= [ | j js hrec] hwi.
  + by apply khoare_ret.
  eapply khoare_bind.
  + by apply (khoare_iresult herr); apply hwi; left.
  by apply: (khoare_bind hc); apply hrec => z hz; apply hwi; right.
Qed.

Lemma hoare_for P Pi Qerr ii i d lo hi c :
  (forall s e, P s -> Qerr e -> rInvErr s e) ->
  rhoare P (sem_bound (p_globs p) lo hi) (fun _ => True) Qerr ->
  (forall (j:Z), rhoare P (write_var true i (Vint j)) Pi Qerr) ->
  hoare Pi c P ->
  hoare P [:: MkI ii (Cfor i (d, lo, hi) c)] P.
Proof.
  move=> herr hbound hwi.
  apply: (hoare_for_full ii herr hbound) => _ j _ _; apply hwi.
Qed.

Lemma hoare_while_full I I' Qerr ii al e inf c c' :
  (forall s e, I' s -> Qerr e -> rInvErr s e) ->
  hoare I c I' ->
  rhoare I' (sem_cond (p_globs p) e) (fun _ => True) Qerr  ->
  hoare (fun s => I' s /\ sem_cond (p_globs p) e s = ok true) c' I ->
  hoare I [:: MkI ii (Cwhile al c e inf c')]
     (fun s => I' s /\ sem_cond (p_globs p) e s = ok false).
Proof.
  move=> herr hc he hc'; rewrite /hoare /isem_cmd_ /=.
  set Q := (Q in khoare _ _ Q).
  apply khoare_bind with Q; last by move=> >; apply: khoare_ret.
  apply khoare_iter.
  apply: (khoare_bind hc).
  apply khoare_eq_pred => s0.
  apply khoare_read with (fun b => sem_cond (p_globs p) e s0 = ok b).
  + apply khoare_iresult with Qerr.
    + by move=> > []; auto.
    by apply rhoare_id; apply: rhoare_weaken he => // > [].
  move=> [] hb; last first.
  + by apply khoare_ret => _ [-> ?]; constructor.
  apply khoare_bind with I.
  + by apply: khoare_weaken hc' => // _ [-> ?].
  by apply khoare_ret.
Qed.

Lemma hoare_while I I' Qerr ii al e inf c c' :
  (forall s e, I' s -> Qerr e -> rInvErr s e) ->
  hoare I c I' ->
  rhoare I' (sem_cond (p_globs p) e) (fun _ => True) Qerr  ->
  hoare I' c' I ->
  hoare I [:: MkI ii (Cwhile al c e inf c')] I'.
Proof.
  move=> herr hc hcond hc'.
  apply hoare_weaken1 with I (fun s => I' s /\ sem_cond (p_globs p) e s = ok false) => //.
  + by move=> ? [].
  apply hoare_while_full with Qerr => //.
  by apply: hoare_weaken1 hc' => // ? [].
Qed.

Lemma hoare_call (Pf : PreF) (Qf : PostF) Rv P Q Qerr ii xs fn es :
  (forall s e, P s -> Qerr e -> rInvErr s e) ->
  rhoare P (fun s => sem_pexprs (~~ direct_call) (p_globs p) s es) Rv Qerr ->
  (forall s vs, P s -> Rv vs -> Pf fn (mk_fstate vs s)) ->
  hoare_f Pf fn Qf ->
  (forall fs fr,
    Pf fn fs -> Qf fn fs fr ->
    rhoare P (upd_estate (~~ direct_call) (p_globs p) xs fr) Q Qerr) ->
  hoare P [:: MkI ii (Ccall xs fn es)] Q.
Proof.
  move=> herr hes hPPf hCall hPQf; rewrite /hoare /isem_cmd_ /=.
  apply khoare_bind with Q; last by apply khoare_ret.
  apply khoare_read with Rv.
  + by apply (khoare_iresult herr) => >; apply: hes.
  move=> vs hvs; apply khoare_eq_pred => s0.
  set (fs := mk_fstate vs s0).
  apply khoare_read with (Qf fn fs).
  + by move=> _ [-> hP]; apply/hCall/hPPf.
  move=> fr hQf; apply khoare_iresult with Qerr.
  + by move=> > []; auto.
  move=> _ [-> hP]; apply (hPQf fs fr) => //.
  by apply hPPf.
Qed.

Definition hoare_fun_body_hyp (Pf : PreF) fn (Qf : PostF) Qerr :=
  forall fs,
  Pf fn fs ->
  (forall e, Qerr e -> rInvErr (estate0 fs) e) /\
  match get_fundef (p_funcs p) fn with
  | None => Qerr ErrType
  | Some fd =>
    exists (P Q : Pred_c),
      [/\ rhoare (Pf fn) (initialize_funcall p ev fd) P Qerr
        , hoare P fd.(f_body) Q
        , (forall s e, Q s -> Qerr e -> rInvErr (estate0 fs) e)
        & rhoare Q (finalize_funcall fd) (Qf fn fs) Qerr]
  end.

Lemma preInv_Throw e : preInv (subevent void (Throw e)) = invErr e.
Proof. by rewrite /preInv /subevent /resum /fromErr mid12. Qed.

Lemma hoare_fun_body Pf fn Qf Qerr :
  hoare_fun_body_hyp Pf fn Qf Qerr ->
  hoare_f_body Pf fn Qf.
Proof.
  move=> hf; rewrite /hoare_f_body /isem_fun_body.
  apply khoare_ioP => fs hPf; have [herr {}hf] := hf _ hPf.
  apply khoare_read with (fun fd => get_fundef (p_funcs p) fn = Some fd).
  + rewrite /kget_fundef => ??.
    case: get_fundef hf => /= [fd | ] h; [apply lutt_Ret | apply lutt_Vis] => //.
    by rewrite preInv_Throw; apply herr.
  move=> fd hfd; move: hf; rewrite hfd => -[P] [Q] [hinit hbody hQerr hfin].
  apply khoare_bind with P.
  + move=> _ ->; have := hinit _ hPf.
    case: initialize_funcall => [s | e] h; [apply lutt_Ret | apply lutt_Vis] => //.
    by rewrite preInv_Throw; apply herr.
  by apply: (khoare_bind hbody); apply (khoare_iresult hQerr).
Qed.

End HOARE_CORE.

Section TRIVIAL.

Context {E E0: Type -> Type}  {sem_F : sem_Fun E} {wE: with_Error E E0}.

Context (p : prog) (ev: extra_val_t).

#[local] Existing Instance trivial_invErr.
#[local] Existing Instance trivial_invEvent.

Lemma hoare_f_true (P : PreF) (fn : funname) : hoare_f p ev P fn (fun _ _ _ => True).
Proof. apply khoare_io_true. Qed.

Lemma hoare_f_body_true (P : PreF) (fn : funname) : hoare_f_body p ev P fn (fun _ _ _ => True).
Proof. apply khoare_io_true. Qed.

Lemma hoare_io_true (P : Pred_c) (c : cmd) : hoare_io p ev P c (fun _ _ => True).
Proof. apply khoare_io_true. Qed.

Lemma hoare_true (P : Pred_c) (c : cmd) : hoare p ev P c PredT.
Proof. apply khoare_io_true. Qed.

End TRIVIAL.

Notation ihoare_f := (hoare_f (sem_F := sem_fun_full)).
Notation ihoare   := (hoare (sem_F := sem_fun_full)).

Section HOARE_FUN.

Context {E E0: Type -> Type} {wE: with_Error E E0} {iE0 : InvEvent E0} {iEr : InvErr}.

Context (p : prog) (ev: extra_val_t) (spec : HoareSpec).

Definition hoare_f_rec Pf fn Qf :=
  hoare_f (iE0 := invEvent_recCall spec) p ev Pf fn Qf.

Definition hoare_rec P c Q :=
  hoare (iE0 := invEvent_recCall spec) p ev P c Q.

Definition hoare_fun_body_hyp_rec Pf fn Qf Qerr :=
  forall fs,
  Pf fn fs ->
  (forall e, Qerr e -> rInvErr (estate0 fs) e) /\
  match get_fundef (p_funcs p) fn with
  | None => Qerr ErrType
  | Some fd =>
    exists (P Q : Pred_c),
      [/\ rhoare (Pf fn) (initialize_funcall p ev fd) P Qerr
        , hoare_rec P fd.(f_body) Q
        , (forall s e, Q s -> Qerr e -> rInvErr (estate0 fs) e)
        & rhoare Q (finalize_funcall fd) (Qf fn fs) Qerr]
  end.

Lemma weak_pre  (T : Type) (e : (recCall +' E) T) :
  preInv (iE0 := invEvent_recCall spec) e ->
  sum_prepred (preD spec) preInv e.
Proof.
  rewrite /preInv /=.
  case: e => [[fn fs] | e] /= h; constructor.
  + by dependent destruction h.
  move: h; case: mfun1 => //.
  by move=> e0 h; dependent destruction h.
Qed.

Lemma weak_post (T : Type) (e : (recCall +' E) T) (t : T) :
  preInv (iE0 := invEvent_recCall spec) e ->
  sum_postpred (postD spec) postInv  e t ->
  postInv (iE0 := invEvent_recCall spec) e t.
Proof.
  move=> _; case: e t => [[fn fs] fr | e t] h; dependent destruction h; rewrite /postInv /=.
  + by constructor.
  by move: H; rewrite /postInv; case: mfun1 => // *; constructor.
Qed.

Lemma ihoare_fun Qerr :
  ((forall fn, hoare_f_rec preF fn postF) ->
   forall fn, hoare_fun_body_hyp_rec preF fn postF Qerr) ->
  forall fn, ihoare_f p ev preF fn postF.
Proof.
  have hrec : (forall fn, hoare_f_rec preF fn postF).
  + move=> fn' fs' hpre' /=; apply lutt_trigger.
    + by apply sum_prepred_inl.
    by rewrite /postInv /= => fr h; dependent destruction h.
  move=> /(_ hrec) hbody {hrec}.
  move=> fn fs hpre.
  apply interp_mrec_lutt with (DPEv := preD spec) (DPAns := postD spec).
  + move=> {hpre fn fs}.
    move=> ? [fn fs] /= hpre.
    have := hoare_fun_body (iE0 := invEvent_recCall spec) (hbody fn) hpre.
    apply lutt_weaken; auto using weak_pre, weak_post.
  have := hoare_fun_body (iE0 := invEvent_recCall spec) (hbody fn) hpre.
  apply lutt_weaken; auto using weak_pre, weak_post.
Qed.

End HOARE_FUN.

(* Weak version of hoare logic where the post condition on errors is True *)
Definition invErrT : InvErr :=
  {| invErr_ := fun=> True |}.

Notation whoare := (hoare (iEr := invErrT)).
Notation whoare_f := (hoare_f (iEr := invErrT)).

Section WHOARE_CORE.

Context {E E0: Type -> Type}  {sem_F : sem_Fun E} {wE: with_Error E E0} {iE0 : InvEvent E0}.

Context (p : prog) (ev: extra_val_t).

Lemma whoare_assgn (Rv Rtr: Pred_v) (P Q : Pred_c) ii x tg ty e :
  rhoare P (fun s => sem_pexpr true (p_globs p) s e) Rv PredT ->
  (forall s, P s -> rhoare Rv (truncate_val ty) Rtr PredT) ->
  (forall v, Rtr v -> rhoare P (write_lval true (p_globs p) x v) Q PredT) ->
  whoare p ev P [:: MkI ii (Cassgn x tg ty e)] Q.
Proof. by apply hoare_assgn. Qed.

Lemma whoare_opn (Rve Rvo : Pred_vs) P Q ii xs tag o es :
  rhoare P (fun s => sem_pexprs true (p_globs p) s es) Rve PredT ->
  (forall s, P s -> rhoare Rve (exec_sopn o) Rvo PredT) ->
  (forall vs, Rvo vs -> rhoare P (fun s => write_lvals true (p_globs p) s xs vs) Q PredT) ->
  whoare p ev P [:: MkI ii (Copn xs tag o es)] Q.
Proof. by apply hoare_opn. Qed.

Lemma whoare_syscall Rv Ro P Q ii xs sc es :
  rhoare P (fun s => sem_pexprs true (p_globs p) s es) Rv PredT ->
  (forall s, P s ->
     rhoare Rv (fun vs => fexec_syscall sc (mk_fstate vs s)) Ro PredT) ->
  (forall fs, Ro fs ->
     rhoare P (upd_estate true (p_globs p) xs fs) Q PredT) ->
  whoare p ev P [:: MkI ii (Csyscall xs sc es)] Q.
Proof. by apply hoare_syscall. Qed.

Lemma whoare_if_full P Q ii e c c' :
  rhoare P (sem_cond (p_globs p) e) (fun _ => True) PredT ->
  (forall b,
     whoare p ev (fun s => P s /\ sem_cond (p_globs p) e s = ok b) (if b then c else c') Q) ->
  whoare p ev P [:: MkI ii (Cif e c c')] Q.
Proof. by apply hoare_if_full. Qed.

Lemma whoare_if P Q ii e c c' :
  rhoare P (sem_cond (p_globs p) e) (fun _ => True) PredT ->
  (forall b, whoare p ev P (if b then c else c') Q) ->
  whoare p ev P [:: MkI ii (Cif e c c')] Q.
Proof. by apply hoare_if. Qed.

Lemma whoare_for_full P Pb Pi ii i d lo hi c :
  rhoare P (sem_bound (p_globs p) lo hi) Pb PredT ->
  (forall bounds (j:Z),
    Pb bounds ->
    (* FIXME : j \in (wrange d bounds.1 bounds.2) *)
    List.In j (wrange d bounds.1 bounds.2) ->
    rhoare P (write_var true i (Vint j)) Pi PredT) ->
  whoare p ev Pi c P ->
  whoare p ev P [:: MkI ii (Cfor i (d, lo, hi) c)] P.
Proof. by apply hoare_for_full. Qed.

Lemma whoare_for P Pi ii i d lo hi c :
  rhoare P (sem_bound (p_globs p) lo hi) (fun _ => True) PredT ->
  (forall (j:Z), rhoare P (write_var true i (Vint j)) Pi PredT) ->
  whoare p ev Pi c P ->
  whoare p ev P [:: MkI ii (Cfor i (d, lo, hi) c)] P.
Proof. by apply hoare_for. Qed.

Lemma whoare_while_full I I' ii al e inf c c' :
  whoare p ev I c I' ->
  rhoare I' (sem_cond (p_globs p) e) (fun _ => True) PredT  ->
  whoare p ev (fun s => I' s /\ sem_cond (p_globs p) e s = ok true) c' I ->
  whoare p ev I [:: MkI ii (Cwhile al c e inf c')]
     (fun s => I' s /\ sem_cond (p_globs p) e s = ok false).
Proof. by apply hoare_while_full. Qed.

Lemma whoare_while I I' ii al e inf c c' :
  whoare p ev I c I' ->
  rhoare I' (sem_cond (p_globs p) e) (fun _ => True) PredT  ->
  whoare p ev I' c' I ->
  whoare p ev I [:: MkI ii (Cwhile al c e inf c')] I'.
Proof. by apply hoare_while. Qed.

Lemma whoare_call (Pf : PreF) (Qf : PostF) Rv P Q ii xs fn es :
  rhoare P (fun s => sem_pexprs (~~ direct_call) (p_globs p) s es) Rv PredT ->
  (forall s vs, P s -> Rv vs -> Pf fn (mk_fstate vs s)) ->
  whoare_f p ev Pf fn Qf ->
  (forall fs fr,
    Pf fn fs -> Qf fn fs fr ->
    rhoare P (upd_estate (~~ direct_call) (p_globs p) xs fr) Q PredT) ->
  whoare p ev P [:: MkI ii (Ccall xs fn es)] Q.
Proof. by apply hoare_call. Qed.

End WHOARE_CORE.

Notation iwhoare_f := (hoare_f (sem_F := sem_fun_full) (iEr := invErrT)).
Notation iwhoare   := (hoare (sem_F := sem_fun_full) (iEr := invErrT)).

Section WHOARE_FUN.

Context {E E0: Type -> Type} {wE: with_Error E E0} {iE0 : InvEvent E0}.

Context (p : prog) (ev: extra_val_t) (spec : HoareSpec).

Definition whoare_f_rec Pf fn Qf :=
  hoare_f (iE0 := invEvent_recCall spec) (iEr := invErrT) p ev Pf fn Qf.

Definition whoare_rec P c Q :=
  hoare (iE0 := invEvent_recCall spec) (iEr := invErrT) p ev P c Q.

Definition whoare_fun_body_hyp_rec Pf fn Qf :=
  forall fs,
  Pf fn fs ->
  forall fd, get_fundef (p_funcs p) fn = Some fd ->
  exists (P Q : Pred_c),
    [/\ rhoare (Pf fn) (initialize_funcall p ev fd) P PredT
      , whoare_rec P fd.(f_body) Q
      & rhoare Q (finalize_funcall fd) (Qf fn fs) PredT].

Lemma iwhoare_fun :
  ((forall fn, whoare_f_rec preF fn postF) ->
   forall fn, whoare_fun_body_hyp_rec preF fn postF) ->
  forall fn, iwhoare_f p ev preF fn postF.
Proof.
  move=> h; apply ihoare_fun with PredT.
  move=> /h{}h fn fs /h{}h; split => //.
  case heq : get_fundef => [fd | ] //.
  by have [P [Q [???]]]:= h _ heq; exists P, Q.
Qed.

End WHOARE_FUN.

End Section.

Notation whoare := (hoare (iEr := invErrT)).
Notation whoare_f := (hoare_f (iEr := invErrT)).

Notation iwhoare_f := (hoare_f (sem_F := sem_fun_full) (iEr := invErrT)).
Notation iwhoare   := (hoare (sem_F := sem_fun_full) (iEr := invErrT)).

(* Should we do that in core ? *)
Hint Immediate rhoare_true rhoare_false : core.

(* A test *)

Section Test.
Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {asm_op: Type}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {wsw : WithSubWord}
  {scP : semCallParams}
  {dc : DirectCall}.

Context {E E0: Type -> Type} {sem_F : sem_Fun E} {wE: with_Error E E0}.

Context (p : prog) (ev : extra_val_t).

#[local] Existing Instance trivial_invErr.
#[local] Existing Instance trivial_invEvent.

#[local]
Notation pre := (fun s0 s => s = s0).
#[local]
Notation post X := (fun s0 s => s0.(evm) =[\ X] s.(evm)).

Let Pc c := forall s0, whoare p ev (pre s0) c (post (write_c c) s0).

Let Pi i := forall s0, whoare p ev (pre s0) [::i] (post (write_I i) s0).

Let Pi_r ir := forall ii, Pi (MkI ii ir).

(* FIXME: move this *)
Definition trivial_spec : HoareSpec :=
  {| preF_ := fun _ _ => True; postF_ := fun _ _ _ => True |}.

#[local]Existing Instance trivial_spec.

(** psem needed *)
Lemma writeP c : Pc c.
Proof.
  apply: (cmd_rect (Pr:=Pi_r) (Pi:=Pi) (Pc:=Pc)) => {c} //.
  + by move=> s0; apply hoare_skip => _ ->.
  + move=> i c hi hc s0; apply (hoare_cons (hi s0)).
    apply hoareP => s1 hs1; move: (hc s1).
    apply: hoare_weaken1 => // s2 hs2 z.
    rewrite write_c_cons => hnin; rewrite hs1 ?hs2 //; SvD.fsetdec.
  + move=> x tg ty e ii s0.
    apply whoare_assgn with PredT PredT; try auto using rhoare_true.
    move=> v _; apply wrhoareP => s s' <-.
    rewrite write_Ii write_i_assgn; apply vrvP.
  + move=> xs tg o es ii s0.
    apply whoare_opn with PredT PredT; try auto using rhoare_true.
    move=> v _; apply wrhoareP => s s' <-.
    rewrite write_Ii write_i_opn; apply vrvsP.
  + move=> xs o es ii s0.
    apply whoare_syscall with PredT PredT; try auto using rhoare_true.
    move=> v _; apply wrhoareP => s s' <-.
    by rewrite write_Ii write_i_syscall => /vrvsP /=.
  + move=> e c1 c2 hc1 hc2 ii s0.
    apply whoare_if; first by auto using rhoare_true.
    move=> b; rewrite write_Ii.
    apply hoare_weaken1 with (eq^~ s0)
      (fun s : estate => evm s0 =[\ write_c (if b then c1 else c2)] evm s) => //.
    + by move=> s; rewrite write_i_if; apply eq_exI; case: b; SvD.fsetdec.
    by case: b.
  + move=> i d lo hi c hc ii s0.
    set P := (fun s => evm s0 =[\ Sv.add i (write_c c)] evm s).
    apply hoare_weaken1 with P P.
    + by move=> _ ->.
    + by move=> s; apply eq_exI; rewrite write_Ii write_i_for; SvD.fsetdec.
    apply whoare_for with P; first by auto using rhoare_true.
    + move=> j;apply wrhoareP => s s' hP /vrvP_var h.
      by apply (eq_exT hP); apply : eq_exI h; SvD.fsetdec.
    apply hoareP => s1 hs1.
    apply: hoare_weaken1 (hc s1) => //.
    by move=> s2 hs2; apply (eq_exT hs1); apply: eq_exI hs2; SvD.fsetdec.
  + move=> a c e inf c' hc hc' ii s0.
    set P := (fun s => evm s0 =[\ Sv.union (write_c c) (write_c c') ] evm s).
    apply hoare_weaken1 with P P.
    + by move=> _ ->.
    + by move=> s; apply eq_exI; rewrite write_Ii write_i_while; SvD.fsetdec.
    apply whoare_while; try auto using rhoare_true.
    + apply hoareP => s1 hs1; apply: hoare_weaken1 (hc s1) => // s2 h.
      by apply (eq_exT hs1); apply: eq_exI h; SvD.fsetdec.
    apply hoareP => s1 hs1; apply: hoare_weaken1 (hc' s1) => // s2 h.
    by apply (eq_exT hs1); apply: eq_exI h; SvD.fsetdec.
  move=> xs fn es ii s0.
  apply whoare_call with preF postF PredT; try auto using rhoare_true.
  + by apply hoare_f_true.
  move=> fs fr _ _; apply wrhoareP => s s' <-.
  by rewrite write_Ii write_i_call => /vrvsP /=.
Qed.

End Test.


