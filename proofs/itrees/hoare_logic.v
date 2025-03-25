From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     EquivDec
     Equality
     Program.Tactics.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

From ITree Require Import
     ITree
     ITreeFacts
     Monad
     Basics.HeterogeneousRelations
     Events.Map
     Events.State
     Events.StateFacts
     Events.Reader
     Events.Exception
     Events.FailFacts.

Require Import Paco.paco.
Require Import Psatz.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype fintype.

From ITree Require Import
(*     Basics.Tacs *)
     Basics.Category
     Basics.Basics
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Eq.Eqit
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion.

From ITree Require Import Rutt RuttFacts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import expr psem_defs psem oseq compiler_util xrutt_aux.
Require Import it_gen_lib it_jasmin_lib it_sems_core core_logics.

(* Definition of a relational logic over program *)

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

Class invEvent (E : Type -> Type) :=
  { PreInv  :: prepred E
  ; PostInv :: postpred E }.

Definition Pred (T : Type) := T -> Prop.
Definition Pred_io (T1 T2 : Type) := T1 -> T2 -> Prop.

Definition PreF := funname -> Pred fstate.
Definition PostF := funname -> Pred_io fstate fstate.

Definition Pred_e  := Pred pexpr.
Definition Pred_v  := Pred value.
Definition Pred_vs := Pred values.
Definition Pred_c  := Pred estate.

Section TR_MutualRec.

Class hoare_spec :=
  { preF  : PreF
  ; postF : PostF }.

Context (spec : hoare_spec) {E: Type -> Type} {wE: with_Error E}.

Definition PreD T (d : recCall T) : Prop :=
  match d with
  | RecCall fn fs => preF fn fs
  end.

Definition PostD T (d : recCall T) (t: T) : Prop :=
  match d in recCall T_ return T_ -> Prop with
  | RecCall fn fs => postF fn fs
  end t.

Definition invEvent_recCall {IE : invEvent E} : invEvent (recCall +' E) :=
  {| PreInv := sum_prepred (@PreD) PreInv; PostInv := sum_postpred (@PostD) PostInv|}.

End TR_MutualRec.

Section RHOARE.

Context {Err : Set}.

Definition fresult T1 T2 := T1 -> result Err T2.

(* P : precondition
   Q : postcondition
   QE : postcondition for error *)

Definition rhoare_io {I O}
   (P : Pred I) (F : fresult I O) (Q : Pred_io I O) (QE : I -> Pred Err) :=
  forall i, P i ->
    match F i with
    | Ok o => Q i o
    | Error e => QE i e
    end.

Definition rhoare {I O} (P : Pred I) (F : fresult I O) (Q : Pred O) (QE : I -> Pred Err) :=
  rhoare_io P F (fun _ => Q) QE.

Lemma rhoare_ioP {I O} (P : Pred I) (F : fresult I O) (Q : Pred_io I O) (QE : I -> Pred Err) :
  rhoare_io P F Q QE <-> (forall i0, rhoare (fun i => i = i0 /\ P i) F (Q i0) QE).
Proof.
  split.
  + by move=> h i0 i [? hP]; have := h _ hP; subst i0.
  by move=> h i hP; apply (h i i).
Qed.

Lemma rhoare_io_weaken {I O} (F : fresult I O)
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

Lemma rhoare_weaken {I O} (F : fresult I O) (P P' : Pred I) (Q Q': Pred O) (QE QE' : I -> Pred Err) :
  (forall i, P' i -> P i) ->
  (forall o, Q o -> Q' o) ->
  (forall i e, P' i -> QE i e -> QE' i e) ->
  rhoare P F Q QE ->
  rhoare P' F Q' QE'.
Proof.
  move=> hP'P hQQ'; apply rhoare_io_weaken => //.
  move=> > ?; apply hQQ'.
Qed.

Lemma rhoare_ok {T} (Q : Pred T) (QE : T -> Pred Err) :
  rhoare Q (fun t => ok t) Q QE.
Proof. done. Qed.

Lemma rhoare_Error {T} (P Q : Pred T) (QE : T -> Pred Err) e:
  (forall t, P t -> QE t e) <->
  rhoare P (fun t => Error e) Q QE.
Proof. done. Qed.

Lemma rhoare_bind {I T O} (F1 : fresult I T) (F2 : fresult T O)
  (P : Pred I) (R : Pred T) (Q : Pred O) (QE : I -> Pred Err) (QET : T -> Pred Err) :
  (forall i t e , P i -> R t -> QET t e -> QE i e) ->
  rhoare P F1 R QE ->
  rhoare R F2 Q QET ->
  rhoare P (fun i => Let r := F1 i in F2 r) Q QE.
Proof.
  move=> hQE hF1 hF2 i hP.
  case: (F1 i) (hF1 i hP) => //=.
  move=> t hR; case: (F2 t) (hF2 t hR) => //=.
  by move=> e; apply hQE.
Qed.

Lemma rhoare_read {S T O} (F1 : fresult S T) (F2 : T -> fresult S O)
  (P : Pred S) (R : Pred T) (Q : Pred O) (QE : S -> Pred Err) :
  rhoare P F1 R QE ->
  (forall t, R t -> rhoare P (F2 t) Q QE) ->
  rhoare P (fun s => Let r := F1 s in F2 r s) Q QE.
Proof.
  move=> hF1 hF2 s hP.
  case: (F1 s) (hF1 s hP) => //=.
  move=> t hR; case: (F2 t s) (hF2 t hR s hP) => //=.
Qed.

Lemma rhoare_bind_eval {S I T O} (F1 : fresult I T) (F2 : T -> fresult S O)
  (P : Pred S) (R : Pred T) (Q : Pred O) (QE : S -> Pred Err) i :
  (forall s, P s -> rhoare (fun i' => i' = i) F1 R (fun _ => QE s)) ->
  (forall t, R t -> rhoare P (F2 t) Q QE) ->
  rhoare P (fun s => Let r := F1 i in F2 r s) Q QE.
Proof.
  move=> hF1 hF2 s hP.
  case: (F1 i) (hF1 s hP i erefl) => //=.
  move=> t hR; case: (F2 t s) (hF2 t hR s hP) => //=.
Qed.

Lemma rhoare_eval {S I O} (F : fresult I O)
  (P : Pred S) (Q : Pred O) (QE : S -> Pred Err) i :
  (forall s, P s -> rhoare (fun i' => i' = i) F Q (fun _ => QE s)) ->
  rhoare P (fun s => F i) Q QE.
Proof. by move=> hF s hP; case: (F i) (hF s hP i erefl). Qed.

Lemma rhoare_write {S O} (F1 : fresult S S) (F2 : fresult S O)
  (P R : Pred S) (Q : Pred O) (QE : S -> Pred Err) :
  rhoare_io P F1 (fun s s' => R s' /\ forall e, QE s' e -> QE s e) QE ->
  rhoare R F2 Q QE ->
  rhoare P (fun s => Let s := F1 s in F2 s) Q QE.
Proof.
  move=> hF1 hF2 s hP.
  case: (F1 s) (hF1 s hP) => //=.
  by move=> s' [hR hQE]; case: (F2 s') (hF2 s' hR).
Qed.

Lemma rhoare_id {I O} (F : fresult I O) i0 (P : Pred I) (QE : I -> Pred Err):
  rhoare (fun i => i = i0 /\ P i) F (fun=> True) QE ->
  rhoare (fun i => i = i0 /\ P i) F (fun o => F i0 = ok o) QE.
Proof.
  by move=> h i hP; have := h i hP; case: hP => ? _; subst i0; case: (F i).
Qed.

End RHOARE.

Section KHOARE.

Context {E: Type -> Type} {wE: with_Error E} {rE : invEvent E}.

Definition khoare_io {I O}
   (P : Pred I) (F : ktree E I O) (Q : Pred_io I O) :=
  forall i, P i -> lutt PreInv PostInv (Q i) (F i).

Definition khoare {I O} (P : Pred I) (F : ktree E I O) (Q : Pred O) :=
  khoare_io P F (fun i => Q).

(* Remark: in pratice khoare_io and khoare are equivalent *)
Lemma khoare_ioP {I O} (P : Pred I) (F : ktree E I O) (Q : Pred_io I O) :
  khoare_io P F Q <-> (forall i0, P i0 -> khoare (fun i => i = i0 /\ P i) F (Q i0)).
Proof.
  split.
  + by move=> h i0 _ i [? hP]; have := h _ hP; subst i0.
  by move=> h i hP; apply (h i hP i).
Qed.

Lemma khoare_io_weaken {I O} (P P' : Pred I) (Q Q': Pred_io I O) F :
  (forall i, P' i -> P i) ->
  (forall i o, P' i -> Q i o -> Q' i o) ->
  khoare_io P F Q ->
  khoare_io P' F Q'.
Proof.
  move=> hP'P hQQ' heqv i hP'.
  apply lutt_weaken with PreInv PostInv (Q i) => //.
  + by move=> >; apply hQQ'.
  by apply/heqv/hP'P.
Qed.

Lemma khoare_weaken {I O} (P P' : Pred I) (Q Q': Pred O) F :
  (forall i, P' i -> P i) ->
  (forall o, Q o -> Q' o) ->
  khoare P F Q ->
  khoare P' F Q'.
Proof. move=> hP hQ; apply khoare_io_weaken => // > _; apply hQ. Qed.

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

Definition Qerr (s : estate) e := PreInv (subevent void (Throw (mk_error_data s e))).

Lemma khoare_io_iresult (T : Type) F (P : Pred_c) (Q: Pred_io estate T) :
  rhoare_io P F Q Qerr ->
  khoare_io P (fun s => iresult s (F s)) Q.
Proof.
  move=> hr s hP; have := hr s hP.
  case: (F s) => [v | e] hQ.
  + by apply lutt_Ret.
  by apply lutt_Vis.
Qed.

Lemma khoare_iresult (T : Type) F (P : Pred_c) (Q: Pred T) :
  rhoare P F Q Qerr ->
  khoare P (fun s => iresult s (F s)) Q.
Proof. apply khoare_io_iresult. Qed.

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

Lemma khoare_eq_pred {I O} (F : ktree E I O) (P : Pred I) (Q : Pred O) :
  (forall i0, khoare (fun i => i = i0 /\ P i) F Q) ->
  khoare P F Q.
Proof. by move=> h i0 hP; apply (h i0 i0). Qed.

Lemma khoare_iter (IT T : Type) (I : Pred IT) (Q : Pred T) (body : ktree E IT (IT + T)) :
  khoare I body (sum_pred I Q) ->
  khoare I (ITree.iter body) Q.
Proof. move=> hbody i hI; apply: lutt_iter hI => {}i; apply hbody. Qed.

End KHOARE.

Section HOARE_CORE.

Context {E : Type -> Type} {wE: with_Error E} {inv : invEvent E}.
Context {sem_F : sem_Fun E} (p : prog) (ev: extra_val_t).

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
  hoare_io P c Q <-> (forall s0, P s0 -> hoare (fun s => s = s0 /\ P s) c (Q s0)).
Proof. apply khoare_ioP. Qed.

(* FIXME allow to weaken the invPred *)
Lemma hoare_weaken P1 P2 Q1 Q2 c :
  (forall s, P1 s -> P2 s) ->
  (forall s, Q2 s -> Q1 s) ->
  hoare P2 c Q2 ->
  hoare P1 c Q1.
Proof. apply khoare_weaken. Qed.

Lemma hoare_cat (R P Q : Pred_c) (c c' : cmd) :
  hoare P c R ->
  hoare R c' Q ->
  hoare P (c ++ c') Q.
Proof.
  move=> h h' s hP ; rewrite isem_cmd_cat.
  apply lutt_bind with R => //.
  by apply h.
Qed.

Lemma hoare_nil Q : hoare Q [::] Q.
Proof. move=> hQ; apply lutt_Ret. Qed.

Lemma hoare_cons (R P Q : Pred_c) (i : instr) (c : cmd) :
  hoare P [::i] R ->
  hoare R c Q ->
  hoare P (i :: c) Q.
Proof. rewrite -(cat1s i c); apply hoare_cat. Qed.

Lemma hoare_assgn (Rv Rtr: Pred_v) (P Q : Pred_c) ii x tg ty e :
  rhoare P (fun s => sem_pexpr true (p_globs p) s e) Rv Qerr ->
  (forall s, P s -> rhoare Rv (truncate_val ty) Rtr (fun _ => Qerr s)) ->
  (forall v, Rtr v -> rhoare P (write_lval true (p_globs p) x v) Q Qerr) ->
  hoare P [:: MkI ii (Cassgn x tg ty e)] Q.
Proof.
  move=> he htr hwr; rewrite /hoare /isem_cmd_ /=.
  apply khoare_bind with Q; last by apply khoare_ret.
  apply khoare_iresult; rewrite /sem_assgn.
  apply: (rhoare_read he) => v hv.
  apply rhoare_bind_eval with Rtr.
  + by move=> s /htr; apply rhoare_weaken => // > ->.
  apply hwr.
Qed.

Lemma hoare_opn (Rve Rvo : Pred_vs) P Q ii xs tag o es :
  rhoare P (fun s => sem_pexprs true (p_globs p) s es) Rve Qerr ->
  (forall s, P s -> rhoare Rve (exec_sopn o) Rvo (fun _ => Qerr s)) ->
  (forall vs, Rvo vs -> rhoare P (fun s => write_lvals true (p_globs p) s xs vs) Q Qerr) ->
  hoare P [:: MkI ii (Copn xs tag o es)] Q.
Proof.
  move=> he ho hwr; rewrite /hoare /isem_cmd_ /=.
  apply khoare_bind with Q; last by apply khoare_ret.
  apply khoare_iresult; rewrite /sem_sopn.
  eapply rhoare_read.
  + eapply rhoare_read; first apply he.
    move=> t ht; eapply rhoare_eval.
    move=> s /ho; apply rhoare_weaken; last done.
    + by move=> > ->.
    by move=> > h; apply h.
  by apply hwr.
Qed.

Lemma hoare_syscall Rv Ro P Q ii xs sc es :
  rhoare P (fun s => sem_pexprs true (p_globs p) s es) Rv Qerr ->
  (forall s, P s ->
     rhoare Rv (fun vs => fexec_syscall sc (mk_fstate vs s)) Ro (fun _ => Qerr s)) ->
  (forall fs, Ro fs ->
     rhoare P (upd_estate true (p_globs p) xs fs) Q Qerr) ->
  hoare P [:: MkI ii (Csyscall xs sc es)] Q.
Proof.
  move=> he ho hwr; rewrite /hoare /isem_cmd_ /=.
  apply khoare_bind with Q; last by apply khoare_ret.
  apply khoare_iresult; rewrite /sem_syscall.
  apply (rhoare_read he).
  move=> t ht; eapply rhoare_read; last by apply hwr.
  move=> s hP; apply (ho s hP _ ht).
Qed.

Lemma hoare_if_full P Q ii e c c' :
  rhoare P (sem_cond (p_globs p) e) (fun _ => True) Qerr ->
  (forall b,
     hoare (fun s => P s /\ sem_cond (p_globs p) e s = ok b) (if b then c else c') Q) ->
  hoare P [:: MkI ii (Cif e c c')] Q.
Proof.
  move=> he hc; rewrite /hoare /isem_cmd_ /=.
  apply khoare_bind with Q; last by apply khoare_ret.
  apply khoare_eq_pred => s0.
  apply khoare_read with (fun b => sem_cond (p_globs p) e s0 = ok b).
  + rewrite /isem_cond; apply khoare_iresult.
    by apply rhoare_id; apply: rhoare_weaken he => // > [].
  by move=> b hb; apply: khoare_weaken (hc b) => // s [->].
Qed.

Lemma hoare_if P Q ii e c c' :
  rhoare P (sem_cond (p_globs p) e) (fun _ => True) Qerr ->
  (forall b, hoare P (if b then c else c') Q) ->
  hoare P [:: MkI ii (Cif e c c')] Q.
Proof.
  move=> he hc; apply hoare_if_full => //.
  by move=> b; apply: hoare_weaken (hc b) => // s [].
Qed.

Lemma hoare_for_full P Pb Pi ii i d lo hi c :
  rhoare P (sem_bound (p_globs p) lo hi) Pb Qerr ->
  (forall bounds (j:Z),
    Pb bounds ->
    (* FIXME : j \in (wrange d bounds.1 bounds.2) *)
    List.In j (wrange d bounds.1 bounds.2) ->
    rhoare P (write_var true i (Vint j)) Pi Qerr) ->
  hoare Pi c P ->
  hoare P [:: MkI ii (Cfor i (d, lo, hi) c)] P.
Proof.
  move=> hbound hwi hc; rewrite /hoare /isem_cmd_ /=.
  apply khoare_bind with P; last by apply khoare_ret.
  apply khoare_read with Pb.
  + by apply khoare_iresult.
  move=> bounds {}/hwi; elim (wrange _ _) => /= [ | j js hrec] hwi.
  + by apply khoare_ret.
  eapply khoare_bind.
  + by apply khoare_iresult; apply hwi; left.
  by apply: (khoare_bind hc); apply hrec => z hz; apply hwi; right.
Qed.

Lemma hoare_for P Pi ii i d lo hi c :
  rhoare P (sem_bound (p_globs p) lo hi) (fun _ => True) Qerr ->
  (forall (j:Z), rhoare P (write_var true i (Vint j)) Pi Qerr) ->
  hoare Pi c P ->
  hoare P [:: MkI ii (Cfor i (d, lo, hi) c)] P.
Proof.
  move=> hbound hwi.
  apply: (hoare_for_full ii hbound) => _ j _ _; apply hwi.
Qed.

Lemma hoare_while_full I I' ii al e c c' :
  hoare I c I' ->
  rhoare I' (sem_cond (p_globs p) e) (fun _ => True) Qerr  ->
  hoare (fun s => I' s /\ sem_cond (p_globs p) e s = ok true) c' I ->
  hoare I [:: MkI ii (Cwhile al c e c')]
     (fun s => I' s /\ sem_cond (p_globs p) e s = ok false).
Proof.
  move=> hc he hc'; rewrite /hoare /isem_cmd_ /=.
  set Q := (Q in khoare _ _ Q).
  apply khoare_bind with Q; last by move=> >; apply: khoare_ret.
  apply khoare_iter.
  apply: (khoare_bind hc).
  apply khoare_eq_pred => s0.
  apply khoare_read with (fun b => sem_cond (p_globs p) e s0 = ok b).
  + apply khoare_iresult.
    by apply rhoare_id; apply: rhoare_weaken he => // > [].
  move=> [] hb; last first.
  + by apply khoare_ret => _ [-> ?]; constructor.
  apply khoare_bind with I.
  + by apply: khoare_weaken hc' => // _ [-> ?].
  by apply khoare_ret.
Qed.

Lemma hoare_while I I' ii al e c c' :
  hoare I c I' ->
  rhoare I' (sem_cond (p_globs p) e) (fun _ => True) Qerr  ->
  hoare I' c' I ->
  hoare I [:: MkI ii (Cwhile al c e c')] I'.
Proof.
  move=> hc hcond hc'.
  apply hoare_weaken with I (fun s => I' s /\ sem_cond (p_globs p) e s = ok false) => //.
  + by move=> ? [].
  apply hoare_while_full => //.
  by apply: hoare_weaken hc' => // ? [].
Qed.

Lemma hoare_call (Pf : PreF) (Qf : PostF) Rv P Q ii xs fn es :
  rhoare P (fun s => sem_pexprs (~~ direct_call) (p_globs p) s es) Rv Qerr ->
  (forall s vs, P s -> Rv vs -> Pf fn (mk_fstate vs s)) ->
  hoare_f Pf fn Qf ->
  (forall fs fr,
    Pf fn fs -> Qf fn fs fr ->
    rhoare P (upd_estate (~~ direct_call) (p_globs p) xs fr) Q Qerr) ->
  hoare P [:: MkI ii (Ccall xs fn es)] Q.
Proof.
  move=> hes hPPf hCall hPQf; rewrite /hoare /isem_cmd_ /=.
  apply khoare_bind with Q; last by apply khoare_ret.
  apply khoare_read with Rv.
  + by apply khoare_iresult => >; apply: hes.
  move=> vs hvs; apply khoare_eq_pred => s0.
  set (fs := mk_fstate vs s0).
  apply khoare_read with (Qf fn fs).
  + by move=> _ [-> hP]; apply/hCall/hPPf.
  move=> fr hQf; apply khoare_iresult.
  move=> _ [-> hP]; apply (hPQf fs fr) => //.
  by apply hPPf.
Qed.

Definition hoare_fun_body_hyp (Pf : PreF) fn (Qf : PostF) :=
  forall fs,
  Pf fn fs ->
  match get_fundef (p_funcs p) fn with
  | None => PreInv (subevent void (Throw (ErrType, tt)))
  | Some fd =>
    exists (P Q : Pred_c),
      [/\ rhoare (Pf fn) (initialize_funcall p ev fd) P (fun _ => Qerr (estate0 fs))
        , hoare P fd.(f_body) Q
        & rhoare Q (finalize_funcall fd) (Qf fn fs) Qerr]
  end.

Lemma hoare_fun_body Pf fn Qf :
  hoare_fun_body_hyp Pf fn Qf ->
  hoare_f_body Pf fn Qf.
Proof.
  move=> hf; rewrite /hoare_f_body /isem_fun_body.
  apply khoare_ioP => fs hPf; have {}hf := hf _ hPf.
  apply khoare_read with (fun fd => get_fundef (p_funcs p) fn = Some fd).
  + rewrite /kget_fundef => _ [-> _].
    by case: get_fundef hf => /= [fd | ] h; [apply lutt_Ret | apply lutt_Vis].
  move=> fd hfd; move: hf; rewrite hfd => -[P] [Q] [hinit hbody hfin].
  apply khoare_bind with P.
  + move=> _ [-> _]; have := hinit _ hPf.
    by case: initialize_funcall => [s | e] h; [apply lutt_Ret | apply lutt_Vis].
  by apply: (khoare_bind hbody); apply khoare_iresult.
Qed.

End HOARE_CORE.

Section HOARE_FUN.

Context {E : Type -> Type} {wE: with_Error E} {rE : invEvent E}.

Context (p : prog) (ev: extra_val_t) (spec : hoare_spec).

Definition hoare_f_rec Pf fn Qf :=
  hoare_f (inv := invEvent_recCall spec) p ev Pf fn Qf.

Definition hoare_rec P c Q :=
  hoare (inv := invEvent_recCall spec) p ev P c Q.

Definition hoare_fun_body_hyp_rec Pf fn Qf :=
  forall fs,
  Pf fn fs ->
  match get_fundef (p_funcs p) fn with
  | None => PreInv (subevent void (Throw (ErrType, tt)))
  | Some fd =>
    exists (P Q : Pred_c),
      [/\ rhoare (Pf fn) (initialize_funcall p ev fd) P (fun _ => Qerr (estate0 fs))
        , hoare_rec P fd.(f_body) Q
        & rhoare Q (finalize_funcall fd) (Qf fn fs) Qerr]
  end.

Lemma isem_fun_ind :
  ((forall fn, hoare_f_rec preF fn postF) ->
   forall fn, hoare_fun_body_hyp_rec preF fn postF) ->
  forall fn, hoare_f p ev preF fn postF.
Proof.
  have hrec : (forall fn, hoare_f_rec preF fn postF).
  + move=> fn' fs' hpre'; apply lutt_trigger.
    + by apply sum_prepred_inl.
    by rewrite /PostInv /= => fr h; dependent destruction h.
  move=> /(_ hrec) hbody.
  have {}hbody : forall fn,  hoare_fun_body_hyp (inv := invEvent_recCall spec) p ev preF fn postF.
  + move=> fn fs hp.
    have := hbody fn fs hp.
    case: get_fundef => [fd | ].
    + move=> [P [Q [h1 h2 h3]]]; exists P, Q; split => //.
      + apply: rhoare_weaken h1 => //.
        by rewrite /Qerr /= => *; constructor.
      apply: rhoare_weaken h3 => //.
      by rewrite /Qerr /= => *; constructor.
    by rewrite /Qerr /= => *; constructor.
  move=> fn fs hpre.
  apply interp_mrec_lutt with (DPEv := PreD spec) (DPAns := PostD spec).
  + move=> {hpre fn fs}.
    move=> ? [fn fs] /= hpre.
    by apply (hoare_fun_body (hbody fn) hpre).
  apply (hoare_fun_body (hbody fn) hpre).
Qed.

End HOARE_FUN.

End Section.

