From Coq Require Import
     Equality. 

From ExtLib Require Import
     Data.List 
     Core.RelDec. 

From ITree Require Import
     ITree 
     ITreeFacts 
     Basics.HeterogeneousRelations.

From ITree Require Import XRutt XRuttFacts.

From mathcomp Require Import ssreflect ssrfun ssrbool.  

From Jasmin Require Import expr psem_defs psem compiler_util xrutt_aux.
From Jasmin Require Import it_sems_alt1.

Import MonadNotation. 
Local Open Scope monad_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section RuttRec.
  Context (E1 E2 : Type -> Type) {A1 A2 B1 B2: Type}.

  Context (EE1: forall X, E1 X -> bool).
  Context (EE2: forall X, E2 X -> bool).
            
  Context (bodies1 : A1 -> itree (callE A1 B1 +' E1) B1)
          (bodies2 : A2 -> itree (callE A2 B2 +' E2) B2).
  
  Context (RPre : prerel E1 E2) (RPreInv : prerel (callE A1 B1) (callE A2 B2))
     (RPost : postrel E1 E2) (RPostInv : postrel (callE A1 B1) (callE A2 B2)).

  Context (Hbodies: forall (A B : Type)
                           (d1 : callE A1 B1 A) (d2 : callE A2 B2 B),
  @RPreInv A B d1 d2 -> 
  rutt (EE_MR EE1 (callE A1 B1)) (EE_MR EE2 (callE A2 B2))  
    (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost)
    (fun (a : A) (b : B) => @RPostInv A B d1 a d2 b) 
    (calling' bodies1 A d1) (calling' bodies2 B d2)).

  Lemma rec_rutt (RR : B1 -> B2 -> Prop) a1 a2 : 
    @RPreInv B1 B2 (Call a1) (Call a2) ->
    RR = (fun (t1 : B1) (t2 : B2) =>  
         @RPostInv B1 B2 (Call a1) t1 (Call a2) t2) ->
    rutt EE1 EE2 RPre RPost RR
         (rec bodies1 a1) (rec bodies2 a2).
  Proof.
    intros.
    unfold rec, mrec.
    eapply interp_mrec_rutt with (RPreInv:=RPreInv); eauto.
    rewrite H0; eauto.
  Qed.  
  
End RuttRec.


(* PROBLEM with sections *)

(* This files contains proofs to test the semantic models in
 it_sems. It turns out that double recursion leads to a duplication of
 inductive proofs, and thus that mutual recursion leads to simpler
 proofs. The proofs on the modular model are still based on eutt and
 need to be revised. The proofs on the flat models are much longer and
 more laden with detail than those on the error-aware model. *)

Class with_Error (E: Type -> Type) {HasErr: ErrEvent -< E} := {
  is_error : forall {X}, E X -> bool;
  is_error_has : forall {X} (e: ErrEvent X), is_error (HasErr X e)
}.
Arguments with_Error : clear implicits.
Arguments with_Error E {_}.

Definition ErrorCutoff {E: Type -> Type}
  {HasErr: ErrEvent -< E} {wE : with_Error E} X (m : E X) :=
  ~~(is_error m).

Definition NoCutoff {E: Type -> Type}
  {HasErr: ErrEvent -< E} {wE : with_Error E} X (m : E X) := true.

Definition rutt_err {E1 E2: Type -> Type}
  {HasErr1: ErrEvent -< E1} {wE1 : with_Error E1}
  {HasErr2: ErrEvent -< E2} {wE2 : with_Error E2}
  {O1 O2 : Type}
  (RpreInv : prerel E1 E2)
  (RpostInv: postrel E1 E2)
  (post      : O1 -> O2 -> Prop) :=
  @rutt E1 E2 O1 O2 ErrorCutoff NoCutoff RpreInv RpostInv post.

Instance with_Error_suml {E: Type -> Type} {HasErr: ErrEvent -< E} {wE : with_Error E} (T:Type -> Type) :
  with_Error (T +' E).
Proof.
  apply (@Build_with_Error _ _  (EE_MR (fun X (e: E X) => is_error e) T)).
  move=> x e => /=.
  apply is_error_has.
Defined.

Lemma interp_mrec_rutt_err {D1 D2 E1 E2 : Type -> Type}
   {HasErr1: ErrEvent -< E1} {wE1 : with_Error E1}
   {HasErr2: ErrEvent -< E2} {wE2 : with_Error E2}
   (RPre : prerel E1 E2)
   (RPreInv : prerel D1 D2)
   (RPost : postrel E1 E2)
   (RPostInv : postrel D1 D2)
   (bodies1 : forall T : Type, D1 T -> itree (D1 +' E1) T)
   (bodies2 : forall T : Type, D2 T -> itree (D2 +' E2) T):
   (forall (R1 R2 : Type) (d1 : D1 R1) (d2 : D2 R2),
       RPreInv R1 R2 d1 d2 ->
       rutt_err (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost)
         (fun v1 : R1 => [eta RPostInv R1 R2 d1 v1 d2])
         (bodies1 R1 d1) (bodies2 R2 d2)) ->
   (forall (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
           (t1 : itree (D1 +' E1) R1) (t2 : itree (D2 +' E2) R2),
    rutt_err (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost) RR t1 t2 ->
    rutt_err RPre RPost RR (interp_mrec bodies1 t1) (interp_mrec bodies2 t2)).
Proof.
  move=> hrec R1 R2 RR t1 t2 ht.
  apply interp_mrec_rutt with (RPreInv := RPreInv) (RPostInv := RPostInv).
  + admit. (* this is hrec modulo extentional equality *)
  admit. (* this is ht modulo extentional equality *)
Admitted.

Lemma interp_rec_rutt_err {E1 E2 : Type -> Type} {A1 A2 B1 B2: Type}
   {HasErr1: ErrEvent -< E1} {wE1 : with_Error E1}
   {HasErr2: ErrEvent -< E2} {wE2 : with_Error E2}
   (RPre : prerel E1 E2)
   (RPreInv : prerel (callE A1 B1) (callE A2 B2))
   (RPost : postrel E1 E2)
   (RPostInv : postrel (callE A1 B1) (callE A2 B2))
   (bodies1 : A1 -> itree (callE A1 B1 +' E1) B1)
   (bodies2 : A2 -> itree (callE A2 B2 +' E2) B2):
   (forall (R1 R2 : Type) d1 d2, (* (d1 : callE A1 B1 R1) (d2 : callE A2 B2 R2),*)
       RPreInv R1 R2 d1 d2 ->
       rutt_err (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost)
         (fun v1 : R1 => [eta RPostInv R1 R2 d1 v1 d2])
         (calling' bodies1 R1 d1) (calling' bodies2 R2 d2)) ->
   (forall (RR : B1 -> B2 -> Prop)
           (t1 : A1) (t2 : A2),
       RPreInv B1 B2 (Call t1) (Call t2) ->
       RR = (fun t0 : B1 => [eta RPostInv B1 B2 (Call t1) t0 (Call t2)]) ->
 (*   rutt_err (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost) RR t1 t2 -> *)
    rutt_err RPre RPost RR (rec bodies1 t1) (rec bodies2 t2)).
Proof.
  move=> hrec RR t1 t2 ht he.
  apply rec_rutt with (RPreInv := RPreInv) (RPostInv := RPostInv); eauto.
  + intros; inv he. 
    admit. (* this is hrec modulo extentional equality *)
Admitted.

Lemma rutt_err_weaken {E1 E2: Type -> Type}
  {HasErr1: ErrEvent -< E1} {wE1 : with_Error E1}
  {HasErr2: ErrEvent -< E2} {wE2 : with_Error E2}
  {O1 O2 : Type}
  (RpreInv : prerel E1 E2)
  (RpostInv: postrel E1 E2)
  (post post' : O1 -> O2 -> Prop) t1 t2 :
  (forall o1 o2, post o1 o2 -> post' o1 o2) ->
  rutt_err RpreInv RpostInv post t1 t2 ->
  rutt_err RpreInv RpostInv post' t1 t2.
Admitted.

Definition rel (I1 I2 : Type) := I1 -> I2 -> Prop.

Definition relIO (I1 I2 O1 O2 : Type) := I1 -> I2 -> O1 -> O2 -> Prop.

Section REQUIV.

Context {E:Set}.

Definition fresult T1 T2 := T1 -> result E T2.

Definition requiv_io {I1 I2 O1 O2}
   (P : rel I1 I2) (F1 : fresult I1 O1) (F2 : fresult I2 O2) (Q : relIO I1 I2 O1 O2) :=
  forall i1 i2 o1, P i1 i2 -> F1 i1 = ok o1 -> exists2 o2, F2 i2 = ok o2 & Q i1 i2 o1 o2.

Definition requiv {I1 I2 O1 O2}
   (P : rel I1 I2) (F1 : fresult I1 O1) (F2 : fresult I2 O2) (Q : rel O1 O2) :=
  requiv_io P F1 F2 (fun _ _ => Q).

Lemma requiv_io_weaken {I1 I2 O1 O2} (P P' : rel I1 I2) (Q Q': relIO I1 I2 O1 O2) F1 F2 :
  (forall i1 i2, P' i1 i2 -> P i1 i2) ->
  (forall i1 i2 o1 o2, P' i1 i2 -> Q i1 i2 o1 o2 -> Q' i1 i2 o1 o2) ->
  requiv_io P F1 F2 Q ->
  requiv_io P' F1 F2 Q'.
Proof.
  move=> hP'P hQQ' h i1 i2 o1 hP' hF1.
  have [o2 -> hQ]:= h _ _ _ (hP'P _ _ hP') hF1; eauto.
Qed.

Lemma requiv_weaken {I1 I2 O1 O2} (P P' : rel I1 I2) (Q Q': rel O1 O2) F1 F2 :
  (forall i1 i2, P' i1 i2 -> P i1 i2) ->
  (forall o1 o2, Q o1 o2 -> Q' o1 o2) ->
  requiv P F1 F2 Q ->
  requiv P' F1 F2 Q'.
Proof. move=> hP'P hQQ'; apply requiv_io_weaken => //; auto. Qed.

Lemma requiv_io_ok {I1 I2} (P:rel I1 I2) (Q: relIO I1 I2 I1 I2):
  (forall i1 i2, P i1 i2 -> Q i1 i2 i1 i2) ->
  requiv_io P (@Ok _ _) (@Ok _ _) Q.
Proof. by move=> hPQ i1 i2 o1 hQ [<-]; exists i2 => //; apply hPQ. Qed.

Lemma requiv_ok {I1 I2} (Q:rel I1 I2) : requiv Q (@Ok _ _) (@Ok _ _) Q.
Proof. by apply requiv_io_ok. Qed.

Lemma requiv_io_err {I1 I2 O1 O2} (P:rel I1 I2) (Q: relIO I1 I2 O1 O2) (Err : E) F :
  requiv_io P (fun i1 => Error Err) F Q.
Proof. by move=> ?. Qed.

Lemma requiv_err {I1 I2 O1 O2} (P:rel I1 I2) (Q: rel O1 O2) (Err : E) F :
  requiv P (fun i1 => Error Err) F Q.
Proof. apply requiv_io_err. Qed.

Lemma requiv_io_bind {I1 I2 T1 T2 O1 O2}
  (R : relIO I1 I2 T1 T2)
  (P : rel I1 I2)
  (Q : relIO I1 I2 O1 O2) F1 F1' F2 F2' :
  requiv_io P F1 F2 R ->
  (forall i1 i2, P i1 i2 -> requiv (R i1 i2) F1' F2' (Q i1 i2)) ->
  requiv_io P (fun i => F1 i >>r= F1') (fun i => F2 i >>r= F2') Q.
Proof.
  move=> h h' i1 i2 o1 hP; t_xrbindP => t1 /(h _ _ _ hP) [t2 -> /= hR].
  by apply: h'.
Qed.

Lemma requiv_bind {I1 I2 T1 T2 O1 O2}
  (R : rel T1 T2)
  (P : rel I1 I2)
  (Q : rel O1 O2) F1 F1' F2 F2' :
  requiv P F1 F2 R ->
  requiv R F1' F2' Q ->
  requiv P (fun i => F1 i >>r= F1') (fun i => F2 i >>r= F2') Q.
Proof. by move=> h h'; apply requiv_io_bind with (R:= fun _ _ => R). Qed.

Lemma requiv_bind2 {I1 I2 U1 U2 T1 T2 O1 O2}
  (R : rel T1 T2) (P : rel I1 I2) (Q : rel O1 O2)
  (F1 : U1 -> I1 -> result E T1) (F1' : T1 -> I1 -> result E O1)
  (F2 : U2 -> I2 -> result E T2) (F2' : T2 -> I2 -> result E O2)
  u1 u2 :
  requiv P (F1 u1) (F2 u2) R ->
  (forall t1 t2, R t1 t2 -> requiv P (F1' t1) (F2' t2) Q) ->
  requiv P (fun i => Let t := F1 u1 i in F1' t i)
           (fun i => Let t := F2 u2 i in F2' t i) Q.
Proof.
  move=> hF hF' i1 i2 o1 hP; t_xrbindP.
  by move => t1 /(hF _ _ _ hP) [t2 -> /hF'] /=; apply.
Qed.

Lemma requiv_eq {I O} (F: fresult I O) : requiv eq F F eq.
Proof. move=> i _ o <-; eauto. Qed.

Lemma requiv_mapM {I1 I2 O1 O2} (P : rel I1 I2) (Q : rel O1 O2) F1 F2 :
  requiv P F1 F2 Q ->
  requiv (List.Forall2 P) (mapM F1) (mapM F2) (List.Forall2 Q).
Proof.
  move=> heqv s1; elim: s1 => [ | i1 is1 hrec] [ | i2 is2] os /List_Forall2_inv //=.
  + by move=> _ [<-]; eauto.
  move=> [hP halli]; t_xrbindP => o1 ho1 os1 hos1 <-.
  have [o2 -> /= hQ] := heqv _ _ _ hP ho1.
  have [os2 -> /= hallo] := hrec _ _ halli hos1; eauto.
Qed.

Lemma requiv_fold2 {A1 B1 A2 B2 R1 R2} (Err : E)
  (I: rel R1 R2) (PA : rel A1 A2) (PB : rel B1 B2)
  (F1 : A1 -> B1 -> R1 -> result E R1) (F2 : A2 -> B2 -> R2 -> result E R2)
  (la1 : seq A1) (la2 : seq A2) (lb1 : seq B1) (lb2 : seq B2) :
  Forall2 PA la1 la2 ->
  Forall2 PB lb1 lb2 ->
  (forall a1 a2 b1 b2, PA a1 a2 -> PB b1 b2 -> requiv I (F1 a1 b1) (F2 a2 b2) I) ->
  requiv I (fold2 Err F1 la1 lb1) (fold2 Err F2 la2 lb2) I.
Proof.
  move=> halla hallb hF.
  elim: halla lb1 lb2 hallb => {la1 la2}.
  + by move=> _ _ [] => //=; apply requiv_ok.
  move=> a1 a2 la1 la2 hPA halla hrec _ _ [] => //= b1 b2 lb1 lb2 hPB hallb.
  apply requiv_bind with I; auto.
Qed.

Lemma requiv_mapM_all2 {S1 S2 I1 I2 O1 O2} (PS : rel S1 S2) (P : rel I1 I2) (Q : rel O1 O2) F1 F2 is1 is2:
  Forall2 P is1 is2 ->
  (forall s1 s2, PS s1 s2 -> requiv P (F1 s1) (F2 s2) Q) ->
  requiv PS (fun s => mapM (F1 s) is1) (fun s => mapM (F2 s) is2) (Forall2 Q).
Proof.
  move=> his hPQ s1 s2 o1 hPS.
  by apply (requiv_mapM (hPQ _ _ hPS)).
Qed.

End REQUIV.

Lemma requiv_to_bool : requiv value_uincl to_bool to_bool eq.
Proof.
  move=> v1 v2 b1 hu hb1.
  have [b2 /= -> /value_uinclE /= [->]] := val_uincl_of_val (ty:= sbool) hu hb1; eauto.
Qed.

Lemma requiv_to_int : requiv value_uincl to_int to_int eq.
Proof.
  move=> v1 v2 i1 hu hi1.
  have [b2 /= -> /value_uinclE /= [->]] := val_uincl_of_val (ty:= sint) hu hi1; eauto.
Qed.

Lemma requiv_truncate_val ty :
  requiv value_uincl (truncate_val ty) (truncate_val ty) value_uincl.
Proof. move=> v1 v2 v1'; apply value_uincl_truncate. Qed.

Class relEvent (E : Type -> Type) :=
  { HasErr1  :: ErrEvent -< E
  ; wE      :: with_Error E
  ; RPreInv  :: prerel E E
  ; RPostInv :: postrel E E }.

Section IEQUIV.

Context {E: Type -> Type} {rE : relEvent E}.

Definition fitree E (I O : Type) := I -> itree E O.

Definition iequiv_io {I1 I2 O1 O2}
   (P : rel I1 I2) (F1 : fitree E I1 O1) (F2 : fitree E I2 O2) (Q : relIO I1 I2 O1 O2) :=
  forall i1 i2, P i1 i2 -> rutt_err RPreInv RPostInv (Q i1 i2) (F1 i1) (F2 i2).

Definition iequiv {I1 I2 O1 O2}
   (P : rel I1 I2) (F1 : fitree E I1 O1) (F2 : fitree E I2 O2) (Q : rel O1 O2) :=
   iequiv_io P F1 F2 (fun i1 i2 => Q).

Lemma iequiv_io_weaken {I1 I2 O1 O2} (P P' : rel I1 I2) (Q Q': relIO I1 I2 O1 O2) F1 F2 :
  (forall i1 i2, P' i1 i2 -> P i1 i2) ->
  (forall i1 i2 o1 o2, P' i1 i2 -> Q i1 i2 o1 o2 -> Q' i1 i2 o1 o2) ->
  iequiv_io P F1 F2 Q ->
  iequiv_io P' F1 F2 Q'.
Proof.
  move=> hP'P hQQ' heqv i1 i2 hP'.
  apply rutt_err_weaken with (Q i1 i2).
  + by move=> >; apply hQQ'.
  by apply/heqv/hP'P.
Qed.

Lemma iequiv_weaken {I1 I2 O1 O2} (P P' : rel I1 I2) (Q Q': rel O1 O2) F1 F2 :
  (forall i1 i2, P' i1 i2 -> P i1 i2) ->
  (forall o1 o2, Q o1 o2 -> Q' o1 o2) ->
  iequiv P F1 F2 Q ->
  iequiv P' F1 F2 Q'.
Proof. move=> hP hQ; apply iequiv_io_weaken => // > _; apply hQ. Qed.

Lemma iequiv_io_ret {I1 I2} (P: rel I1 I2) (Q : relIO I1 I2 I1 I2) :
  (forall i1 i2, P i1 i2 -> Q i1 i2 i1 i2) ->
  iequiv_io P (fun i => Ret i) (fun i => Ret i) Q.
Proof. by move=> hPQ i1 i2 hP; apply/rutt_Ret/hPQ. Qed.

Lemma iequiv_ret {I1 I2} (Q: rel I1 I2) :
  iequiv Q (fun i => Ret i) (fun i => Ret i) Q.
Proof. by apply iequiv_io_ret. Qed.

Lemma iequiv_io_bind {I1 I2 T1 T2 O1 O2}
  (R : relIO I1 I2 T1 T2)
  (P : rel I1 I2)
  (Q : relIO I1 I2 O1 O2) F1 F1' F2 F2' :
  iequiv_io P F1 F2 R ->
  (forall i1 i2, P i1 i2 -> iequiv (R i1 i2) F1' F2' (Q i1 i2)) ->
  iequiv_io P (fun i => t <- F1 i;; F1' t) (fun i => t <- F2 i;; F2' t) Q.
Proof.
  move=> h h' i1 i2 hP.
  apply rutt_bind with (R i1 i2); first by apply h.
  by move=> t1 t2 hR; apply h'.
Qed.

Lemma iequiv_bind {I1 I2 T1 T2 O1 O2}
  (R : rel T1 T2)
  (P : rel I1 I2)
  (Q : rel O1 O2) F1 F1' F2 F2' :
  iequiv P F1 F2 R ->
  iequiv R F1' F2' Q ->
  iequiv P (fun i => t <- F1 i;; F1' t) (fun i => t <- F2 i;; F2' t) Q.
Proof. by move=> h h'; apply iequiv_io_bind with (R := fun t1 t2 => R). Qed.

End IEQUIV.

(* Definition of a relational logic over program *)

Section WSW.

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

Section IRESULT.
Context {E: Type -> Type} {rE: relEvent E}.

Lemma rutt_iresult (T1 T2:Type) (s1 : estate1) (s2 : estate2) (x1 : exec T1) (x2 : exec T2) (R : T1 -> T2 -> Prop) :
  (forall v1, x1 = ok v1 -> exists2 v2, x2 = ok v2 & R v1 v2) ->
  rutt_err RPreInv RPostInv R (iresult s1 x1) (iresult s2 x2).
Proof.
  case: x1 => [ v1 | e1] hok.
  + have [v2 -> /=] := hok _ erefl.
    by apply: rutt_Ret.
  apply rutt_CutL => //.
  by rewrite /ErrorCutoff /= is_error_has.
Qed.

End IRESULT.

Class sem_call_2 {E : Type -> Type} {rE: relEvent E} :=
 { sem_call1 : prog1 -> extra_val_t1 -> funname -> fstate -> itree E fstate
 ; sem_call2 : prog2 -> extra_val_t2 -> funname -> fstate -> itree E fstate }.

#[global]
Instance sc2_full {E : Type -> Type} {rE: relEvent E} : sem_call_2 | 100 :=
  {| sem_call1 := isem_fun1
   ; sem_call2 := isem_fun2 |}.

Section TR_MutualRec.

Context (RPreF : funname -> funname -> fstate -> fstate -> Prop).
Context (RPostF : funname -> funname -> fstate -> fstate -> fstate -> fstate -> Prop).

Context {E: Type -> Type} {rE:relEvent E}.
Notation recCall := (callE (funname * fstate) fstate).

Definition RPreD {T1 T2} (d1 : recCall T1)
                         (d2 : recCall T2) : Prop :=
  match d1, d2 with
  | Call (fn1, fs1), Call (fn2, fs2) => RPreF fn1 fn2 fs1 fs2
  end.

Definition RPostD {T1 T2} (d1 : recCall T1) (t1: T1) (d2 : recCall T2) (t2: T2) : Prop :=
  match d1 in callE _ _ T1_ return T1_ -> T2 -> Prop with
  | Call (fn1, fs1) =>
    match d2 in callE _ _ T2_ return fstate -> T2_ -> Prop with
    | Call (fn2, fs2) => RPostF fn1 fn2 fs1 fs2
    end
  end t1 t2.

Definition relEvent_recCall : relEvent (recCall +' E).
econstructor.
+ apply with_Error_suml.
+ exact (sum_prerel (@RPreD) RPreInv).
+ exact (sum_postrel (@RPostD) RPostInv).
Defined.

Definition sc2_rec : sem_call_2 (rE := relEvent_recCall) :=
  {| sem_call1 := rec_call (E:=E)
   ; sem_call2 := rec_call (E:=E) |}.

End TR_MutualRec.

Section EQUIV_CORE.

Context {E : Type -> Type} {rE: relEvent E}.

Lemma iequiv_iresult (P Q : rel estate1 estate2) (F1 : estate1 -> exec estate1) (F2: estate2 -> exec estate2) :
  requiv P F1 F2 Q ->
  iequiv P (fun s => iresult s (F1 s)) (fun s => iresult s (F2 s)) Q.
Proof. by move=> h s1 s2 hP; apply rutt_iresult => s1'; apply: h. Qed.

Context {SC2 : sem_call_2} (p1 : prog1) (p2 : prog2) (ev1: extra_val_t1) (ev2 : extra_val_t2).

Definition relPreF := funname -> funname -> fstate -> fstate -> Prop.
Definition relPostF := funname -> funname -> fstate -> fstate -> fstate -> fstate -> Prop.

Definition rel_e := rel pexpr pexpr.
Definition rel_v := rel value value.
Definition rel_vs := rel values values.
Definition rel_c := rel estate1 estate2.

Definition equiv_f (P : relPreF) (fn1 fn2 : funname) (Q:relPostF) :=
  iequiv_io (P fn1 fn2) (sem_call1 p1 ev1 fn1) (sem_call2 p2 ev2 fn2) (Q fn1 fn2).

Definition equiv_f_body (P : relPreF) (fn1 fn2 : funname) (Q:relPostF) :=
  iequiv_io (P fn1 fn2)
            (isem_funcall (dc:=dc1) sem_call1 p1 ev1 fn1) (isem_funcall (dc:=dc2) sem_call2 p2 ev2 fn2)
            (Q fn1 fn2).

Definition equiv (pre:rel_c) (c1 c2 : cmd) (post : rel_c) :=
  iequiv pre (isem_cmd_ (dc:=dc1) sem_call1 p1 ev1 c1) (isem_cmd_ (dc:=dc2) sem_call2 p2 ev2 c2) post.

Lemma equiv_weaken P1 P2 Q1 Q2 c1 c2 :
  (forall s1 s2, P1 s1 s2 -> P2 s1 s2) ->
  (forall s1 s2, Q2 s1 s2 -> Q1 s1 s2) ->
  equiv P2 c1 c2 Q2 ->
  equiv P1 c1 c2 Q1.
Proof. by apply iequiv_weaken. Qed.

Lemma equiv_cat (R P Q : rel_c) (c1 c1' c2 c2' : cmd) :
  equiv P c1 c2 R ->
  equiv R c1' c2' Q ->
  equiv P (c1 ++ c1') (c2 ++ c2') Q.
Proof.
  move=> h h' s1 s2 hP; rewrite !isem_cmd_cat.
  apply rutt_bind with R; first by apply h.
  apply h'.
Qed.

Lemma equiv_nil Q : equiv Q [::] [::] Q.
Proof. apply iequiv_ret. Qed.

Lemma equiv_cons (R P Q : rel_c) (i1 i2 : instr) (c1 c2 : cmd) :
  equiv P [::i1] [::i2] R ->
  equiv R c1 c2 Q ->
  equiv P (i1 :: c1) (i2 :: c2) Q.
Proof. rewrite -(cat1s i1 c1) -(cat1s i2 c2); apply equiv_cat. Qed.

Lemma equiv_assgn (Rv Rtr: rel_v) (P Q : rel_c) ii1 x1 tg1 ty1 e1 ii2 x2 tg2 ty2 e2 :
  requiv P (fun s => sem_pexpr true (p_globs p1) s e1)
           (fun s => sem_pexpr true (p_globs p2) s e2) Rv ->
  requiv Rv (truncate_val ty1) (truncate_val ty2) Rtr ->
  (forall v1 v2, Rtr v1 v2 ->
    requiv P (write_lval true (p_globs p1) x1 v1) (write_lval true (p_globs p2) x2 v2) Q) ->
  equiv P [:: MkI ii1 (Cassgn x1 tg1 ty1 e1)] [:: MkI ii2 (Cassgn x2 tg2 ty2 e2)] Q.
Proof.
  move=> he htr hwr; rewrite /equiv /isem_cmd_ /=.
  apply iequiv_bind with Q; last apply iequiv_ret.
  apply iequiv_iresult; rewrite /sem_assgn.
  move=> s1 s2 s1' hP.
  t_xrbindP => v1 /(he _ _ _ hP) [v2 -> /= hv] v1' /(htr _ _ _ hv) [v2' ->] hv' /=.
  by apply hwr.
Qed.

Lemma equiv_assgn_eq (P Q : rel_c) ii1 x1 tg1 ty e1 ii2 x2 tg2 e2 :
  requiv P (fun s => sem_pexpr true (p_globs p1) s e1)
           (fun s => sem_pexpr true (p_globs p2) s e2) eq ->
  (forall v, requiv P (write_lval true (p_globs p1) x1 v) (write_lval true (p_globs p2) x2 v) Q) ->
  equiv P [:: MkI ii1 (Cassgn x1 tg1 ty e1)] [:: MkI ii2 (Cassgn x2 tg2 ty e2)] Q.
Proof.
  move=> he hx; apply equiv_assgn with eq eq => //.
  + by apply requiv_eq.
  by move=> > <-; apply hx.
Qed.

Lemma equiv_assgn_uincl (P Q : rel_c) ii1 x1 tg1 ty e1 ii2 x2 tg2 e2 :
  requiv P (fun s => sem_pexpr true (p_globs p1) s e1)
           (fun s => sem_pexpr true (p_globs p2) s e2) value_uincl ->
  (forall v1 v2, value_uincl v1 v2 ->
    requiv P (write_lval true (p_globs p1) x1 v1) (write_lval true (p_globs p2) x2 v2) Q) ->
  equiv P [:: MkI ii1 (Cassgn x1 tg1 ty e1)] [:: MkI ii2 (Cassgn x2 tg2 ty e2)] Q.
Proof. move=> he; apply equiv_assgn with value_uincl => //; apply requiv_truncate_val. Qed.

Lemma equiv_opn (Rve Rvo : rel_vs) P Q ii1 xs1 at1 o1 es1 ii2 xs2 at2 o2 es2 :
  requiv P (fun s => sem_pexprs true (p_globs p1) s es1)
           (fun s => sem_pexprs true (p_globs p2) s es2) Rve ->
  requiv Rve (exec_sopn o1) (exec_sopn o2) Rvo ->
  (forall vs1 vs2,
    Rvo vs1 vs2 -> requiv P (fun s1 => write_lvals true (p_globs p1) s1 xs1 vs1)
                            (fun s2 => write_lvals true (p_globs p2) s2 xs2 vs2) Q) ->
  equiv P [:: MkI ii1 (Copn xs1 at1 o1 es1)] [:: MkI ii2 (Copn xs2 at2 o2 es2)] Q.
Proof.
  move=> he ho hwr; rewrite /equiv /isem_cmd_ /=.
  apply iequiv_bind with Q; last apply iequiv_ret.
  apply iequiv_iresult.
  move=> s1 s2 s1' hP; rewrite /sem_sopn.
  t_xrbindP => vr1 v1 /(he _ _ _ hP) [v2 -> /= hv]  /(ho _ _ _ hv) [v2' ->] hv' /=.
  by apply hwr.
Qed.

Lemma equiv_opn_eq P Q ii1 xs1 at1 o es1 ii2 xs2 at2 es2 :
  requiv P (fun s => sem_pexprs true (p_globs p1) s es1)
           (fun s => sem_pexprs true (p_globs p2) s es2) eq ->
  (forall vs,
    requiv P (fun s1 => write_lvals true (p_globs p1) s1 xs1 vs)
             (fun s2 => write_lvals true (p_globs p2) s2 xs2 vs) Q) ->
  equiv P [:: MkI ii1 (Copn xs1 at1 o es1)] [:: MkI ii2 (Copn xs2 at2 o es2)] Q.
Proof.
  move=> he hx; apply equiv_opn with eq eq => //.
  + by apply requiv_eq.
  by move=> > <-; apply hx.
Qed.

Lemma requiv_exec_sopn o :
  requiv (Forall2 value_uincl) (exec_sopn o) (exec_sopn o) (Forall2 value_uincl).
Proof. move=> vs1 vs2 vs1'; apply vuincl_exec_opn. Qed.

Lemma equiv_opn_uincl P Q ii1 xs1 at1 o es1 ii2 xs2 at2 es2 :
  requiv P (fun s => sem_pexprs true (p_globs p1) s es1)
           (fun s => sem_pexprs true (p_globs p2) s es2) (Forall2 value_uincl) ->
  (forall vs1 vs2,
    Forall2 value_uincl vs1 vs2 ->
    requiv P (fun s1 => write_lvals true (p_globs p1) s1 xs1 vs1)
             (fun s2 => write_lvals true (p_globs p2) s2 xs2 vs2) Q) ->
  equiv P [:: MkI ii1 (Copn xs1 at1 o es1)] [:: MkI ii2 (Copn xs2 at2 o es2)] Q.
Proof.
  move=> he; apply equiv_opn with (Forall2 value_uincl) => //; apply requiv_exec_sopn.
Qed.

Lemma equiv_syscall Rv Ro P Q ii1 xs1 sc1 es1 ii2 xs2 sc2 es2 :
  requiv P (fun s => sem_pexprs true (p_globs p1) s es1)
           (fun s => sem_pexprs true (p_globs p2) s es2) Rv ->
  (forall vs1 vs2,
     Rv vs1 vs2 ->
     requiv P (fun (s:estate1) => fexec_syscall (scP:=scP1) sc1 (mk_fstate vs1 s))
              (fun (s:estate2) => fexec_syscall sc2 (mk_fstate vs2 s)) Ro)->
  (forall fs1 fs2,
    Ro fs1 fs2 ->
    requiv P (upd_estate true (p_globs p1) xs1 fs1)
             (upd_estate true (p_globs p2) xs2 fs2) Q) ->
  equiv P [:: MkI ii1 (Csyscall xs1 sc1 es1)] [:: MkI ii2 (Csyscall xs2 sc2 es2)] Q.
Proof.
  move=> he ho hwr; rewrite /equiv /isem_cmd_ /=.
  apply iequiv_bind with Q; last apply iequiv_ret.
  apply iequiv_iresult.
  move=> s1 s2 s1' hP; rewrite /sem_syscall.
  t_xrbindP => vs1 /(he _ _ _ hP) [vs2 -> /= hvs] fs1.
  by move=> /(ho _ _ hvs _ _ _ hP) [fs2 -> /hwr /=]; apply.
Qed.

Lemma equiv_syscall_eq P Q ii1 xs1 sc1 es1 ii2 sc2 xs2 es2 :
  (forall s1 s2, P s1 s2 -> escs s1 = escs s2 /\ emem s1 = emem s2) ->
  requiv P (fun s => sem_pexprs true (p_globs p1) s es1)
           (fun s => sem_pexprs true (p_globs p2) s es2) eq ->
  requiv eq (fexec_syscall (scP:=scP1) sc1)
            (fexec_syscall (scP:=scP2) sc2) eq ->
  (forall fs,
    requiv P (upd_estate true (p_globs p1) xs1 fs)
             (upd_estate true (p_globs p2) xs2 fs) Q) ->
  equiv P [:: MkI ii1 (Csyscall xs1 sc1 es1)] [:: MkI ii2 (Csyscall xs2 sc2 es2)] Q.
Proof.
  move=> heq he hsc hx.
  apply equiv_syscall with eq eq => //.
  + by rewrite /mk_fstate => > <- s1 s2 fs1 /heq [<- <-]; apply hsc.
  move=> > <-; apply hx.
Qed.

Definition fs_uincl (fs1 fs2: fstate) :=
  [/\ fs1.(fscs) = fs2.(fscs)
    , fs1.(fmem) = fs2.(fmem)
    & Forall2 value_uincl fs1.(fvals) fs2.(fvals)].

Lemma equiv_syscall_uincl P Q ii1 xs1 sc1 es1 ii2 sc2 xs2 es2 :
  (forall s1 s2, P s1 s2 -> escs s1 = escs s2 /\ emem s1 = emem s2) ->
  requiv P (fun s => sem_pexprs true (p_globs p1) s es1)
           (fun s => sem_pexprs true (p_globs p2) s es2) (Forall2 value_uincl) ->
  requiv fs_uincl (fexec_syscall (scP:=scP1) sc1)
                  (fexec_syscall (scP:=scP2) sc2) fs_uincl ->
  (forall fs1 fs2,
    fs_uincl fs1 fs2 ->
    requiv P (upd_estate true (p_globs p1) xs1 fs1)
             (upd_estate true (p_globs p2) xs2 fs2) Q) ->
  equiv P [:: MkI ii1 (Csyscall xs1 sc1 es1)] [:: MkI ii2 (Csyscall xs2 sc2 es2)] Q.
Proof.
  move=> heq he hsc.
  apply equiv_syscall with (Forall2 value_uincl) => //.
  by rewrite /mk_fstate => vs1 vs2 hu s1 s2 fs1 /heq [<- <-]; apply hsc.
Qed.

Lemma equiv_if_full P Q ii1 e1 c1 c1' ii2 e2 c2 c2' :
  requiv P (sem_cond (p_globs p1) e1) (sem_cond (p_globs p2) e2) eq ->
  equiv (fun s1 s2 => [/\ P s1 s2, sem_cond (p_globs p1) e1 s1 = ok true & sem_cond (p_globs p2) e2 s2 = ok true])
        c1 c2 Q ->
  equiv (fun s1 s2 => [/\ P s1 s2, sem_cond (p_globs p1) e1 s1 = ok false & sem_cond (p_globs p2) e2 s2 = ok false])
        c1' c2' Q ->
  equiv P [:: MkI ii1 (Cif e1 c1 c1')] [:: MkI ii2 (Cif e2 c2 c2')] Q.
Proof.
  move=> he hc hc' s1 s2 hP; rewrite /isem_cmd_ /=.
  apply rutt_bind with Q; last by move=> >; apply rutt_Ret.
  apply rutt_bind with (fun b1 b2 =>
     [/\ b1 = b2, sem_cond (p_globs p1) e1 s1 = ok b1 & sem_cond (p_globs p2) e2 s2 = ok b2]).
  + by apply/rutt_iresult => b1 he1; have [b2 he2 heq] := he _ _ _ hP he1; exists b2.
  by move=> [] _ [<- ??]; [apply hc | apply hc'].
Qed.

Lemma equiv_if P Q ii1 e1 c1 c1' ii2 e2 c2 c2' :
  requiv P (sem_cond (p_globs p1) e1) (sem_cond (p_globs p2) e2) eq ->
  equiv P c1 c2 Q ->
  equiv P c1' c2' Q ->
  equiv P [:: MkI ii1 (Cif e1 c1 c1')] [:: MkI ii2 (Cif e2 c2 c2')] Q.
Proof.
  move=> hcond hc hc'; apply equiv_if_full => //.
  + by apply: equiv_weaken hc => // > [].
  by apply: equiv_weaken hc' => // > [].
Qed.

Lemma sem_cond_uincl P e1 e2 :
  requiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s e1)
           (fun (s:estate2) => sem_pexpr true (p_globs p2) s e2) value_uincl ->
  requiv P (sem_cond (p_globs p1) e1) (sem_cond (p_globs p2) e2) eq.
Proof.
  move=> he; rewrite /sem_cond.
  apply: requiv_bind requiv_to_bool; apply he.
Qed.

Lemma equiv_if_uincl P Q ii1 e1 c1 c1' ii2 e2 c2 c2' :
  requiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s e1)
           (fun (s:estate2) => sem_pexpr true (p_globs p2) s e2) value_uincl ->
  equiv P c1 c2 Q ->
  equiv P c1' c2' Q ->
  equiv P [:: MkI ii1 (Cif e1 c1 c1')] [:: MkI ii2 (Cif e2 c2 c2')] Q.
Proof. move=> /sem_cond_uincl; apply equiv_if. Qed.

Lemma equiv_if_eq P Q ii1 e1 c1 c1' ii2 e2 c2 c2' :
  requiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s e1)
           (fun (s:estate2) => sem_pexpr true (p_globs p2) s e2) eq ->
  equiv P c1 c2 Q ->
  equiv P c1' c2' Q ->
  equiv P [:: MkI ii1 (Cif e1 c1 c1')] [:: MkI ii2 (Cif e2 c2 c2')] Q.
Proof. by move=> he; apply equiv_if_uincl; apply: requiv_weaken he => // > <-. Qed.

Lemma equiv_for P Pi ii1 i1 d lo1 hi1 c1 ii2 i2 lo2 hi2 c2 :
  requiv P (sem_bound (p_globs p1) lo1 hi1) (sem_bound (p_globs p2) lo2 hi2) eq ->
  (forall i : Z, requiv P (write_var true i1 (Vint i)) (write_var true i2 (Vint i)) Pi) ->
  equiv Pi c1 c2 P ->
  equiv P [:: MkI ii1 (Cfor i1 (d, lo1, hi1) c1)] [:: MkI ii2 (Cfor i2 (d, lo2, hi2) c2)] P.
Proof.
  move=> hbound hwi hc s1 s2 hP; rewrite /isem_cmd_ /=.
  apply rutt_bind with P; last by move=> >; apply rutt_Ret.
  apply rutt_bind with eq.
  + by apply rutt_iresult => >; apply hbound.
  move=> [vlo vhi] _ <- /=; elim: wrange s1 s2 hP=> [|j js hrec] /= s1 s2 hP.
  + by apply rutt_Ret.
  apply rutt_bind with Pi.
  + by apply rutt_iresult => >; apply hwi.
  move=> r1 r2 hPi; apply rutt_bind with P => //.
  by apply hc.
Qed.

Lemma requiv_sem_bound (P : rel_c) lo1 hi1 lo2 hi2 :
  requiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s lo1)
           (fun (s:estate2) => sem_pexpr true (p_globs p2) s lo2) value_uincl ->
  requiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s hi1)
           (fun (s:estate2) => sem_pexpr true (p_globs p2) s hi2) value_uincl ->
  requiv P (sem_bound (p_globs p1) lo1 hi1) (sem_bound (p_globs p2) lo2 hi2) eq.
Proof.
  move=> hlo hhi; rewrite /sem_bound.
  have h : forall e1 e2,
    requiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s e1)
             (fun (s:estate2) => sem_pexpr true (p_globs p2) s e2) value_uincl ->
    requiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s e1 >>r= to_int)
             (fun (s:estate2) => sem_pexpr true (p_globs p2) s e2 >>r= to_int) eq.
  + by move=> e1 e2 he; apply: requiv_bind requiv_to_int; apply he.
  move=> s1 s2 lh1 hP.
  apply rbindP => vlo /(h _ _ hlo _ _ _ hP) [_ -> <-].
  apply rbindP => vhi /(h _ _ hhi _ _ _ hP) [_ -> <-] [<-] /=; eauto.
Qed.

Lemma equiv_for_uincl P Pi ii1 i1 d lo1 hi1 c1 ii2 i2 lo2 hi2 c2 :
  requiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s lo1)
           (fun (s:estate2) => sem_pexpr true (p_globs p2) s lo2) value_uincl ->
  requiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s hi1)
           (fun (s:estate2) => sem_pexpr true (p_globs p2) s hi2) value_uincl ->
  (forall i : Z, requiv P (write_var true i1 (Vint i)) (write_var true i2 (Vint i)) Pi) ->
  equiv Pi c1 c2 P ->
  equiv P [:: MkI ii1 (Cfor i1 (d, lo1, hi1) c1)] [:: MkI ii2 (Cfor i2 (d, lo2, hi2) c2)] P.
Proof. by move=> hlo hhi; apply/equiv_for/requiv_sem_bound. Qed.

Lemma equiv_for_eq P Pi ii1 i1 d lo1 hi1 c1 ii2 i2 lo2 hi2 c2 :
  requiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s lo1)
           (fun (s:estate2) => sem_pexpr true (p_globs p2) s lo2) eq ->
  requiv P (fun (s:estate1) => sem_pexpr true (p_globs p1) s hi1)
           (fun (s:estate2) => sem_pexpr true (p_globs p2) s hi2) eq ->
  (forall i : Z, requiv P (write_var true i1 (Vint i)) (write_var true i2 (Vint i)) Pi) ->
  equiv Pi c1 c2 P ->
  equiv P [:: MkI ii1 (Cfor i1 (d, lo1, hi1) c1)] [:: MkI ii2 (Cfor i2 (d, lo2, hi2) c2)] P.
Proof.
  move=> hlo hhi; apply equiv_for_uincl.
  + by apply: requiv_weaken hlo => // > <-.
  by apply: requiv_weaken hhi => // > <-.
Qed.

Lemma equiv_while_full I I' ii1 al1 e1 c1 c1' ii2 al2 e2 c2 c2' :
  equiv I c1 c2 I' ->
  requiv I' (sem_cond (p_globs p1) e1) (sem_cond (p_globs p2) e2) eq ->
  equiv (fun s1 s2 =>
    [/\ I' s1 s2, sem_cond (p_globs p1) e1 s1 = ok true & sem_cond (p_globs p2) e2 s2 = ok true]) c1' c2' I ->
  equiv I [:: MkI ii1 (Cwhile al1 c1 e1 c1')] [:: MkI ii2 (Cwhile al2 c2 e2 c2')]
     (fun s1 s2 => [/\ I' s1 s2, sem_cond (p_globs p1) e1 s1 = ok false & sem_cond (p_globs p2) e2 s2 = ok false]).
Proof.
  move=> hc hcond hc' s1 s2 hI; rewrite /isem_cmd_ /=.
  set Q := (fun s1 s2 =>
    [/\ I' s1 s2, sem_cond (p_globs p1) e1 s1 = ok false & sem_cond (p_globs p2) e2 s2 = ok false]).
  apply rutt_bind with Q; last by move=> >; apply rutt_Ret.
  rewrite /isem_while; apply XRuttFacts.rutt_iter with (RI := I) => //.
  move=> {}s1 {}s2 {}hI; rewrite /isem_while_loop.
  apply rutt_bind with I'; first by apply hc.
  move=> {hI} {}s1 {}s2 hI'.
  apply rutt_bind with
    (fun b1 b2 => [/\ b1 = b2, sem_cond (p_globs p1) e1 s1 = ok b1 & sem_cond (p_globs p2) e2 s2 = ok b2]).
  + by apply/rutt_iresult => b1 he1; have [b2 he2 heq] := hcond _ _ _ hI' he1; exists b2.
  move=> [] _ [<- he1 he2].
  + apply rutt_bind with I; first by apply hc'.
    by move=> r1 r2 hI; apply rutt_Ret; constructor.
  by apply rutt_Ret; constructor.
Qed.

Lemma equiv_while I I' ii1 al1 e1 c1 c1' ii2 al2 e2 c2 c2' :
  requiv I' (sem_cond (p_globs p1) e1) (sem_cond (p_globs p2) e2) eq ->
  equiv I c1 c2 I' ->
  equiv I' c1' c2' I ->
  equiv I [:: MkI ii1 (Cwhile al1 c1 e1 c1')] [:: MkI ii2 (Cwhile al2 c2 e2 c2')] I'.
Proof.
  move=> hcond hc hc'.
  apply equiv_weaken with (P2 := I)
    (Q2 := fun s1 s2 =>
      [/\ I' s1 s2, sem_cond (p_globs p1) e1 s1 = ok false & sem_cond (p_globs p2) e2 s2 = ok false]) => //.
  + by move=> > [].
  apply equiv_while_full => //.
  by apply: equiv_weaken hc' => // > [].
Qed.

Lemma equiv_while_uincl I I' ii1 al1 e1 c1 c1' ii2 al2 e2 c2 c2' :
  requiv I' (fun (s:estate1) => sem_pexpr true (p_globs p1) s e1)
            (fun (s:estate2) => sem_pexpr true (p_globs p2) s e2) value_uincl ->
  equiv I c1 c2 I' ->
  equiv I' c1' c2' I ->
  equiv I [:: MkI ii1 (Cwhile al1 c1 e1 c1')] [:: MkI ii2 (Cwhile al2 c2 e2 c2')] I'.
Proof. move=> /sem_cond_uincl; apply equiv_while. Qed.

Lemma equiv_while_eq I I' ii1 al1 e1 c1 c1' ii2 al2 e2 c2 c2' :
  requiv I' (fun (s:estate1) => sem_pexpr true (p_globs p1) s e1)
            (fun (s:estate2) => sem_pexpr true (p_globs p2) s e2) eq ->
  equiv I c1 c2 I' ->
  equiv I' c1' c2' I ->
  equiv I [:: MkI ii1 (Cwhile al1 c1 e1 c1')] [:: MkI ii2 (Cwhile al2 c2 e2 c2')] I'.
Proof. by move=> he; apply equiv_while_uincl; apply: requiv_weaken he => // > <-. Qed.

Lemma equiv_call (Pf : relPreF) (Qf : relPostF) Rv P Q ii1 xs1 fn1 es1 ii2 xs2 fn2 es2 :
  requiv P (fun s => sem_pexprs (~~ (@direct_call dc1)) (p_globs p1) s es1)
           (fun s => sem_pexprs (~~ (@direct_call dc2)) (p_globs p2) s es2) Rv ->
  (forall s1 s2 vs1 vs2,
     P s1 s2 -> Rv vs1 vs2 ->
     Pf fn1 fn2 (mk_fstate vs1 s1) (mk_fstate vs2 s2)) ->
  equiv_f Pf fn1 fn2 Qf ->
  (forall fs1 fs2 fr1 fr2,
    Pf fn1 fn2 fs1 fs2 -> Qf fn1 fn2 fs1 fs2 fr1 fr2 ->
    requiv P (upd_estate (~~ (@direct_call dc1)) (p_globs p1) xs1 fr1)
             (upd_estate (~~ (@direct_call dc2)) (p_globs p2) xs2 fr2) Q) ->
  equiv P [:: MkI ii1 (Ccall xs1 fn1 es1)] [:: MkI ii2 (Ccall xs2 fn2 es2)] Q.
Proof.
  move=> hes hPPf hCall hPQf s1 s2 hP; rewrite /isem_cmd_ /=.
  apply rutt_bind with Q; last by move=> >; apply rutt_Ret.
  apply rutt_bind with Rv.
  + by apply rutt_iresult => >; apply: hes.
  move=> vs1 vs2 hvs.
  set fs1 := mk_fstate vs1 s1; set fs2 := mk_fstate vs2 s2.
  apply rutt_bind with (Qf fn1 fn2 fs1 fs2).
  + by apply/hCall/hPPf.
  move=> fr1 fr2 hr; apply rutt_iresult => >.
  apply (hPQf fs1 fs2 fr1 fr2) => //.
  by apply hPPf.
Qed.

Definition isem_fun_body_hyp (RPreF:relPreF) fn1 fn2 (RPostF:relPostF) :=
  forall fs1 fs2,
  RPreF fn1 fn2 fs1 fs2 ->
  forall fd1, get_fundef (p_funcs p1) fn1 = Some fd1 ->
  exists2 fd2, get_fundef (p_funcs p2) fn2 = Some fd2 &
    exists (P Q : rel_c),
      forall s11, initialize_funcall (dc:=dc1) p1 ev1 fd1 fs1 = ok s11 ->
      exists s21,
        [/\ initialize_funcall (dc:=dc2) p2 ev2 fd2 fs2 = ok s21
          , P s11 s21
          , equiv P fd1.(f_body) fd2.(f_body) Q
          & requiv Q (finalize_funcall (dc:=dc1) fd1) (finalize_funcall (dc:=dc2) fd2) (RPostF fn1 fn2 fs1 fs2)].

Lemma equiv_fun_body RPreF fn1 fn2 RPostF :
  isem_fun_body_hyp RPreF fn1 fn2 RPostF ->
  equiv_f_body RPreF fn1 fn2 RPostF.
Proof.
  move=> hf fs1 fs2 hpre.
  rewrite /isem_funcall.
  have {}hf := hf _ _ hpre.
  rewrite /iget_fundef.
  apply rutt_bind with (fun fd1 fd2 => get_fundef (p_funcs p1) fn1 = Some fd1 /\
                                        get_fundef (p_funcs p2) fn2 = Some fd2).
  + case heq: get_fundef => [fd1 | ] /=.
    + by have [fd2 -> _] := hf _ heq; apply rutt_Ret.
    by apply rutt_CutL; rewrite /ErrorCutoff /= is_error_has.
  move=> fd1 fd2 [hfd1 hfd2]; have := hf fd1 hfd1.
  rewrite hfd2 => -[ _ [<- [P] [Q] {}hf]].
  apply rutt_bind with (fun s1 s2 => initialize_funcall (dc:=dc1) p1 ev1 fd1 fs1 = ok s1 /\
                                     initialize_funcall (dc:=dc2) p2 ev2 fd2 fs2 = ok s2).
  + apply rutt_iresult.
    by move=> s hs; have [s' [?]] := hf _ hs; eauto.
  move=> s1 s1' [hs1 hs1']; have := hf _ hs1.
  rewrite hs1' => -[?] [[<-] hP heqv hpost].
  apply rutt_bind with Q.
  + by apply heqv.
  move=> r1 r2 hQ; apply rutt_iresult.
  by move=> fr1; apply hpost.
Qed.

End EQUIV_CORE.

Section EQUIV_FUN.

Context {E : Type -> Type} {rE : relEvent E}.

Context (p1 : prog1) (p2 : prog2) (ev1: extra_val_t1) (ev2 : extra_val_t2).

Definition equiv_f_rec RPreF fn1 fn2 RPostF :=
  equiv_f (rE:=relEvent_recCall RPreF RPostF) (SC2:=sc2_rec RPreF RPostF) p1 p2 ev1 ev2 RPreF fn1 fn2 RPostF.

Definition equiv_rec (RPreF : relPreF) (RPostF : relPostF) P c1 c2 Q :=
  equiv (rE:=relEvent_recCall RPreF RPostF) (SC2:=sc2_rec RPreF RPostF) p1 p2 ev1 ev2 P c1 c2 Q.

Definition isem_fun_body_hyp_rec (RPreF:relPreF) fn1 fn2 (RPostF:relPostF) :=
  forall fs1 fs2,
  RPreF fn1 fn2 fs1 fs2 ->
  forall fd1, get_fundef (p_funcs p1) fn1 = Some fd1 ->
  exists2 fd2, get_fundef (p_funcs p2) fn2 = Some fd2 &
    exists (P Q : rel_c),
      forall s11, initialize_funcall (dc:=dc1) p1 ev1 fd1 fs1 = ok s11 ->
      exists s21,
        [/\ initialize_funcall (dc:=dc2) p2 ev2 fd2 fs2 = ok s21
          , P s11 s21
          , equiv_rec RPreF RPostF P fd1.(f_body) fd2.(f_body) Q
          & requiv Q (finalize_funcall (dc:=dc1) fd1) (finalize_funcall (dc:=dc2) fd2) (RPostF fn1 fn2 fs1 fs2)].

Lemma isem_fun_ind (RPreF : relPreF) (RPostF : relPostF) :
  ((forall fn1 fn2, equiv_f_rec RPreF fn1 fn2 RPostF) ->
   (forall fn1 fn2, isem_fun_body_hyp_rec RPreF fn1 fn2 RPostF)) ->
  forall fn1 fn2,
  equiv_f (rE:=rE) (SC2:=sc2_full) p1 p2 ev1 ev2 RPreF fn1 fn2 RPostF.
Proof.
  have hrec : (forall fn1 fn2, equiv_f_rec RPreF fn1 fn2 RPostF).
  + move=> fn1' fn2' fs1' fs2' hpre'; apply rutt_trigger => //.
    + by apply sum_prerel_inl.
    by rewrite /RPostInv /= => fr1 fr2 h; dependent destruction h.
    move=> /(_ hrec) hbody fn1 fn2 fs1 fs2 hpre.

  apply interp_rec_rutt_err with (RPreInv := @RPreD RPreF) (RPostInv := @RPostD RPostF).
    + move=> {hpre fn1 fn2 fs1 fs2}.
      move=> R1 R2 [[fn1 fs1]] [[fn2 fs2]] /=hpre.
      by apply (equiv_fun_body (hbody fn1 fn2) hpre).
      unfold RPreD; eauto.
      unfold RPreD; eauto.
Qed.       

End EQUIV_FUN.

End WSW.

Section TEST.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {asm_op: Type}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {wsw: WithSubWord}
  {scP : semCallParams}
  {dc: DirectCall}.

Context {E : Type -> Type} {rE : relEvent E}.

Context (tr_lval : lval -> lval)
        (tr_expr : pexpr -> pexpr).

Local Notation tr_lvals ls := (map tr_lval ls).
Local Notation tr_exprs es := (map tr_expr es).

Fixpoint tr_i (i : instr) : instr :=
  let: (MkI ii i) := i in
  let i' :=
    match i with
    | Cassgn x tg ty e => Cassgn (tr_lval x) tg ty (tr_expr e)
    | Copn xs tg o es =>
        Copn (tr_lvals xs) tg o (tr_exprs es)
    | Csyscall xs sc es =>
        Csyscall (tr_lvals xs) sc (tr_exprs es)
    | Cif e c1 c2 => Cif (tr_expr e) (map tr_i c1) (map tr_i c2)
    | Cfor i (d, lo, hi) c => Cfor i (d, tr_expr lo, tr_expr hi) (map tr_i c)
    | Cwhile a c1 e c2 => Cwhile a (map tr_i c1) (tr_expr e) (map tr_i c2)
    | Ccall xs fn es => Ccall (tr_lvals xs) fn (tr_exprs es)
    end in
  MkI ii i'.

Local Notation tr_c := (map tr_i).

Definition tr_fundef (f: fundef) : fundef :=
  {| f_info := f_info f
   ; f_tyin := f_tyin f
   ; f_params := f_params f
   ; f_body := tr_c (f_body f)
   ; f_tyout := f_tyout f
   ; f_res := f_res f
   ; f_extra := f_extra f |}.

Context (p1 : prog) (ev:extra_val_t).

Let p2 := map_prog tr_fundef p1.

Definition RPreFeq (fn1 fn2 : funname) (fs1 fs2 : fstate) := fn1 = fn2 /\ fs1 = fs2.
Definition RPostFeq (fn1 fn2 : funname) (fs1 fs2 fr1 fr2: fstate) := fr1 = fr2.

Context (tr_exprP : forall wdb gd e,
  requiv eq (fun s => sem_pexpr wdb gd s e) (fun s => sem_pexpr wdb gd s (tr_expr e)) eq).

Context (tr_lvalP : forall wdb gd x v,
   requiv eq (write_lval wdb gd x v) (write_lval wdb gd (tr_lval x) v) eq).

Context (tr_exprsP : forall wdb gd es,
   requiv eq ((sem_pexprs wdb gd)^~ es) ((sem_pexprs wdb gd)^~ (tr_exprs es)) eq).

Context (tr_lvalsP : forall wdb gd x v,
   requiv eq (fun s => write_lvals wdb gd s x v) (fun s => write_lvals wdb gd s (tr_lvals x) v) eq).

Lemma eq_globs : p_globs p1 = p_globs p2.
Proof. done. Qed.

Lemma tr_updP wdb xs fs :
  requiv eq (upd_estate wdb (p_globs p1) xs fs) (upd_estate wdb (p_globs p2) (tr_lvals xs) fs) eq.
Admitted.

Lemma Tr_fundefP fn : equiv_f p1 p2 ev ev RPreFeq fn fn RPostFeq.
Proof.
 apply isem_fun_ind => hrec {fn}.
 move=> fn _ fs _ [<- <-] fd hget.
 exists (tr_fundef fd).
 + by rewrite get_map_prog hget.
 move=> {hget}; exists eq, eq => s1 hinit.
 exists s1; split => //; last first.
 + by move=> s1' _ fr1 <- hfinal; exists fr1.
 set Pi := fun (i:instr) => equiv_rec p1 p2 ev ev RPreFeq RPostFeq eq [::i] [::tr_i i] eq.
 set Pr := fun (i:instr_r) => forall ii, Pi (MkI ii i).
 set Pc := fun (c:cmd) => equiv_rec p1 p2 ev ev RPreFeq RPostFeq eq c (tr_c c) eq.
 move=> {fn fs hinit}.
 apply (cmd_rect (Pr := Pr) (Pi:=Pi) (Pc:=Pc)) => // {fd}.
 + by apply equiv_nil.
 + by move=> i c; apply equiv_cons.
 + by move=> x tg ty e ii; apply equiv_assgn_eq.
 + by move=> xs t o es ii; apply equiv_opn_eq.
 + move=> xs o es ii; apply equiv_syscall_eq => //.
   + by move=> > <-.
   + by apply requiv_eq.
   by apply tr_updP.
 + by move=> e c1 c2 hc1 hc2 ii; apply equiv_if_eq.
 + move=> j d lo hi c hc ii; apply equiv_for_eq with eq => //.
   by move=> i s _ s' <-; eauto.
 + by move=> al c e c' hc hc' ii; apply equiv_while_eq.
 move=> xs f es ii; apply equiv_call with RPreFeq RPostFeq eq => //.
 + by move=> > <- <-.
 + by apply hrec.
 move=> fs1 fs2 fr _ _ <-.
 by apply tr_updP.
Qed.

End TEST.

