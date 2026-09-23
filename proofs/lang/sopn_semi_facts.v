(* * Facts about the semantics of the instructions.

   [sopn_semi.v] is in the extraction cone and contains definitions only; what
   is proved about [mk_semi], about the filtering of the undefined outputs and
   about the conditions of a guarded instruction is here. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import sopn_semi safety_cond_facts values.
Import Utf8.

Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** Filtering the undefined outputs                                    *)

Lemma filter_add_tuple (t : ctype) (lt : seq ctype) (b : bool) (mask : seq bool)
   (v : sem_t t) (xs : sem_tuple_t lt) :
  filter_tuple (t :: lt) (b :: mask) (add_tuple v xs)
  = add_tuple (filter_ot b v) (filter_tuple lt mask xs).
Proof. by case: lt xs => [ | t1 lt] xs //=; case: xs. Qed.

(* -------------------------------------------------------------------- *)
(* ** Generic properties of the construction                             *)

(* Two pointwise equal post-treatments give two equal semantics. *)
Lemma mk_semi_aux_eq {T T'} (P Q : values -> T -> exec T') vs tin (f : sem_prod tin T) :
  (forall vs t, P vs t = Q vs t) ->
  sem_prod_eq tin (mk_semi_aux P vs tin f) (mk_semi_aux Q vs tin f).
Proof. by move=> h; elim: tin vs f => /= [vs f | t tin ih vs f v]; [apply h | apply ih]. Qed.

(* An application of the construction: the arguments are truncated, the total
   semantics is applied, then [P] sees the truncated arguments and the result. *)
Lemma mk_semi_aux_app_sopnE {T T'} (P : values -> T -> exec T') vs0 tin (f : sem_prod tin T) vs :
  app_sopn tin (mk_semi_aux P vs0 tin f) vs =
  (Let vs' := mapM2 ErrType truncate_val tin vs in
   Let t := app_sopn tin (sem_prod_ok tin f) vs in P (vs0 ++ vs') t).
Proof.
elim: tin f vs vs0 => /= [f [|v vs] vs0 | t tin ih f [|v vs] //= vs0].
+ by rewrite /= cats0.
+ by [].
rewrite /truncate_val; case: (of_val t v) => //= x.
rewrite ih; case: mapM2 => //= lc; case: app_sopn => //= t0.
by rewrite cat_rcons.
Qed.

(* Post-composing the result is the same as post-composing the post-treatment. *)

Lemma mk_semi_aux_ok_cat {T T'} (P : values -> T -> exec T') (g : T -> T') vs1
    (tin : seq ctype) (f : sem_prod tin T) :
  (forall vs2 t, P (vs1 ++ vs2) t = ok (g t)) ->
  sem_prod_eq tin (mk_semi_aux P vs1 tin f) (sem_prod_ok tin (sem_prod_app f g)).
Proof.
elim: tin vs1 f => /= [vs1 f h | t tin ih vs1 f h v].
+ by have := h [::] f; rewrite cats0.
by apply: ih => vs2 t2; rewrite cat_rcons h.
Qed.

(* Same, when the total semantics is a constant. *)
Lemma mk_semi_aux_const {T T'} (P : values -> T -> exec T') vs1
    (tin : seq ctype) (t0 : T) (r : exec T') :
  (forall vs2, P (vs1 ++ vs2) t0 = r) ->
  sem_prod_eq tin (mk_semi_aux P vs1 tin (sem_prod_const tin t0)) (sem_prod_const tin r).
Proof.
elim: tin vs1 => /= [vs1 h | t tin ih vs1 h v].
+ by have := h [::]; rewrite cats0.
by apply: ih => vs2; rewrite cat_rcons h.
Qed.

Lemma sem_prod_ok_app {A} (lt : seq ctype) (X : sem_prod lt A) :
  sem_prod_eq lt (sem_prod_ok lt X) (sem_prod_app X (fun a : A => ok a)).
Proof. by elim: lt X => //= t lt ih X v. Qed.

Lemma sem_prod_app_comp {A B C} (lt : seq ctype) (f : sem_prod lt A)
    (g : A -> B) (h : B -> C) :
  sem_prod_eq lt (sem_prod_app (sem_prod_app f g) h) (sem_prod_app f (fun x => h (g x))).
Proof. by elim: lt f => //= t lt ih f v. Qed.

(* Building a tuple out of the arguments and filtering it with an all-true
   mask is building the tuple of the semantics. *)
Lemma sem_prod_tuple_filter {A} (lt : seq ctype) (mask : seq bool)
      (K : sem_tuple lt -> A) (K' : sem_tuple_t lt -> A) :
  all id mask -> size mask = size lt ->
  (forall t, K' t = K (filter_tuple lt mask t)) ->
  sem_prod_eq lt (sem_prod_app (sem_prod_tuple_t lt) K') (sem_prod_app (sem_prod_tuple lt) K).
Proof.
elim: lt mask K K'.
+ by move=> mask K K' _ _ h /=; rewrite h.
move=> t lt ih [ | b mask] // K K' /andP [hb hall] [hsz] h v /=.
apply: sem_prod_eq_trans; first by apply: sem_prod_app_comp.
apply: sem_prod_eq_trans; last by apply: sem_prod_eq_sym; apply: sem_prod_app_comp.
apply: (ih mask _ _ hall hsz) => t2.
by rewrite h filter_add_tuple hb filter_ot_true.
Qed.

(* -------------------------------------------------------------------- *)
(* ** Guarded conditions                                                 *)

Lemma safety_cond_holds_cond_init (vs0 vs2 : values) (b : bool) (c : safety_cond) (bb : bool) :
  safety_cond_below (size vs0) c ->
  sem_safety_cond vs0 c = ok (Vbool bb) ->
  safety_cond_holds (vs0 ++ Vbool b :: vs2) (cond_init (size vs0) c) = (~~ b) || bb.
Proof. exact: safety_cond_holds_guarded. Qed.

Lemma cond_init_val (ts : seq ctype) (vs0 vs2 : values) (b : bool) (c : safety_cond) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) ts vs0 ->
  safety_cond_total c -> safety_cond_wt ts c ->
  safety_cond_holds (vs0 ++ Vbool b :: vs2) (cond_init (size ts) c)
  = (~~ b) || safety_cond_holds vs0 c.
Proof.
move=> hall htot hwt.
have hsz : size ts = size vs0 by apply: Forall2_size hall.
have [x hx] := safety_cond_type_ok hall htot (eqP hwt).
have hbelow : safety_cond_below (size vs0) c.
+ by rewrite -hsz; apply: (safety_cond_type_below (eqP hwt)).
have -> : safety_cond_holds vs0 c = x by rewrite /safety_cond_holds hx.
by rewrite hsz; apply: (@safety_cond_holds_cond_init vs0 vs2 b c x hbelow hx).
Qed.

(* The mask seen by the generic construction under a guard: everything is
   defined when the guard is false, and the original mask otherwise. *)
Lemma cond_init_mask (ts : seq ctype) (vs0 : values) (init : seq safety_cond) (b : bool)
    (vs2 : values) (n : nat) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) ts vs0 ->
  all safety_cond_total init -> all (safety_cond_wt ts) init ->
  size init = n ->
  map (safety_cond_holds (rcons vs0 (Vbool b) ++ vs2)) (map (cond_init (size ts)) init)
  = (if b then map (safety_cond_holds vs0) init else nseq n true).
Proof.
move=> hall htot hwt <-; rewrite cat_rcons.
elim: init htot hwt => [ | c init ih] /=; first by case: b.
move=> /andP [htc htot] /andP [hwc hwt].
rewrite (cond_init_val vs2 b hall htc hwc) (ih htot hwt) => {ih}.
by case: b.
Qed.

(* The safety conditions of a conditional instruction are the guarded ones:
   under a false guard they all hold, under a true one they amount to the
   conditions themselves. *)
Lemma safety_cond_holds_all_guarded (ts : seq ctype) (vs0 : values) (safe : seq safety_cond)
    (b : bool) (vs2 : values) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) ts vs0 ->
  all safety_cond_total safe -> all (safety_cond_wt ts) safe ->
  all (safety_cond_holds (rcons vs0 (Vbool b) ++ vs2)) (map (sc_guarded (size ts)) safe)
  = (if b then all (safety_cond_holds vs0) safe else true).
Proof.
move=> hall htot hwt; rewrite cat_rcons.
elim: safe htot hwt => [ | c safe ih] /=; first by case: b.
move=> /andP [] ht htot /andP [] hw hwt.
have hc := cond_init_val vs2 b hall ht hw; rewrite /cond_init in hc.
by rewrite hc (ih htot hwt); case: b {ih hc}.
Qed.
