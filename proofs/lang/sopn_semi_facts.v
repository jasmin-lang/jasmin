(* * Facts about the semantics of the instructions.

   [sopn_semi.v] is in the extraction cone and contains definitions only; what
   is proved about [mk_semi], about the filtering of the undefined outputs and
   about the conditions of a guarded instruction is here. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import safety_cond_facts sopn_semi values.
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
(* ** Defaulting the undefined outputs                                   *)

Lemma undefined_flagE : undefined_flag = false.
Proof. by []. Qed.

(* An undefined boolean component is [undefined_flag], every other component
   is left untouched. *)
Definition ot_dflt (t : ctype) : sem_ot t -> sem_t t :=
  if t is cbool then (fun o => if o is Some b then b else undefined_flag) else id.

Fixpoint sem_tuple_dflt (ts : seq ctype) : sem_tuple ts -> sem_tuple_t ts :=
  match ts return sem_tuple ts -> sem_tuple_t ts with
  | [::] => fun t => t
  | t :: ts =>
    let rec := @sem_tuple_dflt ts in
    match ts return (sem_tuple ts -> sem_tuple_t ts) ->
                    sem_tuple (t :: ts) -> sem_tuple_t (t :: ts) with
    | [::] => fun _ (x : sem_ot t) => ot_dflt x
    | t1 :: ts' => fun rec (p : sem_ot t * sem_tuple (t1 :: ts')) =>
        (ot_dflt p.1, rec p.2)
    end rec
  end.
Arguments sem_tuple_dflt : clear implicits.

(* Filtering by a mask then defaulting is defaulting by the mask. *)
Lemma sem_tuple_dflt_filter ts mask (t : sem_tuple_t ts) :
  sem_tuple_dflt ts (filter_tuple ts mask t) = dflt_mask_tuple ts mask t.
Proof.
have hd : forall b t1 (x : sem_t t1), ot_dflt (filter_ot b x) = dflt_ot b x by move=> [] [].
elim: ts mask t => [ | t1 ts ih] mask //= t; first by case: t.
case: ts ih t => [ | t2 ts] ih t /=; first by apply hd.
by rewrite hd; congr pair; apply ih.
Qed.

(* A value that is undefined takes the default value of its type. *)
Definition value_dflt (v : value) : value :=
  if is_defined v then v else dfl_val (type_of_val v).

(* Seen as values, defaulting a tuple defaults its undefined components. *)
Lemma list_ltuple_dflt ts (t : sem_tuple ts) :
  list_ltuple (filter_tuple ts (nseq (size ts) true) (sem_tuple_dflt ts t)) =
  map value_dflt (list_ltuple t).
Proof.
have hd : forall t1 (x : sem_ot t1),
  oto_val (filter_ot true (ot_dflt x)) = value_dflt (oto_val x).
+ by move=> [] //= [b | ]; rewrite /value_dflt //= undefined_flagE.
elim: ts t => [ | t1 ts ih] //= t.
case: ts ih t => [ | t2 ts] ih t /=; first by rewrite hd.
by case: t => x xs /=; rewrite hd; congr cons; apply ih.
Qed.

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

(* When the post-treatment is known on the arguments prefixed by [vs1]. *)
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
(* ** The [total_init] semantics                                         *)

(* [init_dflt] read on the arguments the semantics is applied to. *)
Lemma init_dflt_aux_app_sopn vs0 tin tout init (f : sem_prod tin (sem_tuple_t tout)) vs vs' t :
  init_dflt_aux vs0 tin tout init f ->
  mapM2 ErrType truncate_val tin vs = ok vs' ->
  app_sopn tin (sem_prod_ok tin f) vs = ok t ->
  dflt_mask_tuple tout (map (safety_cond_holds (vs0 ++ vs')) init) t = t.
Proof.
elim: tin f vs vs0 vs' => [ | ty tin ih] f [ | v vs] //= vs0 vs'.
+ by move=> h [<-] [<-]; rewrite cats0.
rewrite /truncate_val; case: (of_val ty v) => //= x h.
case hm: mapM2 => [lc | ] //= [<-] happ.
by rewrite -cat_rcons; apply: ih (h x) hm happ.
Qed.

(* When the total semantics gives [undefined_flag] to the outputs it leaves
   undefined, the [total_init] semantics is the [total] one where every
   undefined output takes that value. *)
Lemma mk_semi_total_initE tin tout safe err init (f : sem_prod tin (sem_tuple_t tout)) vs :
  init_dflt tin tout init f ->
  app_sopn tin (mk_semi (sm := total_init) safe err init f) vs =
  Let t := app_sopn tin (mk_semi (sm := total) safe err init f) vs in
  ok (filter_tuple tout (nseq (size tout) true) (sem_tuple_dflt tout t)).
Proof.
move=> h; rewrite /mk_semi !mk_semi_aux_app_sopnE.
case hm: mapM2 => [vs' | ] //=; case happ: app_sopn => [t | ] //=.
by rewrite sem_tuple_dflt_filter (init_dflt_aux_app_sopn h hm happ).
Qed.

(* -------------------------------------------------------------------- *)
(* ** Guarded conditions                                                 *)

(* The safety conditions of a conditional instruction are the guarded ones:
   under a false guard they all hold, under a true one they amount to the
   conditions themselves. *)
Lemma safety_cond_holds_all_guarded (ts : seq ctype) (vs0 : values) (safe : seq safety_cond)
    (b : bool) (vs2 : values) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) ts vs0 ->
  all (safety_cond_wt ts) safe ->
  all (safety_cond_holds (rcons vs0 (Vbool b) ++ vs2)) (map (sc_guarded (size ts)) safe)
  = (if b then all (safety_cond_holds vs0) safe else true).
Proof.
move=> hall hwt; rewrite cat_rcons.
elim: safe hwt => [ | c safe ih] /=; first by case: b.
move=> /andP [] hw hwt.
by rewrite (safety_cond_holds_guarded_wt vs2 b hall hw) (ih hwt); case: b {ih}.
Qed.
