(* * The semantics of an instruction, from its total semantics and its
   conditions.

   An instruction is described like an operator (see [op_semi.v]), by a total
   semantics, a list of conditions on its arguments and the error it raises
   when one of them fails; [mk_semi] assembles them.  Two things are specific
   to the instructions: an instruction has several outputs, some of which may
   be left undefined (one condition of [seq safety_cond] per output says when
   an output is defined).

   Only the definitions and the lemmas the descriptors require are here; what
   else is proved about them is in [sopn_semi_facts.v]. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Export safety_cond.
Require Import values.
Import Utf8.

Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** Total tuples and filtering                                         *)

(* Like [sem_tuple], but boolean components are [bool] instead of
   [option bool]: the result of a total semantics. *)
Definition sem_tuple_t (ts : seq ctype) := ltuple (map sem_t ts).

(* A boolean component is kept when the mask says so, every other component is
   left untouched. *)
Definition filter_ot (b : bool) (t : ctype) : sem_t t -> sem_ot t :=
  if t is cbool then (fun x => if b then Some x else None) else id.

(* A component whose condition holds is the value itself. *)
Lemma filter_ot_true t (x : sem_t t) : filter_ot true x = sem_prod_id x.
Proof. by case: t x. Qed.

Fixpoint filter_tuple (ts : seq ctype) (mask : seq bool) : sem_tuple_t ts -> sem_tuple ts :=
  match ts return sem_tuple_t ts -> sem_tuple ts with
  | [::] => fun _ => tt
  | t :: ts =>
    let rec := @filter_tuple ts (behead mask) in
    match ts return (sem_tuple_t ts -> sem_tuple ts) ->
                    sem_tuple_t (t :: ts) -> sem_tuple (t :: ts) with
    | [::] => fun _ (x : sem_t t) => filter_ot (head false mask) x
    | t1 :: ts' => fun rec (p : sem_t t * sem_tuple_t (t1 :: ts')) =>
        (filter_ot (head false mask) p.1, rec p.2)
    end rec
  end.
Arguments filter_tuple : clear implicits.

(* Value given by the total semantics of an instruction to a boolean output it
   leaves undefined. It mirrors the abstract [undefined_flag] of the EasyCrypt
   model (eclib/JWord.ec), which is what the extraction computes for such an
   output. *)
Definition undefined_flag : bool := false.
Global Opaque undefined_flag.

(* A boolean component whose condition fails is [undefined_flag], every other
   component is left untouched. *)
Definition dflt_ot (b : bool) (t : ctype) : sem_t t -> sem_t t :=
  if t is cbool then (fun x => if b then x else undefined_flag) else id.

Fixpoint dflt_mask_tuple (ts : seq ctype) (mask : seq bool) : sem_tuple_t ts -> sem_tuple_t ts :=
  match ts return sem_tuple_t ts -> sem_tuple_t ts with
  | [::] => fun t => t
  | t :: ts =>
    let rec := @dflt_mask_tuple ts (behead mask) in
    match ts return (sem_tuple_t ts -> sem_tuple_t ts) ->
                    sem_tuple_t (t :: ts) -> sem_tuple_t (t :: ts) with
    | [::] => fun _ (x : sem_t t) => dflt_ot (head false mask) x
    | t1 :: ts' => fun rec (p : sem_t t * sem_tuple_t (t1 :: ts')) =>
        (dflt_ot (head false mask) p.1, rec p.2)
    end rec
  end.
Arguments dflt_mask_tuple : clear implicits.

(* The total semantics of an instruction gives [undefined_flag] to a boolean
   output whose initialisation condition fails: defaulting the outputs by the
   conditions leaves them unchanged. The arguments are collected as values
   along the [sem_prod], as in [mk_semi_aux]. *)
Fixpoint init_dflt_aux (vs : values) (tin tout : seq ctype) (init : seq safety_cond) :
    sem_prod tin (sem_tuple_t tout) -> Prop :=
  match tin return sem_prod tin (sem_tuple_t tout) -> Prop with
  | [::] => fun t => dflt_mask_tuple tout (map (safety_cond_holds vs) init) t = t
  | t :: tin => fun f => forall v, @init_dflt_aux (rcons vs (to_val v)) tin tout init (f v)
  end.
Arguments init_dflt_aux : clear implicits.

Definition init_dflt tin tout init (f : sem_prod tin (sem_tuple_t tout)) : Prop :=
  init_dflt_aux [::] tin tout init f.
Arguments init_dflt : clear implicits.

Definition is_true_cond (c : safety_cond) : bool := if c is IBool true then true else false.

(* A mask that keeps every component defaults nothing. *)
Lemma dflt_mask_tuple_true ts mask (t : sem_tuple_t ts) :
  size mask = size ts -> all id mask -> dflt_mask_tuple ts mask t = t.
Proof.
elim: ts mask t => [ | t1 ts ih] [ | b mask] //= t [hsz] /andP [hb hall].
have hd : forall x : sem_t t1, dflt_ot b x = x by rewrite hb; case: (t1).
case: ts ih t hsz => [ | t2 ts] ih t hsz /=; first by apply hd.
by case: t => x xs; rewrite hd; congr pair; apply ih.
Qed.

(* Conditions that always hold default nothing. *)
Lemma init_dflt_true tin tout init (f : sem_prod tin (sem_tuple_t tout)) :
  size init = size tout -> all is_true_cond init -> init_dflt tin tout init f.
Proof.
move=> hsz hall; rewrite /init_dflt; elim: tin [::] f => [ | t tin ih] vs f /=; last by move=> v; apply ih.
apply: dflt_mask_tuple_true; first by rewrite size_map.
by rewrite all_map; apply: sub_all hall => -[] // [].
Qed.
Arguments init_dflt_true {tin tout init f} & _ _.

(* A constant semantics satisfies [init_dflt_aux] when its result does under
   every extension of the arguments collected so far. *)
Lemma init_dflt_aux_const vs tl tout init (res : sem_tuple_t tout) :
  (forall vs2, dflt_mask_tuple tout (map (safety_cond_holds (vs ++ vs2)) init) res = res) ->
  init_dflt_aux vs tl tout init (sem_prod_const tl res).
Proof.
elim: tl vs => [ | t tl ih] vs h /=; first by have := h [::]; rewrite cats0.
by move=> v; apply: ih => vs2; rewrite cat_rcons.
Qed.

(* Conditions that hold under every extension of the arguments collected so
   far default nothing. *)
Lemma init_dflt_aux_all_true vs tl tout init (g : sem_prod tl (sem_tuple_t tout)) :
  size init = size tout ->
  (forall vs2, all (safety_cond_holds (vs ++ vs2)) init) ->
  init_dflt_aux vs tl tout init g.
Proof.
move=> hsz; elim: tl vs g => [ | t tl ih] vs g h /=.
+ by apply: dflt_mask_tuple_true; [rewrite size_map | have := h [::]; rewrite cats0 all_map].
by move=> v; apply: ih => vs2; rewrite cat_rcons.
Qed.

(* A transformation of the outputs that preserves the defaulting by the
   conditions, applied after the total semantics, preserves [init_dflt_aux]. *)
Lemma init_dflt_aux_sem_prod_app vs tin tout tout' init init'
    (g : sem_tuple_t tout -> sem_tuple_t tout') (f : sem_prod tin (sem_tuple_t tout)) :
  (forall vs t, dflt_mask_tuple tout (map (safety_cond_holds vs) init) t = t ->
     dflt_mask_tuple tout' (map (safety_cond_holds vs) init') (g t) = g t) ->
  init_dflt_aux vs tin tout init f -> init_dflt_aux vs tin tout' init' (sem_prod_app f g).
Proof.
move=> hg; elim: tin vs f => /= [ | t tin ih] vs f; first by apply hg.
by move=> h v; apply ih.
Qed.

(* A default total tuple, for the operators that have no semantics. *)
Definition dflt_t (t : ctype) : sem_t t :=
  match t return sem_t t with
  | cbool => false
  | cint => 0%Z
  | carr n => WArray.empty n
  | cword ws => 0%w
  end.

Fixpoint dflt_tuple (ts : seq ctype) : sem_tuple_t ts :=
  match ts return sem_tuple_t ts with
  | [::] => tt
  | t :: ts =>
    match ts return sem_tuple_t ts -> sem_tuple_t (t :: ts) with
    | [::] => fun _ => dflt_t t
    | t1 :: ts' => fun r => (dflt_t t, r)
    end (dflt_tuple ts)
  end.

(* Total counterpart of [sem_prod_tuple]: the identity on a tuple of
   arguments, without wrapping the booleans in [Some]. *)
Fixpoint sem_prod_tuple_t (lt : seq ctype) : sem_prod lt (sem_tuple_t lt) :=
  match lt return sem_prod lt (sem_tuple_t lt) with
  | [::] => tt
  | t :: lt' =>
      fun v => sem_prod_app (sem_prod_tuple_t lt') (fun xs => add_tuple v xs)
  end.

(* -------------------------------------------------------------------- *)
(* ** The construction for the instructions                              *)

Definition is_ErrType (e : error) : bool := if e is ErrType then true else false.

(* The semantics of an instruction: the safety conditions are checked on the
   arguments, then the total semantics is filtered by the initialisation
   conditions, one per output; in the [total_init] mode nothing is filtered. *)
Definition mk_semi {sm : SemMode} (tin tout : seq ctype) (safe : seq safety_cond) (err : error)
    (init : seq safety_cond)
    (f : sem_prod tin (sem_tuple_t tout)) : sem_prod tin (exec (sem_tuple tout)) :=
  mk_semi_aux
    (fun vs t => Let _ := check_safe vs safe err in
                 ok (filter_tuple tout
                       (if undef_outputs then map (safety_cond_holds vs) init
                        else nseq (size tout) true) t))
    [::] tin f.
Arguments mk_semi {sm !tin tout} safe err init f / : assert.

(* -------------------------------------------------------------------- *)
(* ** Guarded conditions                                                 *)

(* A condition guarded by the boolean argument that follows the arguments it
   reads is well typed. *)
Lemma safety_cond_wt_guarded tin tin' c :
  safety_cond_wt tin c -> safety_cond_wt (tin ++ cbool :: tin') (sc_guarded (size tin) c).
Proof.
rewrite /safety_cond_wt /sc_guarded /sc_or /sc_not /=
  => /eqP /safety_cond_type_cat -> /=.
rewrite size_cat /= nth_cat ltnn subnn /=.
by have -> : (size tin < size tin + (size tin').+1)%nat by rewrite -addn1 leq_add2l.
Qed.

Lemma safety_cond_holds_guarded_wt (ts : seq ctype) (vs0 vs2 : values) (b : bool) (c : safety_cond) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) ts vs0 ->
  safety_cond_wt ts c ->
  safety_cond_holds (vs0 ++ Vbool b :: vs2) (sc_guarded (size ts) c)
  = (~~ b) || safety_cond_holds vs0 c.
Proof.
move=> hall hwt.
have hsz : size ts = size vs0 by apply: Forall2_size hall.
have [x hx] := safety_cond_type_ok hall (eqP hwt).
have hbelow : safety_cond_below (size vs0) c.
+ by rewrite -hsz; apply: (safety_cond_type_below (eqP hwt)).
have -> : safety_cond_holds vs0 c = x by rewrite /safety_cond_holds hx.
by rewrite hsz; apply: (@safety_cond_holds_guarded vs0 vs2 b c x hbelow hx).
Qed.

(* The mask seen by the generic construction under a guard: everything is
   defined when the guard is false, and the original mask otherwise. *)
Lemma safety_cond_holds_guarded_map (ts : seq ctype) (vs0 : values) (init : seq safety_cond) (b : bool)
    (vs2 : values) (n : nat) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) ts vs0 ->
  all (safety_cond_wt ts) init ->
  size init = n ->
  map (safety_cond_holds (rcons vs0 (Vbool b) ++ vs2)) (map (sc_guarded (size ts)) init)
  = (if b then map (safety_cond_holds vs0) init else nseq n true).
Proof.
move=> hall hwt <-; rewrite cat_rcons.
elim: init hwt => [ | c init ih] /=; first by case: b.
move=> /andP [hwc hwt].
rewrite (safety_cond_holds_guarded_wt vs2 b hall hwc) (ih hwt) => {ih}.
by case: b.
Qed.
