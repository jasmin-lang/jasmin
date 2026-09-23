(* * The semantics of an instruction, from its total semantics and its
   conditions.

   An instruction is described like an operator (see [op_semi.v]), by a total
   semantics, a list of conditions on its arguments and the error it raises
   when one of them fails; [mk_semi] assembles them.  Two things are specific
   to the instructions: an instruction has several outputs, some of which may
   be left undefined (one condition of [seq safety_cond] per output says when
   an output is defined), and its safety conditions are the ones of
   [wsize.safe_cond], decided by [values.check_safe_cond].

   Only the definitions and the lemmas the descriptors require are here; what
   else is proved about them is in [sopn_semi_facts.v]. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Export op_semi.
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

(* A default total tuple, for the operators that have no semantics. *)
Definition dflt_t (t : ctype) : sem_t t :=
  match t return sem_t t with
  | cbool => false
  | cint => 0%Z
  | carr n => WArray.empty n
  | cword ws => 0%R
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

(* The safety check of an instruction: its conditions are the old
   [wsize.safe_cond], decided by [values.check_safe_cond]; if one of them
   fails, the instruction raises the error it declares. *)
Definition check_safe_old (vs : values) (safe : seq safe_cond) (err : error) : exec unit :=
  if all (check_safe_cond vs) safe then ok tt else Error err.

(* The semantics of an instruction: the safety conditions are checked on the
   arguments, then the total semantics is filtered by the initialisation
   conditions, one per output. *)
Definition mk_semi (tin tout : seq ctype) (safe : seq safe_cond) (err : error)
    (init : seq safety_cond)
    (f : sem_prod tin (sem_tuple_t tout)) : sem_prod tin (exec (sem_tuple tout)) :=
  mk_semi_aux
    (fun vs t => Let _ := check_safe_old vs safe err in
                 ok (filter_tuple tout (map (safety_cond_holds vs) init) t))
    [::] tin f.
Arguments mk_semi {tin tout} safe err init f : assert.

(* -------------------------------------------------------------------- *)
(* ** Guarded conditions                                                 *)

(* The initialisation condition of a conditional instruction: the output keeps
   its previous value when the guard (the argument [g]) is false, so it is
   defined in that case too. *)
Definition cond_init (g : nat) (c : safety_cond) : safety_cond :=
  sc_or (sc_not (IVar g)) c.

Lemma safety_cond_wt_cond_init tin tin' c :
  safety_cond_wt tin c -> safety_cond_wt (tin ++ cbool :: tin') (cond_init (size tin) c).
Proof.
rewrite /safety_cond_wt /cond_init /sc_or /sc_not /= => /eqP /safety_cond_type_cat -> /=.
rewrite size_cat /= nth_cat ltnn subnn /=.
by have -> : (size tin < size tin + (size tin').+1)%nat by rewrite -addn1 leq_add2l.
Qed.

Lemma safety_cond_total_cond_init g c :
  safety_cond_total c -> safety_cond_total (cond_init g c).
Proof. by move=> h; rewrite /cond_init /= h. Qed.

Lemma safety_cond_wf_cond_init tin tin' c :
  safety_cond_wf tin c -> safety_cond_wf (tin ++ cbool :: tin') (cond_init (size tin) c).
Proof.
by move=> /andP [h1 h2];
  rewrite /safety_cond_wf safety_cond_wt_cond_init // safety_cond_total_cond_init.
Qed.

(* Guarding a condition adds a dependency on the guard. *)
Lemma sc_needed_args_guarded n sc :
  ssrnat.leq (sc_needed_args sc) n ->
  ssrnat.leq (sc_needed_args (Guarded n sc)) (S n).
Proof.
by move=> h; rewrite /= ssrnat.geq_max ssrnat.leqnn /=; apply: (ssrnat.leq_trans h).
Qed.

Lemma all_sc_needed_args_guarded n safe :
  all (fun sc => ssrnat.leq (sc_needed_args sc) n) safe ->
  all (fun sc => ssrnat.leq (sc_needed_args sc) (S n)) (map (Guarded n) safe).
Proof.
by move=> h; rewrite all_map; apply: sub_all h => sc; apply: sc_needed_args_guarded.
Qed.
