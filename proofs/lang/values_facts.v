(* * Facts about the values.

   [values.v] is in the extraction cone; what is proved here about the
   conversions of the values is needed by the proofs only. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
Require Import values.

(* -------------------------------------------------------------------- *)
(* ** Conversions of a defined value                                     *)

(* A value converts to any type smaller than its own. *)
Lemma of_val_defined_ok t v :
  is_defined v -> subctype t (type_of_val v) -> exists x, of_val t v = ok x.
Proof.
case: v => [b | z | len a | ws w | //] _ /=.
1-2: by move=> /subctypeE ->; eexists.
+ by move=> /subctypeE ->; exists a; apply: to_arrK.
by move=> /subctypeE [ws' [-> hle]]; rewrite /= (truncate_word_le _ hle); eexists.
Qed.

Lemma to_val_typed t (x : sem_t t) : type_of_val (to_val x) = t /\ is_defined (to_val x).
Proof. by rewrite type_of_to_val; split => //; case: t x. Qed.

Lemma truncate_val_defined_ok t v :
  is_defined v -> subctype t (type_of_val v) ->
  exists2 v', truncate_val t v = ok v' & type_of_val v' = t /\ is_defined v'.
Proof.
move=> hd /(of_val_defined_ok hd) [x hx].
exists (to_val x); first by rewrite /truncate_val hx.
exact: to_val_typed.
Qed.

Lemma truncate_vals_defined_ok tys vs :
  List.Forall2 (fun t v => is_defined v /\ subctype t (type_of_val v)) tys vs ->
  is_ok (mapM2 ErrType truncate_val tys vs).
Proof.
elim => {tys vs} [ | t v tys vs [hd hsub] _ ih] //=.
have [v' -> _] := truncate_val_defined_ok hd hsub.
by move: ih; case: mapM2.
Qed.

(* A function that succeeds on all its arguments succeeds on defined values
   of larger types. *)
Lemma app_sopn_ok T ts (f : sem_prod ts (exec T)) vs :
  sem_forall (fun r => is_ok r) ts f ->
  List.Forall2 (fun t v => is_defined v /\ subctype t (type_of_val v)) ts vs ->
  exists r, app_sopn ts f vs = ok r.
Proof.
move=> hf hall; elim: hall f hf => {ts vs} [ | t v ts vs [hd hsub] _ ih] f /=.
+ by case: f => // r _; exists r.
move=> hf; have [x hx] := of_val_defined_ok hd hsub.
by rewrite hx /=; apply: ih.
Qed.
