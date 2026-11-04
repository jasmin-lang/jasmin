(* -------------------------------------------------------------------- *)
From Coq Require Setoid.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Notation ocons x := (omap (cons x)).

(* -------------------------------------------------------------------- *)
Section ONth.
Context {T : Type}.

Fixpoint onth (s : seq T) (i : nat) :=
  if s is x :: s' then
    if i is i'.+1 then onth s' i' else Some x
  else None.

Lemma onth_nth s i : onth s i = nth None (map Some s) i.
Proof. by elim: s i => [|x s ih] [|i] /=. Qed.
End ONth.

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Section OMap.
Context {T U : Type} (f : T -> option U).

Fixpoint omap (s : seq T) :=
  if s is x :: s' then
    if f x is Some y then ssrfun.omap (cons y) (omap s') else None
  else Some [::].
End OMap.

(* -------------------------------------------------------------------- *)
Notation "[ 'oseq' E | i <- s ]" := (omap (fun i => E) s)
  (at level 0, E at level 99, i ident,
   format "[ '[hv' 'oseq'  E '/ '  |  i  <-  s ] ']'") : seq_scope.

Notation "[ 'oseq' E | i : T <- s ]" := (omap (fun i : T => E) s)
  (at level 0, E at level 99, i ident, only parsing) : seq_scope.

(* -------------------------------------------------------------------- *)

Declare Scope option_scope.
Delimit Scope option_scope with O.

Notation "m >>= f" := (ssrfun.Option.bind f m)
  (at level 58, left associativity) : option_scope.

Local Open Scope option_scope.

(* -------------------------------------------------------------------- *)
