(* Strong existential unforgeability under chosen message attacks (SUF-CMA). *)

From mathcomp Require Import
  ssreflect
  ssrbool
  ssralg
  ssrfun
  ssrnum
  ssrnat
  order
.
From mathcomp Require Import
  choice
  constructive_ereal
  distr
  eqtype
  fintype
  order
  reals
  seq
.
Import GRing.Theory.

From ITree Require Import
  Basics
  ITree
  ITreeFacts
  Interp
  InterpFacts
  Rutt
  RuttFacts
  State
.
Import Monads.

Require Import distr.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

Notation "'let*' p ':=' c1 'in' c2" :=
  (@ITree.bind _ _ _ c1 (fun p => c2))
  (at level 61, p as pattern, c1 at next level, right associativity).

Notation "x |> f" := (f x) (only parsing, at level 25).

Section MAIN.

Context {R : realType}.

Notation distr := (distr R).
Notation Rnd := (Rnd (R := R)).

Section GAME.

  (* The challenger [(GenKey, Sign, Verif)] comprises:
     - A key generation algorithm [GenKey : itree Rnd (pkey * skey)].
     - A signing algorithm [Sign : skey -> msg -> itree Rnd signature].
     - A verification algorithm
         [Verif : pkey -> msg -> signature -> itree Rnd bool].

     The adversary is an algorithm that queries the signing oracle and produces
     a forgery [Query : pkey -> itree (ESign +' Rnd) (msg * signature)].

     The adversary is allowed to make at most [Q] queries to the decapsulation
     oracle.
     The security game is as follows:
         pk, sk <- GenKey()
         m, s <- Query[Sign(sk)](pk)
         b <- Verif(pk, m, s)
         return (
           b
           && (m, s) was never queried
           && number of queries <= Q
         )

     We write A[C] for the ITree that interprets the [Sign] events of [A]
     calling [C]. *)

  Context
    {pkey skey : Type}
    {msg signature : choiceType}
  .

  Variant ESign : Type -> Type :=
  | EvSign : msg -> ESign signature.

  Record Challenger :=
    {
      GenKey : itree Rnd (pkey * skey);
      Sign : skey -> msg -> itree Rnd signature;
      Verify : pkey -> msg * signature -> itree Rnd bool;
    }.

  (* Adversary can run Encap by themselves because they have [pk]. *)
  Record Adversary :=
    {
      Query : pkey -> itree (ESign +' Rnd) (msg * signature);
    }.

  Context (C : Challenger) (A : Adversary) (Q : nat).

  (* Log for the game.
     It tracks the list of messages and signatures that have been queried. *)
  Definition S : Type := seq (msg * signature).

  (* Increment the number of queries and log a message-signature pair. *)
  Definition log
    E `{stateE S -< E} (m : msg) (s : signature) : itree E unit :=
    let* l := get in put ((m, s) :: l).

  (* Handle a signing query by incrementing the query count and recording the
     message and signature. *)
  Definition handle_ESign (sk : skey) : ESign ~> itree (stateE S +' Rnd) :=
    fun T e =>
      let 'EvSign m := e in
      let* s := translate inr1 (C.(Sign) sk m) in
      let* _ := log m s in
      Ret s.

  Definition interact
    (X : Type) (A : itree (ESign +' Rnd) X) (sk : skey) : itree Rnd (S * X) :=
    let t := interp (case_ (handle_ESign sk) inr_) A in
    run_state t [::].

  (* The trace records the query log and the forgery. *)
  Definition trace : Type := S * (msg * signature).

  Definition game : itree Rnd (bool * trace) :=
    let* (pk, sk) := C.(GenKey) in
    let* (l, f) := interact (A.(Query) pk) sk in
    let* b := C.(Verify) pk f in
    Ret (b, (l, f)).

  (* Interpret the game as a distribution. *)
  Definition dgame : distr (bool * trace)%type := dinterp game.

  Definition valid (t : trace) : bool :=
    let '(l, f) := t in
    [&& f \notin l & (size l <= Q)%N].

  (* The adversary's advantage is the probability of winning the game. *)
  Definition advantage : R :=
    \P_[ dgame ] (fun '(b, t) => b && valid t).

End GAME.

Arguments Challenger : clear implicits.
Arguments Adversary : clear implicits.

Section REDUCE.

  Context
    {pkey skey : Type}
    {msg signature : choiceType}
  .

  Notation advantage := (@advantage pkey skey msg signature).

  (* Every adversary for [C1] can be converted into an adversary for [C2] that
     performs at most the same number of oracle queries and whose advantage is
     at least that of the former's.

     In our case, we show that the adversary performs the same number of queries
     and has the same advantage. *)
  Definition reduction C1 C2 :=
    forall A1 Q, advantage C1 A1 Q = advantage C2 A1 Q.

End REDUCE.

End MAIN.
