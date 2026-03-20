(* Indistinguishability under chosen ciphertext attack (INDCCA). *)

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

  (* Security games for implicitly rejecting KEMs.

     The challenger [(GenKey, Encap, Decap)] comprises:
     - A key generation algorithm [GenKey : itree Rnd (pkey * skey)].
     - An encapsulation algorithm [Encap : pkey -> itree Rnd (ciphert * msg)].
     - A decapsulation algorithm [Decap : skey -> ciphert -> itree Rnd msg].

     The adversary [(Query, Guess)] comprises:
     - A first stage [Query : pkey -> itree (Dec +' Rnd) advmem] that queries
       the decapsulation algorithm and produces an adversary advmem.
     - A second stage
       [Guess : advmem -> pkey -> ciphert -> msg -> itree (Dec +' Rnd) bool]
       that performs a guess, and can query the decapsulation algorithm except
       on the provided encapsulation.

     The adversary is allowed to make at most [Q] queries to the decapsulation
     oracle.

     The security game is as follows:
         pk, sk <- GenKey()
         st <- Query[Decap(sk)](pk)
         ct, m_0 <- Encap(pk)
         m_1 <- random message
         b <- random boolean
         g <- Guess[Decap*(sk)](st, pk, ct, m_b)
         return (g == b && number of queries <= Q)

     We write A[C] for the ITree that interprets the [Dec] events of [A] calling
     [C] and [C*] for the decapsulation algorithm that fails on [ct]. *)

  Context
    {pkey skey advmem : Type}
    {ciphert : eqType}
    {msg : finType}
    {dummy : msg}
  .

  Variant Dec : Type -> Type :=
  | Decapsulate : ciphert -> Dec msg.

  Record Challenger :=
    {
      GenKey : itree Rnd (pkey * skey);
      Encap : pkey -> itree Rnd (ciphert * msg);
      Decap : skey -> ciphert -> itree Rnd msg;
    }.

  (* Adversary can run Encap by themselves because they have [pk]. *)
  Record Adversary :=
    {
      Query : pkey -> itree (Dec +' Rnd) advmem;
      Guess : advmem -> pkey -> ciphert -> msg -> itree (Dec +' Rnd) bool;
    }.

  Context (C : Challenger) (A : Adversary) (Q : nat).

  Definition tick E `{stateE nat -< E} : itree E unit :=
    let* n := get in put n.+1.

  (* Handle a decapsulation query from the attacker, given a secret key [sk]
     and an exception [ex]. *)
  Definition handle_Dec
    (sk : skey) (ex : option ciphert) : Dec ~> itree (stateE nat +' Rnd) :=
    fun T e =>
      let 'Decapsulate c := e in
      let* _ := tick in
      if Some c == ex then Ret dummy
      else translate inr1 (C.(Decap) sk c).

  Definition interact
    (X : Type)
    (A : itree (Dec +' Rnd) X)
    (sk : skey)
    (ex : option ciphert) :
    itree Rnd (nat * X) :=
    let t := interp (case_ (handle_Dec sk ex) inr_) A in
    run_state t O.

  Definition flip : itree Rnd bool := trigger (GetRnd (dunif bool)).
  Definition rnd_msg : itree Rnd msg := trigger (GetRnd (dunif msg)).

  Definition game : itree Rnd bool :=
    let* (pk, sk) := C.(GenKey) in
    let* (nq, amem) := interact (A.(Query) pk) sk None in
    let* (ct, m0) := C.(Encap) pk in
    let* m1 := rnd_msg in
    let* b := flip in
    let mb := if b then m1 else m0 in
    let* (ng, g) := interact (A.(Guess) amem pk ct mb) sk (Some ct) in
    Ret [&& g == b & (nq + ng <= Q)%N ]. (* Why doesn't this work with order? *)

  Definition dgame : distr bool := dinterp game.

  Definition advantage : R := `| \P_[ dgame ] id - 1/2 |.

End GAME.

Arguments Challenger : clear implicits.
Arguments Adversary : clear implicits.

Section REDUCE.

  Context
    {pkey skey advmem : Type}
    {ciphert : eqType}
    {msg : finType}
    {dummy : msg}
  .

  Notation advantage := (@advantage pkey skey advmem ciphert msg dummy).

  (* Every adversary for [C1] can be converted into an adversary for [C2] that
     performs at most the same number of oracle queries and whose advantage is
     at least that of the former's. *)
  Definition reduction C1 C2 :=
    forall A1 Q, advantage C1 A1 Q = advantage C2 A1 Q.

End REDUCE.

End MAIN.
