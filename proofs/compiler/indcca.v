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

Require Import distr_extra dinterp.

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

  (* Security games for implicitly rejecting KEMs (penalty style).

     The challenger [(GenKey, Encap, Decap)] comprises:
     - A key generation algorithm [GenKey : itree Rnd (pkey * skey)].
     - An encapsulation algorithm [Encap : pkey -> itree Rnd (ctxt * msg)].
     - A decapsulation algorithm [Decap : skey -> ctxt -> itree Rnd msg].

     The adversary [(Query, Guess)] comprises:
     - A first stage [Query : pkey -> itree (Dec +' Rnd) advmem] that queries
       the decapsulation algorithm and produces an adversary advmem.
     - A second stage
       [Guess : advmem -> pkey -> ctxt -> msg -> itree (Dec +' Rnd) bool]
       that performs a guess and can query the decapsulation algorithm.

     The adversary is allowed to make at most [Q] queries to the decapsulation
     oracle. All queries are logged and answered honestly. The adversary is
     penalized (game returns false) if they query the chosen ciphertext during
     the guess phase.

     The security game is as follows:
         pk, sk <- GenKey()
         st <- Query[Decap(sk)](pk)
         ct, m_0 <- Encap(pk)
         m_1 <- random message
         b <- random boolean
         g <- Guess[Decap(sk)](st, pk, ct, m_b)
         return (g == b && ct not queried in guess phase
                        && number of queries <= Q) *)

  Context
    {pkey skey advmem : Type}
    {ctxt : choiceType}
    {msg : finType}
  .

  Variant Dec : Type -> Type :=
  | Decapsulate : ctxt -> Dec msg.

  Record Challenger :=
    {
      GenKey : itree Rnd (pkey * skey);
      Encap : pkey -> itree Rnd (ctxt * msg);
      Decap : skey -> ctxt -> itree Rnd msg;
    }.

  (* Adversary can run Encap by themselves because they have [pk]. *)
  Record Adversary :=
    {
      Query : pkey -> itree (Dec +' Rnd) advmem;
      Guess : advmem -> pkey -> ctxt -> msg -> itree (Dec +' Rnd) bool;
    }.

  Context (C : Challenger) (A : Adversary) (Q : nat).

  (* Log for the game.
     It tracks the list of ciphertexts that have been queried. *)
  Definition S : Type := seq ctxt.

  (* Log a decapsulation query. *)
  Definition log E `{stateE S -< E} (c : ctxt) : itree E unit :=
    let* l := get in put (c :: l).

  (* Handle a decapsulation query from the attacker, given a secret key [sk].
     The query is logged and answered honestly. *)
  Definition handle_Dec (sk : skey) : Dec ~> itree (stateE S +' Rnd) :=
    fun T e =>
      let 'Decapsulate c := e in
      let* _ := log c in
      translate inr1 (C.(Decap) sk c).

  Definition interact
    (X : Type)
    (A : itree (Dec +' Rnd) X)
    (sk : skey) :
    itree Rnd (S * X) :=
    let t := interp (case_ (handle_Dec sk) inr_) A in
    run_state t [::].

  Definition flip : itree Rnd bool := trigger (GetRnd (dunif bool)).
  Definition rnd_msg : itree Rnd msg := trigger (GetRnd (dunif msg)).

  (* The trace records the query and guess phase logs, and the chosen
     ciphertext. *)
  Definition trace : Type := S * S * ctxt.

  Definition game : itree Rnd (bool * trace) :=
    let* (pk, sk) := C.(GenKey) in
    let* (lq, amem) := interact (A.(Query) pk) sk in
    let* (ct, m0) := C.(Encap) pk in
    let* m1 := rnd_msg in
    let* b := flip in
    let mb := if b then m1 else m0 in
    let* (lg, g) := interact (A.(Guess) amem pk ct mb) sk in
    Ret (g == b, (lq, lg, ct)).

  Definition dgame : distr (bool * trace)%type := dinterp game.

  Definition valid (t : trace) : bool :=
    let '(lq, lg, ct) := t in
    [&& ct \notin lg & (size lq + size lg <= Q)%N ].

  Definition advantage : R :=
    `| \P_[ dgame ] (fun '(b, t) => b && valid t) - 1/2 |.

End GAME.

Arguments Challenger : clear implicits.
Arguments Adversary : clear implicits.

Section REDUCE.

  Context
    {pkey skey advmem : Type}
    {ctxt : choiceType}
    {msg : finType}
  .

  Notation advantage := (@advantage pkey skey advmem ctxt msg).

  (* Every adversary for [C1] can be converted into an adversary for [C2] that
     performs at most the same number of oracle queries and whose advantage is
     at least that of the former's. *)
  Definition reduction C1 C2 :=
    forall A1 Q, advantage C1 A1 Q = advantage C2 A1 Q.

End REDUCE.

End MAIN.
