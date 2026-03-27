From elpi.apps Require Import derive.std.
From HB Require Import structures.

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

Section CIL.

Class OracleSystem :=
  {
    Mo : choiceType; (* Oracle memories. *)
    No : choiceType; (* Oracle names. *)
    In : No -> choiceType; (* Oracle input types. *)
    Out : No -> choiceType; (* Oracle output types. *)
    Oo : (* Oracle implementation. *)
      forall (o : No), In o -> Mo -> itree Rnd (Out o * Mo);
    orac_init_mem : Mo; (* Initial oracle memory. *)
  }.

Context {O : OracleSystem}.

(* An exchange: the name of an oracle, an input to that oracle, and the output
   returned by that oracle. *)
Definition Xch := { o : No & (In o * Out o)%type }.

(* A trace is a sequence of exchanges and intermediate memories. *)
Definition trace := seq (Mo * Xch).

(* Exchange event that the adversary triggers. *)
Variant Exch : Type -> Type :=
  Exchange : forall o : No, In o -> Exch (Out o).

Class Adversary :=
  {
    Ma : choiceType; (* Adversary's memory. *)
    Aa : itree Exch Ma; (* Adversary's algorithm. *)
  }.

Context {A : Adversary}.

Definition get_Mo E `{stateE trace -< E} : itree E Mo :=
  let* t := get in Ret (head orac_init_mem [seq fst x | x <- t ]).

Definition mk {o : No} (m : Mo) (i : In o) (r : Out o) : Mo * Xch :=
  (m, existT (fun _ => _)%type o (i, r)).

Definition log E `{stateE trace -< E}
  (m : Mo) (o : No) (i : In o) (r : Out o) : itree E unit :=
  let* t := get in put (mk m i r :: t).

Definition handle_Exch : Exch ~> itree (stateE trace +' Rnd) :=
  fun T e =>
    let 'Exchange o i := e in
    let* m := get_Mo in
    let* (r, m') := translate inr1 (Oo i m) in
    let* _ := log m' i r in
    Ret r.

Definition interact : itree Rnd (trace * Ma) :=
  run_state (interp handle_Exch Aa) [::].

Definition dinteract : distr (trace * Ma)%type := dinterp interact.

Class WinningCondition :=
  {
    win : trace -> Ma -> bool;
  }.

Context {W : WinningCondition}.

Definition pwin : R := \P_[ dinteract ] (fun p => win p.1 p.2).

End CIL.

End MAIN.

Arguments pwin {_} _ _ _.

Require indcca.

Section INSTANCE.

Context
  {R : realType}
  {pkey skey advmem : choiceType}
  {ciphert : choiceType}
  {msg : finType}
  {dummy : msg}
  {C : @indcca.Challenger R pkey skey ciphert msg}
  {A : @indcca.Adversary R pkey advmem ciphert msg}
  {Q : nat}
.

Notation distr := (distr R).
Notation Rnd := (Rnd (R := R)).
Notation OracleSystem := (OracleSystem (R := R)).
Notation Adversary := (Adversary (R := R)).
Notation WinningCondition := (WinningCondition (R := R)).

Definition advantage := indcca.advantage (dummy := dummy) C A Q.
Definition game := indcca.game (dummy := dummy) C A Q.

Definition _Mo := option (skey * msg).

Definition _No := option bool. (* finType doesn't work with a variant... *)

Notation "'GenKey'" := (None) (at level 0, only parsing).
Notation "'Encap'" := (Some true) (at level 0, only parsing).
Notation "'Decap'" := (Some false) (at level 0, only parsing).

Definition _In (x : _No) : choiceType :=
  match x with
  | GenKey => unit
  | Encap => pkey
  | Decap => ciphert
  end.

Definition _Out (x : _No) : choiceType :=
  match x with
  | GenKey => pkey
  | Encap => ciphert
  | Decap => msg
  end.

Definition _Oo (x : _No) : _In x -> _Mo -> itree Rnd (_Out x * _Mo) :=
  match x return _In x -> _Mo -> itree Rnd (_Out x * _Mo) with
  | GenKey =>
      fun _ _ =>
        let* (pk, sk) := C.(indcca.GenKey) in
        Ret (pk, Some (sk, dummy))
  | Encap =>
      fun pk s =>
        let* (ct, m) := C.(indcca.Encap) pk in
        if s is Some (sk, _) then Ret (ct, Some (sk, m))
        else Ret (ct, None)
  | Decap =>
      fun ct s =>
        if s is Some (sk, _) then
          let* m := C.(indcca.Decap) sk ct in
          Ret (m, s)
        else Ret (dummy, None)
  end.

Instance INDCCA : OracleSystem :=
  {|
    Mo := _Mo;
    No := _No;
    In := _In;
    Out := _Out;
    Oo := _Oo;
    orac_init_mem := None;
  |}.

Context {A' : Adversary}.

Instance W : WinningCondition. Admitted. (* ?? *)

Definition interact_aux : itree Rnd bool :=
  let* (t, m) := interact in Ret (win t m).

Lemma pr_dlet_id T (mu : distr.distr R T) E :
  \P_[mu] E = \P_[ \dlet_(x <- mu) dunit (E x) ] id.
Proof. by rewrite -dmarginE pr_dmargin. Qed.

Lemma dinterp_bind (T1 T2 : choiceType) (t : itree Rnd T1) (k : T1 -> itree Rnd T2) :
  dinterp (let* x := t in k x) = \dlet_(x <- dinterp t) dinterp (k x).
Admitted.

Lemma dinterp_Ret (T : choiceType) (r : T) :
  dinterp (R := R) (Ret r) =1 dunit r.
Proof.
move=> x; rewrite -dlim_bump (eq_dlim (g := fun=> dunit r)) //; exact/dlimC.
Qed.

Lemma interact_auxP : pwin INDCCA A' W = \P_[ dinterp interact_aux ] id.
Proof.
rewrite /pwin/interact_aux pr_dlet_id; apply/eq_mu_pr => x.
rewrite dinterp_bind; apply/eq_in_dlet; last done.
move=> [t m] _ b; by rewrite dinterp_Ret.
Qed.

Lemma eutt_interact_game : eutt eq interact_aux game.
Admitted.

Lemma correct_indcca : `| pwin INDCCA A' W - 1/2 | = advantage.
Proof.
rewrite interact_auxP /advantage /indcca.advantage; do 2!f_equal.
exact/eq_mu_pr/dinterp_eutt/eutt_interact_game.
Qed.

End INSTANCE.
