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
    init_oracle : No; (* Oracle called first by the adversary. *)
    final_oracle : No; (* Oracle called last by the adversary. *)
  }.

Context {O : OracleSystem}.

(* An exchange: the name of an oracle, an input to that oracle, and the output
   returned by that oracle.
   TODO use Tagged2 instead of Tagged *)
Definition Xch := { o : No & (In o * Out o)%type }.

(* A trace is a sequence of exchanges and intermediate memories. *)
Definition trace := seq (Mo * Xch).

(* Exchange event that the adversary triggers. *)
Variant Exch : Type -> Type :=
  Exchange : forall o : No, In o -> Exch (Out o).

(* The adversary is an arbitrary computation that triggers exchange events.
   It may be stateful, probabilistic, and almost-surely terminating. *)
Class Adversary :=
  {
    Aa : itree (Exch +' Rnd) unit; (* Adversary's algorithm. *)
  }.

Context {A : Adversary}.

(* Get the latest oracle memory, or the initial memory if there is no trace. *)
Definition get_Mo E `{stateE trace -< E} : itree E Mo :=
  let* t := get in Ret (head orac_init_mem [seq fst x | x <- t ]).

Definition mk {o : No} (m : Mo) (i : In o) (r : Out o) : Mo * Xch :=
  (m, existT (fun _ => _)%type o (i, r)).

(* Log an exchange by adding it to the front of the trace. *)
Definition log E `{stateE trace -< E}
  (m : Mo) (o : No) (i : In o) (r : Out o) : itree E unit :=
  let* t := get in put (mk m i r :: t).

(* Oracle query handler.
   This
     1. Gets the oracle name and input from the event
     2. Gets the latest oracle memory from the trace
     3. Runs the oracle implementation
     4. Logs the exchange and the resulting memory
     5. Return the oracle's output. *)
Definition handle_Exch : Exch ~> itree (stateE trace +' Rnd) :=
  fun T e =>
    let 'Exchange o i := e in
    let* m := get_Mo in
    let* (r, m') := translate inr1 (Oo i m) in
    let* _ := log m' i r in
    Ret r.

(* Adversary-Oracle interaction. *)
Definition interact : itree Rnd trace :=
  let: H := case_ handle_Exch inr_ in
  let* (t, _) := run_state (interp H Aa) [::] in
  Ret t.

(* Interpret the interaction as a distribution over traces. *)
Definition dinteract : distr trace := dinterp interact.

Class WinningCondition :=
  {
    win : trace -> bool;
  }.

Context {W : WinningCondition}.

Definition pwin : R := \P_[ dinteract ] win.

End CIL.

End MAIN.

Arguments pwin {_} _ _ _.
Arguments interact {_} _ _.

Require indcca.

Section INSTANCE.

Context
  {R : realType}
  {pkey skey advmem : choiceType}
  {ciphert : choiceType}
  {msg : finType}
  {dummy : msg}
  {dummy_ct : ciphert}
  {C : @indcca.Challenger R pkey skey ciphert msg}
  {A : @indcca.Adversary R pkey advmem ciphert msg}
  {Q : nat}
.

Notation distr := (distr R).
Notation Rnd := (Rnd (R := R)).
Notation OracleSystem := (OracleSystem (R := R)).
Notation Adversary := (Adversary (R := R)).
Notation WinningCondition := (WinningCondition (R := R)).

(* --- Oracle system definition --- *)

Definition _No := (bool * bool)%type.

Notation "'OGenKey'"       := (true, true)   (at level 0, only parsing).
Notation "'ODecap'"        := (true, false)  (at level 0, only parsing).
Notation "'OGetChallenge'" := (false, true)  (at level 0, only parsing).
Notation "'OSubmitGuess'"  := (false, false) (at level 0, only parsing).

(* Oracle memory:
   - keys: set after GenKey
   - chall: (hidden bit, challenge ciphertext), set after GetChallenge
   - lq/lg: query/guess phase Decap logs
   - ph: phase flag (false = query, true = guess)
   - guess: adversary's guess, set after SubmitGuess *)
Definition _Mo :=
  (option (pkey * skey) *
   option (bool * ciphert) *
   seq ciphert *
   seq ciphert *
   bool *
   option bool)%type.

Definition _orac_init_mem : _Mo := (None, None, [::], [::], false, None).

Definition _In (x : _No) : choiceType :=
  match x with
  | OGenKey       => unit
  | ODecap        => ciphert
  | OGetChallenge => unit
  | OSubmitGuess  => bool
  end.

Definition _Out (x : _No) : choiceType :=
  match x with
  | OGenKey       => pkey
  | ODecap        => msg
  | OGetChallenge => (ciphert * msg)%type
  | OSubmitGuess  => unit
  end.

Definition _Oo_GenKey (_ : unit) (mo : _Mo) : itree Rnd (pkey * _Mo) :=
  let '(_, chall, lq, lg, ph, g) := mo in
  let* (pk, sk) := C.(indcca.GenKey) in
  Ret (pk, (Some (pk, sk), chall, lq, lg, ph, g)).

Definition _Oo_Decap (ct : ciphert) (mo : _Mo) : itree Rnd (msg * _Mo) :=
  let '(keys, chall, lq, lg, ph, g) := mo in
  match keys with
  | Some (_, sk) =>
      let* m := C.(indcca.Decap) sk ct in
      if ph
      then Ret (m, (keys, chall, lq, ct :: lg, ph, g))
      else Ret (m, (keys, chall, ct :: lq, lg, ph, g))
  | None => Ret (dummy, mo)
  end.

Definition _Oo_GetChallenge (_ : unit) (mo : _Mo) :
  itree Rnd ((ciphert * msg)%type * _Mo) :=
  let '(keys, _, lq, lg, _, g) := mo in
  match keys with
  | Some (pk, sk) =>
      let* (ct, m0) := C.(indcca.Encap) pk in
      let* m1 := indcca.rnd_msg in
      let* b := indcca.flip in
      let mb := if b then m1 else m0 in
      Ret ((ct, mb), (Some (pk, sk), Some (b, ct), lq, lg, true, g))
  | None => Ret ((dummy_ct, dummy), mo)
  end.

Definition _Oo_SubmitGuess (guess : bool) (mo : _Mo) : itree Rnd (unit * _Mo) :=
  let '(keys, chall, lq, lg, ph, _) := mo in
  Ret (tt, (keys, chall, lq, lg, ph, Some guess)).

Definition _Oo (x : _No) : _In x -> _Mo -> itree Rnd (_Out x * _Mo) :=
  match x return _In x -> _Mo -> itree Rnd (_Out x * _Mo) with
  | OGenKey       => _Oo_GenKey
  | ODecap        => _Oo_Decap
  | OGetChallenge => _Oo_GetChallenge
  | OSubmitGuess  => _Oo_SubmitGuess
  end.

Instance INDCCA : OracleSystem :=
  {|
    Mo := _Mo;
    No := _No;
    In := _In;
    Out := _Out;
    Oo := _Oo;
    orac_init_mem := _orac_init_mem;
    init_oracle := OGenKey;
    final_oracle := OSubmitGuess;
  |}.

(* --- CIL adversary --- *)

Let EE := @Exch R INDCCA.

Definition exch {o : _No} (i : _In o) : EE (_Out o) :=
  @Exchange R INDCCA o i.

Definition dec_to_exch : indcca.Dec ~> itree (EE +' Rnd) :=
  fun T e =>
    match e in indcca.Dec T return itree (EE +' Rnd) T with
    | indcca.Decapsulate c => trigger (inl1 (exch (o := ODecap) c))
    end.

Definition trig {T} (e : EE T) : itree (EE +' Rnd) T :=
  trigger (inl1 e : (EE +' Rnd) T).

Definition cil_adversary : itree (EE +' Rnd) unit :=
  let* pk := trig (exch (o := OGenKey) tt) in
  let* amem := interp (case_ dec_to_exch inr_) (A.(indcca.Query) pk) in
  let* (ct, mb) := trig (exch (o := OGetChallenge) tt) in
  let* g := interp (case_ dec_to_exch inr_) (A.(indcca.Guess) amem pk ct mb) in
  let* _ := trig (exch (o := OSubmitGuess) g) in
  Ret tt.

Instance A' : Adversary := {| Aa := cil_adversary |}.

(* --- Winning condition --- *)

Definition _win (t : @trace _ INDCCA) : bool :=
  match t with
  | (mo, _) :: _ =>
      let '(_, chall, lq, lg, _, guess) := mo in
      match chall, guess with
      | Some (b, ct), Some g =>
          [&& g == b, ct \notin lg & (size lq + size lg <= Q)%N]
      | _, _ => false
      end
  | _ => false
  end.

Instance W : WinningCondition := {| win := _win |}.

(* --- Equivalence proof --- *)

Definition advantage := indcca.advantage C A Q.

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

Definition interact_aux : itree Rnd bool :=
  let* t := interact INDCCA A' in Ret (_win t).

Lemma interact_auxP : pwin INDCCA A' W = \P_[ dinterp interact_aux ] id.
Proof.
rewrite /pwin /interact_aux pr_dlet_id; apply/eq_mu_pr => x.
rewrite dinterp_bind; apply/eq_in_dlet; last done.
move=> t _ b; by rewrite dinterp_Ret.
Qed.

Definition game_bool : itree Rnd bool :=
  let* (b, t) := indcca.game C A in
  Ret (b && indcca.valid Q t).

Lemma game_boolP :
  \P_[dinterp game_bool] id =
  \P_[dinterp (indcca.game C A)] (fun '(b, t) => b && indcca.valid Q t).
Proof.
have h : dinterp game_bool =1
  dmargin (fun '(b, t) => b && indcca.valid Q t) (dinterp (indcca.game C A)).
{ move=> x; rewrite /game_bool dinterp_bind dmarginE.
  apply/eq_in_dlet; last done.
  move=> [b t] _ y; by rewrite dinterp_Ret. }
by rewrite (eq_mu_pr _ h) pr_dmargin.
Qed.

Lemma eutt_interact_game : eutt eq interact_aux game_bool.
Admitted.

Lemma correct_indcca : `| pwin INDCCA A' W - 1/2 | = advantage.
Proof.
rewrite /advantage /indcca.advantage interact_auxP; do 2!f_equal.
rewrite (eq_mu_pr _ (dinterp_eutt eutt_interact_game)).
exact: game_boolP.
Qed.

End INSTANCE.
