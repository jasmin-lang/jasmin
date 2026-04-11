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
  Events.StateFacts
  Interp.TranslateFacts
.
From Paco Require Import paco.
Import Monads.

Require Import distr_extra dinterp.
Require Import rutt_extras.

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
    In_init : In init_oracle = unit;
    Out_final : Out final_oracle = unit;
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

(* -------------------------------------------------------------------------- *)
(* Instantiation for INDCCA, doesn't work and the encoding is probably wrong *)

Require indcca.

(* Oracle names for IND-CCA instantiation. *)

#[only(eqbOK)] derive
Variant oracle_name : Type :=
| OGenKey
| ODecap
| OGetChallenge
| OSubmitGuess
.

HB.instance Definition _ := hasDecEq.Build oracle_name oracle_name_eqb_OK.

Definition oracle_name_pickle (x : oracle_name) : nat :=
  match x with
  | OGenKey => 0
  | ODecap => 1
  | OGetChallenge => 2
  | OSubmitGuess => 3
  end.

Definition oracle_name_unpickle (n : nat) : option oracle_name :=
  match n with
  | 0 => Some OGenKey
  | 1 => Some ODecap
  | 2 => Some OGetChallenge
  | 3 => Some OSubmitGuess
  | _ => None
  end.

Lemma oracle_name_pickleK : pcancel oracle_name_pickle oracle_name_unpickle.
Proof. by case. Qed.

HB.instance Definition _ := PCanIsCountable oracle_name_pickleK.

Definition oracle_names := [:: OGenKey; ODecap; OGetChallenge; OSubmitGuess].

Lemma oracle_name_fin_axiom : Finite.axiom oracle_names.
Proof. by case. Qed.

HB.instance Definition _ := isFinite.Build oracle_name oracle_name_fin_axiom.

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

Definition _In (x : oracle_name) : choiceType :=
  match x with
  | OGenKey       => unit
  | ODecap        => ciphert
  | OGetChallenge => unit
  | OSubmitGuess  => bool
  end.

Definition _Out (x : oracle_name) : choiceType :=
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

Definition _Oo (x : oracle_name) : _In x -> _Mo -> itree Rnd (_Out x * _Mo) :=
  match x return _In x -> _Mo -> itree Rnd (_Out x * _Mo) with
  | OGenKey       => _Oo_GenKey
  | ODecap        => _Oo_Decap
  | OGetChallenge => _Oo_GetChallenge
  | OSubmitGuess  => _Oo_SubmitGuess
  end.

Instance INDCCA : OracleSystem :=
  {|
    Mo := _Mo;
    No := oracle_name;
    In := _In;
    Out := _Out;
    Oo := _Oo;
    orac_init_mem := _orac_init_mem;
    init_oracle := OGenKey;
    final_oracle := OSubmitGuess;
    In_init := erefl;
    Out_final := erefl;
  |}.

(* --- CIL adversary --- *)

Let EE := @Exch R INDCCA.

Definition exch {o : oracle_name} (i : _In o) : EE (_Out o) :=
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

(* Relation between CIL traces and IND-CCA game results. *)
Definition game_RR
  (tr : @trace _ INDCCA)
  (bg : bool * (indcca.S * indcca.S * ciphert)) : Prop :=
  _win tr = (bg.1 && indcca.valid Q bg.2).

Let H : (EE +' Rnd) ~> itree (stateE (@trace _ INDCCA) +' Rnd) :=
  case_ (@handle_Exch R INDCCA) inr_.

Let iinteract := indcca.interact C.

(* State invariant for the Dec-phase simulation.
   Relates a CIL trace to an IND-CCA log. *)
Definition dec_inv
  (pk : pkey) (sk : skey) (chall : option (bool * ciphert))
  (other_log : seq ciphert) (ph : bool) (g0 : option bool)
  (tr : @trace _ INDCCA) (log : indcca.S) : Prop :=
  exists rest xch,
    tr = ((Some (pk, sk), chall,
           (if ph then other_log else log ++ other_log),
           (if ph then log ++ other_log else other_log),
           ph, g0), xch) :: rest.

(* Dec-phase simulation: the CIL handling of Dec events is eutt to
   the IND-CCA handling, preserving the state invariant. *)
Local Lemma sim_dec (X : Type) (t : itree (indcca.Dec +' Rnd) X)
  (sk : skey) (pk : pkey) (chall : option (bool * ciphert))
  (other_log : seq ciphert) (ph : bool) (g0 : option bool)
  (tr0 : @trace _ INDCCA) :
  dec_inv pk sk chall other_log ph g0 tr0 [::] ->
  eutt (fun '(tr, x) '(log, x') =>
          x = x' /\ dec_inv pk sk chall other_log ph g0 tr log)
    (run_state (interp H (interp (case_ dec_to_exch inr_) t)) tr0)
    (run_state (interp (case_ (indcca.handle_Dec C sk) inr_) t) [::]).
Admitted.

(* GenKey oracle step. *)
Local Lemma step_genkey :
  eutt (fun '(tr, pk) '(pk', sk') =>
          pk = pk' /\ dec_inv pk' sk' None [::] false None tr [::])
    (run_state (interp H (trig (exch (o := OGenKey) tt))) [::])
    (C.(indcca.GenKey)).
Admitted.

(* GetChallenge oracle step. *)
Local Lemma step_getchallenge
  (pk : pkey) (sk : skey) (lq : seq ciphert)
  (tr0 : @trace _ INDCCA) :
  dec_inv pk sk None [::] false None tr0 lq ->
  eutt (fun '(tr, p) '(ct', mb') =>
          p.1 = ct' /\ p.2 = mb' /\
          exists b, mb' = (if b then p.2 else p.2) /\
            dec_inv pk sk (Some (b, ct')) lq true None tr [::])
    (run_state (interp H (trig (exch (o := OGetChallenge) tt))) tr0)
    (ITree.bind (C.(indcca.Encap) pk) (fun '(ct, m0) =>
     ITree.bind indcca.rnd_msg (fun m1 =>
     ITree.bind indcca.flip (fun b =>
     Ret (ct, if b then m1 else m0))))).
Admitted.

(* SubmitGuess oracle step. *)
Local Lemma step_submitguess
  (pk : pkey) (sk : skey) (b : bool) (ct : ciphert)
  (lq lg : seq ciphert) (g : bool)
  (tr0 : @trace _ INDCCA) :
  dec_inv pk sk (Some (b, ct)) lq true None tr0 lg ->
  eutt (fun '(tr, _) _ =>
          _win tr = [&& g == b, ct \notin lg & (size lq + size lg <= Q)%N])
    (run_state (interp H (trig (exch (o := OSubmitGuess) g))) tr0)
    (Ret tt).
Admitted.

(* Helper: decompose run_state (interp H (bind t k)). *)
Local Lemma rs_interp_bind (T U : Type)
  (t : itree (EE +' Rnd) T) (k : T -> itree (EE +' Rnd) U)
  (s : @trace _ INDCCA) :
  eq_itree eq
    (run_state (interp H (ITree.bind t k)) s)
    (ITree.bind (run_state (interp H t) s)
                (fun p => run_state (interp H (k p.2)) p.1)).
Proof.
etransitivity.
{ apply eq_itree_interp_state. exact: interp_bind. reflexivity. }
etransitivity. exact: interp_state_bind.
eapply eqit_bind'; first reflexivity.
intros ? ? <-; reflexivity.
Qed.

Lemma eutt_interact_game :
  eutt game_RR (interact INDCCA A') (indcca.game C A).
Proof.
(* This lemma is proved by decomposing the CIL interaction step by step
   and showing it mirrors the IND-CCA game at each step. The proof remains
   admitted pending the detailed ITree equational reasoning for each step. *)
Admitted.

Lemma correct_indcca : `| pwin INDCCA A' W - 1/2 | = advantage.
Proof.
rewrite /advantage /indcca.advantage /pwin; do 2!f_equal.
apply: (eutt_deqX eutt_interact_game) => tr [b t]; exact: id.
Qed.

End INSTANCE.
