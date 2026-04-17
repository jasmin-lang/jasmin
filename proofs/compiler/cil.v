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

Require Import distr_extra dinterp.
Require Import rutt_extras oseq utils.
Require indcca.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

Notation "'let*' p ':=' c1 'in' c2" :=
  (@ITree.bind _ _ _ c1 (fun p => c2))
  (at level 61, p as pattern, c1 at next level, right associativity).

Notation "x |> f" := (f x) (only parsing, at level 25).

Section REAL.

Context {R : realType}.

Notation distr := (distr R).
Notation Rnd := (Rnd (R := R)).

(* An oracle system interface fixes the oracle names and their memory/IO
   signature but not the oracles' implementation. Two oracle systems that
   share an interface can be compared for equivalence. *)
Class OracleSystemInterface :=
  {
    Mo : choiceType; (* Oracle memories. *)
    No : choiceType; (* Oracle names. *)
    In : No -> choiceType; (* Oracle input types. *)
    Out : No -> choiceType; (* Oracle output types. *)
    mi : Mo; (* Initial oracle memory. *)
  }.

Section MAIN.

Section CIL.

Context {I : OracleSystemInterface}.

(* An exchange: the name of an oracle, an input to that oracle, and the output
   returned by that oracle. *)
Definition Xch := { o : No & (In o * Out o)%type }.

(* A trace is a sequence of exchanges and intermediate memories. *)
Definition trace := seq (Xch * Mo).

(* Exchange event that the adversary triggers. *)
Variant Exch : Type -> Type :=
| Exchange : forall o, In o -> Exch (Out o).

(* The adversary is an arbitrary computation that triggers exchange events.
   It may be stateful, probabilistic, and almost-surely terminating. *)
Class Adversary := { Aa : itree (Exch +' Rnd) unit; }.

(* Get the latest oracle memory, or the initial memory if there is no trace. *)
Definition get_Mo E `{stateE trace -< E} : itree E Mo :=
  let* t := get in Ret (head mi [seq x.2 | x <- t ]).

Definition mk {o : No} (m : Mo) (i : In o) (r : Out o) : Xch * Mo :=
  (existT (fun _ => _)%type o (i, r), m).

(* Log an exchange by adding it to the front of the trace. *)
Definition log E `{stateE trace -< E}
  (m : Mo) (o : No) (i : In o) (r : Out o) : itree E unit :=
  let* t := get in put (mk m i r :: t).

(* An oracle system is an implementation for each oracle in the interface. *)
Class OracleSystem :=
  {
    Oo : forall (o : No), In o -> Mo -> itree Rnd (Out o * Mo);
  }.

Context {O : OracleSystem}.
Context {A : Adversary}.

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

Class WinningCondition := { win : trace -> bool; }.

Context {W : WinningCondition}.

Definition pwin : R := \P_[ dinteract ] win.

End CIL.

End MAIN.

Arguments Exchange {I}.
Arguments interact {I}.
Arguments dinteract {I}.
Arguments pwin {I}.
Arguments OracleSystem : clear implicits.

(* -------------------------------------------------------------------------- *)
(* Equivalence of oracle systems sharing an interface. *)

Section EQUIV.

Context {I : OracleSystemInterface}.

(* Two oracle systems implementing the same interface are equivalent when, on
   every oracle name, input, and memory, their implementations produce
   equivalent ITrees (up to silent steps). *)
Definition equivalent (O1 O2 : OracleSystem I) : Prop :=
  forall (o : No) (i : In o) (m : Mo),
    eutt eq (O1.(Oo) i m) (O2.(Oo) i m).

Lemma equivalent_handle_Exch (O1 O2 : OracleSystem I) :
  equivalent O1 O2 ->
  forall T (e : Exch T),
    eutt eq
      (handle_Exch (O := O1) (T := T) e)
      (handle_Exch (O := O2) (T := T) e).
Proof.
move=> hO T [o i]; rewrite /handle_Exch.
apply: eqit_bind'; first reflexivity.
move=> m m' heq; rewrite heq.
apply: eqit_bind'; first exact: eutt_translate_gen (hO o i m').
move=> r1 r2 heq'; rewrite heq'; reflexivity.
Qed.

Lemma equivalent_interact (O1 O2 : OracleSystem I) (A : Adversary) :
  equivalent O1 O2 ->
  eutt eq (interact O1 A) (interact O2 A).
Proof.
move=> hO; rewrite /interact.
apply: (eqit_bind' eq); last by move=> ?? ->; reflexivity.
set ds := interp _ _; set dt := interp _ _.
suff -> : eutt eq ds dt by reflexivity.
apply/eutt_interp; last reflexivity.
move=> ??; apply/Proper_Case_Handler; last reflexivity.
move=> T e; exact: equivalent_handle_Exch hO T e.
Qed.

Lemma equivalent_dinteract (O1 O2 : OracleSystem I) (A : Adversary) :
  equivalent O1 O2 ->
  dinteract O1 A =1 dinteract O2 A.
Proof. move=> /equivalent_interact h; exact/dinterp_eutt/h. Qed.

Theorem equivalent_pwin
  (O1 O2 : OracleSystem I) (A : Adversary) (W : WinningCondition) :
  equivalent O1 O2 ->
  pwin O1 A W = pwin O2 A W.
Proof. move=> /equivalent_dinteract h; rewrite /pwin; exact: eq_mu_pr h. Qed.

End EQUIV.

(* -------------------------------------------------------------------------- *)
(* Instantiation for INDCCA. *)

(* Oracle names for IND-CCA instantiation. *)

#[only(eqbOK)] derive
Variant oracle_name : Type :=
| OGenKey
| ODecap
| OGetChallenge
| OSubmitGuess
.

HB.instance Definition _ := hasDecEq.Build oracle_name oracle_name_eqb_OK.

Definition oracle_names := [:: OGenKey; ODecap; OGetChallenge; OSubmitGuess ].

Definition oracle_name_pickle (x : oracle_name) : nat :=
  find (fun y => x == y) oracle_names.

Definition oracle_name_unpickle (n : nat) : option oracle_name :=
  onth oracle_names n.

Lemma oracle_name_pickleK : pcancel oracle_name_pickle oracle_name_unpickle.
Proof. by case. Qed.

HB.instance Definition _ := PCanIsCountable oracle_name_pickleK.

Lemma oracle_name_fin_axiom : Finite.axiom oracle_names.
Proof. by case. Qed.

HB.instance Definition _ := isFinite.Build oracle_name oracle_name_fin_axiom.

Section INSTANCE.

Context
  {pkey skey : choiceType}
  {ctxt : choiceType}
  {msg : finType}
  {C : indcca.Challenger
      (R := R) (pkey := pkey) (skey := skey) (ctxt := ctxt) (msg := msg)}
  (Q : nat)
  (dummy_ct : ctxt) (* Malformed interactions return dummies. *)
  (dummy_msg : msg) (* Malformed interactions return dummies. *)
.

(* Oracle memory:
   - keys: the result of GenKey
   - bit: the sampled bit
*)
Record _Mo :=
  {
    mo_keys : option (pkey * skey);
    mo_bit : option bool;
  }.

(* Isomorphic definition to prove that [_Mo] is a [choiceType]. *)
Let _Mo_choice : Type := option (pkey * skey) * option bool.

Let pickle__Mo (m : _Mo) : _Mo_choice :=
  (mo_keys m, mo_bit m).

Let unpickle__Mo (mk : _Mo_choice) : _Mo :=
  {| mo_keys := mk.1; mo_bit := mk.2; |}.

Lemma pickle__MoK : cancel pickle__Mo unpickle__Mo.
Proof. by case. Qed.

HB.instance Definition _ := Choice.copy _Mo (can_type pickle__MoK).

Definition mo_with_bit (m : _Mo) (b : bool) : _Mo :=
  {| mo_keys := mo_keys m; mo_bit := Some b; |}.

Let _mi : _Mo := {| mo_keys := None; mo_bit := None; |}.

Let _In (x : oracle_name) : choiceType :=
  match x with
  | OGenKey => unit
  | ODecap => ctxt
  | OGetChallenge => unit
  | OSubmitGuess => bool
  end.

Let _Out (x : oracle_name) : choiceType :=
  match x with
  | OGenKey => pkey
  | ODecap => msg
  | OGetChallenge => ctxt * msg
  | OSubmitGuess => unit
  end%type.

Let _Oo_GenKey (_ : unit) (_ : _Mo) : itree Rnd (pkey * _Mo) :=
  let* (pk, sk) := C.(indcca.GenKey) in
  let mo := {| mo_keys := Some (pk, sk); mo_bit := None; |} in
  Ret (pk, mo).

Let _Oo_Decap (ct : ctxt) (mo : _Mo) : itree Rnd (msg * _Mo) :=
  if mo_keys mo is Some (_, sk) then
    let* m := C.(indcca.Decap) sk ct in
    Ret (m, mo)
  else Ret (dummy_msg, mo).

Let _Oo_GetChallenge
  (_ : unit) (mo : _Mo) : itree Rnd ((ctxt * msg) * _Mo) :=
  if mo_keys mo is Some (pk, _) then
    let* (ct, m0) := C.(indcca.Encap) pk in
    let* m1 := indcca.rnd_msg in
    let* b := indcca.flip in
    let mb := if b then m1 else m0 in
    Ret ((ct, mb), mo_with_bit mo b)
  else Ret ((dummy_ct, dummy_msg), mo).

Let _Oo_SubmitGuess (g : bool) (_ : _Mo) : itree Rnd (unit * _Mo) :=
  Ret (tt, _mi).

Let _Oo (x : oracle_name) : _In x -> _Mo -> itree Rnd (_Out x * _Mo) :=
  match x return _In x -> _Mo -> itree Rnd (_Out x * _Mo) with
  | OGenKey => _Oo_GenKey
  | ODecap => _Oo_Decap
  | OGetChallenge => _Oo_GetChallenge
  | OSubmitGuess => _Oo_SubmitGuess
  end.

Instance INDCCA_I : OracleSystemInterface :=
  {|
    Mo := _Mo;
    No := oracle_name;
    In := _In;
    Out := _Out;
    mi := _mi;
  |}.

Instance INDCCA : OracleSystem INDCCA_I :=
  {| Oo := _Oo; |}.

Definition is_genkey (x : Xch) : option pkey :=
  let 'existT o (_, p) := x in
  match o as a return Out a -> option pkey with
  | OGenKey => Some
  | _ => fun _ => None
  end p.

Definition is_getchallenge (x : Xch) : option (ctxt * msg) :=
  let 'existT o (_, p) := x in
  match o as a return Out a -> option (ctxt * msg) with
  | OGetChallenge => Some
  | _ => fun _ => None
  end p.

Definition is_decap (x : Xch) : option (ctxt * msg) :=
  let 'existT o p := x in
  match o as a return In a * Out a -> option (ctxt * msg) with
  | ODecap => Some
  | _ => fun _ => None
  end p.

Definition is_decap_ct (ct : ctxt) (x : Xch) : bool :=
  if is_decap x is Some (ct', _) then ct == ct' else false.

Definition is_submitguess (x : Xch) : option bool :=
  let 'existT o (p, _) := x in
  match o as a return In a -> option bool with
  | OSubmitGuess => Some
  | _ => fun _ => None
  end p.

(* Return the same as the IND-CCA game, thus we can use the same winning
   condition. *)
Definition destruct_trace
  (t : trace) : option (bool * seq ctxt * seq ctxt * ctxt) :=
  let t := rev t in (* Oldest first. *)

  (* First query is to [GenKey]. *)
  let%opt ((x, _), t) := uncons t in
  let%opt _ := oassert (isSome (is_genkey x)) in

  (* Many queries to [Decap]. *)
  let: (qs, t) := split_after (fun x => isSome (is_decap x.1)) t in
  let qs := pmap (fun x => ssrfun.omap fst (is_decap x.1)) qs in

  (* Next query is to [GetChallenge]. *)
  let%opt ((x, m), t) := uncons t in
  let%opt (ct, _) := is_getchallenge x in (* Challenge ciphertext. *)
  let%opt b := mo_bit m in (* Challenge bit. *)

  (* Many queries to [Decap]. *)
  let: (qs', t) := split_after (fun x => isSome (is_decap x.1)) t in
  let qs' := pmap (fun x => ssrfun.omap fst (is_decap x.1)) qs' in

  (* Last query is to [SubmitGuess]. *)
  let%opt ((x, _), t) := uncons t in
  let%opt g := is_submitguess x in (* Guess bit. *)
  let%opt _ := oassert (nilp t) in

  Some (g == b, rev qs, rev qs', ct).

Let _win (t : trace) : bool :=
  if destruct_trace t is Some  (b, qs, qs', ct) then
    [&& b & indcca.valid Q (qs, qs', ct) ]
  else false.

Instance W : WinningCondition := {| win := _win; |}.

Definition indcca_adv (A : Adversary) : R :=
  `| pwin INDCCA A W - 1/2 |.

End INSTANCE.

End REAL.
