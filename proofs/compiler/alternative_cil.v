Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Uniform Inductive Parameters.

From Coq Require Import JMeq RelationClasses.
From HB Require Import structures.
From elpi.apps Require Import derive.std.

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
  Subevent
  Interp.TranslateFacts
  Eq.Rutt
  Eq.RuttFacts
.

Require Import distr_extra dinterp.
Require Import rutt_extras oseq utils rutt_translate state_facts rutt_interp.

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

(* Two oracle systems that share an interface can be compared for
   equivalence. *)
Class OracleSystemInterface :=
  {
    Mo : choiceType; (* Oracle memories. *)
    mi : Mo; (* Initial oracle memory. *)
    No : choiceType; (* Oracle names. *)
    In : No -> choiceType; (* Oracle input types. *)
    Out : No -> choiceType; (* Oracle output types. *)
  }.

Section MAIN.

Section CIL.

Context {I : OracleSystemInterface}.

(* An oracle system is an implementation for each oracle in the interface. *)
Class OracleSystem :=
  {
    Oo : forall (o : No), In o -> Mo -> itree Rnd (Out o * Mo);
  }.

(* An exchange: the name of an oracle, an input to that oracle, and the output
   returned by that oracle. *)
Definition Xch := { o : No & (In o * Out o)%type }.

(* Exchange event that the adversary triggers. *)
Variant Exch : Type -> Type :=
| Exchange : forall o, In o -> Exch (Out o).

(* The adversary is an arbitrary computation that triggers exchange events.
   It may be stateful, probabilistic, and almost-surely terminating. *)
Class Adversary := { Aa : itree (Exch +' Rnd) unit; }.

Context {O : OracleSystem}.

(* A trace is a sequence of exchanges and intermediate memories. *)
Definition trace := seq (Xch * Mo).

(* Get the latest oracle memory, or the initial memory if there is no trace. *)
Definition get_Mo E `{stateE trace -< E} : itree E Mo :=
  let* t := get in Ret (head mi [seq x.2 | x <- t ]).

Definition mk {o : No} (m : Mo) (i : In o) (r : Out o) : Xch * Mo :=
  (existT (fun _ => _)%type o (i, r), m).

(* Log an exchange by adding it to the front of the trace. *)
Definition log E `{stateE trace -< E}
  (m : Mo) (o : No) (i : In o) (r : Out o) : itree E unit :=
  let* t := get in put (mk m i r :: t).

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

Arguments Mo {I} : rename.
Arguments In {I} _ : rename.
Arguments Out {I} _ : rename.
Arguments mi {I} : rename.
Arguments Oo {_ O} _ _ _ : rename.
Arguments Exchange {I}.
Arguments log {_ _ _} _ _ _ _.
Arguments interact {I}.
Arguments dinteract {I}.
Arguments pwin {I}.
Arguments OracleSystem : clear implicits.

(* -------------------------------------------------------------------------- *)
(* Equivalence of oracle systems sharing an interface. *)

Section EQUIV.

Context
  {I : OracleSystemInterface}
  (O1 O2 : OracleSystem I)
.

(* Notations for clarity. *)
Notation Mo1 := (Mo (I := I)).
Notation Mo2 := (Mo (I := I)).
Notation trace1 := (trace (I := I)).
Notation trace2 := (trace (I := I)).
Notation E1 := (stateE trace1 +' Rnd).
Notation E2 := (stateE trace2 +' Rnd).

Definition eqR {X A B} (R : A -> B -> Prop) (a : X * A) (b : X * B) : Prop :=
  a.1 = b.1 /\ R a.2 b.2.

Class is_inv_mo (inv_mo : Mo1 -> Mo2 -> Prop) :=
  {
    inv_mo_mi : inv_mo mi mi;
    inv_mo_Oo :
      forall o i m1 m2,
        inv_mo m1 m2 ->
        eutt (eqR inv_mo) (O1.(Oo) o i m1) (O2.(Oo) o i m2);
  }.

Definition equivalent : Prop := exists inv_mo, is_inv_mo inv_mo.

Context
  (inv_mo : Mo1 -> Mo2 -> Prop)
  {InvMo : is_inv_mo inv_mo}
.

Notation inv_eq := (eqR inv_mo) (only parsing).

Definition inv_trace : trace1 -> trace2 -> Prop := List.Forall2 inv_eq.

Notation ruttO := (rutt_inv (E := Rnd) inv_trace) (only parsing).

Lemma ruttO_get_Mo : ruttO inv_mo get_Mo get_Mo.
Proof.
apply: rutt_bind; first exact: rutt_inv_get.
move=> [|[e1 m1] t1] [|[e2 m2] t2] /List_Forall2_inv //.
- move=> _; apply/rutt_Ret; exact: inv_mo_mi.
move=> [[/= _ h] _]; exact/rutt_Ret/h.
Qed.

Lemma ruttO_log o i r m1 m2 :
  inv_mo m1 m2 ->
  ruttO (fun _ _ => True) (log m1 o i r) (log m2 o i r).
Proof.
move=> hm; apply: rutt_bind; first exact: rutt_inv_get.
move=> t1 t2 ht; apply: rutt_trigger => //=; exact: List.Forall2_cons ht.
Qed.

Lemma ruttO_handle_Exch T (e : Exch T) :
  ruttO eq (handle_Exch (O := O1) e) (handle_Exch (O := O2) e).
Proof.
move: e => [o i]; apply: rutt_bind; first exact: ruttO_get_Mo.
move=> m1 m2 h; apply: (rutt_bind _ _ inv_eq).
- apply:
    (rutt_translate_gen
       (REv := fun A B (e1 : Rnd A) (e2 : Rnd B) =>
                 exists p : A = B, eq_rect A Rnd e1 B p = e2)
       (RAns := fun A B e1 a e2 b => JMeq a b)).
  - done.
  - by move=> A B [X1 mu1] [X2 mu2].
  apply: gen_eutt_rutt (inv_mo_Oo _ h) => [u e | u e a b];
    first by exists (erefl u).
  exact: JMeq_eq.
move=> [r {}m1] [_ {}m2] [/= <- {}h].
apply: rutt_bind; first exact: ruttO_log.
move=> _ _ _; exact/rutt_Ret.
Qed.

Lemma ruttO_interp_handle_Exch {A : Adversary} :
  ruttO (fun _ _ => True)
    (interp (case_ (handle_Exch (O := O1)) inr_) Aa)
    (interp (case_ (handle_Exch (O := O2)) inr_) Aa).
Proof.
apply: (
  rutt_weaken
     (REv := REv_inv inv_trace)
     (RAns := RAns_inv inv_trace)
     (RR := eq)
) => //.
apply: rutt_interp_h => T [[o i] | r] /=; first exact: ruttO_handle_Exch.
apply: rutt_trigger; first by exists erefl.
move=> v1 v2 /=; exact: JMeq_eq.
Qed.

Lemma eutt_interact A : eutt inv_trace (interact O1 A) (interact O2 A).
Proof.
apply: (eutt_clo_bind _ (UU := RR_run_state inv_trace (fun _ _ => True)));
  last first.
- move=> [t1 []] [t2 []] [/= h _]; apply eutt_Ret; exact: h.
apply: rutt_inv_run_state => //; exact/ruttO_interp_handle_Exch.
Qed.

Definition inv_mo_win (W : WinningCondition) : Prop :=
  forall (mu1 : distr trace1) (mu2 : distr trace2),
    deqX (R := R) inv_trace mu1 mu2 ->
    \P_[mu1] win = \P_[mu2] win.

Lemma equivalent_pwin A W :
  inv_mo_win W ->
  pwin O1 A W = pwin O2 A W.
Proof. apply; exact/eutt_deqX/eutt_interact. Qed.

End EQUIV.

Arguments equivalent_pwin {_ _ _ _ _} _.

(* -------------------------------------------------------------------------- *)
(* Instantiation for INDCCA. *)

(* Oracle names for IND-CCA instantiation. *)

Section INSTANCE.

#[only(eqbOK)] derive
Variant kem_oracle_name : Type :=
| OGenKey
| OEncap
| ODecap
.

HB.instance Definition _ := hasDecEq.Build kem_oracle_name kem_oracle_name_eqb_OK.

Definition kem_oracle_names := [:: OGenKey; OEncap; ODecap ].

Definition kem_oracle_name_pickle (x : kem_oracle_name) : nat :=
  find (fun y => x == y) kem_oracle_names.

Definition kem_oracle_name_unpickle (n : nat) : option kem_oracle_name :=
  onth kem_oracle_names n.

Lemma kem_oracle_name_pickleK : pcancel kem_oracle_name_pickle kem_oracle_name_unpickle.
Proof. by case. Qed.

HB.instance Definition _ := PCanIsCountable kem_oracle_name_pickleK.

Lemma kem_oracle_name_fin_axiom : Finite.axiom kem_oracle_names.
Proof. by case. Qed.

HB.instance Definition _ := isFinite.Build kem_oracle_name kem_oracle_name_fin_axiom.

(* -------------------------------------------------------------------------- *)
(* KEMs *)

Class KEMParams :=
  {
    M : choiceType;
    M0 : M;
    pkey : choiceType;
    skey : choiceType;
    ctxt : choiceType;
    msg : finType;
    dummy_ct : ctxt; (* Malformed interactions return dummies. *)
    dummy_msg : msg; (* Malformed interactions return dummies. *)
  }.

Context {KEMP : KEMParams}.

Definition flip : itree Rnd bool := trigger (GetRnd (dunif bool)).
Definition rnd_msg : itree Rnd msg := trigger (GetRnd (dunif msg)).

(* KEM interface for source and target programs. *)
Instance KEM : OracleSystemInterface :=
  {|
    No := kem_oracle_name;
    In := fun x =>
      match x with
      | OGenKey => unit
      | OEncap => pkey
      | ODecap => skey * ctxt
      end%type;
    Out := fun x =>
      match x with
      | OGenKey => pkey * skey
      | OEncap => ctxt * msg
      | ODecap => msg
      end%type;
    mi := M0;
  |}.

(* -------------------------------------------------------------------------- *)
(* IND-CCA *)

Context
  {K : OracleSystem KEM}
  (Q : nat).

#[only(eqbOK)] derive
Variant cca_oracle_name : Type :=
| OInit
| OQuery
| OGetChallenge
| OFinalize
.

HB.instance Definition _ := hasDecEq.Build cca_oracle_name cca_oracle_name_eqb_OK.

Definition cca_oracle_names := [:: OInit; OQuery; OGetChallenge; OFinalize ].

Definition cca_oracle_name_pickle (x : cca_oracle_name) : nat :=
  find (fun y => x == y) cca_oracle_names.

Definition cca_oracle_name_unpickle (n : nat) : option cca_oracle_name :=
  onth cca_oracle_names n.

Lemma cca_oracle_name_pickleK : pcancel cca_oracle_name_pickle cca_oracle_name_unpickle.
Proof. by case. Qed.

HB.instance Definition _ := PCanIsCountable cca_oracle_name_pickleK.

Lemma cca_oracle_name_fin_axiom : Finite.axiom cca_oracle_names.
Proof. by case. Qed.

HB.instance Definition _ := isFinite.Build cca_oracle_name cca_oracle_name_fin_axiom.

(* IND-CCA Oracle memory:
   - keys: the result of GenKey
   - bit: the sampled bit *)
Record _Mo :=
  {
    mo_keys : option (pkey * skey);
    mo_bit : option bool;
    mo_mem : M;
  }.

(* Isomorphic definition to prove that [_Mo] is a [choiceType]. *)
Let _Mo_choice : Type := option (pkey * skey) * option bool * M.

Let pickle__Mo (m : _Mo) : _Mo_choice :=
  (mo_keys m, mo_bit m, mo_mem m).

Let unpickle__Mo (mk : _Mo_choice) : _Mo :=
  {| mo_keys := mk.1.1; mo_bit := mk.1.2; mo_mem := mk.2; |}.

Lemma pickle__MoK : cancel pickle__Mo unpickle__Mo.
Proof. by case. Qed.

HB.instance Definition _ := Choice.copy _Mo (can_type pickle__MoK).

Definition mo_with_bit (m : _Mo) (b : bool) : _Mo :=
  {| mo_keys := mo_keys m; mo_bit := Some b; mo_mem := mo_mem m; |}.

Definition mo_with_mem (m : _Mo) (mem : M) : _Mo :=
  {| mo_keys := mo_keys m; mo_bit := mo_bit m; mo_mem := mem; |}.

Definition _mi : _Mo :=
  {| mo_keys := None; mo_bit := None; mo_mem := M0; |}.

(* Oracle input types. *)
Definition _In (x : cca_oracle_name) : choiceType :=
  match x with
  | OInit => unit
  | OQuery => ctxt
  | OGetChallenge => unit
  | OFinalize => bool
  end.

(* Oracle output types. *)
Definition _Out (x : cca_oracle_name) : choiceType :=
  match x with
  | OInit => pkey
  | OQuery => msg
  | OGetChallenge => ctxt * msg
  | OFinalize => unit
  end%type.

Definition _Oo_Init (_ : unit) (m : _Mo) : itree Rnd (pkey * _Mo) :=
  let* ((pk, sk), m') := Oo OGenKey tt (mo_mem m) in
  let mo :=
    {| mo_keys := Some (pk, sk); mo_bit := None; mo_mem := m'; |}
  in
  Ret (pk, mo).

Definition _Oo_Query (ct : ctxt) (mo : _Mo) : itree Rnd (msg * _Mo) :=
  if mo_keys mo is Some (_, sk) then
    let* (m, mem') := Oo ODecap (sk, ct) (mo_mem mo) in
    Ret (m, mo_with_mem mo mem')
  else Ret (dummy_msg, mo).

Definition _Oo_GetChallenge
  (_ : unit) (mo : _Mo) : itree Rnd ((ctxt * msg) * _Mo) :=
  if mo_keys mo is Some (pk, _) then
    let* ((ct, m0), mem') := Oo OEncap pk (mo_mem mo) in
    let* m1 := rnd_msg in
    let* b := flip in
    let mb := if b then m1 else m0 in
    Ret ((ct, mb), mo_with_bit (mo_with_mem mo mem') b)
  else Ret ((dummy_ct, dummy_msg), mo).

Definition _Oo_Finalize (g : bool) (_ : _Mo) : itree Rnd (unit * _Mo) :=
  Ret (tt, _mi).

(* Oracle implementation. *)
Definition _Oo
  (x : cca_oracle_name) : _In x -> _Mo -> itree Rnd (_Out x * _Mo) :=
  match x return _In x -> _Mo -> itree Rnd (_Out x * _Mo) with
  | OInit => _Oo_Init
  | OQuery => _Oo_Query
  | OGetChallenge => _Oo_GetChallenge
  | OFinalize => _Oo_Finalize
  end.

Instance INDCCA_I : OracleSystemInterface :=
  {|
    Mo := _Mo;
    No := cca_oracle_name;
    In := _In;
    Out := _Out;
    mi := _mi;
  |}.

Instance INDCCA : OracleSystem INDCCA_I :=
  {| Oo := _Oo; |}.

Definition is_init (x : Xch) : option pkey :=
  let 'existT o (_, p) := x in
  match o as a return Out a -> option pkey with
  | OInit => Some
  | _ => fun _ => None
  end p.

Definition is_query (x : Xch) : option (ctxt * msg) :=
  let 'existT o p := x in
  match o as a return In a * Out a -> option (ctxt * msg) with
  | OQuery => Some
  | _ => fun _ => None
  end p.

Definition is_query_ct (ct : ctxt) (x : Xch) : bool :=
  if is_query x is Some (ct', _) then ct == ct' else false.

Definition is_getchallenge (x : Xch) : option (ctxt * msg) :=
  let 'existT o (_, p) := x in
  match o as a return Out a -> option (ctxt * msg) with
  | OGetChallenge => Some
  | _ => fun _ => None
  end p.

Definition is_finalize (x : Xch) : option bool :=
  let 'existT o (p, _) := x in
  match o as a return In a -> option bool with
  | OFinalize => Some
  | _ => fun _ => None
  end p.

(* Return the same as the IND-CCA game, thus we can use the same winning
   condition.
   Attention: The order in which elements are take from the trace
   is reverse to the order in which they are put in the trace.
   The trace is reversed before the check or log should do append. *)
Definition destruct_trace
  (t : trace) : option (bool * seq ctxt * seq ctxt * ctxt) :=
  let t := rev t in (* Oldest first. *)

  (* First query is to [GenKey]. *)
  let%opt ((x, _), t) := uncons t in
  let%opt _ := oassert (isSome (is_init x)) in

  (* Many queries to [Decap]. *)
  let: (qs, t) := split_after (fun x => isSome (is_query x.1)) t in
  let qs := pmap (fun x => ssrfun.omap fst (is_query x.1)) qs in

  (* Next query is to [GetChallenge]. *)
  let%opt ((x, m), t) := uncons t in
  let%opt (ct, _) := is_getchallenge x in (* Challenge ciphertext. *)
  let%opt b := mo_bit m in (* Challenge bit. *)

  (* Many queries to [Decap]. *)
  let: (qs', t) := split_after (fun x => isSome (is_query x.1)) t in
  let qs' := pmap (fun x => ssrfun.omap fst (is_query x.1)) qs' in

  (* Last query is to [Finalize]. *)
  let%opt ((x, _), t) := uncons t in
  let%opt g := is_finalize x in (* Guess bit. *)
  let%opt _ := oassert (nilp t) in

  Some (g == b, rev qs, rev qs', ct).

Let _win (t : trace) : bool :=
  if destruct_trace t is Some  (b, qs, qs', ct) then
    [&& b, ct \notin qs' & size qs + size qs' <= Q ]%N
  else false.

Instance W : WinningCondition := {| win := _win; |}.

Definition indcca_adv (A : Adversary) : R :=
  `| pwin INDCCA A W - 1/2 |.

End INSTANCE.

Arguments INDCCA {_} _.
Arguments indcca_adv {_} _ _ _.

Section REDUCTION.

Context {KEMP : KEMParams}.

Definition reduction (K K' : OracleSystem KEM) : Prop :=
  forall A Q, indcca_adv K Q A = indcca_adv K' Q A.

Context (K K' : OracleSystem KEM).

Definition indcca_inv_mo (kem_inv_mo : M -> M -> Prop) (m1 m2 : _Mo) : Prop :=
  [/\ mo_keys m1 = mo_keys m2
    , mo_bit m1 = mo_bit m2
    & kem_inv_mo (mo_mem m1) (mo_mem m2) ].

(* ===== PROOF PLAN FOR indcca_inv_mo_win =====

GOAL
----
  forall mu1 mu2 : distr (trace (I := INDCCA_I)),
    deqX (R := R) (List.Forall2 (eqR (indcca_inv_mo kem_inv_mo))) mu1 mu2 ->
    \P_[mu1] _win = \P_[mu2] _win

where
  - trace = seq (Xch * _Mo)
  - Xch   = { o : cca_oracle_name & (_In o * _Out o)%type }
  - _Mo   = record with fields mo_keys, mo_bit, mo_mem
  - eqR R (x1,m1) (x2,m2) := x1 = x2 /\ R m1 m2
  - indcca_inv_mo kem_inv_mo m1 m2 :=
        [/\ mo_keys m1 = mo_keys m2,
            mo_bit  m1 = mo_bit  m2   (* key fact: bit is preserved *)
          & kem_inv_mo (mo_mem m1) (mo_mem m2) ]
  - deqX RR mu1 mu2 :=
        forall X Y, (forall x y, RR x y -> X x = Y y) ->
        \P_[mu1] X = \P_[mu2] Y
    (definition in distr_extra.v, line ~39)
  - _win Q t := if destruct_trace t is Some (b, qs, qs', ct) then
                  [&& b, ct \notin qs' & size qs + size qs' <= Q]
                else false

OVERVIEW
--------
The key observation is that _win reads from the trace only:
  (a) the Xch parts (oracle name + I/O) of every element, and
  (b) mo_bit of the _Mo stored at the GetChallenge element.
Both are preserved by eqR (indcca_inv_mo kem_inv_mo).

TOP-LEVEL PROOF
---------------
  move=> mu1 mu2 h.
  apply: h => t1 t2 hinv.    (* deqX applied with X = Y = _win *)
  (* hinv : List.Forall2 (eqR (indcca_inv_mo kem_inv_mo)) t1 t2 *)
  (* goal : _win t1 = _win t2 *)
  ...

Note on `apply: h`: deqX is universally quantified over predicates X Y
satisfying the pointwise condition; applying it with X = Y = _win leaves
the subgoal `forall t1 t2, hinv -> _win t1 = _win t2`.

The old partial proof (pr_dlet' / eq_mu_pr) is WRONG: eq_mu_pr requires
mu1 =1 mu2 (pointwise equal distributions), not just deqX-related.
Replace the proof body entirely.

STEP 1 — DEFINE PROJECTED TRACE TYPE
-------------------------------------
Define:
  Let proj_el (e : Xch * _Mo) : Xch * option bool := (e.1, mo_bit e.2).

Note: proj_el preserves the first component, i.e., (proj_el e).1 = e.1.

STEP 2 — DEFINE destruct_trace_proj
-------------------------------------
Define a copy of destruct_trace for projected traces (type seq (Xch * option bool)).
The only change: replace `let%opt b := mo_bit m` with `let%opt b := b`
(the memory slot already holds the option bool directly).

  Let destruct_trace_proj (t : seq (Xch * option bool))
      : option (bool * seq ctxt * seq ctxt * ctxt) :=
    let t := rev t in
    let%opt ((x, _), t) := uncons t in
    let%opt _ := oassert (isSome (is_init x)) in
    let: (qs, t) := split_after (fun x => isSome (is_query x.1)) t in
    let qs := pmap (fun x => ssrfun.omap fst (is_query x.1)) qs in
    let%opt ((x, b), t) := uncons t in          (* b : option bool directly *)
    let%opt (ct, _) := is_getchallenge x in
    let%opt b := b in                           (* NO mo_bit call here *)
    let: (qs', t) := split_after (fun x => isSome (is_query x.1)) t in
    let qs' := pmap (fun x => ssrfun.omap fst (is_query x.1)) qs' in
    let%opt ((x, _), t) := uncons t in
    let%opt g := is_finalize x in
    let%opt _ := oassert (nilp t) in
    Some (g == b, rev qs, rev qs', ct).

STEP 3 — AUXILIARY LEMMA: split_after commutes with map proj_el
----------------------------------------------------------------
State and prove BEFORE indcca_inv_mo_win:

  Lemma split_after_proj_el (p : pred (Xch (I := INDCCA_I)))
      (t : seq (Xch * _Mo)) :
    split_after (fun x => p x.1) (map proj_el t) =
      (map proj_el (fst (split_after (fun x => p x.1) t)),
       map proj_el (snd (split_after (fun x => p x.1) t))).

Proof: by induction on t.
  - t = [::]: both sides ([::], [::]), trivial.
  - t = e :: t':
      LHS head: split_after (fun x => p x.1) (proj_el e :: map proj_el t')
        = if p (proj_el e).1 then ... else ...
        = if p e.1 then ...                    (* since (proj_el e).1 = e.1 *)
      Apply IH to get the split of map proj_el t', substitute, match RHS.

STEP 4 — AUXILIARY LEMMA: destruct_trace factors through map proj_el
----------------------------------------------------------------------
State and prove BEFORE indcca_inv_mo_win:

  Lemma factor_destruct_trace (t : trace (I := INDCCA_I)) :
    destruct_trace t = destruct_trace_proj (map proj_el t).

Proof: Unfold both definitions and rewrite step by step using:
  (a) map_rev (MathComp): map proj_el (rev t) = rev (map proj_el t)
      Search to find the name; likely `map_rev` in ssrfun/seq.
  (b) uncons (map proj_el t): case split.
      - t = [::]: uncons [::] = None; both sides None.
      - t = e :: t': uncons (proj_el e :: map proj_el t') = Some (proj_el e, map proj_el t').
      In destruct_trace_proj, the first uncons gives (x, _) with x = (proj_el e).1 = e.1. ✓
  (c) split_after: use split_after_proj_el (Step 3).
  (d) pmap: use pmap_map (MathComp):
        pmap (fun x => g x.1) (map proj_el t)
          = pmap (fun x => g (proj_el x).1) t   [pmap_map]
          = pmap (fun x => g x.1) t              [(proj_el x).1 = x.1]
      Search for `pmap_map` or check with `Search (pmap _ (map _ _))`.
  (e) mo_bit: at GetChallenge step, after uncons the projected trace gives
      (x, b) where b = (proj_el (x0, m)).2 = mo_bit m. Then `let%opt b := b`
      in destruct_trace_proj gives the same b as `let%opt b := mo_bit m`. ✓
  (f) nilp: nilp (map proj_el t) = nilp t, since size_map preserves size.
  (g) rev of qs, qs': map_rev again.

The proof unfolds both sides and rewrites until they are definitionally equal.
It may help to prove it by structural induction on the shape that the
bind-chain explores (the rev of t), but a direct rewrite proof also works.

STEP 5 — AUXILIARY LEMMA: Forall2 implies map proj_el equality
---------------------------------------------------------------
State and prove BEFORE indcca_inv_mo_win:

  Lemma Forall2_proj_el t1 t2 :
    List.Forall2 (eqR (indcca_inv_mo kem_inv_mo)) t1 t2 ->
    map proj_el t1 = map proj_el t2.

Proof: by induction on the Forall2 (using List_Forall2_inv from utils.v line 981,
or plain induction + List.Forall2_cons):
  - Base (both [::]):  map proj_el [::] = [::], trivially.
  - Step: given eqR (indcca_inv_mo kem_inv_mo) (x1, m1) (x2, m2) at the head:
      * heq  : x1 = x2       (from eqR, first component)
      * hinv : indcca_inv_mo kem_inv_mo m1 m2
              = [/\ mo_keys m1 = mo_keys m2, mo_bit m1 = mo_bit m2 & ...]
      * hbit : mo_bit m1 = mo_bit m2    (second conjunct of indcca_inv_mo)
    Therefore:
        proj_el (x1, m1) = (x1, mo_bit m1) = (x2, mo_bit m2) = proj_el (x2, m2)
    By IH: map proj_el t1' = map proj_el t2'.
    Conclude: map proj_el ((x1,m1) :: t1') = map proj_el ((x2,m2) :: t2').

To extract hbit from hinv: `move: hinv => [_ hbit _]` or `hinv.2` depending
on how [/\ P, Q & R] destructures. In SSReflect, `[/\ P, Q & R]` is And3
and the projections are `hinv.1, hinv.2, hinv.3` or `let: And3 p q r := hinv`.
Actually use `case: hinv => _ hbit _` or `move/and3P: hinv => [_ hbit _]`.
Better: `case: hinv => [hkeys hbit hmem]`.

STEP 6 — MAIN PROOF
--------------------
  Proof.
  move=> mu1 mu2 h.
  apply: h => t1 t2 hinv.
  rewrite /_win !factor_destruct_trace.
  congr (if _ is Some _ then _ else _).   (* or just `by rewrite ...` *)
  exact: congr1 _ (Forall2_proj_el hinv).
  Qed.

Or more directly:
  Proof.
  move=> mu1 mu2 h.
  apply: h => t1 t2 hinv.
  by rewrite /_win !factor_destruct_trace (Forall2_proj_el hinv).
  Qed.

The rewrite `!factor_destruct_trace` rewrites both `destruct_trace t1` and
`destruct_trace t2` into `destruct_trace_proj (map proj_el t1)` and
`destruct_trace_proj (map proj_el t2)`, and then `(Forall2_proj_el hinv)`
identifies `map proj_el t1 = map proj_el t2`, completing the proof.

SUMMARY OF NEW LEMMAS (all in Section REDUCTION, before indcca_inv_mo_win)
---------------------------------------------------------------------------
  Let proj_el (e : Xch * _Mo) : Xch * option bool := (e.1, mo_bit e.2).

  Let destruct_trace_proj (t : seq (Xch * option bool)) : option (...) := ...

  Lemma split_after_proj_el p t : ...   (* Step 3 *)
  Lemma factor_destruct_trace t : ...   (* Step 4 *)
  Lemma Forall2_proj_el t1 t2 : ...     (* Step 5 *)

EXISTING LEMMAS TO LOOK UP (Search in rocq-mcp with the file in scope)
-----------------------------------------------------------------------
  - map_rev        : map f (rev s) = rev (map f s)    [MathComp seq]
  - pmap_map       : pmap f (map g s) = pmap (f ∘ g) s [MathComp seq]
  - List_Forall2_inv : inversion for Forall2            [lang/utils.v:981]
  - List.Forall2_cons : constructor for Forall2          [Coq stdlib]
  Use `Search (map _ (rev _))` and `Search (pmap _ (map _ _))` to confirm names.

===== END PROOF PLAN ===== *)

Let proj_el (e : Xch (I := INDCCA_I) * _Mo)
    : Xch (I := INDCCA_I) * option bool := (e.1, mo_bit e.2).

Let destruct_trace_proj
    (t : seq (Xch (I := INDCCA_I) * option bool))
    : option (bool * seq ctxt * seq ctxt * ctxt) :=
  let t := rev t in
  let%opt ((x, _), t) := uncons t in
  let%opt _ := oassert (isSome (is_init x)) in
  let: (qs, t) := split_after (fun x => isSome (is_query x.1)) t in
  let qs := pmap (fun x => ssrfun.omap fst (is_query x.1)) qs in
  let%opt ((x, b), t) := uncons t in
  let%opt (ct, _) := is_getchallenge x in
  let%opt b := b in
  let: (qs', t) := split_after (fun x => isSome (is_query x.1)) t in
  let qs' := pmap (fun x => ssrfun.omap fst (is_query x.1)) qs' in
  let%opt ((x, _), t) := uncons t in
  let%opt g := is_finalize x in
  let%opt _ := oassert (nilp t) in
  Some (g == b, rev qs, rev qs', ct).

Lemma split_after_proj_el {A}
    (f : Xch (I := INDCCA_I) -> option A)
    (t : seq (Xch (I := INDCCA_I) * _Mo)) :
  split_after (fun x : Xch * option bool => isSome (f x.1))
              [seq proj_el e | e <- t] =
    ([seq proj_el e | e <- (split_after (fun x : Xch * _Mo => isSome (f x.1)) t).1],
     [seq proj_el e | e <- (split_after (fun x : Xch * _Mo => isSome (f x.1)) t).2]).
Proof.
elim: t => [|[x m] t ih] //=.
case: (isSome (f x)) => /=; last done.
by rewrite ih; case: (split_after _ t).
Qed.

Lemma pmap_proj_el {A} (f : Xch (I := INDCCA_I) -> option A)
    (s : seq (Xch (I := INDCCA_I) * _Mo)) :
  pmap (fun x : Xch * option bool => f x.1) [seq proj_el e | e <- s] =
  pmap (fun x : Xch * _Mo => f x.1) s.
Proof. by elim: s => [|[x m] s ih] //=; rewrite ih. Qed.

Lemma factor_destruct_trace (t : trace (I := INDCCA_I)) :
  destruct_trace t = destruct_trace_proj [seq proj_el e | e <- t].
Proof.
rewrite /destruct_trace /destruct_trace_proj -map_rev.
move: (rev t) => s.
case: s => [|[x0 m0] s1] //=.
rewrite split_after_proj_el.
case: (split_after (fun x => isSome (is_query x.1)) s1) => [qs s2] /=.
rewrite (pmap_proj_el (fun x => ssrfun.omap fst (is_query x))).
case: s2 => [|[x1 m1] s3] //=.
rewrite split_after_proj_el.
case: (split_after (fun x => isSome (is_query x.1)) s3) => [qs' s4] /=.
rewrite (pmap_proj_el (fun x => ssrfun.omap fst (is_query x))).
case: s4 => [|[x2 m2] s5] //=.
by case: s5.
Qed.

Lemma indcca_inv_mo_win Q kem_inv_mo :
  inv_mo_win (I := INDCCA_I) (indcca_inv_mo kem_inv_mo) (W Q).
Proof.
move=> mu1 mu2 h.
apply: h => t1 t2 hinv.
rewrite /W /win !factor_destruct_trace.
have hproj : [seq proj_el e | e <- t1] = [seq proj_el e | e <- t2].
{ move: hinv; elim=> [| [x1 m1] [x2 m2] t1' t2' [heq hinv] _ ih] //.
  case: hinv => [_ hbit _].
  congr (_ :: _); [by rewrite /proj_el heq hbit | exact ih]. }
by rewrite hproj.
Qed.

Lemma equivalent_INDCCA kem_inv_mo :
  is_inv_mo K K' kem_inv_mo ->
  is_inv_mo (INDCCA K) (INDCCA K') (indcca_inv_mo kem_inv_mo).
Proof.
move=> heq; split.
- split=> //=; exact: heq.(inv_mo_mi).
case.
- move=> [] [mk mb m1] [_ _ m2] [/= <- <- hm].
  apply: (eutt_clo_bind _ (UU := eqR kem_inv_mo));
    first exact: heq.(inv_mo_Oo) hm.
  by move=> [[pk sk] m1'] [_ m2'] [/= <- hm']; apply eutt_Ret.
- move=> ct [mk mb m1] [_ _ m2] [/= <- <- hm].
  rewrite /_Oo_Query; case: mk => [[pk sk]|] /=; last by apply eutt_Ret.
  apply: (eutt_clo_bind _ (UU := eqR kem_inv_mo));
    first exact: (heq.(inv_mo_Oo) (o := ODecap) (_, _) hm).
  by move=> [r m1'] [_ m2'] [/= <- hm']; apply eutt_Ret.
- move=> [] [mk mb m1] [_ _ m2] [/= <- <- hm].
  rewrite /_Oo_GetChallenge; case: mk => [[pk sk]|] /=; last by apply eutt_Ret.
  apply: (eutt_clo_bind _ (UU := eqR kem_inv_mo));
    first exact: (heq.(inv_mo_Oo) (o := OEncap) _ hm).
  move=> [[ct m0] m1'] [[_ _] m2'] [[/= <- <-] hm'].
  by apply: eutt_eq_bind => ?; apply: eutt_eq_bind => ?; apply eutt_Ret.
move=> g [mk mb m1] [_ _ m2] [/= <- <- hm].
apply eutt_Ret; split=> //; split=> //=; exact: heq.(inv_mo_mi).
Qed.

Theorem indcca_adv_equiv : equivalent K K' -> reduction K K'.
Proof.
move=> [inv_mo /equivalent_INDCCA heq] A Q.
congr (`| _ - 1/2 |); exact/(equivalent_pwin (InvMo := heq))/indcca_inv_mo_win.
Qed.

End REDUCTION.

End REAL.

Arguments Exchange {I}.
Arguments interact {_ I}.
Arguments dinteract {_ I}.
Arguments pwin {_ I}.
Arguments OracleSystem {_} _.
