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
Require Import rutt_extras oseq utils rutt_translate state_facts.

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
       (REv := fun A B e1 e2 => JMeq e1 e2)
       (RAns := fun A B e1 a e2 b => JMeq a b)).
  - move=> A B [X1 mu1] [X2 mu2] /= {}h; exact h.
  - by move=> A B [X1 mu1] [X2 mu2].
  apply: gen_eutt_rutt (inv_mo_Oo _ h) => // ??; exact: JMeq_eq.
move=> [r {}m1] [_ {}m2] [/= <- {}h].
apply: rutt_bind; first exact: ruttO_log.
move=> _ _ _; exact/rutt_Ret.
Qed.

Lemma ruttO_interp_handle_Exch {A : Adversary} :
  ruttO (fun _ _ => True)
    (interp (case_ (handle_Exch (O := O1)) inr_) Aa)
    (interp (case_ (handle_Exch (O := O2)) inr_) Aa).
Proof using. Admitted.

Lemma eutt_interact A : eutt inv_trace (interact O1 A) (interact O2 A).
Proof.
apply: (eutt_clo_bind _ (UU := RR_run_state inv_trace (fun _ _ => True)));
  last first.
- move=> [t1 []] [t2 []] [/= h _]; apply eutt_Ret; exact: h.
apply: rutt_inv_run_state => //; exact/ruttO_interp_handle_Exch.
Qed.

Definition inv_mo_win (W : WinningCondition) : Prop :=
  forall A (mu1 : distr trace1) (mu2 : distr trace2),
    deqX (R := R) inv_trace mu1 mu2 ->
    \P_[dinteract O1 A] win = \P_[dinteract O2 A] win.

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

(*
Lemma equivalent_INDCCA :
  equivalent K K' ->
  equivalent (INDCCA K) (INDCCA K').
Proof.
move=> h; case=> [[] m | ct m | [] m | g m] /=; last reflexivity.
- by apply: (eqit_bind' eq) => [|? _ <-]; [exact/h|reflexivity].
- rewrite /_Oo_Query; case: (mo_keys m) => [[pk sk] |]; last reflexivity.
  by apply: (eqit_bind' eq) => [|? _ <-]; [exact/h|reflexivity].
rewrite /_Oo_GetChallenge; case: (mo_keys m) => [[pk sk] |]; last reflexivity.
by apply: (eqit_bind' eq) => [|? _ <-]; [exact/h|reflexivity].
Qed.

Theorem indcca_adv_equiv : equivalent K K' -> reduction K K'.
Proof.
move=> /equivalent_INDCCA/equivalent_pwin h A Q; by rewrite /indcca_adv h.
Qed.
*)

End REDUCTION.

End REAL.

Arguments Exchange {I}.
Arguments interact {_ I}.
Arguments dinteract {_ I}.
Arguments pwin {_ I}.
Arguments OracleSystem {_} _.
