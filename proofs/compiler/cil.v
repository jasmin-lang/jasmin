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

Section UTILS.

(* foldl (fun s x => if p x then x :: s else s) [::] s *)
Fixpoint take_while T (p : pred T) (s : seq T) : seq T :=
  if s is x :: s then
    if p x then x :: take_while p s else [::]
  else s.

Fixpoint drop_while T (p : pred T) (s : seq T) : seq T :=
  if s is x :: s then
    if p x then drop_while p s else x :: s
  else s.

Fixpoint split_after T (p : pred T) (s : seq T) : seq T * seq T :=
  if s is x :: s then
    if p x then
      let: (s1, s2) := split_after p s in
      (x :: s1, s2)
    else ([::], x :: s)
  else ([::], [::]).

Lemma split_after_take_drop T p (s : seq T) :
  split_after p s = (take_while p s, drop_while p s).
Proof. elim: s => [|x s hi] //=; case: ifP => _ //; by rewrite hi. Qed.

Definition uncons T (s : seq T) : option (T * seq T) :=
  if s is x :: s then Some (x, s) else None.

End UTILS.

Section REAL.

Context {R : realType}.

Notation distr := (distr R).
Notation Rnd := (Rnd (R := R)).

Section MAIN.

Section CIL.

Class OracleSystem :=
  {
    Mo : choiceType; (* Oracle memories. *)
    No : choiceType; (* Oracle names. *)
    In : No -> choiceType; (* Oracle input types. *)
    Out : No -> choiceType; (* Oracle output types. *)
    Oo : (* Oracle implementation. *)
      forall (o : No), In o -> Mo -> itree Rnd (Out o * Mo);
    mi : Mo; (* Initial oracle memory. *)
    oI : No; (* Initial oracle. *)
    oF : No; (* Final oracle. *)
    In_oI : In oI = unit;
    Out_oF : Out oF = unit;
  }.

Context {O : OracleSystem}.

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

Context {A : Adversary}.

(* Get the latest oracle memory, or the initial memory if there is no trace. *)
Definition get_Mo E `{stateE trace -< E} : itree E Mo :=
  let* t := get in Ret (head mi [seq x.2 | x <- t ]).

Definition mk {o : No} (m : Mo) (i : In o) (r : Out o) : Xch * Mo :=
  (existT (fun _ => _)%type o (i, r), m).

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

Class WinningCondition := { win : trace -> bool; }.

Context {W : WinningCondition}.

Definition pwin : R := \P_[ dinteract ] win.

End CIL.

End MAIN.

Arguments Exchange {_}.
Arguments interact : clear implicits.
Arguments pwin : clear implicits.

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
HB.instance Definition _ := Choice.copy oracle_name (pcan_type oracle_name_pickleK).

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
  (dummy_ct : ctxt)
  (dummy_msg : msg)
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

(* Alternative definition that is a [choiceType]. *)
Definition _Mo_choice : Type := option (pkey * skey) * option bool.

Definition pickle__Mo (m : _Mo) : _Mo_choice :=
  (mo_keys m, mo_bit m).

Definition unpickle__Mo (mk : _Mo_choice) : _Mo :=
  {| mo_keys := mk.1; mo_bit := mk.2; |}.

Lemma pickle__MoK : cancel pickle__Mo unpickle__Mo.
Proof. by case. Qed.

HB.instance Definition _ := Choice.copy _Mo (can_type pickle__MoK).

Definition mo_with_bit (m : _Mo) (b : bool) : _Mo :=
  {| mo_keys := mo_keys m; mo_bit := Some b; |}.

Definition _mi : _Mo := {| mo_keys := None; mo_bit := None; |}.

Definition _In (x : oracle_name) : choiceType :=
  match x with
  | OGenKey => unit
  | ODecap => ctxt
  | OGetChallenge => unit
  | OSubmitGuess => bool
  end.

Definition _Out (x : oracle_name) : choiceType :=
  match x with
  | OGenKey => pkey
  | ODecap => msg
  | OGetChallenge => ctxt * msg
  | OSubmitGuess => unit
  end%type.

Definition _Oo_GenKey (_ : unit) (_ : _Mo) : itree Rnd (pkey * _Mo) :=
  let* (pk, sk) := C.(indcca.GenKey) in
  let mo := {| mo_keys := Some (pk, sk); mo_bit := None; |} in
  Ret (pk, mo).

Definition _Oo_Decap (ct : ctxt) (mo : _Mo) : itree Rnd (msg * _Mo) :=
  if mo_keys mo is Some (_, sk) then
    let* m := C.(indcca.Decap) sk ct in
    Ret (m, mo)
  else Ret (dummy_msg, mo).

Definition _Oo_GetChallenge
  (_ : unit) (mo : _Mo) : itree Rnd ((ctxt * msg) * _Mo) :=
  if mo_keys mo is Some (pk, _) then
    let* (ct, m0) := C.(indcca.Encap) pk in
    let* m1 := indcca.rnd_msg in
    let* b := indcca.flip in
    let mb := if b then m1 else m0 in
    Ret ((ct, mb), mo_with_bit mo b)
  else Ret ((dummy_ct, dummy_msg), mo).

Definition _Oo_SubmitGuess (g : bool) (_ : _Mo) : itree Rnd (unit * _Mo) :=
  Ret (tt, _mi).

Definition _Oo (x : oracle_name) : _In x -> _Mo -> itree Rnd (_Out x * _Mo) :=
  match x return _In x -> _Mo -> itree Rnd (_Out x * _Mo) with
  | OGenKey => _Oo_GenKey
  | ODecap => _Oo_Decap
  | OGetChallenge => _Oo_GetChallenge
  | OSubmitGuess => _Oo_SubmitGuess
  end.

Instance INDCCA : OracleSystem :=
  {|
    Mo := _Mo;
    No := oracle_name;
    In := _In;
    Out := _Out;
    Oo := _Oo;
    mi := _mi;
    oI := OGenKey;
    oF := OSubmitGuess;
    In_oI := erefl;
    Out_oF := erefl;
  |}.

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

Definition destruct_trace
  (t : trace) : option (bool * seq ctxt * seq ctxt * ctxt) :=
  let t := rev t in
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

Definition _win (t : trace) : bool :=
  if destruct_trace t is Some  (b, qs, qs', ct) then
    [&& b & indcca.valid Q (qs, qs', ct) ]
  else false.

Instance W : WinningCondition := {| win := _win; |}.

Definition indcca_adv A := `| pwin INDCCA A W - 1/2 |.

Section PROOF.

Definition match_res
  (t : bool * indcca.trace (ctxt := ctxt)) (t' : trace) : bool :=
  if destruct_trace t' is Some (b2, qs2, qs2', ct2) then
    let: (b1, (qs1, qs1', ct1)) := t in
    [&& b1 == b2, ct1 == ct2, qs1 == qs2 & qs1' == qs2' ]
  else false.

Lemma match_resP t t' :
  match_res t t' ->
  [&& t.1 & indcca.valid Q t.2 ] = win t'.
Proof.
rewrite /match_res /= /_win; case: destruct_trace => // -[[[b2 qs2] qs2'] ct2].
by move: t => [b1 [[qs1 qs1'] ct1]] /and4P [/eqP -> /eqP -> /eqP -> /eqP ->].
Qed.

Section ADV.

  Context
    {advmem : Type}
    (A : @indcca.Adversary R pkey advmem ctxt msg)
  .

  Definition Exch_of_Dec : Handler indcca.Dec (Exch +' Rnd) :=
    fun T e =>
      let 'indcca.Decapsulate ct := e in
      trigger (Exchange ODecap ct).

  Let Query pk := interp (case_ Exch_of_Dec inr_) (A.(indcca.Query) pk).
  Let Guess st pk ct msg :=
    interp (case_ Exch_of_Dec inr_) (A.(indcca.Guess) st pk ct msg).

  Definition _Aa  : itree (Exch +' Rnd) unit :=
    let* pk := trigger (Exchange OGenKey tt) in
    let* st := Query pk in
    let* (ct, msg) := trigger (Exchange OGetChallenge tt) in
    let* b := Guess st pk ct msg in
    trigger (Exchange OSubmitGuess b).

  #[export] Instance A_of_indcca : Adversary := {| Aa := _Aa; |}.

 End ADV.

(* Convert eq_itree to eutt. *)
Local Lemma eqi2eutt {E0 X0} (t1 t2 : itree E0 X0) : t1 ≅ t2 -> t1 ≈ t2.
Proof. exact: eq_sub_eutt. Qed.

(* One-step unfolding of run_state (interp hI (Ret/Tau/Vis)). *)

Lemma rsi_ret {E F0 St X} (hI : E ~> itree (stateE St +' F0)) (r : X) (s : St) :
  run_state (interp hI (Ret r)) s ≈ Ret (s, r).
Proof.
rewrite /run_state; etransitivity.
{ eapply eutt_interp_state_eq; last reflexivity.
  apply eqi2eutt; exact (interp_ret (f := hI) r). }
apply eqi2eutt; apply interp_state_ret.
Qed.

Lemma rsi_tau {E F0 St X} (hI : E ~> itree (stateE St +' F0))
  (t : itree E X) (s : St) :
  run_state (interp hI (Tau t)) s ≈ Tau (run_state (interp hI t) s).
Proof.
rewrite /run_state; etransitivity.
{ eapply eutt_interp_state_eq; last reflexivity.
  apply eqi2eutt; exact (interp_tau (f := hI) t). }
apply eqi2eutt; apply interp_state_tau.
Qed.

Lemma rsi_vis {E F0 St X T} (hI : E ~> itree (stateE St +' F0))
  (e : E T) (k : T -> itree E X) (s : St) :
  run_state (interp hI (Vis e k)) s ≈
  let* sx := run_state (@hI T e) s in
    Tau (run_state (interp hI (k sx.2)) sx.1).
Proof.
rewrite /run_state; etransitivity.
{ eapply eutt_interp_state_eq; last reflexivity.
  apply eqi2eutt; exact (interp_vis (f := hI) T e k). }
etransitivity.
{ apply eqi2eutt; apply interp_state_bind. }
apply eutt_clo_bind with (UU := eq).
- reflexivity.
- move=> [s' x] _ <-.
  apply eqi2eutt; apply interp_state_tau.
Qed.

Lemma rsi_bind {E F0 St X Y} (hI : E ~> itree (stateE St +' F0))
  (t : itree E X) (k : X -> itree E Y) (s : St) :
  run_state (interp hI (ITree.bind t k)) s ≈
  ITree.bind (run_state (interp hI t) s) (fun sx =>
    run_state (interp hI (k (snd sx))) (fst sx)).
Proof.
rewrite /run_state; etransitivity.
{ eapply eutt_interp_state_eq; last reflexivity.
  apply eqi2eutt; exact (interp_bind hI t k). }
apply eqi2eutt.
Admitted.

(* Observation-based variants: given observe t = ..., unfold run_state(interp). *)
Local Lemma obs_eq {E X} (t : itree E X) ot :
  observe t = ot -> t ≅ go ot.
Proof. intro H; subst; exact (itree_eta_ t). Qed.

Lemma rsi_obs_ret {E F0 St X} (hI : E ~> itree (stateE St +' F0))
  (t : itree E X) (s : St) r :
  observe t = RetF r ->
  run_state (interp hI t) s ≈ Ret (s, r).
Proof.
move=> /obs_eq Ht. setoid_rewrite Ht. exact (rsi_ret hI r s).
Qed.

Lemma rsi_obs_tau {E F0 St X} (hI : E ~> itree (stateE St +' F0))
  (t : itree E X) (s : St) t' :
  observe t = TauF t' ->
  run_state (interp hI t) s ≈ Tau (run_state (interp hI t') s).
Proof.
move=> /obs_eq Ht. setoid_rewrite Ht. exact (rsi_tau hI t' s).
Qed.

Lemma rsi_obs_vis {E F0 St X T} (hI : E ~> itree (stateE St +' F0))
  (t : itree E X) (s : St) (e : E T) (k : T -> itree E X) :
  observe t = VisF e k ->
  run_state (interp hI t) s ≈
  let* sx := run_state (@hI T e) s in
    Tau (run_state (interp hI (k sx.2)) sx.1).
Proof.
move=> /obs_eq Ht. setoid_rewrite Ht. exact (rsi_vis hI e k s).
Qed.

Definition oracle_inv pk sk (s : trace) : Prop :=
  mo_keys ((head mi [seq x.2 | x <- s]) : _Mo) = Some (pk, sk).

(* Helper lemma: both sides of the adversary phase produce the same
   adversary output. The left side interprets Dec events directly (with
   handle_Dec), while the right side first translates Dec to Exchange events
   and then handles them through the oracle system. *)
Lemma eutt_adv_phase {X}
  (t : itree (indcca.Dec +' Rnd) X) sk pk lq (s : trace) :
  oracle_inv pk sk s ->
  eutt (fun '(_, x) '(s', x') => x = x' /\ oracle_inv pk sk s')
    (run_state (interp (case_ (indcca.handle_Dec C sk) inr_) t) lq)
    (run_state (interp (case_ handle_Exch inr_)
                  (interp (case_ Exch_of_Dec inr_) t)) s).
Proof.
intro Hinv; revert t lq s Hinv.
einit. ecofix CIH. intros t0 lq0 s0 Hinv0.
pose proof (obs_eq (ot := observe t0) erefl) as Ht.
destruct (observe t0) as [r | t' | T0 e0 k0] eqn:Hobs; simpl in Ht.
- setoid_rewrite Ht; do 2 setoid_rewrite (interp_ret r);
   by rewrite /run_state !unfold_interp_state /=; eret.
- rewrite /=. setoid_rewrite Ht. admit.
setoid_rewrite Ht. admit.
Admitted.

(* GenKey step: the oracle system's GenKey produces the same keys as C.GenKey,
   and establishes the oracle invariant. *)
Lemma step_genkey :
  eutt (fun '(pk, sk) sx => pk = snd sx /\ oracle_inv pk sk (fst sx))
    C.(indcca.GenKey)
    (run_state (interp (case_ handle_Exch inr_)
      (trigger (Exchange OGenKey tt))) [::]).
Proof.
rewrite /run_state.
setoid_rewrite interp_trigger.
rewrite /= /handle_Exch /get_Mo /log /_Oo /= /_Oo_GenKey /=.
rewrite !interp_state_bind interp_state_trigger /= !bind_ret_l /=.
setoid_rewrite translate_bind.
setoid_rewrite interp_state_bind.
rewrite -[in eutt _ _](bind_ret_r (indcca.GenKey C)).
eapply eutt_clo_bind; last first.
- (* Continuation *)
  move=> [pk sk] [s' [r m']] /= HUU.
  repeat setoid_rewrite interp_state_bind.
  repeat setoid_rewrite interp_state_trigger.
  repeat setoid_rewrite bind_ret_l.
  simpl.
  (* Goal: eutt RR (Ret (pk,sk)) (right side with state ops) *)
  (* HUU constrains (r, m') to match (pk, sk) *)
  admit.
- (* Head: C.GenKey vs interp_state(translate inr1 C.GenKey) [::] *)
  (* The translate/interp_state passes C.GenKey's Rnd events through *)
  admit.
Admitted.

(* Remaining steps after GenKey + Query: GetChallenge, Guess, SubmitGuess. *)
(* Steps 3-5: GetChallenge, Guess, SubmitGuess.
   The left side is the tail of indcca.game after GenKey + Query.
   The right side is the decomposed oracle computation. *)
Lemma step_getchallenge_to_end
  {advmem} {A : @indcca.Adversary R pkey advmem ctxt msg}
  pk sk (lq : indcca.S (ctxt := ctxt)) amem (s : trace) right
  (Hinv : oracle_inv pk sk s) :
  eutt match_res
    (@ITree.bind _ _ _ (C.(indcca.Encap) pk) (fun p1 =>
     let '(ct, m0) := p1 in
     @ITree.bind _ _ _ indcca.rnd_msg (fun m1 =>
     @ITree.bind _ _ _ indcca.flip (fun b =>
     let mb := if b then m1 else m0 in
     @ITree.bind _ _ _
       (run_state (interp (case_ (indcca.handle_Dec C sk) inr_)
         (A.(indcca.Guess) amem pk ct mb)) [::])
       (fun p2 => let '(lg, g) := p2 in
        Ret (g == b, (lq, lg, ct)))))))
    right.
Proof. Admitted.

Lemma eutt_games {advmem} {A : @indcca.Adversary R pkey advmem ctxt msg} :
  eutt match_res (indcca.game C A) (interact INDCCA (A_of_indcca A)).
Proof.
rewrite /indcca.game /interact /_Aa.
(* Decompose right side: split run_state(interp H (bind chain)) into steps *)
repeat setoid_rewrite (rsi_bind (case_ handle_Exch inr_)).
(* Reassociate all binds *)
repeat setoid_rewrite bind_bind.
(* Step 1: GenKey — both sides sample (pk, sk) from C.GenKey *)
apply eutt_clo_bind with (UU := fun '(pk, sk) sx =>
  pk = snd sx /\ oracle_inv pk sk (fst sx)).
{ exact step_genkey. }
move=> [pk sk] [s1 ?] /= [<- Hinv1].
(* Step 2: Query — use eutt_adv_phase *)
apply eutt_clo_bind with
  (UU := fun '(_, x) '(s', x') => x = x' /\ oracle_inv pk sk s').
{ rewrite /indcca.interact. exact (@eutt_adv_phase _ _ sk pk _ _ Hinv1). }
move=> [lq amem] [s2 st] /= [? Hinv2]; subst st.
(* Steps 3-5: GetChallenge, Guess, SubmitGuess *)
exact (@step_getchallenge_to_end _ _ pk sk lq amem s2 _ Hinv2).
Qed.

Lemma correct_indcca advmem (A : @indcca.Adversary R _ advmem _ _) :
  exists A', indcca.advantage C A Q =  indcca_adv A'.
Proof.
exists (A_of_indcca A); rewrite /indcca_adv /indcca.advantage; do 2!f_equal.
by apply/(eutt_deqX eutt_games) => /= -[b t] t' /match_resP ->.
Qed.

(* This is a problem because I don't know how to pick [advmem] such that we
   can split the adversary in two. *)
Lemma complete_indcca (A : Adversary) :
  exists advmem (A' : @indcca.Adversary R _ advmem _ _),
    indcca.advantage C A' Q = indcca_adv A.
Proof. Admitted.

End PROOF.

End INSTANCE.

End REAL.
