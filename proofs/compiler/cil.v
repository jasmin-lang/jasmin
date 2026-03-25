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
    Mo : Type;
    No : choiceType;
    In : No -> choiceType;
    Out : No -> choiceType;
    Oo : forall (o : No), In o -> Mo -> itree Rnd (Out o * Mo);
    orac_init_mem : Mo;
    oI : No;
    oI_ty : In oI = unit;
    oF : No;
    oF_ty : Out oF = unit;
  }.

Context {O : OracleSystem}.

Definition Res := In oF.

Definition Xch := { o : No & In o & Out o }.
Definition trace := seq (Mo * Xch).

Variant Exch : Type -> Type :=
  Exchange : forall o : No, In o -> Exch (Out o).

Class Adversary :=
  {
    Ma : choiceType;
    adv_init_mem : Ma;
    adv_run : Ma -> itree Exch Ma;
  }.

Context {A : Adversary}.

Definition get_Mo E `{stateE trace -< E} : itree E Mo :=
  let* t := get in Ret (head orac_init_mem [seq fst x | x <- t ]).

Definition mk (m : Mo) (o : No) (i : In o) (r : Out o) :=
  (m, existT2 In Out o i r).

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

Definition composition (E : trace -> Ma -> bool) : itree Rnd bool :=
  let c := interp handle_Exch (adv_run adv_init_mem) in
  let* (t, m) := run_state c [::] in
  Ret (E t m).

End CIL.

Notation "\Pr_[ A | O | E ]" :=
  (\P_[ dinterp (composition (A := A) (O := O) E) ] id).

Context {O : OracleSystem} {A : Adversary}.

Check \Pr_[ A | O | fun _ _ => true ] : R.

End MAIN.
