(* * Utility definition for dmasm *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq choice eqtype.
Require Import ZArith FMapPositive finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset.
Local Open Scope fmap.

(* ** LEM
 * -------------------------------------------------------------------- *)

Axiom LEM : forall {T : Type}, forall (x y : T), {x=y}+{x<>y}.

(* ** Result monad
 * -------------------------------------------------------------------- *)

Inductive result (E : Type) (A : Type) : Type :=
| Ok of A
| Error of E.

Arguments Error {E} {A} s.

Module Result.

Definition apply eT aT rT (f : aT -> rT) (x : rT) (u : result eT aT) :=
  if u is Ok y then f y else x.

Definition bind eT aT rT (f : aT -> result eT rT) g :=
  match g with
  | Ok x    => f x
  | Error s => Error s
  end.

Definition map eT aT rT (f : aT -> rT) := bind (fun x => Ok eT (f x)).
Definition default eT aT := @apply eT aT aT (fun x => x).

End Result.

Definition o2r eT aT (e : eT) (o : option aT) :=
  match o with
  | None   => Error e
  | Some x => Ok eT x
  end.

Notation rapp  := Result.apply.
Notation rdflt := Result.default.
Notation rbind := Result.bind.
Notation rmap  := Result.map.
Notation ok    := (@Ok _) (only parsing).

Notation "m >>= f" := (rbind f m) (at level 25, left associativity).

Fixpoint mapM eT aT bT (f : aT -> result eT bT) (xs : seq aT) : result eT (seq bT) :=
  match xs with
  | [::] =>
      Ok eT [::]
  | [:: x & xs] =>
      f x >>= fun y =>
      mapM f xs >>= fun ys =>
      Ok eT [:: y & ys]
  end.

Fixpoint foldM eT aT bT (f : aT -> bT -> result eT bT) (acc : bT) (l : seq aT) :=
  match l with
  | [::]         => Ok eT acc
  | [:: a & la ] => f a acc >>= fun acc => foldM f acc la
  end.

Definition isOk e a (r : result e a) :=
  if r is Ok _ then true else false.

(* ** Misc functions
 * -------------------------------------------------------------------- *)

Definition isSome aT (o : option aT) :=
  if o is Some _ then true else false.

Fixpoint list_to_rev (ub : nat) :=
  match ub with
  | O    => [::]
  | x.+1 => [:: x & list_to_rev x ]
  end.

Definition list_to ub := rev (list_to_rev ub).

Definition list_from_to (lb : nat) (ub : nat) :=
  map (fun x => x + lb)%nat (list_to (ub - lb)).

Definition conc_map aT bT (f : aT -> seq bT) (l : seq aT) :=
  flatten (map f l).

Fixpoint unions_seq (K : choiceType) (ss : seq {fset K}) : {fset K} :=
  match ss with
  | [::]         => fset0
  | [:: x & xs ] => x `|` unions_seq xs
  end.

Definition unions (K : choiceType) (ss : {fset {fset K}}) : {fset K} :=
  unions_seq (fset_keys ss).

Lemma seq_fset0 (aT : choiceType):  @seq_fset aT [::] = fset0.
Proof. by apply/fsetP => x; rewrite in_seq_fsetE in_fset0 in_nil. Qed.

Lemma unions_set_map_fset1 (aT : choiceType) (vs : seq aT):
  unions_seq (map fset1 vs) = seq_fset vs.
Proof.
elim: vs; last by move=> v vs; rewrite /= fset_cons => ->.
by rewrite /= seq_fset0.
Qed.

Definition oeq aT (f : aT -> aT -> Prop) (o1 o2 : option aT) :=
  match o1, o2 with
  | Some x1, Some x2 => f x1 x2
  | None,    None    => true
  | _ ,      _       => false
  end.

Definition req eT aT (f : aT -> aT -> Prop) (o1 o2 : result eT aT) :=
  match o1, o2 with
  | Ok x1,   Ok x2 => f x1 x2
  | Error _, Error _ => true
  | _ ,       _      => false
  end.

(* ** Fmap equality on subset of keys
 * -------------------------------------------------------------------- *)

Definition eq_on (K : choiceType) V (s : {fset K}) (m1 m2 : {fmap K -> V}) :=
  m1.[& s] = m2.[& s]. (* FIXME: maybe this should be just a notation? *)

Notation "m1 = m2 [& s ]" := (eq_on s m1 m2) (at level 70, m2 at next level,
  format "'[hv ' m1  '/' =  m2  '/' [&  s ] ']'").

Section EqOn.

Variable K : choiceType.
Variable V : Type.

Lemma eq_on_fsubset (s1 s2 : {fset K}) (m1 m2 : {fmap K -> V}):
  s1 `<=` s2 ->
  m1 = m2 [& s2] ->
  m1 = m2 [& s1].
Proof.
rewrite /eq_on; move=> Hsub Hs2.
move: (f_equal (fun m => m.[& s1]) Hs2); rewrite !restrictf_comp.
by rewrite (_ : s2 `&` s1 = s1); [ | exact (fsetIidPr Hsub) ].
Qed.

Lemma eq_on_Ur(s1 s2 : {fset K}) (m1 m2 : {fmap K -> V}):
  m1 = m2 [& s1 `|` s2] ->
  m1 = m2 [& s2].
Proof. by apply eq_on_fsubset; apply /fsetUidPr; rewrite fsetUCA fsetUid /=. Qed.

Lemma eq_on_Ul(s1 s2 : {fset K}) (m1 m2 : {fmap K -> V}):
  m1 = m2 [& s1 `|`  s2]->
  m1 = m2 [& s1].
Proof. by apply eq_on_fsubset; apply /fsetUidPr; rewrite fsetUA fsetUid /=. Qed.

Lemma eq_on_U(s1 s2 : {fset K}) (m1 m2 : {fmap K -> V}):
  m1 = m2 [& s1 `|`  s2] ->
  m1 = m2 [& s1] /\ m1 = m2 [& s2].
Proof. by move=> HU; split; [ apply: eq_on_Ul HU | apply: eq_on_Ur HU ]. Qed.

Lemma eq_on_get_in (s : {fset K}) (m1 m2 : {fmap K -> V}) (k : K) :
  m1 = m2 [& s] ->
  k \in s ->
  m1.[? k] = m2.[? k].
Proof.
move=> Heq_on Hin.
rewrite (_: m1.[? k] = m1.[& s].[? k]). 
+ by rewrite Heq_on fnd_restrict Hin.
by rewrite fnd_restrict Hin.
Qed.

Lemma eq_on_get_fset1 (m1 m2 : {fmap K -> V}) (k : K) :
  m1 = m2 [& [fset k]] ->
  m1.[? k] = m2.[? k].
Proof. by move=> Heq_on; apply: (eq_on_get_in Heq_on); rewrite in_fset1. Qed.

Lemma eq_on_setf_same (s : {fset K}) (m1 m2 : {fmap K -> V}) k v:
  m1 = m2 [& s] ->
  m1.[k <- v] = m2.[k <- v] [& s].
Proof. by rewrite /eq_on !restrictf_set /= => ->. Qed.

End EqOn.

Definition req_on eT (K : choiceType) V (s : {fset K}) (m1 m2 : result eT {fmap K -> V}) :=
  req (eq_on s) m1 m2.

Notation "m1 = m2 [&& s ]" := (req_on s m1 m2) (at level 70, m2 at next level,
  format "'[hv ' m1  '/' =  m2  '/' [&&  s ] ']'").

Section ReqOn.

Variable K : choiceType.
Variable V : Type.

Lemma req_on_rbind eT (om1 om2 : {fmap K -> V} -> result eT {fmap K -> V})
    (m1 m2 : {fmap K -> V}) ks:
  m1 = m2 [& ks] ->
  om1 m1 = om1 m2 [&& ks] ->
  (forall m1_ m2_,
    m1_ = m2_ [& ks] ->
    om2 m1_ = om2 m2_ [&& ks]) ->
  (om1 m1 >>= fun m1_ => om2 m1_) = (om1 m2 >>= fun m2_ => om2 m2_) [&& ks].
Proof.
move=> Heq Hom1_eq Hom2_eq.
by move: Hom1_eq; case (om1 m2); case (om1 m1) => //=.
Qed.

Lemma req_on_ofold eT (aT : eqType) (step : aT -> {fmap K -> V} -> result eT {fmap K -> V})
    ks (ws : seq aT):
  forall (m1 m2 : {fmap K -> V}),
    m1 = m2 [& ks] ->
    (forall (m1_ m2_ : {fmap K -> V}) (w : aT),
      w \in ws ->
      m1_ = m2_ [& ks] ->
      step w m1_ = step w m2_ [&& ks]) ->
    foldM step m1 ws = foldM step m2 ws [&& ks].
Proof.
elim: ws => //= w ws IH m1 m2 Heq Hinv.
apply:
  (@req_on_rbind eT 
     (fun m => step w m) (fun m => foldM step m ws)
     m1 m2 ks Heq).
+ by apply Hinv => //=; apply mem_head.
move=> m1_ m2_ Heq_.
apply: (IH m1_ m2_ Heq_).
move=> m1__ m2__ w__ Hin__ Heq__.
apply: Hinv => //=.
by rewrite in_cons; apply /orP; right.
Qed.

Lemma req_on_refl eT (m : result eT {fmap K -> V}) (ks : {fset K}):
  m = m [&& ks].
Proof. by rewrite /req_on /req; case m. Qed.

End ReqOn.

(* -------------------------------------------------------------------------- *)
(* Operators to build comparison                                              *)
(* ---------------------------------------------------------------------------*)

Section CTRANS.

  Definition ctrans c1 c2 := nosimpl (
    match c1, c2 with
    | Eq, _  => Some c2 
    | _ , Eq => Some c1
    | Lt, Lt => Some Lt 
    | Gt, Gt => Some Gt
    | _ , _  => None 
    end).
 
  Lemma ctransI c : ctrans c c = Some c.
  Proof. by case: c. Qed.

  Lemma ctransC c1 c2 : ctrans c1 c2 = ctrans c2 c1.
  Proof. by case: c1 c2 => -[]. Qed.

  Lemma ctrans_Eq c1 c2 : ctrans Eq c1 = Some c2 <-> c1 = c2.
  Proof. by rewrite /ctrans;case:c1=> //=;split=>[[]|->]. Qed.

  Lemma ctrans_Lt c1 c2 : ctrans Lt c1 = Some c2 -> Lt = c2.
  Proof. by rewrite /ctrans;case:c1=> //= -[] <-. Qed.

  Lemma ctrans_Gt c1 c2 : ctrans Gt c1 = Some c2 -> Gt = c2.
  Proof. by rewrite /ctrans;case:c1=> //= -[] <-. Qed.
 
End CTRANS.

Notation Lex u v := 
  match u with
  | Lt => Lt
  | Eq => v
  | Gt => Gt
  end.

Section LEX.

  Class Cmp {T:Type} (cmp:T -> T -> comparison) := {
    cmp_sym    : forall x y, cmp x y = CompOpp (cmp y x);
    cmp_ctrans : forall y x z c, ctrans (cmp x y) (cmp y z) = Some c -> cmp x z = c;
    cmp_eq     : forall x y, cmp x y = Eq -> x = y;
  }.

  Lemma cmp_trans {T} {cmp} {C:@Cmp T cmp} y x z c:
    cmp x y = c -> cmp y z = c -> cmp x z = c.
  Proof.
    by move=> H1 H2;apply (@cmp_ctrans _ _ C y);rewrite H1 H2 ctransI.
  Qed.

  Lemma cmp_refl  {T} {cmp} {C:@Cmp T cmp} x : cmp x x = Eq.
  Proof. by have := @cmp_sym _ _ C x x;case: (cmp x x). Qed.
 
  Variables (T1 T2:Type) (cmp1:T1 -> T1 -> comparison) (cmp2:T2 -> T2 -> comparison).

  Definition lex x y := Lex (cmp1 x.1 y.1) (cmp2 x.2 y.2).

  Lemma Lex_lex x1 x2 y1 y2 : Lex (cmp1 x1 y1) (cmp2 x2 y2) = lex (x1,x2) (y1,y2).
  Proof. done. Qed.

  Lemma lex_sym x y :
    cmp1 x.1 y.1 = CompOpp (cmp1 y.1 x.1) ->
    cmp2 x.2 y.2 = CompOpp (cmp2 y.2 x.2) ->
    lex  x y = CompOpp (lex  y x).
  Proof.
    by move=> H1 H2;rewrite /lex H1;case: cmp1=> //=;apply H2.
  Qed.
 
  Lemma lex_trans y x z:
    (forall c, ctrans (cmp1 x.1 y.1) (cmp1 y.1 z.1) = Some c -> cmp1 x.1 z.1 = c) ->
    (forall c, ctrans (cmp2 x.2 y.2) (cmp2 y.2 z.2) = Some c -> cmp2 x.2 z.2 = c) ->
    forall  c, ctrans (lex x y) (lex y z) = Some c -> lex x z = c.
  Proof.
    rewrite /lex=> Hr1 Hr2 c;case: cmp1 Hr1.
    + move=> H;rewrite (H (cmp1 y.1 z.1));last by rewrite ctrans_Eq. 
      (case: cmp1;first by apply Hr2);
        rewrite ctransC; [apply ctrans_Lt | apply ctrans_Gt].
    + move=> H1 H2;rewrite (H1 Lt);move:H2;first by apply: ctrans_Lt.
      by case: cmp1.
    move=> H1 H2;rewrite (H1 Gt);move:H2;first by apply: ctrans_Gt.
    by case: cmp1.
  Qed.

  Lemma lex_eq x y :
    lex x y = Eq -> cmp1 x.1 y.1 = Eq /\ cmp2 x.2 y.2 = Eq.
  Proof.
    case: x y => [x1 x2] [y1 y2] /=.
    by rewrite /lex;case:cmp1 => //;case:cmp2.
  Qed.

  Instance LexO (C1:Cmp cmp1) (C2:Cmp cmp2) : Cmp lex.
  Proof.
    constructor=> [x y | y x z | x y].
    + by apply /lex_sym;apply /cmp_sym.
    + by apply /lex_trans;apply /cmp_ctrans.
    by case: x y => ?? [??] /lex_eq /= [] /(@cmp_eq _ _ C1) -> /(@cmp_eq _ _ C2) ->.
  Qed.

End LEX.

Definition bool_cmp b1 b2 := 
  match b1, b2 with
  | false, true  => Lt
  | false, false => Eq
  | true , true  => Eq
  | true , false => Gt
  end.

Instance boolO : Cmp bool_cmp. 
Proof.
  constructor=> [[] [] | [] [] [] c | [] []] //=; apply ctrans_Eq.
Qed.

Instance positiveO : Cmp Pos.compare.
Proof.
  constructor.
  + by move=> ??;rewrite Pos.compare_antisym.
  + move=> ????;case:Pos.compare_spec=> [->|H1|H1];
    case:Pos.compare_spec=> H2 //= -[] <- //;subst;
    rewrite ?Pos.compare_lt_iff ?Pos.compare_gt_iff //.
    + by apply: Pos.lt_trans H1 H2. 
    by apply: Pos.lt_trans H2 H1.
  apply Pos.compare_eq.
Qed.
