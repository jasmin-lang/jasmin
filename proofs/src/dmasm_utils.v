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

(* ** Admit
 * -------------------------------------------------------------------- *)

Definition admit {T: Type} : T.  Admitted.

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

Lemma unions_set_map_fset1 (aT : choiceType) (vs : seq aT):
  unions_seq (map fset1 vs) = seq_fset vs.
Proof.
elim: vs; last by move=> v vs; rewrite /= fset_cons => ->.
by rewrite /=; apply/fsetP => x; rewrite in_seq_fsetE in_fset0 in_nil.
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
Lemma appendA : associative append.
Proof. by elim => //= p Hp y z;rewrite Hp. Qed.

Lemma log_app n p : log_inf (append n p) = (log_inf n + log_inf p)%Z.
Proof. elim: n => /= [ n -> | n -> | ];omega. Qed.

Lemma append_inj n1 n2 p1 p2: log_inf p1 = log_inf p2 -> 
  append n1 p1 = append n2 p2 -> n1 = n2 /\ p1 = p2.
Proof.
  elim: n1 n2 p1 p2 => [ n1 Hn1 | n1 Hn1 | ] [ n2 | n2 | ] //= p1 p2. 
  + by move=> Hl [] /(@Hn1 _ _ _ Hl) []-> ->.
  + move=> Heq Hp2;move: Heq;rewrite -Hp2 /= log_app => ?.
    have ?:= log_inf_correct1 n1;omega.
  + by move=> Hl [] /(@Hn1 _ _ _ Hl) []-> ->.
  + move=> Heq Hp2;move: Heq;rewrite -Hp2 /= log_app => ?.
    have ?:= log_inf_correct1 n1;omega.
  + move=> Heq Hp2;move: Heq;rewrite Hp2 /= log_app => ?.
    have ?:= log_inf_correct1 n2;omega.
  move=> Heq Hp2;move: Heq;rewrite Hp2 /= log_app => ?.
  have ?:= log_inf_correct1 n2;omega.
Qed.

Definition b2P b := 
  if b then 2%positive else 3%positive.

Definition b2P_app b n := 
  if b then xO n else xI n.

Lemma b2P_appP b n : b2P_app b n = append (b2P b) n.
Proof. by case:b. Qed.

Lemma log_b2P_app b n : log_inf (b2P_app b n) = Z.succ (log_inf n).
Proof. by case: b. Qed.

Lemma b2P_app_inj b1 b2 n1 n2 : b2P_app b1 n1 = b2P_app b2 n2 -> b1 = b2 /\ n1 = n2.
Proof. by case: b1 b2 => -[] //= []. Qed.

