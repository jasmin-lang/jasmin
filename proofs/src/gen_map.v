(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import FMaps FMapAVL.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** *)

Module Type OrdDecT.

  Parameter t : Type.

  Parameter cmp : t -> t -> comparison.

  Parameter cmp_eq : forall x y, cmp x y = Eq <-> x = y.

  Parameter cmp_sym : forall x y, cmp x y = CompOpp (cmp y x).

  Parameter cmp_trans : forall y x z c, cmp x y = c -> cmp y z = c -> cmp x z = c.

End OrdDecT.

Module MkOrdT (T:OrdDecT) <: OrderedType.

  Definition t := T.t.

  Definition eq x y := T.cmp x y = Eq.
  Definition lt x y := T.cmp x y = Lt.

  Lemma eq_refl x: eq x x. 
  Proof. by rewrite /eq T.cmp_eq. Qed.
 
  Lemma eq_sym x y: eq x y -> eq y x.
  Proof. by rewrite /eq=> Heq;rewrite T.cmp_sym Heq. Qed.

  Lemma eq_trans x y z: eq x y -> eq y z -> eq x z.
  Proof. by apply T.cmp_trans. Qed.

  Lemma lt_trans x y z: lt x y -> lt y z -> lt x z.
  Proof. apply T.cmp_trans. Qed.

  Lemma lt_not_eq x y: lt x y -> ~ eq x y.
  Proof. by rewrite /lt /eq => ->. Qed.

  Lemma gt_lt x y : T.cmp x y = Gt -> lt y x.
  Proof. by rewrite /lt=> H;rewrite T.cmp_sym H. Qed.

  Definition compare x y : Compare lt eq x y := 
    let c := T.cmp x y in
    match c as c0 return c = c0 -> Compare lt eq x y with
    | Lt => @LT t lt eq x y 
    | Eq => @EQ t lt eq x y 
    | Gt => fun h => @GT t lt eq x y (gt_lt h)
    end (erefl c).

  Definition eq_dec x y: {eq x y} + {~ eq x y}.
  Proof. (rewrite /eq;case:T.cmp;first by left); by right. Qed.

End MkOrdT.

Module Type CompuEqDec.

  Parameter t: eqType.
  
  Parameter eq_dec : forall (t1 t2:t), {t1 = t2} + {True}.

  Axiom eq_dec_r : forall t1 t2 tt, eq_dec t1 t2 = right tt -> t1 != t2.

End CompuEqDec.

Reserved Notation "x .[ k <- v ]"
     (at level 2, k at level 200, v at level 200, format "x .[ k  <-  v ]").

Module DMmake (K:CompuEqDec) (T:OrdDecT with Definition t := Equality.sort K.t).

  Record boxed (P:K.t -> Type) := Box {
    box_t : K.t;
    box_v : P box_t;
  }.

  Definition from_boxed {P} (k:K.t) (b:option (boxed P)) : option (P k):= 
    match b with
    | Some (Box k' v) =>
      match K.eq_dec k' k with
      | left Heq => Some (eq_rect k' P v k Heq)
      | _        => None
      end
    | _ => None
    end.

  Module Ordered := MkOrdT T.

  Module Map := FMapAVL.Make Ordered.

  Module Facts := WFacts_fun Ordered Map.

  Definition t (P:K.t -> Type) := Map.t (boxed P).

  Definition empty P : t P := Map.empty (boxed P).

  Definition get {P} (m:t P) (k:K.t) := 
    from_boxed k (Map.find k m). 

  Definition set {P} (m:t P) (k:K.t) (v:P k) := 
    Map.add k (Box v) m.

  Local Notation "m .[ s ]" := (get m s).
  Local Notation "x .[ k <- v ]" := (@set _ x k v).
  
  Lemma get0 P x : (empty P).[x] = None.
  Proof. 
    rewrite /empty /get;have := @Map.empty_1 (boxed P).
    case Heq: (Map.find x (Map.empty (boxed P)))=>[?|] //=.
  Qed.

  Lemma setP {P} (m: t P) x y (v:P x) :
    m.[x <- v].[y] = 
    match K.eq_dec x y with
    | left Heq => Some (eq_rect x P v y Heq)
    | _        => m.[y]
    end.
  Proof.  
    rewrite /set /get /from_boxed /=.
    case H: (K.eq_dec x y) (@K.eq_dec_r x y) => [Heq | []] => [ _ | Hneq].
    + by rewrite Facts.add_eq_o ?H // T.cmp_eq.
    have {Hneq} /eqP Hneq := Hneq I (erefl _).  
    by rewrite Facts.add_neq_o // T.cmp_eq. 
  Qed.

  Lemma setP_eq {P} (m: t P) x (v:P x) : m.[x <- v].[x] = Some v.
  Proof. 
    rewrite setP;case: (K.eq_dec x x) (@K.eq_dec_r x x) => [eq _ | [] H ].
    + by rewrite (eq_irrelevance eq (erefl x)).
    by move: (H I (erefl _))=> /eqP.
  Qed.

  Lemma setP_neq {P} (m: t P) x y (v:P x) : x != y -> m.[x <- v].[y] = m.[y].
  Proof. 
    by rewrite setP;case: K.eq_dec=> // a /negP neq;elim neq;rewrite a.
  Qed.

End DMmake.

