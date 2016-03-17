(* ** Imports and settings *)
Require Import FMaps FMapAVL.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import dmasm_utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** *)

Module Type CmpType.

  Parameter t : eqType.

  Parameter cmp : t -> t -> comparison.

  Parameter cmpO : Cmp cmp.

End CmpType.

Module MkOrdT (T:CmpType) <: OrderedType.

  Definition t := Equality.sort T.t.

  Definition eq x y := T.cmp x y = Eq.
  Definition lt x y := T.cmp x y = Lt.

  Lemma eq_refl x: eq x x. 
  Proof. apply: cmp_refl. Qed.

  Lemma eq_sym x y: eq x y -> eq y x.
  Proof. by rewrite /eq=> Heq;rewrite cmp_sym Heq. Qed.

  Lemma eq_trans x y z: eq x y -> eq y z -> eq x z.
  Proof. by apply cmp_trans. Qed.

  Lemma lt_trans x y z: lt x y -> lt y z -> lt x z.
  Proof. apply cmp_trans. Qed.

  Lemma lt_not_eq x y: lt x y -> ~ eq x y.
  Proof. by rewrite /lt /eq => ->. Qed.

  Lemma gt_lt x y : T.cmp x y = Gt -> lt y x.
  Proof. by rewrite /lt=> H;rewrite cmp_sym H. Qed.

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

Module Type MAP.

  Declare Module K: CmpType.

  Parameter t : Type -> Type.

  Parameter empty : forall T, t T.

  Parameter get : forall {T}, t T -> K.t -> option T.

  Parameter set : forall {T}, t T -> K.t -> T -> t T.

  Parameter map : forall {T1 T2}, (T1 -> T2) -> t T1 -> t T2.

  Parameter remove :  forall {T}, t T -> K.t -> t T.

  Notation "m .[ s ]" := (get m s).
  Notation "x .[ k <- v ]" := (@set _ x k v).

  Parameter get0 : forall {T} x, (empty T).[x] = None.

  Parameter setP : forall {T} (m: t T) x y (v:T),
    m.[x <- v].[y] = if x == y then Some v else m.[y].

  Parameter setP_eq : forall {T} (m: t T) x (v:T), m.[x <- v].[x] = Some v.

  Parameter setP_neq : forall {T} (m: t T) x y (v:T), x != y -> m.[x <- v].[y] = m.[y].

  Parameter mapP : forall {T1 T2} (f:T1 -> T2) (m:t T1) (x:K.t),
    (map f m).[x] = omap f m.[x].

  Parameter removeP : forall {T} (m: t T) x y,
    (remove m x).[y] = if x == y then None else m.[y].

  Parameter removeP_eq : forall {T} (m: t T) x,
    (remove m x).[x] = None.

  Parameter removeP_neq : forall {T} (m: t T) x y,
    x != y -> (remove m x).[y] = m.[y].
     
End MAP.

Module Mmake (K:CmpType) <: MAP.

  Module K := K.

  Module Ordered := MkOrdT K.

  Module Map := FMapAVL.Make Ordered.

  Module Facts := WFacts_fun Ordered Map.

  Definition t (T:Type) := Map.t T.

  Definition empty T : t T := Map.empty T.

  Definition get {T} (m:t T) (k:K.t) := Map.find k m. 

  Definition set {T} (m:t T) (k:K.t) (v:T) := Map.add k v m.

  Definition map := Map.map.

  Definition remove {T} (m:t T) (k:K.t) := Map.remove k m.

  Notation "m .[ s ]" := (get m s).
  Notation "x .[ k <- v ]" := (@set _ x k v).
  
  Lemma get0 T x : (empty T).[x] = None.
  Proof. by rewrite /empty /get Facts.empty_o. Qed.

  Lemma setP {T} (m: t T) x y (v:T) :
    m.[x <- v].[y] = if x == y then Some v else m.[y].
  Proof.  
    rewrite /set /get /=;case: eqP=> H.
    + by rewrite Facts.add_eq_o // H cmp_refl.
    by rewrite Facts.add_neq_o // => H1;apply H;apply cmp_eq.
  Qed.

  Lemma setP_eq {T} (m: t T) x (v:T) : m.[x <- v].[x] = Some v.
  Proof. by rewrite setP eq_refl. Qed.

  Lemma setP_neq {T} (m: t T) x y (v:T) : x != y -> m.[x <- v].[y] = m.[y].
  Proof. by rewrite setP=> /negPf ->. Qed.

  Lemma mapP {T1 T2} (f:T1 -> T2) (m:t T1) (x:K.t):
    (map f m).[x] = omap f m.[x].
  Proof. by rewrite /map /get Facts.map_o. Qed.

  Lemma removeP {T} (m: t T) x y:
    (remove m x).[y] = if x == y then None else m.[y].
  Proof.
    rewrite /remove/get Facts.remove_o.
    case: Ordered.eq_dec.
    + by move=> /(@cmp_eq _ _ _ _ _) <-;rewrite eq_refl. (* Enrico : Bug *)
    move=> Hneq;have -> // : (x == y) = false.
    by case : (x =P y) => // ?;subst;elim Hneq.
  Qed.

  Lemma removeP_eq {T} (m: t T) x: (remove m x).[x] = None.
  Proof. by rewrite removeP eq_refl. Qed.

  Lemma removeP_neq {T} (m: t T) x y: x != y -> (remove m x).[y] = m.[y].
  Proof. by rewrite removeP => /negPf ->. Qed.

End Mmake.

Module DMmake (K:CmpType) (E:CompuEqDec with Definition t := K.t).

  Record boxed (P:K.t -> Type) := Box {
    box_t : K.t;
    box_v : P box_t;
  }.

  Definition from_boxed {P} (k:K.t) (b:option (boxed P)) : option (P k):= 
    match b with
    | Some (Box k' v) =>
      match E.eq_dec k' k with
      | left Heq => Some (eq_rect k' P v k Heq)
      | _        => None
      end
    | _ => None
    end.

  Module Ordered := MkOrdT K.

  Module Map := FMapAVL.Make Ordered.

  Module Facts := WFacts_fun Ordered Map.

  Definition t (P:K.t -> Type) := Map.t (boxed P).

  Definition empty P : t P := Map.empty (boxed P).

  Definition get {P} (m:t P) (k:K.t) := 
    from_boxed k (Map.find k m). 

  Definition set {P} (m:t P) (k:K.t) (v:P k) := 
    Map.add k (Box v) m.

  Definition map {P1 P2} (f:forall k:K.t, P1 k -> P2 k) (m:t P1) : t P2 := 
    Map.map (fun b => {|box_t := b.(box_t); box_v := @f b.(box_t) b.(box_v) |}) m.

  Notation "m .[ s ]" := (get m s).
  Notation "x .[ k <- v ]" := (@set _ x k v).
  
  Lemma get0 P x : (empty P).[x] = None.
  Proof. 
    rewrite /empty /get;have := @Map.empty_1 (boxed P).
    case Heq: (Map.find x (Map.empty (boxed P)))=>[?|] //=.
  Qed.

  Lemma setP {P} (m: t P) x y (v:P x) :
    m.[x <- v].[y] = 
    match E.eq_dec x y with
    | left Heq => Some (eq_rect x P v y Heq)
    | _        => m.[y]
    end.
  Proof.  
    rewrite /set /get /from_boxed /=.
    case H: (E.eq_dec x y) (@E.eq_dec_r x y) => [Heq | []] => [ _ | Hneq].
    + by rewrite Facts.add_eq_o ?H // Heq cmp_refl. 
    have {Hneq} /eqP Hneq := Hneq I (erefl _).  
    by rewrite Facts.add_neq_o // => H1;apply Hneq;apply cmp_eq.
  Qed.

  Lemma setP_eq {P} (m: t P) x (v:P x) : m.[x <- v].[x] = Some v.
  Proof. 
    rewrite setP;case: (E.eq_dec x x) (@E.eq_dec_r x x) => [eq _ | [] H ].
    + by rewrite (eq_irrelevance eq (erefl x)).
    by move: (H I (erefl _))=> /eqP.
  Qed.

  Lemma setP_neq {P} (m: t P) x y (v:P x) : x != y -> m.[x <- v].[y] = m.[y].
  Proof. 
    by rewrite setP;case: E.eq_dec=> // a /negP neq;elim neq;rewrite a.
  Qed.

  Lemma mapP {P1 P2} (f:forall k:K.t, P1 k -> P2 k) (m:t P1) (x:K.t):
    (map f m).[x] = omap (f x) m.[x].
  Proof. 
    rewrite /map /get Facts.map_o;case: Map.find => // -[z pz] /=.
    case E.eq_dec=> e //=; move:(e);rewrite -e=> {e} e.                    
    by rewrite (eq_irrelevance e (erefl z)).
  Qed.

End DMmake.

(* --------------------------------------------------------------------------
 ** Map of positive    
 * -------------------------------------------------------------------------- *) 

Require Import ZArith.

Module CmpPos.

  Definition t := [eqType of positive].

  Definition cmp : t -> t -> comparison := Pos.compare.

  Lemma cmpO : Cmp cmp.
  Proof. apply positiveO. Qed.

End CmpPos.

Module Mp := Mmake CmpPos.

(* --------------------------------------------------------------------------
 ** Finite Set    
 * -------------------------------------------------------------------------- *) 

Require Import MSets.

Module MkMOrdT (T:CmpType) <: Orders.OrderedType.
  Definition t := Equality.sort T.t.
 
  Definition eq := @Logic.eq t.

  Lemma eq_equiv : Equivalence eq.
  Proof. by auto. Qed.

  Definition lt x y := T.cmp x y = Lt.
  
  Lemma lt_strorder : StrictOrder lt.
  Proof. 
    constructor. 
    + by move=> x;rewrite /complement /lt cmp_refl.
    move=> ???;apply cmp_trans.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. by rewrite /eq;move=> ?? -> ?? ->. Qed.

  Definition compare : t -> t -> comparison := T.cmp.

  Lemma compare_spec :
     forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    move=> x y;rewrite /compare /eq /lt (cmp_sym y x).
    case: T.cmp (@cmp_eq _ _ T.cmpO x y);constructor;auto.
  Qed.
    
  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof. 
    by move=> x y;case:(x =P y);[left | right].
  Qed.

End MkMOrdT.

Module Smake (T:CmpType).
  Module Ordered := MkMOrdT T.
  Include (MSetAVL.Make Ordered).
End Smake.

