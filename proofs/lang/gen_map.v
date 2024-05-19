(* ** Imports and settings *)
Require Import FMaps FMapAVL FSetAVL.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma InAE (A: Type) (eqA: relation A) a m :
  InA eqA a m ->
  match m with
  | [::] => False
  | a' :: m' => eqA a a' \/ InA eqA a m'
  end.
Proof. by case; [ left | right ]. Qed.

Arguments InAE {A eqA a m}.

Lemma NoDupAE (A: Type) (eqA: relation A) m :
  NoDupA eqA m ->
  match m with
  | [::] => True
  | a' :: m' => ~ InA eqA a' m' /\ NoDupA eqA m'
  end.
Proof. by case. Qed.


(* ** *)

Module Type CmpType.

  Parameter t : eqType.

  Parameter cmp : t -> t -> comparison.

  Parameter cmpO : Cmp cmp.

End CmpType.

Module MkOrdT (T:CmpType) <: OrderedType.

#[global]
  Existing Instance T.cmpO | 1.

  Definition t := Equality.sort T.t.

  Definition eq x y := T.cmp x y = Eq.
  Definition lt x y := T.cmp x y = Lt.

  Lemma eq_refl x: eq x x.
  Proof. apply: cmp_refl. Qed.

  Lemma eq_sym x y: eq x y -> eq y x.
  Proof. by rewrite /eq=> Heq;rewrite cmp_sym Heq. Qed.

  Lemma eq_trans x y z: eq x y -> eq y z -> eq x z.
  Proof. apply cmp_trans. Qed.

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

  Parameter is_empty : forall T, t T -> bool.

  Parameter get : forall {T}, t T -> K.t -> option T.

  Parameter set : forall {T}, t T -> K.t -> T -> t T.

  Parameter remove :  forall {T}, t T -> K.t -> t T.

  Parameter map : forall {T1 T2}, (T1 -> T2) -> t T1 -> t T2.

  Parameter mapi : forall {T1 T2}, (K.t -> T1 -> T2) -> t T1 -> t T2.

  Parameter map2 : forall {T1 T2 T3},
    (K.t -> option T1 -> option T2 -> option T3) ->
    t T1 -> t T2 -> t T3.

  Parameter filter_map : forall {T1 T2}, (K.t -> T1 -> option T2) -> t T1 -> t T2.

  Parameter incl_def : forall {T1 T2},
     (K.t -> T1 -> bool) ->
     (K.t -> T1 -> T2 -> bool) ->
     t T1 -> t T2 -> bool.

  Parameter incl : forall {T1 T2},
     (K.t -> T1 -> T2 -> bool) ->
     t T1 -> t T2 -> bool.

  Parameter all : forall {T},
    (K.t -> T -> bool) ->
    t T -> bool.
  
  Parameter has : 
    forall {T},
      (K.t -> T -> bool) ->
      t T -> bool.

  Parameter elements : forall {T}, t T -> seq (K.t * T).

  Parameter fold : forall {T A}, (K.t -> T -> A -> A) -> t T -> A -> A.

  Parameter in_codom : forall {T:eqType}, T -> t T -> bool.

  Notation "m .[ s ]" := (get m s).
  Notation "x .[ k <- v ]" := (@set _ x k v).

  Parameter get0 : forall {T} x, (empty T).[x] = None.

  Parameter is_emptyP : forall {T} (m: t T), 
    reflect (forall x, m.[x] = None) (is_empty m).

  Parameter setP : forall {T} (m: t T) x y (v:T),
    m.[x <- v].[y] = if x == y then Some v else m.[y].

  Parameter setP_eq : forall {T} (m: t T) x (v:T), m.[x <- v].[x] = Some v.

  Parameter setP_neq : forall {T} (m: t T) x y (v:T), x != y -> m.[x <- v].[y] = m.[y].

  Parameter removeP : forall {T} (m: t T) x y,
    (remove m x).[y] = if x == y then None else m.[y].

  Parameter removeP_eq : forall {T} (m: t T) x,
    (remove m x).[x] = None.

  Parameter removeP_neq : forall {T} (m: t T) x y,
    x != y -> (remove m x).[y] = m.[y].

  Parameter mapP : forall {T1 T2} (f:T1 -> T2) (m:t T1) (x:K.t),
    (map f m).[x] = omap f m.[x].

  Parameter mapiP : forall {T1 T2} (f:K.t -> T1 -> T2) (m:t T1) (x:K.t),
    (mapi f m).[x] = omap (f x) m.[x].

  Parameter map2P : forall {T1 T2 T3}
    (f:K.t -> option T1 -> option T2 -> option T3) (m1:t T1) (m2:t T2) (x:K.t),
    f x None None = None ->
    (map2 f m1 m2).[x] = f x m1.[x] m2.[x].

  Parameter filter_mapP : forall {T1 T2} (f:K.t -> T1 -> option T2) (m:t T1) (x:K.t),
    (filter_map f m).[x] = obind (f x) m.[x].

  Parameter elementsP : forall {T:eqType} (kv:K.t * T) m,
    reflect (m.[kv.1] = Some kv.2) (kv \in elements m).

  Parameter elementsIn : forall T (kv:K.t * T) m,
     List.In kv (elements m) <-> m.[kv.1] = Some kv.2.

  Parameter elementsU : forall T (m:t T), uniq [seq x.1 | x <- (elements m)].

  Parameter foldP : forall {T A} (f:K.t -> T -> A -> A) m a,
    fold f m a = foldl (fun a (kv:K.t * T) => f kv.1 kv.2 a) a (elements m).

  Parameter incl_defP : forall {T1 T2} (f1:K.t -> T1 -> bool) (f:K.t -> T1 -> T2 -> bool) (m1: t T1) (m2: t T2),
     incl_def f1 f m1 m2 <->
     (forall k,
       match get m1 k, get m2 k with
       | None, _          => true
       | Some t1, None     => f1 k t1 
       | Some t1, Some t2 => f k t1 t2
       end).

  Parameter inclP : forall {T1 T2} (f:K.t -> T1 -> T2 -> bool) (m1: t T1) (m2: t T2),
     incl f m1 m2 <->
     (forall k,
       match get m1 k, get m2 k with
       | None, _          => true
       | Some _, None     => false
       | Some t1, Some t2 => f k t1 t2
       end).

  Parameter allP : forall {T} (f: K.t -> T -> bool) (m: t T),
    all f m <-> (forall k t, get m k = Some t -> f k t).

  Parameter hasP : forall {T} (f: K.t -> T -> bool) (m: t T),
    has f m <-> (exists k t, get m k = Some t /\ f k t).

  Parameter in_codomP : forall {T:eqType} (m:t T) v,
    in_codom v m <-> exists k, m.[k] = Some v.

End MAP.

Module Mmake (K':CmpType) <: MAP.

  Module K := K'.

  Module Ordered := MkOrdT K.

  Module Map := FMapAVL.Make Ordered.

  Module Facts := WFacts_fun Ordered Map.

  Definition t (T:Type) := Map.t T.

  Definition empty T : t T := Map.empty T.
  
  Definition is_empty  {T} (m:t T) := Map.is_empty m.

  Definition get {T} (m:t T) (k:K.t) := Map.find k m.

  Definition set {T} (m:t T) (k:K.t) (v:T) := Map.add k v m.

  Definition remove {T} (m:t T) (k:K.t) := Map.remove k m.

  Definition map := Map.map.

  Definition mapi := Map.mapi.

  Definition raw_map2 {T1 T2 T3} (f:K.t -> option T1 -> option T2 -> option T3) m1 m2 :=
    Map.Raw.map2_opt
      (fun k d o => f k (Some d) o)
      (Map.Raw.map_option (fun k d => f k (Some d) None))
      (Map.Raw.map_option (fun k d' => f k None (Some d'))) m1 m2.

  Definition elements := Map.elements.

  Definition fold     := Map.fold.

  Section QUANT.
    Context (T1:Type) (T2:Type) (f: K.t -> T1 -> bool) (f2: K.t -> T1 -> T2 -> bool).

    Fixpoint all_t (t:Map.Raw.tree T1) := 
      match t with
      | Map.Raw.Leaf => true
      | Map.Raw.Node t1 k x t2 _ => f k x && all_t t1 && all_t t2
      end.

    Fixpoint has_t (t:Map.Raw.tree T1) := 
      match t with
      | Map.Raw.Leaf => false
      | Map.Raw.Node t1 k x t2 _ => f k x || has_t t1 || has_t t2
      end.

    Fixpoint incl_t (t1:Map.Raw.tree T1) (t2:Map.Raw.tree T2) :=
      match t1 with
      | Map.Raw.Leaf => true
      | Map.Raw.Node t11 k x1 t12 _ =>
        let '(Map.Raw.mktriple t21 ox2 t22) := Map.Raw.split k t2 in
        [&& match ox2 with
            | None => f k x1
            | Some x2 => f2 k x1 x2 
            end,
            incl_t t11 t21 & incl_t t12 t22]
      end.

    Definition all (m: t T1) := all_t (Map.this m).
    Definition has (m: t T1) := has_t (Map.this m).
    
   End QUANT.

  Definition incl_def (T1:Type) (T2:Type) (f: K.t -> T1 -> bool) (f2: K.t -> T1 -> T2 -> bool) m1 m2:= 
    incl_t f f2 (Map.this m1) (Map.this m2).

  Definition incl T1 T2 := @incl_def T1 T2 (fun _ _ => false).

  Definition in_codom {T:eqType} v (m:t T) :=
    has (fun _ v' => v == v') m.

  Lemma raw_map2_bst {T1 T2 T3} (f:K.t -> option T1 -> option T2 -> option T3) m1 m2:
    Map.Raw.bst (raw_map2 f (Map.this m1) (Map.this m2)).
  Proof.
    rewrite /raw_map2.
    apply: (@Map.Raw.Proofs.map2_opt_bst _ _ _ f).
    + by apply Map.Raw.Proofs.map_option_bst=> ??? /cmp_eq ->.
    + by apply Map.Raw.Proofs.map_option_bst=> ??? /cmp_eq ->.
    + by move=> x m H;apply Map.Raw.Proofs.map_option_find=>// ??? /cmp_eq ->.
    + by move=> x m H;apply Map.Raw.Proofs.map_option_find=>// ??? /cmp_eq ->.
    + by apply Map.is_bst.
    by apply Map.is_bst.
  Qed.

  Definition map2 {T1 T2 T3} (f:K.t -> option T1 -> option T2 -> option T3)
      (m1:t T1) (m2: t T2) : t T3 :=
   (@Map.Bst _ (raw_map2 f m1.(Map.this) m2.(Map.this))
       (raw_map2_bst f m1 m2)).

  Lemma map_option_bst {T1 T2} (f:K.t -> T1 -> option T2) (m:t T1) : 
    Map.Raw.bst (Map.Raw.map_option f (Map.this m)).
  Proof.
    apply: Map.Raw.Proofs.map_option_bst.
    + by move=> ??? h; rewrite (cmp_eq h).
    by apply Map.is_bst.
  Qed.

  Definition filter_map {T1 T2} (f:K.t -> T1 -> option T2) (m:t T1) : t T2 := 
    @Map.Bst _ (Map.Raw.map_option f (Map.this m))
              (map_option_bst f m).

  Notation "m .[ s ]" := (get m s).
  Notation "x .[ k <- v ]" := (@set _ x k v).

  Lemma get0 T x : (empty T).[x] = None.
  Proof. by rewrite /empty /get Facts.empty_o. Qed.

  Lemma is_emptyP T (m: t T): reflect (forall x, m.[x] = None) (is_empty m).
  Proof.
    rewrite /is_empty /get /Map.find /Map.Empty /Map.is_empty; case heq: Map.Raw.is_empty; constructor.
    + move=> x; have h := Map.Raw.Proofs.is_empty_2 heq.
      case heq1:  Map.Raw.find => [ e | //].
      by have /h := Map.Raw.Proofs.find_2 heq1.
    move=> h.
    rewrite Map.Raw.Proofs.is_empty_1 in heq => //.
    rewrite /Map.Raw.Proofs.Empty => k e hm.
    have := Map.Raw.Proofs.find_1 (Map.is_bst m) hm.
    by rewrite h.
  Qed.

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

  Lemma removeP {T} (m: t T) x y:
    (remove m x).[y] = if x == y then None else m.[y].
  Proof.
    rewrite /remove/get Facts.remove_o.
    case: Ordered.eq_dec.
    + by move=> /cmp_eq <-;rewrite eq_refl.
    move=> Hneq;have -> // : (x == y) = false.
    by case : (x =P y) => // ?;subst;elim Hneq; exact: Ordered.eq_refl.
  Qed.

  Lemma removeP_eq {T} (m: t T) x: (remove m x).[x] = None.
  Proof. by rewrite removeP eq_refl. Qed.

  Lemma removeP_neq {T} (m: t T) x y: x != y -> (remove m x).[y] = m.[y].
  Proof. by rewrite removeP => /negPf ->. Qed.

  Lemma mapP {T1 T2} (f:T1 -> T2) (m:t T1) (x:K.t):
    (map f m).[x] = omap f m.[x].
  Proof. by rewrite /map /get Facts.map_o. Qed.

  Lemma mapiP {T1 T2} (f:K.t -> T1 -> T2) (m:t T1) (x:K.t):
    (mapi f m).[x] = omap (f x) m.[x].
  Proof.
    by rewrite /mapi /get Facts.mapi_o // => ??? /cmp_eq ->.
  Qed.

  Lemma filter_mapP {T1 T2} (f:K.t -> T1 -> option T2) (m:t T1) (x:K.t):
    (filter_map f m).[x] = obind (f x) m.[x].
  Proof.
    rewrite /filter_map /= /get /Map.find Map.Raw.Proofs.map_option_find.
    + by case Map.Raw.find.
    + by move=> ??? h; rewrite (cmp_eq h).
    by  apply Map.is_bst.
  Qed.

  Lemma map2P {T1 T2 T3} (f:K.t -> option T1 -> option T2 -> option T3)
    (m1:t T1) (m2:t T2) (x:K.t):
    f x None None = None ->
    (map2 f m1 m2).[x] = f x m1.[x] m2.[x].
  Proof.
    move=> Hnone.
    case: (boolP (Map.mem x m1 || Map.mem x m2)).
    + move=> /orP;rewrite /is_true -!Facts.mem_in_iff /Map.In !Map.Raw.Proofs.In_alt.
      apply Map.Raw.Proofs.map2_opt_1 => //=.
      + by apply Map.Raw.Proofs.map_option_bst=> ??? /cmp_eq ->.
      + by apply Map.Raw.Proofs.map_option_bst=> ??? /cmp_eq ->.
      + by move=> ???;apply Map.Raw.Proofs.map_option_find=>// ??? /cmp_eq ->.
      + by move=> ???;apply Map.Raw.Proofs.map_option_find=>// ??? /cmp_eq ->.
      + by move=> ???? /cmp_eq ->.
      + by apply Map.is_bst.
      by apply Map.is_bst.
    rewrite !Facts.mem_find_b /get;case H1: Map.find;case H2: Map.find=>//= _.
    case H3:Map.find=> //; have : Map.In x (map2 f m1 m2).
    + by rewrite Facts.in_find_iff H3.
    rewrite /map2 /Map.In /= Map.Raw.Proofs.In_alt=> /(@Map.Raw.Proofs.map2_opt_2 _ _ _ f).
    rewrite -!Map.Raw.Proofs.In_alt -/(Map.In x m1) -/(Map.In x m2) !Facts.in_find_iff.
    rewrite H1 H2 => -[] //.
    + by apply Map.Raw.Proofs.map_option_bst=> ??? /cmp_eq ->.
    + by apply Map.Raw.Proofs.map_option_bst=> ??? /cmp_eq ->.
    + by move=> ???;apply Map.Raw.Proofs.map_option_find=>// ??? /cmp_eq ->.
    + by move=> ???;apply Map.Raw.Proofs.map_option_find=>// ??? /cmp_eq ->.
    + by apply Map.is_bst.
    by apply Map.is_bst.
  Qed.

  Lemma elementsP : forall {T:eqType} (kv:K.t * T) m,
    reflect (m.[kv.1] = Some kv.2) (kv \in elements m).
  Proof.
    rewrite /elements;move=> T kv m.
    assert(InA (Map.eq_key_elt (elt:=T)) (kv.1, kv.2) (Map.elements m) <->
           (kv \in Map.elements m)) as step.
    + elim: (Map.elements m) => [|x xs Hrec].
      + by rewrite in_nil; split => // /InAE.
      rewrite in_cons; split=> [| /orP [/eqP|]].
      + case/InAE.
        * rewrite /Map.eq_key_elt /Map.Raw.Proofs.PX.eqke /= => [].
          case: kv x {Hrec} => k v [xk xv] /= [] /= /(@cmp_eq _ _ K.cmpO) -> ->.
          by rewrite eq_refl.
        by move/Hrec ->; exact: orbT.
      + move => ->; constructor;case x;reflexivity.
      by move => H; apply /InA_cons_tl /Hrec.
    revert step.
    case: (boolP (kv \in Map.elements m)) => Hin [Hf Ht];constructor.
    + move: (Ht (erefl _)).
      by move=> /(Facts.elements_mapsto_iff m kv.1 kv.2) /Facts.find_mapsto_iff.
    by move=>  /Facts.find_mapsto_iff /(Facts.elements_mapsto_iff m kv.1 kv.2) /Hf.
  Qed.

  Lemma elementsIn : forall T (kv:K.t * T) m,
     List.In kv (elements m) <-> m.[kv.1] = Some kv.2.
  Proof.
    move=> T kv m;rewrite /get -Facts.find_mapsto_iff Facts.elements_mapsto_iff InA_alt.
    split => [hin | [kv' [heq hin]]].
    + exists kv;split => //;case: (kv) => ??; split => //=.
      apply cmp_refl.
    have -> //: kv = kv'.
    move=> {hin};case: kv kv' heq => k v [k' v'] [/= h ->].
    by have -> := cmp_eq h.
  Qed.

  Lemma elementsU T (m:t T): uniq [seq x.1 | x <- (elements m)].
  Proof.
    rewrite /elements; elim: (Map.elements m) (Map.elements_3w m) => [|p ps Hrec] //=.
    case/NoDupAE => Hp Hps.
    rewrite andbC Hrec //= {Hrec Hps}.
    apply /negP=> H; apply: Hp.
    elim: ps H => [|p' ps Hrec] //=;rewrite in_cons=> /orP [/eqP | ] H.
    + apply InA_cons_hd.
      by rewrite /Map.eq_key /Map.Raw.Proofs.PX.eqk H; apply cmp_refl.
    by apply /InA_cons_tl/Hrec.
  Qed.

  Lemma foldP : forall {T A} (f:K.t -> T -> A -> A) m a,
    fold f m a = foldl (fun a (kv:K.t * T) => f kv.1 kv.2 a) a (elements m).
  Proof.
    move=> T A f m a;rewrite /fold Map.fold_1 /elements.
    by elim: Map.elements a=> //=.
  Qed.

  Lemma bstE {T} (m: Map.Raw.tree T) :
    Map.Raw.bst m ->
    match m with
    | Map.Raw.Leaf => True
    | Map.Raw.Node L k _ R _ =>
        [/\ Map.Raw.bst L, Map.Raw.bst R, Map.Raw.lt_tree k L & Map.Raw.gt_tree k R ]
    end.
  Proof. by case. Qed.


  Lemma allP {T} (f: K.t -> T -> bool) (m: t T) :
    all f m <-> (forall k t, get m k = Some t -> f k t).
  Proof.
    rewrite /all/get/Map.find; case: m => /=.
    elim => //= L hL k v R hR s /bstE[] ?? H6 H7; split.
    - case/andP => /andP[] fkv {}/hL hL {}/hR hR k' v'.
      case: Ordered.compare => k'k; cycle 2.
      + exact: hR.
      + exact: hL.
      by case => <-; rewrite (cmp_eq k'k).
    move => h.
    apply/andP; split; first (apply/andP; split).
    - have := h k v.
      have [? ->] := Map.Raw.Proofs.MX.elim_compare_eq (Map.E.eq_refl k).
      by move => /(_ erefl) -> /=.
    - rewrite (hL _) // => k' v' k'v'; apply: h.
      have := Map.Raw.Proofs.MX.elim_compare_lt (H6 k' (Map.Raw.Proofs.find_in _)).
      by rewrite k'v' => - [] // ? ->.
    rewrite (hR _) // => k' v' k'v'; apply: h.
    have := Map.Raw.Proofs.MX.elim_compare_gt (H7 k' (Map.Raw.Proofs.find_in _)).
    by rewrite k'v' => - [] // ? ->.
  Qed.

  Lemma hasP {T} (f: K.t -> T -> bool) (m: t T) :
    has f m <-> (exists k t, get m k = Some t /\ f k t).
  Proof.
    rewrite /has/get/Map.find; case: m => /=.
    elim => /=.
    + by move=> _; split => // -[] ? [] ? [].
    move=> L hL k v R hR s /bstE[] ?? H6 H7; split.
    + move=> /orP [/orP [] | ].
      + move=> ?; exists k, v.
        by have [? ->] := Map.Raw.Proofs.MX.elim_compare_eq (Map.E.eq_refl k).
      + move=> /hL [] // k' [t] [] h1 h2; exists k', t.
        have := Map.Raw.Proofs.MX.elim_compare_lt (H6 k' (Map.Raw.Proofs.find_in _)).
        by rewrite h1 => -[] // ? ->.
      move=> /hR [] // k' [t] [] h1 h2; exists k', t.
      have := Map.Raw.Proofs.MX.elim_compare_gt (H7 k' (Map.Raw.Proofs.find_in _)).
      by rewrite h1 => -[] // ? ->.
    move => [k'] [t] [].
    case: Ordered.compare => k'k; cycle 2. 
    + by move=> hs hf; apply/orP; right; rewrite hR; eauto.
    + by move=> hs hf; apply/orP; left; apply/orP; right; rewrite hL; eauto.
    by rewrite (cmp_eq k'k) => -[<-] ->.
  Qed.

  Lemma incl_defP {T1 T2} (f:K.t -> T1 -> bool) (f2:K.t -> T1 -> T2 -> bool) (m1: t T1) (m2: t T2) :
     incl_def f f2 m1 m2 <->
     (forall k, 
       match get m1 k, get m2 k with
       | None, _          => true
       | Some t1, None     => f k t1
       | Some t1, Some t2 => f2 k t1 t2
       end).
  Proof.
    rewrite /incl_def/get/Map.find; case: m2 => /=; case: m1 => /=.
    elim => //= L hL k v R hR s /bstE[] ?? H6 H7  t2 hbst2.
    have := Map.Raw.Proofs.split_bst k hbst2.
    case hsplit: Map.Raw.split => [t2l oe2 t2r] /= [] hbst2l hbst2r.
    split.
    - move=> /and3P [] hoe2 {}/hL hL {}/hR hR k'.
      rewrite (Map.Raw.Proofs.split_find k k' hbst2) hsplit /=.
      case: Ordered.compare => k'k.
      + exact: hL.
      + by rewrite (cmp_eq k'k).
      + exact: hR.
    move=> h.
    apply/and3P; split.
    - have := h k.
      rewrite (Map.Raw.Proofs.split_find k k hbst2) hsplit /=.
      by have [? ->] := Map.Raw.Proofs.MX.elim_compare_eq (Map.E.eq_refl k).
    - apply hL => // k'.
      case heq: Map.Raw.find => //.
      have := h k'.
      rewrite (Map.Raw.Proofs.split_find k k' hbst2) hsplit /= heq.
      have := Map.Raw.Proofs.MX.elim_compare_lt (H6 k' (Map.Raw.Proofs.find_in _)).
      by rewrite heq => -[] // _ ->.
    apply hR => // k'.
    case heq: Map.Raw.find => //.
    have := h k'.
    rewrite (Map.Raw.Proofs.split_find k k' hbst2) hsplit /= heq.
    have := Map.Raw.Proofs.MX.elim_compare_gt (H7 k' (Map.Raw.Proofs.find_in _)).
    by rewrite heq => -[] // _ ->.
  Qed.

  Lemma inclP {T1 T2} (f:K.t -> T1 -> T2 -> bool) (m1: t T1) (m2: t T2) :
     incl f m1 m2 <->
     (forall k,
       match get m1 k, get m2 k with
       | None, _          => true
       | Some _, None     => false
       | Some t1, Some t2 => f k t1 t2
       end).
  Proof. by apply incl_defP. Qed.

  Lemma in_codomP : forall {T:eqType} (m:t T) v,
    in_codom v m <-> exists k, m.[k] = Some v.
  Proof.
    rewrite /in_codom => T m v; rewrite hasP; split.
    + by move=> [k [t [H1 /eqP ->]]]; exists k.
    by move=> [k H];exists k, v.
  Qed.

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

  Module Map := Mmake K.

  Definition t (P:K.t -> Type) := Map.t (boxed P).

  Definition empty P : t P := Map.empty (boxed P).

  Definition get {P} (m:t P) (k:K.t) :=
    from_boxed k (Map.get m k).

  Definition set {P} (m:t P) (k:K.t) (v:P k) := Map.set m k (Box v).

  Definition map {P1 P2} (f:forall k:K.t, P1 k -> P2 k) (m:t P1) : t P2 :=
    Map.map (fun b => {|box_t := b.(box_t); box_v := @f b.(box_t) b.(box_v) |}) m.

  Definition map2 {P1 P2 P3}
      (f:forall k:K.t, option (P1 k) -> option (P2 k) -> option (P3 k))
      (m1:t P1) (m2:t P2): t P3 :=
    Map.map2 (fun k o1 o2 =>
        omap (@Box P3 k) (f k (from_boxed k o1) (from_boxed k o2))) m1 m2.

  Notation "m .[ s ]" := (get m s).
  Notation "x .[ k <- v ]" := (@set _ x k v).

  Lemma get0 P x : (empty P).[x] = None.
  Proof. by rewrite /empty /get Map.get0. Qed.

  Lemma eq_dec_refl x: E.eq_dec x x = left (erefl x).
  Proof.
    case: (E.eq_dec x x) (@E.eq_dec_r x x) => [eq _ | b /(_ b (erefl _)) /eqP //].
    by rewrite eq_axiomK.
  Qed.

  Lemma eq_dec_irefl x y: x <> y -> E.eq_dec x y = right I.
  Proof.
    case: (E.eq_dec x y) (@E.eq_dec_r x y) => [| []] //.
  Qed.

  Lemma setP {P} (m: t P) x y (v:P x) :
    m.[x <- v].[y] =
    match E.eq_dec x y with
    | left Heq => Some (eq_rect x P v y Heq)
    | _        => m.[y]
    end.
  Proof.
    rewrite /set /get /from_boxed /=.
    rewrite Map.setP;case : (x =P y) => [<- | neq];first by rewrite eq_dec_refl.
    by rewrite eq_dec_irefl.
  Qed.

  Lemma setP_eq {P} (m: t P) x (v:P x) : m.[x <- v].[x] = Some v.
  Proof. by rewrite setP eq_dec_refl. Qed.

  Lemma setP_neq {P} (m: t P) x y (v:P x) : x != y -> m.[x <- v].[y] = m.[y].
  Proof. by move=> /eqP ?;rewrite setP eq_dec_irefl. Qed.

  Lemma mapP {P1 P2} (f:forall k:K.t, P1 k -> P2 k) (m:t P1) (x:K.t):
    (map f m).[x] = omap (f x) m.[x].
  Proof.
    rewrite /map /get Map.mapP;case: Map.get => // -[z pz] /=.
    case E.eq_dec=> e //=; move:(e);rewrite -e=> {e} e.
    by rewrite eq_axiomK.
  Qed.

  Lemma map2P {P1 P2 P3} (f:forall k:K.t, option (P1 k) -> option (P2 k) -> option (P3 k))
    (m1:t P1)(m2:t P2) (x:K.t):
    f x None None = None ->
    (map2 f m1 m2).[x] = (f x) m1.[x] m2.[x].
  Proof.
    move=> Hf;rewrite /get /map2 Map.map2P /=;last by rewrite Hf.
    by case: (f x)=> //= ?;rewrite eq_dec_refl.
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
 ** Map of Z
 * -------------------------------------------------------------------------- *)
From mathcomp Require Import word_ssrZ.
Module CmpZ.

  Definition t := [eqType of Z].

  Definition cmp : t -> t -> comparison := Z.compare.

  Lemma cmpO : Cmp cmp.
  Proof. apply ZO. Qed.

End CmpZ.

Module Mz := Mmake CmpZ.

(* --------------------------------------------------------------------------
 ** Finite Set
 * -------------------------------------------------------------------------- *)

Require Import MSets.

Module MkMOrdT (T:CmpType) <: Orders.OrderedType.
#[global]
  Existing Instance T.cmpO | 1.

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

Module PosSet.
  Module Sp  := Smake CmpPos.
  Module SpP := MSetEqProperties.EqProperties Sp.
  Module SpD := MSetDecide.WDecide Sp.
End PosSet.
