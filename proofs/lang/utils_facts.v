From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import fintype finfun.
From Coq.Unicode Require Import Utf8.
From Coq Require Import ZArith Zwf Setoid Morphisms CMorphisms CRelationClasses String.
Require Import xseq oseq.
From mathcomp Require Import word_ssrZ.
Require Import utils.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)
Local Open Scope Z_scope.

Lemma is_okP (E A:Type) (r:result E A) : reflect (exists (a:A), r = Ok E a) (is_ok r).
Proof.
  case: r => /=; constructor; first by eauto.
  by move=> [].
Qed.

Open Scope result_scope.

Lemma bindA eT aT bT cT (f : aT -> result eT bT) (g: bT -> result eT cT) m:
  m >>= f >>= g = m >>= (fun a => f a >>= g).
Proof. case:m => //=. Qed.

Lemma bind_eq eT aT rT (f1 f2 : aT -> result eT rT) m1 m2 :
   m1 = m2 -> f1 =1 f2 -> m1 >>= f1 = m2 >>= f2.
Proof. move=> <- Hf; case m1 => //=. Qed.

Lemma map_errP eT1 eT2 aT (f : eT1 -> eT2) (r : result eT1 aT) x :
  Result.map_err f r = ok x ->
  r = ok x.
Proof. by case: r => //= ? [->]. Qed.

Arguments map_errP {_ _ _ _ _ _}.

Lemma bindW {T U} (v : exec T) (f : T -> exec U) r :
  v >>= f = ok r -> exists2 a, v = ok a & f a = ok r.
Proof. by case E: v => [a|//] /= <-; exists a. Qed.

Lemma Let_Let {eT A B C} (a:result eT A) (b:A -> result eT B) (c: B -> result eT C) :
  ((a >>= b) >>= c) = a >>= (fun a => b a >>= c).
Proof. by case: a. Qed.

Lemma LetK {eT T} (r : result eT T) : Let x := r in ok x = r.
Proof. by case: r. Qed.

Lemma mapM_cons aT eT bT x xs y ys (f : aT -> result eT bT):
  f x = ok y /\ mapM f xs = ok ys
  <-> mapM f (x :: xs) = ok (y :: ys).
Proof.
  split.
  by move => [] /= -> ->.
  by simpl; t_xrbindP => y0 -> h0 -> -> ->.
Qed.

Lemma map_Forall2 aT bT (f : aT -> bT) m :
  List.Forall2 (fun a b => f a = b) m (map f m).
Proof. by elim: m => //= a m ih; constructor. Qed.

Lemma mapM_ext eT aT bT (f1 f2: aT → result eT bT) (m: seq aT) :
  (∀ a, List.In a m → f1 a = f2 a) →
  mapM f1 m = mapM f2 m.
Proof.
  elim: m => // a m ih ext /=.
  rewrite (ext a); last by left.
  case: (f2 _) => //= b; rewrite ih //.
  by move => ? h; apply: ext; right.
Qed.

Local Close Scope Z_scope.

Lemma mapM_nth eT aT bT f xs ys d d' n :
  @mapM eT aT bT f xs = ok ys ->
  n < size xs ->
  f (nth d xs n) = ok (nth d' ys n).
Proof.
elim: xs ys n.
- by move => ys n [<-].
move => x xs ih ys n /=; case h: (f _) => [ y | ] //=.
case: (mapM f xs) ih => //= ys' /(_ _ _ erefl) ih [] <- {ys}.
by case: n ih => // n /(_ n).
Qed.

Local Open Scope Z_scope.

Lemma mapMP {eT} {aT bT: eqType} (f: aT -> result eT bT) (s: seq aT) (s': seq bT) y:
  mapM f s = ok s' ->
  reflect (exists2 x, x \in s & f x = ok y) (y \in s').
Proof.
elim: s s' => /= [s' [] <-|x s IHs s']; first by right; case.
apply: rbindP=> y0 Hy0.
apply: rbindP=> ys Hys []<-.
have IHs' := (IHs _ Hys).
rewrite /= in_cons eq_sym; case Hxy: (y0 == y).
  by left; exists x; [rewrite mem_head | rewrite -(eqP Hxy)].
apply: (iffP IHs')=> [[x' Hx' <-]|[x' Hx' Dy]].
  by exists x'; first by apply: predU1r.
rewrite -Dy.
case/predU1P: Hx'=> [Hx|].
+ exfalso.
  move: Hxy=> /negP Hxy.
  apply: Hxy.
  rewrite Hx Hy0 in Dy.
  by move: Dy=> [] ->.
+ by exists x'.
Qed.

Lemma mapM_In {aT bT eT} (f: aT -> result eT bT) (s: seq aT) (s': seq bT) x:
  mapM f s = ok s' ->
  List.In x s -> exists y, List.In y s' /\ f x = ok y.
Proof.
elim: s s'=> // a l /= IH s'.
apply: rbindP=> y Hy.
apply: rbindP=> ys Hys []<-.
case.
+ by move=> <-; exists y; split=> //; left.
+ move=> Hl; move: (IH _ Hys Hl)=> [y0 [Hy0 Hy0']].
  by exists y0; split=> //; right.
Qed.

Lemma mapM_map {aT bT cT eT} (f: aT → bT) (g: bT → result eT cT) (xs: seq aT) :
  mapM g (map f xs) = mapM (g \o f) xs.
Proof. by elim: xs => // x xs ih /=; case: (g (f x)) => // y /=; rewrite ih. Qed.

Lemma mapM_cat  {eT aT bT} (f: aT → result eT bT) (s1 s2: seq aT) :
  mapM f (s1 ++ s2) = Let r1 := mapM f s1 in Let r2 := mapM f s2 in ok (r1 ++ r2).
Proof.
  elim: s1 s2; first by move => s /=; case (mapM f s).
  move => a s1 ih s2 /=.
  case: (f _) => // b; rewrite /= ih{ih}.
  case: (mapM f s1) => // bs /=.
  by case: (mapM f s2).
Qed.

Corollary mapM_rcons  {eT aT bT} (f: aT → result eT bT) (s: seq aT) (a: aT) :
  mapM f (rcons s a) = Let r1 := mapM f s in Let r2 := f a in ok (rcons r1 r2).
Proof. by rewrite -cats1 mapM_cat /=; case: (f a) => // b; case: (mapM _ _) => // bs; rewrite /= cats1. Qed.

Lemma mapM_Forall2 {eT aT bT} (f: aT → result eT bT) (s: seq aT) (s': seq bT) :
  mapM f s = ok s' →
  List.Forall2 (λ a b, f a = ok b) s s'.
Proof.
  elim: s s'.
  - by move => _ [] <-; constructor.
  move => a s ih s'' /=; t_xrbindP => b ok_b s' /ih{}ih <-{s''}.
  by constructor.
Qed.

Lemma mapM_factorization {aT bT cT eT fT} (f: aT → result fT bT) (g: aT → result eT cT) (h: bT → result eT cT) xs ys:
  (∀ a b, f a = ok b → g a = h b) →
  mapM f xs = ok ys →
  mapM g xs = mapM h ys.
Proof.
  move => E.
  elim: xs ys; first by case.
  by move => x xs ih ys' /=; t_xrbindP => y /E -> ys /ih -> <-.
Qed.

Lemma mapM_take eT aT bT (f: aT → result eT bT) (xs: seq aT) ys n :
  mapM f xs = ok ys →
  mapM f (take n xs) = ok (take n ys).
Proof.
  elim: xs ys n => [ | x xs hrec] ys n /=; first by move => /ok_inj<-.
  t_xrbindP => y hy ys' /hrec h ?; subst ys; case: n; first by rewrite take0.
  by move => n; rewrite /= (h n) /= hy.
Qed.

Lemma mapM_ok {eT} {A B:Type} (f: A -> B) (l:list A) :
  mapM (eT:=eT) (fun x => ok (f x)) l = ok (map f l).
Proof. by elim l => //= ?? ->. Qed.

Lemma size_fmapM2 {eT aT bT cT dT} e
  (f : aT -> bT -> cT -> result eT (aT * dT)) a lb lc a2 ld :
  fmapM2 e f a lb lc = ok (a2, ld) ->
  size lb = size lc /\ size lb = size ld.
Proof.
  elim: lb lc a a2 ld.
  + by move=> [|//] _ _ _ [_ <-].
  move=> b lb ih [//|c lc] a /=.
  t_xrbindP=> _ _ _ _ [_ ld] /ih{}ih _ <- /=.
  by Lia.lia.
Qed.

Lemma fmapM2_split {eT aT bT cT dT} e
  (f : aT -> bT -> cT -> result eT (aT * dT)) a lb lc a2 ld i :
  fmapM2 e f a lb lc = ok (a2, ld) ->
  exists a1,
    fmapM2 e f a (take i lb) (take i lc) = ok (a1, take i ld) /\
    fmapM2 e f a1 (drop i lb) (drop i lc) = ok (a2, drop i ld).
Proof.
  elim: lb lc a a2 ld i => [|b lb ih] [|c lc] //= a a2.
  + move=> _ _ [<- <-] /=.
    by eexists.
  t_xrbindP=> _ i [a1 d] /= h1 [{}a2 ld] h2 <- <-.
  case: i => [|i] /=.
  + eexists; split; first by reflexivity.
    by rewrite h1 /= h2.
  rewrite h1 /=.
  have [a1' [-> /= h2']] := ih _ _ _ _ i h2.
  by eexists; split; first by reflexivity.
Qed.

Lemma fmapM2_nth {eT aT bT cT dT} e
  (f : aT -> bT -> cT -> result eT (aT * dT)) a lb lc a2 ld i b c d :
  fmapM2 e f a lb lc = ok (a2, ld) ->
  (i < size lb)%nat ->
  exists a1 a1',
    fmapM2 e f a (take i lb) (take i lc) = ok (a1, take i ld) /\
    f a1 (nth b lb i) (nth c lc i) = ok (a1', nth d ld i) /\
    fmapM2 e f a1' (drop i.+1 lb) (drop i.+1 lc) = ok (a2, drop i.+1 ld).
Proof.
  move=> hmap hi.
  have [a1 [hmap1 hmap2]] := fmapM2_split i hmap.
  have {hmap} [hsize1 hsize2] := size_fmapM2 hmap.
  move: hmap2.
  rewrite (drop_nth b hi).
  rewrite (drop_nth c); last by rewrite -hsize1.
  rewrite (drop_nth d) /=; last by rewrite -hsize2.
  t_xrbindP=> -[a1' d'] hf [a2' ld'] /= hmap2 ???; subst d' a2' ld'.
  by exists a1, a1'.
Qed.

Lemma Forall2_size A B (R : A -> B -> Prop) la lb :
  List.Forall2 R la lb -> size la = size lb.
Proof. by elim {la lb} => // a b la lb _ _ /= ->. Qed.

Lemma Forall3_size A B C (R : A -> B -> C -> Prop) l1 l2 l3 :
  Forall3 R l1 l2 l3 ->
  size l1 = size l2 /\ size l1 = size l3.
Proof. by elim {l1 l2 l3} => // a b c l1 l2 l3 _ _ /= [<- <-]. Qed.

Lemma Forall2_nth A B (R : A -> B -> Prop) la lb :
  List.Forall2 R la lb ->
  forall a b i, (i < size la)%nat ->
  R (nth a la i) (nth b lb i).
Proof.
  elim {la lb} => // a b la lb h _ ih a0 b0 [//|i].
  by apply ih.
Qed.

Lemma nth_Forall2 A B (R : A -> B -> Prop) la lb a b :
  size la = size lb ->
  (forall i : nat, (i < size la)%nat -> R (nth a la i) (nth b lb i)) ->
  List.Forall2 R la lb.
Proof.
  elim: la lb => [|a' la ih] [|b' lb] //= [] /ih{}ih hnth.
  constructor.
  + by apply (hnth 0%nat).
  by apply ih; move=> i; apply (hnth i.+1).
Qed.

Arguments nth_Forall2 [A B R la lb].

Lemma Forall2_impl A B (R1 R2 : A -> B -> Prop) :
  (forall a b, R1 a b -> R2 a b) ->
  forall la lb,
  List.Forall2 R1 la lb ->
  List.Forall2 R2 la lb.
Proof. by move=> himpl l1 l2; elim; eauto. Qed.

Lemma Forall2_flip A B (R : A -> B -> Prop) la lb :
  List.Forall2 R la lb ->
  List.Forall2 (fun x y => R y x) lb la.
Proof. by elim {la lb} => // a b la lb h _ ih; constructor. Qed.

Lemma Forall2_take A B (R : A -> B -> Prop) la lb :
  List.Forall2 R la lb ->
  forall n,
  List.Forall2 R (take n la) (take n lb).
Proof.
  elim {la lb} => //= a b la lb h _ ih n.
  case: n => [|n] //=.
  by constructor.
Qed.

Lemma Forall2_drop A B (R : A -> B -> Prop) la lb :
  List.Forall2 R la lb ->
  forall n,
  List.Forall2 R (drop n la) (drop n lb).
Proof.
  elim {la lb} => //= a b la lb h ? ih n.
  case: n => [|n] //=.
  by constructor.
Qed.

Lemma Forall3_nth A B C (R : A -> B -> C -> Prop) la lb lc :
  Forall3 R la lb lc ->
  forall a b c i,
  (i < size la)%nat ->
  R (nth a la i) (nth b lb i) (nth c lc i).
Proof.
  elim {la lb lc} => // a b c la lb lc hr _ ih a0 b0 c0 [//|i].
  by apply ih.
Qed.

Lemma nth_Forall3 A B C (R : A -> B -> C -> Prop) la lb lc a b c:
  size la = size lb -> size la = size lc ->
  (forall i, (i < size la)%nat -> R (nth a la i) (nth b lb i) (nth c lc i)) ->
  Forall3 R la lb lc.
Proof.
  elim: la lb lc.
  + by move=> [|//] [|//] _ _ _; constructor.
  move=> a0 l1 ih [//|b0 l2] [//|c0 l3] [hsize1] [hsize2] h.
  constructor.
  + by apply (h 0%nat).
  apply ih => //.
  by move=> i; apply (h i.+1).
Qed.

Arguments nth_Forall3 [A B C R la lb lc].

Lemma Forall3_impl A B C (R1 R2 : A -> B -> C -> Prop) :
  (forall a b c, R1 a b c -> R2 a b c) ->
  forall la lb lc,
  Forall3 R1 la lb lc ->
  Forall3 R2 la lb lc.
Proof. by move=> himpl l1 l2 l3; elim; eauto using Forall3. Qed.

Lemma Forall3_impl_in A B C (R1 R2 : A -> B -> C -> Prop) la lb lc :
  (forall a b c, List.In a la -> List.In b lb -> List.In c lc -> R1 a b c -> R2 a b c) ->
  Forall3 R1 la lb lc ->
  Forall3 R2 la lb lc.
Proof.
  move=> himpl hforall.
  elim: {la lb lc} hforall himpl.
  + by constructor.
  move=> a b c la lb lc h _ ih himpl.
  constructor.
  + by apply himpl; [left; reflexivity..|].
  apply ih.
  by move=> ???????; apply himpl; [right..|].
Qed.

Lemma List_Forall2_inv_r A B (R: A → B → Prop) m n :
  List.Forall2 R m n →
  match n with
  | [::] => m = [::]
  | b :: n' => ∃ a m', m = a :: m' ∧ R a b ∧ List.Forall2 R m' n'
  end.
Proof. case; eauto. Qed.

Lemma List_Forall2_inv A B (R: A → B → Prop) m n :
  List.Forall2 R m n →
  if m is a :: m' then if n is b :: n' then R a b ∧ List.Forall2 R m' n' else False else if n is [::] then True else False.
Proof. case; auto. Qed.

Lemma List_Forall3_inv A B C (R : A -> B -> C -> Prop) l1 l2 l3 :
  Forall3 R l1 l2 l3 ->
  match l1, l2, l3 with
  | [::], [::], [::] => True
  | a :: l1, b :: l2, c :: l3 => R a b c /\ Forall3 R l1 l2 l3
  | _, _, _ => False
  end.
Proof. by case. Qed.

Lemma Forall2_trans A B C lb (R1:A->B->Prop) (R2:B->C->Prop)
                    la lc (R3:A->C->Prop) :
  (forall b a c, R1 a b -> R2 b c -> R3 a c) ->
  List.Forall2 R1 la lb ->
  List.Forall2 R2 lb lc ->
  List.Forall2 R3 la lc.
Proof.
  move=> himpl hfor1.
  elim: {la lb} hfor1 lc => [ | a b la lb hr1 _ hrec] + /List_Forall2_inv_l.
  + by move=> _ ->.
  by move=> _ [c [lc [-> [hr2 hfor2]]]]; constructor; eauto.
Qed.

Section Subseq.

  Context (T : eqType).
  Context (p : T -> bool).

  Lemma subseq_has s1 s2 : subseq s1 s2 -> has p s1 -> has p s2.
  Proof.
    move=> /mem_subseq hsub /hasP [x /hsub hin hp].
    apply /hasP.
    by exists x.
  Qed.

  Lemma subseq_all s1 s2 : subseq s1 s2 -> all p s2 -> all p s1.
  Proof.
    move=> /mem_subseq hsub /allP hall.
    by apply /allP => x /hsub /hall.
  Qed.

End Subseq.

Section DifferentTypes.
  Context (S T : Type).
  Context (p : S -> T -> bool).

Section All2.

  Lemma all2P l1 l2 : reflect (List.Forall2 p l1 l2) (all2 p l1 l2).
  Proof.
    elim: l1 l2 => [ | a l1 hrec] [ | b l2] /=;try constructor.
    + by constructor.
    + by move/List_Forall2_inv_l.
    + by move/List_Forall2_inv_r.
    apply: equivP;first apply /andP.
    split => [[]h1 /hrec h2 |];first by constructor.
    by case/List_Forall2_inv_l => b' [n] [] [-> ->] [->] /hrec.
  Qed.

End All2.

End DifferentTypes.

Section FIND_MAP.

Lemma find_map_correct {A: eqType} {B: Type} {f: A → option B} {l b} :
  find_map f l = Some b -> exists2 a, a \in l & f a = Some b.
Proof.
  elim: l => //= a l ih.
  case heq: (f a) => [b'|].
  + by move=> [<-]; exists a => //; rewrite mem_head.
  move=> /ih [a' h1 h2]; exists a'=> //.
  by rewrite in_cons; apply /orP; right.
Qed.

End FIND_MAP.

Lemma isSome_obind (aT bT: Type) (f: aT → option bT) (o: option aT) :
  reflect (exists2 a, o = Some a & isSome (f a)) (isSome (o >>= f)%O).
Proof.
  apply: Bool.iff_reflect; split.
  - by case => a ->.
  by case: o => // a h; exists a.
Qed.

Lemma isSome_omap aT bT (f : aT -> bT) (o : option aT) :
  isSome (Option.map f o) = isSome o.
Proof. by case: o. Qed.

Section CMP.
  Context {T:Type} {cmp:T -> T -> comparison} {C:Cmp cmp}.

  Lemma cmp_lt_trans y x z : cmp_lt x y -> cmp_lt y z -> cmp_lt x z.
  Proof.
    rewrite /cmp_lt /gcmp => /eqP h1 /eqP h2;apply /eqP;apply (@cmp_ctrans _ _ C y).
    by rewrite h1 h2.
  Qed.

  Lemma cmp_lt_le_trans y x z: cmp_lt x y -> cmp_le y z -> cmp_lt x z.
  Proof.
    rewrite /cmp_le /cmp_lt /gcmp (cmp_sym z) => h1 h2.
    have := (@cmp_ctrans _ _ C y x z).
    by case: cmp h1 => // _;case: cmp h2 => //= _;rewrite /ctrans => /(_ _ erefl) ->.
  Qed.

  Lemma cmp_le_lt_trans y x z: cmp_le x y -> cmp_lt y z -> cmp_lt x z.
  Proof.
    rewrite /cmp_le /cmp_lt /gcmp (cmp_sym y) => h1 h2.
    have := (@cmp_ctrans _ _ C y x z).
    by case: cmp h1 => // _;case: cmp h2 => //= _;rewrite /ctrans => /(_ _ erefl) ->.
  Qed.

  Lemma cmp_nle_le x y : ~~ (cmp_le x y) -> cmp_le y x.
  Proof. by rewrite cmp_nle_lt; apply: cmp_lt_le. Qed.

End CMP.

Lemma P_leP (x y:positive) : reflect (x <= y)%Z (x <=? y)%positive.
Proof. apply: (@equivP (Pos.le x y)) => //;rewrite -Pos.leb_le;apply idP. Qed.

Lemma P_ltP (x y:positive) : reflect (x < y)%Z (x <? y)%positive.
Proof. apply: (@equivP (Pos.lt x y)) => //;rewrite -Pos.ltb_lt;apply idP. Qed.

Lemma Pos_leb_trans y x z:
  (x <=? y)%positive -> (y <=? z)%positive -> (x <=? z)%positive.
Proof. move=> /P_leP ? /P_leP ?;apply /P_leP; Lia.lia. Qed.

Lemma Pos_lt_leb_trans y x z:
  (x <? y)%positive -> (y <=? z)%positive -> (x <? z)%positive.
Proof. move=> /P_ltP ? /P_leP ?;apply /P_ltP; Lia.lia. Qed.

Lemma Z_to_nat_le0 z : z <= 0 -> Z.to_nat z = 0%nat.
Proof. by rewrite /Z.to_nat; case: z => //=; rewrite /Z.le. Qed.

Lemma Z_odd_pow_2 n x :
  (0 < n)%Z
  -> Z.odd (2 ^ n * x) = false.
Proof.
  move=> hn.
  rewrite Z.odd_mul.
  by rewrite (Z.odd_pow _ _ hn).
Qed.

Section NAT.
Open Scope nat.

Lemma ZNleP x y :
  reflect (Z.of_nat x <= Z.of_nat y)%Z (x <= y).
Proof.
  case h: (x <= y).
  all: move: h => /leP /Nat2Z.inj_le.
  all: by constructor.
Qed.

Lemma ZNltP x y :
  reflect (Z.of_nat x < Z.of_nat y)%Z (x < y).
Proof.
  case h: (x < y).
  all: move: h => /ZNleP.
  all: rewrite Nat2Z.inj_succ.
  all: move=> /Z.le_succ_l.
  all: by constructor.
Qed.

Lemma lt_nm_n n m :
  (n + m < n) = false.
Proof.
  rewrite -{2}(addn0 n).
  rewrite ltn_add2l.
  exact: ltn0.
Qed.

Lemma sub_nmn n m :
  n + m - n = m.
Proof.
  elim: n => //.
  by rewrite add0n subn0.
Qed.

End NAT.

Lemma ziota_shift i p : ziota i p = map (fun k => i + k)%Z (ziota 0 p).
Proof. by rewrite !ziotaE -map_comp /comp. Qed.

Lemma znthE (A:Type) dfl (l:list A) i :
  (0 <= i)%Z ->
  znth dfl l i = nth dfl l (Z.to_nat i).
Proof.
  case: l; first by rewrite nth_nil.
  case: i => // p a m _.
  elim/Pos.peano_ind: p a m; first by move => ? [].
  move => p /= ih a; rewrite Pos2Nat.inj_succ /=.
  case; first by rewrite nth_nil.
  move => /= b m.
  by case: Pos.succ (Pos.succ_not_1 p) (Pos.pred_succ p) => // _ _ /= ->.
Qed.

Lemma mem_znth (A:eqType) dfl (l:list A) i :
  [&& 0 <=? i & i <? Z.of_nat (size l)]%Z ->
  znth dfl l i \in l.
Proof.
  move=> /andP []/ZleP h0i /ZltP hi.
  by rewrite znthE //; apply/mem_nth/ZNltP; rewrite Z2Nat.id.
Qed.

Lemma znth_index (T : eqType) (x0 x : T) (s : seq T):
  x \in s → znth x0 s (zindex x s) = x.
Proof.
  move=> hin; rewrite /zindex znthE; last by apply Zle_0_nat.
  by rewrite Nat2Z.id nth_index.
Qed.

Lemma neq_sym (T: eqType) (x y: T) :
   (x != y) = (y != x).
Proof. apply/eqP; case: eqP => //; exact: not_eq_sym. Qed.

Lemma nth_not_default T x0 (s:seq T) n x :
  nth x0 s n = x ->
  x0 <> x ->
  (n < size s)%nat.
Proof.
  move=> hnth hneq.
  rewrite ltnNge; apply /negP => hle.
  by rewrite nth_default in hnth.
Qed.

Lemma onth_size (A:Type) (l:list A) n a :
  onth l n = Some a -> (n < size l)%nat.
Proof.
  rewrite onth_nth => h.
  rewrite - (size_map Some).
  by apply (nth_not_default h).
Qed.

Lemma all_behead {A} {p : A -> bool} {xs : seq A} :
  all p xs -> all p (behead xs).
Proof.
  case: xs => // x xs.
  by move=> /andP [] _.
Qed.

Lemma obindP aT bT oa (f : aT -> option bT) a (P : Type) :
  (forall z, oa = Some z -> f z = Some a -> P) ->
  (let%opt a' := oa in f a') = Some a ->
  P.
Proof. case: oa => // a' h h'. exact: (h _ _ h'). Qed.

Lemma oassertP {A b a} {oa : option A} :
  (let%opt _ := oassert b in oa) = Some a ->
  b /\ oa = Some a.
Proof. by case: b. Qed.

Lemma isSomeP {A : Type} {oa : option A} :
  isSome oa ->
  exists a, oa = Some a.
Proof. case: oa; by [|eexists]. Qed.

Lemma cat_inj {T} (a b c d: seq T) :
  size a = size b →
  a ++ c = b ++ d →
  a = b ∧ c = d.
Proof.
  elim: a b c d; first by case.
  by move => x a ih [] // y b c d /= /Nat.succ_inj /ih{}ih [] -> /ih[] -> ->.
Qed.

Lemma map_const_nseq A B (l : list A) (c : B) : map (fun=> c) l = nseq (size l) c.
Proof. by elim: l => // > ? /=; f_equal. Qed.

Lemma is_reflect_some_inv {A B : Type} {P : A -> B} {e a} :
  is_reflect P e (Some a) ->
  e = P a.
Proof. by rewrite -/(if Some a is Some a' then e = P a' else True) => -[]. Qed.
