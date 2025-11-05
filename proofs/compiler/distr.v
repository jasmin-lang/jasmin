From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssralg ssrnum.
From mathcomp Require Import
  bigop
  boolp
  choice
  classical_sets
  constructive_ereal
  distr
  eqtype
  fintype
  finmap
  order
  reals
  realseq
  realsum
  seq
.

Import GRing.Theory Num.Theory Order Order.Theory.

From ITree Require Import ITree ITreeFacts.
From Paco Require Import paco.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

Notation "'let*' p ':=' c1 'in' c2" :=
  (@ITree.bind _ _ _ c1 (fun p => c2))
  (at level 61, p as pattern, c1 at next level, right associativity).

Section ITREE.

Context
  {E : Type -> Type}
  {R R' : Type}
  (RR : R -> R' -> Prop)
  (weakL weakR : bool)
.

Notation eqit := (eqit RR weakL weakR) (only parsing).
Notation eqitF := (eqitF RR weakL weakR id eqit) (only parsing).

Lemma eqitE (t : itree E R) (t' : itree E R') :
  eqit t t' <-> eqitF (observe t) (observe t').
Proof.
split.
- move=> h. punfold h. red in h. apply: eqitF_mono;
    [exact: h | exact: eqit_idclo_mono | done | by move=> ?? -[]].
move=> h. pstep. red. apply: eqitF_mono;
  [exact: h | exact: eqit_idclo_mono | done | by left ].
Qed.

Context
  (P : itree E R -> itree E R' -> Prop)
  (hret :
    forall t t' r r',
      observe t = RetF r ->
      observe t' = RetF r' ->
      RR r r' ->
      P t t')
  (htau :
    forall t t' ot ot',
      observe t = TauF ot ->
      observe t' = TauF ot' ->
      eqit ot ot' ->
      P t t')
  (hvis :
    forall t t' A e k k',
      observe t = VisF e k ->
      observe t' = VisF e k' ->
      (forall v : A, eqit (k v) (k' v)) ->
      P t t')
  (htaul :
    forall t ot t',
      observe t = TauF ot ->
      weakL ->
      eqitF (observe ot) (observe t') ->
      P ot t' ->
      P t t')
  (htaur :
    forall t' t ot',
      observe t' = TauF ot' ->
      weakR ->
      eqitF (observe t) (observe ot') ->
      P t ot' ->
      P t t').

Lemma eqit_ind t t' : eqit t t' -> P t t'.
Proof.
move=> h.
punfold h; red in h.
elim: h {-2}t {-2}t' (erefl (observe t)) (erefl (observe t')) => {t t'}
  [ r1 r2 h t t' ht ht'
  | ot ot' [h|//] t t' ht ht'
  | A e k k' h t t' ht ht'
  | t0 ot hweakL h hind t t' ht ht'
  | t0 ot hweakR h hind t t' ht ht' ].
- exact: hret ht ht' h.
- exact: htau ht ht' h.
- apply: (hvis ht ht') => v; by case: (h v).
- apply: (htaul ht hweakL); last exact: hind.
  apply/eqitE. pstep. red. by rewrite ht'.
apply: (htaur  ht' hweakR); last exact: hind.
apply/eqitE. pstep. red. by rewrite ht.
Qed.

End ITREE.

Section MAIN.

Context {R : realType}.

Section DEFS.

Definition dunif (T : finType) : distr R T := duni (Finite.enum T).

Section CMP.

  Context {T T' : choiceType} (RR : T -> T' -> Prop).

  Definition dle (mu1 mu2 : distr R T) : Prop := forall x, mu1 x <= mu2 x.

  Definition dleX (mu1 : distr R T) (mu2 : distr R T') : Prop :=
    forall (X : pred T) (Y : pred T'),
      (forall x y, RR x y -> X x -> Y y) ->
      \P_[mu1] X <= \P_[mu2] Y.

  Definition deqX (mu1 : distr R T) (mu2 : distr R T') : Prop :=
    forall (X : pred T) (Y : pred T'),
      (forall x y, RR x y -> X x = Y y) ->
      \P_[mu1] X = \P_[mu2] Y.

End CMP.

Lemma deqX_eq T (mu1 mu2 : distr R T) :
  deqX eq mu1 mu2 ->
  mu1 =1 mu2.
Proof. move=> h x; rewrite !pr_pred1; by apply: h => ?? ->. Qed.

Lemma dle_anti {T T'} RR (mu1 : distr R T) (mu2 : distr R T') :
  dleX RR mu1 mu2 ->
  dleX (flip RR) mu2 mu1 ->
  deqX RR mu1 mu2.
Proof.
move=> hle hge X Y hXY.
apply: Order.le_anti; apply/andP; split;
  [apply: hle | apply: hge]; by move=> ?? /hXY ->.
Qed.

Lemma bool_bd (b : bool) : 0 <= (b%:R : R) <= 1.
Proof. case: b; by apply/andP. Qed.

Lemma pr_dnull {T : choiceType} (E : pred T) : \P_[ dnull ] E = 0 :> R.
Proof. apply: psum_eq0 => x. by rewrite dnullE mulr0. Qed.

Lemma has_exp_bd {T} (mu : distr R T) f :
  (forall x, 0 <= f x <= 1) ->
  \E?_[mu] f.
Proof.
move=> h. apply: (eq_summable (S1 := fun x => mu x * f x)).
+ move=> x. exact: mulrC.
exact: summable_mu_wgtd h.
Qed.

Lemma exp_bd {T} (mu : distr R T) f :
  (forall x, 0 <= f x <= 1) ->
  0 <= \E_[mu] f <= 1.
Proof.
move=> h. apply/andP; split.
- rewrite -(exp0 mu). apply: le_exp; [exact: has_exp0 | exact: has_exp_bd|].
  move=> x. by move: (h x) => /andP [-> _].
apply: exp_le_bd => // x. rewrite ler_norml. move: (h x) => /andP [{}h ->].
rewrite andbT. apply: Order.le_trans h. exact: lerN10.
Qed.

Lemma pr_dlet {A B C : choiceType} {f : A -> distr R B} {g : A -> distr R C}
  {RE : pred B -> pred C -> Type} (mu : distr R A) (E : pred B) (E' : pred C) :
  (forall a E E', RE E E' -> \P_[ f a ] E <= \P_[ g a ] E') ->
  RE E E' ->
  \P_[ \dlet_(x <- mu) f x ] E <= \P_[ \dlet_(x <- mu) g x ] E'.
Proof.
move=> h hE. rewrite !pr_exp !__admitted__exp_dlet.
- apply: le_exp.
  + apply: has_exp_bd => x. apply: exp_bd => y. exact: bool_bd.
  + apply: has_exp_bd => x. apply: exp_bd => y. exact: bool_bd.
  + move=> x. have := h x _ _ hE. by rewrite !pr_exp.
- move=> mu'. exact: summable_pr.
move=> mu'. exact: summable_pr.
Qed.

Lemma eq_mu_pr {T} (mu1 mu2 : distr R T) A :
  mu1 =1 mu2 ->
  \P_[mu1] A = \P_[mu2] A.
Proof.
move=> h. rewrite /pr (eq_psum (F2 := fun x => (A x)%:R * mu1 x)) // => x.
by rewrite h.
Qed.

Lemma le_pr_dlim' {T T'} E E' (f : nat -> distr R T) (g : nat -> distr R T') :
  (forall n, exists m, \P_[f n] E <= \P_[g m] E') ->
  (exists m : nat, forall (n : nat) (x : T), f n x <= f m x) ->
  (forall n m : nat, (n <= m)%N -> forall x : T, f n x <= f m x) ->
  (forall n m : nat, (n <= m)%N -> forall x : T', g n x <= g m x) ->
  \P_[dlim f] E <= \P_[dlim g] E'.
Proof.
move => + [xf hleubf] hmonof hmonog.
rewrite /pr => h.
have h12 := dlim_ub _ hmonof (f := f).
have h22 := dlim_ub _ hmonog (f := g).
specialize (h xf) as [xg h].
have h23 := (leub_dlim (f := f)) (f xf) hleubf.
have h32 := h12 xf.
have heqf : (forall x : T, f xf x = (\dlim_(n) f n) x).
+ intros x.
  specialize (h32 x).
  specialize (h23 x).
  by apply: Order.le_anti; apply/andP; split.
move => {h32 h23 hleubf h12 hmonof hmonog}.
rewrite (eq_psum (F2:= (fun x : T => (E x)%:R * f xf x)));
  last by move => x; rewrite heqf.
apply: Order.le_trans.
 + exact: h.
apply le_psum.
+ move => x; apply /andP;split.
  + apply mulr_ge0 => //=.
  apply ler_pM => //=.
exact: summable_pr.
Qed.

Lemma ncvg_sum {T : eqType} [f : nat -> T -> R] [l : T -> R] [J : seq T] :
  (forall x, ncvg (fun n => f n x) (l x)%:E) ->
  ncvg (fun n => \sum_(x <- J) f n x) (\sum_(x <- J) l x)%:E.
Proof.
move=> hcvg; elim: J => //= [|j J ih].
- rewrite big_nil; apply/(@ncvg_eq _ (fun _ => 0))/ncvgC.
  by move=> n /=; rewrite big_nil.
- rewrite big_cons; have := ncvgD (hcvg j) ih; apply/ncvg_eq.
  by move=> n /=; rewrite big_cons.
Qed.

Lemma sum_dlim {T : choiceType} (E : pred T) (f : nat -> distr R T) :
  (forall n m : nat, (n <= m)%N -> forall x : T, f n x <= f m x) ->
  psum (fun x : T => (E x)%:R * (\dlim_(n) f n) x) =
    fine (nlim (fun n => psum (fun x : T => (E x)%:R * f n x))).
Proof.
move=> hmono.
have cvg_f: forall x, exists l, ncvg (fun n => f n x) l%:E.
- move=> x; apply: ncvg_mono_bnd; first by move=> *; apply: hmono.
  apply/asboolP/nboundedP => /=; exists 2%:R => //.
  move=> n; rewrite ger0_norm ?ge0_mu //; apply: (@le_lt_trans _ _ 1%:R).
  - by apply: le1_mu1. - by apply: ltr_nat.
have [l cvgfx]: exists l, forall x, ncvg (fun n => f n x) (l x)%:E.
- have wtn: forall x, exists l, `[< ncvg (fun n => f n x) l%:E >].
  - by move=> x; apply/exists_asboolP/asboolP.
  exists (fun x => xchoose (wtn x)) => x.
  by apply/asboolP/(xchooseP (wtn x)).
have cvgEfx: forall x, ncvg (fun n => (E x)%:R * f n x) ((E x)%:R * l x)%:E.
- by move=> x; apply/ncvgZ.
have ge0_l: forall x, 0 <= l x.
- by move=> x; apply: (ncvg_geC _ (cvgfx x)) => n; apply: ge0_mu.
transitivity (psum (fun x => fine (nlim (fun n => (E x)%:R * f n x)))).
- apply: eq_psum => x /=; rewrite dlimE (nlimE (cvgfx x)) /=.
  by have /(ncvgZ (c := (E x)%:R)) /nlimE -> /= := cvgfx x.
transitivity (psum (fun x => (E x)%:R * l x)); first apply: eq_psum.
- by move=> x /=; have /(ncvgZ (c := (E x)%:R)) /nlimE -> := cvgfx x.
have smb_Efn: forall n, summable (fun x => (E x)%:R * f n x).
- by move=> n; apply: (summable_pr E (f n)).
have mono_psum_Efn: forall m n, (m <= n)%N ->
  psum (fun x => (E x)%:R * f m x) <= psum (fun x => (E x)%:R * f n x).
- move=> m n le_mn; apply/le_psum/smb_Efn => x; rewrite mulr_ge0 //=.
  by apply: ler_pM => //; apply: hmono.
have le1_psum_Efn: forall n, psum (fun x => (E x)%:R * f n x) <= 1.
- by move=> n; apply/le1_pr.
have [lp ncvg_lp]: exists lp, ncvg (fun n => psum (fun x => (E x)%:R * f n x)) lp%:E.
- apply: ncvg_mono_bnd; first by apply: mono_psum_Efn.
  apply/asboolP/nboundedP => /=; exists 2 => // n.
  by rewrite ger0_norm 1?ge0_psum //; apply/(le_lt_trans (y := 1))/ltr1n/le1_psum_Efn.
have le1_lp: lp <= 1.
- by move/ncvg_leC: ncvg_lp; apply; apply/le1_psum_Efn.
have smb_Ef: summable (fun x => (E x)%:R * l x).
- exists 1 => J; rewrite -(big_seq_fsetE _ _ predT (fun x => `|(E x)%:R * l x|)) /=.
  apply: (le_trans (y := \sum_(x <- J) (l x))).
  - apply: ler_sum => /= j _; rewrite ger0_norm 1?mulr_ge0 //.
    by apply: ler_piMl => //; case: (E _).
  have: ncvg (fun n => \sum_(x <- J) (f n x)) (\sum_(x <- J) l x)%:E.
  - by apply: ncvg_sum.
  move/ncvg_leC => /(_ 1); apply => n /=.
  have /gerfin_psum := summable_mu (f n) => /(_ J).
  move/le_trans => /= /(_ _ (le1_mu (f n))); apply/le_trans.
  by rewrite big_seq_fsetE; apply: ler_sum => j _ /=; apply/ler_norm.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: psum_le => J uqJ; have ncvgJ:
    ncvg (fun n => \sum_(j <- J) (E j)%:R * f n j) (\sum_(j <- J) (E j)%:R * (l j))%:E.
  - by apply: (ncvg_sum cvgEfx).
  apply: (le_trans (y := fine (nlim (fun n => \sum_(j <- J) (E j)%:R * f n j)))); last first.
  - rewrite (nlimE ncvgJ) (nlimE ncvg_lp) /=.
    apply: (ncvg_le _ ncvg_lp ncvgJ) => n.
    apply/(le_trans _): (ger_big_psum uqJ (smb_Efn n)).
    by apply/ler_sum => x _; apply/ler_norm.
  rewrite (nlimE ncvgJ) /=; apply: ler_sum => x _.
  by rewrite ger0_norm // mulr_ge0.
- rewrite (nlimE ncvg_lp) /=; apply: (ncvg_leC _ ncvg_lp) => n.
  apply: le_psum => // x; rewrite mulr_ge0 //=.
  apply: ler_pM => //; apply: (ncvg_homo_le _ (cvgfx x)).
  by move=> *; apply: hmono.
Qed.

Lemma ncvg_extract (f : nat -> R) (i : nat -> nat) (l : R) :
  (forall n, (i n < i n.+1)%N) ->
  ncvg f l%:E ->
  ncvg (f \o i) l%:E.
Proof.
move=> imono hcvg; elim/nbh_finW => /= e gt0_e.
case: (hcvg (NFin l gt0_e)) => /= K hK; exists K.
move=> n le_Kn; rewrite inE; apply: hK.
apply: (leq_trans le_Kn); elim: {+}n => [|m ih] //=. (* FIXME: should exist *)
by apply: (@leq_ltn_trans (i m)).
Qed.

Lemma le_dlim (f : nat -> R) (g : nat -> R) :
  (forall n, exists m, f n <= g m) ->
  (exists l, ncvg f l%:E) ->
  (exists l, ncvg g l%:E) ->
  (forall n m : nat, (n <= m)%N -> f n <= f m) ->
  (forall n m : nat, (n <= m)%N -> g n <= g m) ->
  fine (nlim f) <= fine (nlim g).
Proof.
move=> h [cf hcf] [cg hcg] hmonof hmonog.
have ew: forall (n k : nat), exists (e : nat), (f n <= g e) && (k < e)%N.
- move=> n k; case: (h n) => e le_fn_ge.
  exists (maxn k e).+1; apply/andP; split.
  - by apply/(le_trans le_fn_ge)/hmonog/ltnW; rewrite ltnS leq_maxr.
  - by apply: leq_maxl.
pose e (n k : nat) : nat := xchoose (ew n k).
have he: forall (n k : nat), (f n <= g (e n k)) /\ (k < e n k)%N.
- by move=> n k; apply/andP/(xchooseP (ew n k)).
pose i := fix f (n : nat) := e n (if n is k.+1 then f k else 0).
have iE: forall n, i n = e n (if n is k.+1 then i k else 0) by case.
have lei: forall n, (i n < i n.+1)%N.
- by move=> n; rewrite !iE; set j := (X in e n X); case: (he n.+1 (e n j)).
have lt_f_gi: forall n, f n <= g (i n).
- by move=> n; rewrite iE; set j := (X in e n X); case: (he n j).
have ncvg_gi: ncvg (g \o i) cg%:E by apply: ncvg_extract.
have /= := ncvg_le lt_f_gi ncvg_gi hcf.
by rewrite (nlimE hcf) (nlimE hcg).
Qed.

Lemma le_pr_dlim {T T'} E E' (f : nat -> distr R T) (g : nat -> distr R T') :
  (forall n, exists m, \P_[f n] E <= \P_[g m] E') ->
  (forall n m : nat, (n <= m)%N -> forall x : T, f n x <= f m x) ->
  (forall n m : nat, (n <= m)%N -> forall x : T', g n x <= g m x) ->
  \P_[dlim f] E <= \P_[dlim g] E'.
Proof.
have hcvg (Th : choiceType) (Eh : pred Th) (h : nat -> distr R Th):
     (forall n m : nat, (n <= m)%N -> forall x : Th, h n x <= h m x)
  -> exists l, ncvg (fun n => psum (fun x => (Eh x)%:R * h n x)) l%:E.
- move=> mono; apply: ncvg_mono_bnd.
  - move=> m n le_mn; apply/le_psum/summable_pr.
    move=> x; rewrite mulr_ge0 //=.
    by case: (Eh x) => /=; rewrite ?(mul0r, mul1r) // mono.
  - apply/asboolP/nboundedP => /=; exists 2 => //.
    move=> n; rewrite -/(pr _ _) ger0_norm ?ge0_pr //.
    by apply/(le_lt_trans (y := 1))/ltr1n/le1_pr.
move=> h monof monog; rewrite /pr !sum_dlim //.
apply: le_dlim => //; try by apply: hcvg.
- move=> m n le_mn; rewrite -!/(pr _ _) le_mu_pr //.
  by move=> *; apply: monof.
- move=> m n le_mn; rewrite -!/(pr _ _) le_mu_pr //.
  by move=> *; apply: monog.
Qed.

Lemma leX_dlim {T T'} RR (f : nat -> distr R T) (g : nat -> distr R T') :
  (forall n m, (n <= m)%N -> f n <=1 f m) ->
  (forall n m, (n <= m)%N -> g n <=1 g m) ->
  (forall n, exists m, dleX RR (f n) (g m)) ->
  dleX RR (dlim f) (dlim g).
Proof.
move=> hmf hmg h E E' hE; apply: le_pr_dlim => n; move: (h n) => [m {}h].
+ exists m; exact: h.
+ exact: hmf.
exact: hmg.
Qed.

Variant Rnd : Type -> Type :=
| GetRnd : forall {A : finType}, distr R A -> Rnd A.

(* TODO use the fact that \rV_n is a finType to issue only one GetRnd event. *)
Fixpoint unif_seq {T : finType} (n : nat) : itree Rnd (seq T) :=
  if n is n.+1 then
    let* x := trigger (GetRnd (dunif T)) in
    let* xs := unif_seq n in
    Ret (x :: xs)
  else Ret [::].

Section INTERP.

  Context {T : choiceType}.

  Fixpoint dinterp' (t : itree' Rnd T) (n : nat) : distr R T :=
    if n is n.+1 then
      match t with
      | RetF r => dunit r
      | TauF t => dinterp' (observe t) n
      | VisF _ e k =>
          match e in Rnd A return (A -> itree Rnd T) -> distr R T with
          | GetRnd _ mu =>
              fun k0 => \dlet_(t <- mu) (dinterp' (observe (k0 t)) n)
          end k
      end
    else dnull.

  Definition dinterp (t : itree Rnd T) : distr R T :=
    dlim (dinterp' (observe t)).

  Lemma dinterp'_step t n : dle (dinterp' t n) (dinterp' t n.+1).
  Proof.
  elim: n t => [|n hind] t s; first exact: lef_dnull.
  case: t => [//| t | A e k]; first exact: hind.
  case: e k => A' mu k. apply: le_in_dlet => /= bs hbs s'. exact: hind.
  Qed.

  Lemma dinterp'_mono t n m :
    (n <= m)%nat ->
    dle (dinterp' t n) (dinterp' t m).
  Proof.
  move=> h; rewrite -(addnK n m) subDnCA //. elim: (m - n)%nat => [|d hind].
  - by rewrite addn0.
  rewrite addnS => s; exact: Order.le_trans (hind _) (dinterp'_step _ _ _).
  Qed.

End INTERP.

End DEFS.

Section ONE.

Context {T T' : choiceType} (RR : T -> T' -> Prop).

Notation eqit_ind := (eqit_ind (E := Rnd) (R := T) (R' := T')).

Lemma one_way (t : itree Rnd T) (t' : itree Rnd T') :
  eutt RR t t' ->
  forall n, exists m,
    dleX RR (dinterp' (observe t) n) (dinterp' (observe t') m).
Proof.
move=> h n; elim: n t t' h => [|n hind] t t' h.
- exists 0 => X Y _; by rewrite pr_dnull ge0_pr.
elim/eqit_ind: h =>
  {t t'} [ _ _ r1 r2 -> -> h
         | _ _ t t' -> -> h
         | _ _ _ [A mu] k k' -> -> h
         | _ ot t -> _ h [m hm]
         | _ t ot -> _ h [m hm] ].
- exists 1 => X Y /(_ r1 r2 h) hXY; rewrite /= !pr_dunit.
  by case hx: (X _) hXY => // /(_ erefl) ->.
- move: h => /hind [m hle]; by exists m.+1.
- have:
    forall v,
      exists m,
        dleX RR (dinterp' (observe (k v)) n) (dinterp' (observe (k' v)) m).
  + move=> v; apply: hind; exact: h.
  move=> /ClassicalChoice.choice [get {}h].
  exists (\max_i get i).+1 => X Y hXY /=.
  apply: (Order.le_trans (pr_dlet _ h hXY)). apply: le_mu_pr => r2 hX hX'.
  apply: le_in_dlet => /= t ht r2' {r2 hX hX'}. apply: dinterp'_mono.
  exact: leq_bigmax.
- apply/hind/eqitE; exact: h.
exists m.+1; exact: hm.
Qed.

End ONE.

Lemma eutt_deqX {T T' : choiceType} RR (t : itree Rnd T) (t' : itree Rnd T') :
  eutt RR t t' ->
  deqX RR (dinterp t) (dinterp t').
Proof.
have hmonot := dinterp'_mono (observe t).
have hmonot' := dinterp'_mono (observe t').
move=> h; apply: dle_anti.
+ by apply (leX_dlim hmonot hmonot'), one_way.
apply (leX_dlim hmonot' hmonot), one_way; exact: eutt_flip h.
Qed.

Lemma dinterp_eutt {T : choiceType} (t t' : itree Rnd T) :
  eutt eq t t' ->
  dinterp t =1 dinterp t'.
Proof. move=> h; exact/deqX_eq/eutt_deqX. Qed.

End MAIN.
