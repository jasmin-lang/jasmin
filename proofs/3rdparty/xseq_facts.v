From Coq Require List.
From Coq Require Import Utf8.
From mathcomp Require Import ssreflect eqtype ssrbool ssrfun ssrnat.
From mathcomp Require Import seq.
Require Import xseq.

Lemma assoc_mem' (T: eqType) U (s: seq (T * U)) x w :
  assoc s x = Some w → List.In (x, w) s.
Proof.
  elim: s => // [ [t u] s ] ih /=; case: eqP; last by auto.
  by move => a /Some_inj; left; f_equal.
Qed.

Lemma InP (T: eqType) (s: seq T) m :
  reflect (List.In m s) (m \in s).
Proof.
  elim: s. by constructor.
  move => a s ih. rewrite in_cons.
  case: (@eqP _ m a). by constructor; left.
  case ih; constructor. by right. simpl; intuition.
Qed.

Lemma mem_uniq_assoc (T: eqType) U (s: seq (T * U)) x w :
  List.In (x, w) s → uniq (map fst s) → assoc s x = Some w.
Proof.
  elim: s => // [ [t u] s] ih [ /pair_inj [] -> -> | rec ] /andP [nr un] /=.
  by rewrite eq_refl; eauto.
  case: eqP; last by eauto.
  fold (List.In (x, w) s) in rec.
  apply (List.in_map fst), (rwP (InP _ _)) in rec.
  move=> ?; subst. rewrite rec in nr. done.
Qed.

Lemma assoc_mem_dom' (T: eqType) U (s : seq (T * U)) x w :
  assoc s x = Some w -> x \in [seq v.1 | v <- s].
Proof. move => h; apply assoc_mem' in h. apply (rwP (InP _ _)), List.in_map_iff. eexists; split. 2: eassumption. reflexivity. Qed.

Section AssocMap.
Context (T: eqType) (U V: Type) (f: U → V) (g: T → U → V) (h: T * U → T * V).

Lemma assoc_mapE m n :
  (∀ n u, (h (n, u)).1 = n) →
  assoc (map h m) n = omap (λ u, (h (n, u)).2) (assoc m n).
Proof.
  move => E.
  elim: m => // - [] t u m /= ->.
  case htu: h (E t u) => [ ? v ] /= ?; subst.
  case: eqP => //= ->.
  by rewrite htu.
Qed.

End AssocMap.

Section AssocFilter.
Context (T: eqType) (U: Type) (p: pred T).

Lemma assoc_filterI (m: seq (T * U)) (n: T) :
  assoc [seq x <- m | p x.1 ] n = if p n then assoc m n else None.
Proof.
  elim: m n.
  - by move => n /=; case: ifP.
  case => t u m ih n /=.
  case: ifP.
  - by move => /=; case: eqP => // -> ->.
  by case: eqP => // -> {n} h; rewrite ih h.
Qed.

Corollary assoc_filter (m: seq (T * U)) (n: T) :
  p n →
  assoc [seq x <- m | p x.1] n = assoc m n.
Proof.
  by move => h; rewrite assoc_filterI h.
Qed.

End AssocFilter.
