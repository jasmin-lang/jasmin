From Coq Require Import Utf8.
Require Import oseq.
From mathcomp Require Import all_ssreflect ssralg.
Require Import fexpr fexpr_sem.
Require Import expr psem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma free_varsE e s :
  Sv.Equal (free_vars_rec s e) (Sv.union (free_vars e) s).
Proof.
  rewrite /free_vars.
  elim: e s => //=.
  - move => *; SvD.fsetdec.
  - move => _ f1 ih1 f2 ih2 s; rewrite ih2 ih1 (ih2 (free_vars f1)); SvD.fsetdec.
  move => f1 ih1 f2 ih2 f3 ih3 s.
  rewrite ih3 ih2 ih1 (ih3 (free_vars_rec _ _)) (ih2 (free_vars _)).
  SvD.fsetdec.
Qed.

Lemma free_vars_rec_of_pexpr e f s :
  fexpr_of_pexpr e = Some f →
  Sv.Equal (free_vars_rec s f) (read_e_rec s e).
Proof.
  elim: e f s => //=.
  - by move => > /Some_inj <-.
  - case => x [] // > /Some_inj <-.
    exact: SvP.MP.add_union_singleton.
  - move => op e ih ? s /obindI[] f [] /ih{}ih /Some_inj <-.
    exact: ih.
  - move => op e1 ih1 e2 ih2 f s /obindI[] f1 [] /ih1{}ih1 /obindI[] f2 [] /ih2{}ih2 /Some_inj <- /=.
    rewrite ih2 !read_eE ih1 read_eE; SvD.fsetdec.
  case => // e1 ih1 e2 ih2 e3 ih3 f s /obindI[] f1 [] /ih1{}ih1 /obindI[] f2 [] /ih2{}ih2 /obindI[] f3 [] /ih3{}ih3 /Some_inj <- /=.
  rewrite ih3 !read_eE ih2 read_eE ih1 read_eE; SvD.fsetdec.
Qed.

Section Section.

Context {asm_op syscall_state: Type} {spp: SemPexprParams asm_op syscall_state}.
Context (gd: glob_decls).

Lemma fexpr_of_pexprP s e f v :
  fexpr_of_pexpr e = Some f →
  sem_pexpr gd s e = ok v →
  sem_fexpr (evm s) f = ok v.
Proof.
  elim: e f v => //=.
  - by move => > /Some_inj <- /ok_inj <-.
  - by case => x [] // > /Some_inj <-.
  - move => op e ih ? v /obindI[] f [] /ih{}ih /Some_inj <- /=.
    by t_xrbindP => > /ih ->.
  - move => op e1 ih1 e2 ih2 f v /obindI[] f1 [] /ih1{}ih1 /obindI[] f2 [] /ih2{}ih2 /Some_inj <- /=.
    by t_xrbindP => > /ih1 -> > /ih2 ->.
  case => // e1 ih1 e2 ih2 e3 ih3 f v /obindI[] f1 [] /ih1{}ih1 /obindI[] f2 [] /ih2{}ih2 /obindI[] f3 [] /ih3{}ih3 /Some_inj <- /=.
  rewrite /truncate_val /=.
  t_xrbindP => b > /ih1 -> /= -> > /ih2 -> /= > -> <- > /ih3 -> /= > -> <- <- /=.
  by case: b.
Qed.

Lemma rexpr_of_pexpr_ind (P: option rexpr → Prop) e :
  (∀ ws p f, e = Pload ws p f → P (omap (Load ws p) (fexpr_of_pexpr f))) →
  ((∀ ws p f, e ≠ Pload ws p f) → P (omap Rexpr (fexpr_of_pexpr e))) →
  P (rexpr_of_pexpr e).
Proof.
  case: e => > A B.
  7: exact: A.
  all: exact: B.
Qed.

Lemma rexpr_of_pexprP s e r v :
  rexpr_of_pexpr e = Some r →
  sem_pexpr gd s e = ok v →
  sem_rexpr (emem s) (evm s) r = ok v.
Proof.
  elim/rexpr_of_pexpr_ind: (rexpr_of_pexpr e).
  - move => ws p f -> {e} /obindI[] a [] /fexpr_of_pexprP ok_a /Some_inj <-{r} /=.
    by t_xrbindP => > -> /= -> > /ok_a -> /= -> /= > -> <-.
  by move => _ /obindI[] f [] /fexpr_of_pexprP ok_f /Some_inj <-{r} /ok_f.
Qed.

Lemma lexpr_of_lvalP x d s v s' :
  lexpr_of_lval x = Some d →
  write_lval gd x v s = ok s' →
  write_lexpr d v s = ok s'.
Proof.
  case: x => //.
  - by move => x /Some_inj <-.
  move => ws x e /obindI[] a [] /fexpr_of_pexprP ok_a /Some_inj <- {d} /=.
  by t_xrbindP => > -> /= -> > /ok_a -> /= -> /= > -> /= > -> <-.
Qed.

End Section.
