From Coq Require Import Utf8.
Require Import oseq.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
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

Context
  {wsw : WithSubWord}
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  (wdb : bool)
  (gd : glob_decls).

Lemma is_fconstP e z :
  is_fconst e = Some z <-> e = Fconst z.
Proof. case: e => *; by split=> // -[->]. Qed.

Lemma is_fwconstP vm sz e w :
  is_fwconst sz e = Some w ->
  Let x := sem_fexpr vm e in to_word sz x = ok w.
Proof.
  case: e => // -[] //= ws e.
  case: ifP => // hws.
  apply: obindP => z /is_fconstP ? [?]; subst e w.
  by rewrite /= truncate_word_le // zero_extend_wrepr.
Qed.

Lemma fexpr_of_pexprP s e f v :
  fexpr_of_pexpr e = Some f →
  sem_pexpr true gd s e = ok v →
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
  (∀ al ws p f, e = Pload al ws p f → P (omap (Load al ws p) (fexpr_of_pexpr f))) →
  ((∀ al ws p f, e ≠ Pload al ws p f) → P (omap Rexpr (fexpr_of_pexpr e))) →
  P (rexpr_of_pexpr e).
Proof.
  case: e => > A B.
  7: exact: A.
  all: exact: B.
Qed.

Lemma rexpr_of_pexprP s e r v :
  rexpr_of_pexpr e = Some r →
  sem_pexpr true gd s e = ok v →
  sem_rexpr (emem s) (evm s) r = ok v.
Proof.
  elim/rexpr_of_pexpr_ind: (rexpr_of_pexpr e).
  - move => al ws p f -> {e} /obindI[] a [] /fexpr_of_pexprP ok_a /Some_inj <-{r} /=.
    by t_xrbindP => > -> /= -> > /ok_a -> /= -> /= > -> <-.
  by move => _ /obindI[] f [] /fexpr_of_pexprP ok_f /Some_inj <-{r} /ok_f.
Qed.

Lemma lexpr_of_lvalP x d s v s' :
  lexpr_of_lval x = Some d →
  write_lval true gd x v s = ok s' →
  write_lexpr d v s = ok s'.
Proof.
  case: x => //.
  - by move => x /Some_inj <-.
  move => al ws x e /obindI[] a [] /fexpr_of_pexprP ok_a /Some_inj <- {d} /=.
  by t_xrbindP => > -> /= -> > /ok_a -> /= -> /= > -> /= > -> <-.
Qed.

Lemma free_vars_recP vm2 vm1 s f :
  vm1 =[free_vars_rec s f] vm2 ->
  sem_fexpr vm1 f = sem_fexpr vm2 f.
Proof.
  elim: f s => //= [x | o f1 hf1 | o f1 hf1 f2 hf2 | fb hfb f1 hf1 f2 hf2] s.
  + by apply: get_var_eq_on; SvD.fsetdec.
  + by move=> /hf1 ->.
  + move=> heq; rewrite (hf2 _ heq) (hf1 s) //.
    by apply: eq_onI heq; have := free_varsE f2 (free_vars_rec s f1); SvD.fsetdec.
  move=> heq.
  have h1 := free_varsE f1 (free_vars_rec s fb).
  have h2 := free_varsE f2 (free_vars_rec (free_vars_rec s fb) f1).
  rewrite (hf2 _ heq) (hf1 (free_vars_rec s fb)) ?(hfb s) //; apply: eq_onI heq; SvD.fsetdec.
Qed.

Lemma free_varsP vm2 vm1 f :
  vm1 =[free_vars f] vm2 ->
  sem_fexpr vm1 f = sem_fexpr vm2 f.
Proof. apply free_vars_recP. Qed.

Lemma free_vars_rP vm2 vm1 r m:
  vm1 =[free_vars_r r] vm2 ->
  sem_rexpr m vm1 r = sem_rexpr m vm2 r.
Proof.
  case: r => [al w v f | f] /= heq; last by apply free_varsP.
  rewrite (free_vars_recP heq) (get_var_eq_on _ _ heq) // free_varsE; SvD.fsetdec.
Qed.

Lemma sem_fexpr_eq_ex vm1 vm2 e xs :
  disjoint xs (free_vars e) ->
  vm1 =[\ xs ] vm2 ->
  sem_fexpr vm1 e = sem_fexpr vm2 e.
Proof. move=> /eq_ex_disjoint_eq_on /[apply]. exact: free_varsP. Qed.

Lemma sem_rexpr_eq_ex vm1 vm2 m e xs :
  disjoint xs (free_vars_r e) ->
  vm1 =[\ xs ] vm2 ->
  sem_rexpr m vm1 e = sem_rexpr m vm2 e.
Proof. move=> /eq_ex_disjoint_eq_on /[apply]. exact: free_vars_rP. Qed.

Lemma sem_rexprs_eq_ex s vm es xs :
  disjoint xs (free_vars_rs es) ->
  vm =[\ xs ] evm s ->
  sem_rexprs (with_vm s vm) es = sem_rexprs s es.
Proof.
  elim: es => [// | e es hind] /= =>
    /disjoint_sym /disjoint_union [/disjoint_sym he /disjoint_sym hes] hvm.
  by rewrite (sem_rexpr_eq_ex _ he hvm) (hind hes hvm).
Qed.

Lemma write_lexpr_stack_stable e v s1 s2 :
  write_lexpr e v s1 = ok s2 ->
  stack_stable (emem s1) (emem s2).
Proof.
  case: e => [al ws x e|x] /=.
  + t_xrbindP=> ?? _ _ ?? _ _ ? _ ? hw <- /=.
    exact: Memory.write_mem_stable hw.
  t_xrbindP=> ? _ <- /=.
  by reflexivity.
Qed.

Lemma write_lexprs_stack_stable es vs s1 s2 :
  write_lexprs es vs s1 = ok s2 ->
  stack_stable (emem s1) (emem s2).
Proof.
  elim: es vs s1 => [|e es ih] [|v vs] s1 //=.
  + by move=> [<-].
  by t_xrbindP=> s1' /write_lexpr_stack_stable -> /ih.
Qed.

Lemma write_lexpr_validw e v s1 s2 :
  write_lexpr e v s1 = ok s2 ->
  validw (emem s1) =3 validw (emem s2).
Proof.
  case: e => [al ws x e|x] /=.
  + t_xrbindP=> ?? _ _ ?? _ _ ? _ ? hw <- /=.
    by move=> ???; rewrite (write_validw_eq hw).
  t_xrbindP=> ? _ <- /=.
  by move=> ??; reflexivity.
Qed.

Lemma write_lexprs_validw es vs s1 s2 :
  write_lexprs es vs s1 = ok s2 ->
  validw (emem s1) =3 validw (emem s2).
Proof.
  elim: es vs s1 => [|e es ih] [|v vs] s1 //=.
  + by move=> [<-].
  t_xrbindP=> s1' /write_lexpr_validw hvalid1 /ih hvalid2.
  by move=> ???; rewrite hvalid1 hvalid2.
Qed.

Lemma eq_fexpr_sem_fexpr e0 e1 vm :
  eq_fexpr e0 e1 ->
  sem_fexpr vm e0 = sem_fexpr vm e1.
Proof.
  elim: e0 e1 =>
    [z0 | x0 | op e0 h | op e00 h0 e01 h1 | e00 h0 e01 h1 e02 h2] //= [^e1] //=.
  - by move=> /eqP ->.
  - by move=> /eqP ->.
  - by move=> /andP [] /eqP -> /h ->.
  - by move=> /and3P [] /eqP -> /h0 -> /h1 ->.
  by move=> /and3P [] /h0 -> /h1 -> /h2 ->.
Qed.

Lemma eq_fexpr_free_vars e0 e1 :
  eq_fexpr e0 e1 ->
  Sv.Equal (free_vars e0) (free_vars e1).
Proof.
  rewrite /free_vars.
  elim: e0 e1 =>
    [z0 | x0 | ? e0 h | ? e00 h0 e01 h1 | e00 h0 e01 h1 e02 h2] //=
    [z1 | x1 | ? e1 | ? e10 e11 | e10 e11 e12] //=.
  - by move=> /eqP ->.
  - by move=> /andP [] _ /h ->.
  - by rewrite !free_varsE /free_vars => /and3P [] _ /h0 -> /h1 ->.
  by rewrite !free_varsE /free_vars => /and3P [] /h0 -> /h1 -> /h2 ->.
Qed.

End Section.
