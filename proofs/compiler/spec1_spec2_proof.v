(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem.
Require Export compiler_util propagate_inline asm_op_spec1 asm_op_spec2 spec1_spec2.

Import Utf8 ZArith Morphisms Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
Local Open Scope vmap_scope.

Section PROOF.

Context
  {syscall_state asm_op : Type}
  `{asmop : asmOp}
  {fcp : FlagCombinationParams}
  {pd : PointerData}
  {sc_sem : syscall_sem syscall_state}.

Existing Instance progUnit.

Variable (ev:extra_val_t).
Variable (p: @prog asm_op_spec1 asmOp_spec1 _ _).
Variable (p':@prog asm_op_spec2 asmOp_spec2 _ _).
Variable (envp: env).

(*Context {T:eqType} {pT:progT T} `{sCP: semCallParams}.
Variable (ev:extra_val_t).
Variable (p: @prog asm_op_spec1 asmOp_spec1 _ _).
Variable (sppe: SemPexprParams asm_op syscall_state).*)

Definition wf_env (envi : env) (s: estate) (gd : glob_decls) :=
(forall m, Sv.In m envi.2 -> get_var s.(evm) m = ok (Vword (wrepr Uptr (0)))) /\
(forall e fv,
envi.1 = Some (e, fv) ->
fv = read_e e /\
use_mem e = false /\
sem_pexpr gd s e = ok (Vbool true)).

Hypothesis prog_spec1_spec2_ok : prog_spec1_to_spec2 p empty_env = ok (envp, p').

Let Pi_r s1 (i: @instr_r asm_op_spec1 asmOp_spec1) s2 :=
forall ii (envi : env) envi' c', 
wf_env envi s1 (p_globs p) ->
i_spec1_to_spec2 envi (MkI ii i) = ok (envi', c') -> 
sem p' ev s1 c' s2 /\ wf_env envi' s2 (p_globs p').

Let Pi s1 (i: @instr asm_op_spec1 asmOp_spec1) s2 :=
forall (envi : env) envi' c',
wf_env envi s1 (p_globs p) ->
i_spec1_to_spec2 envi i = ok (envi', c') ->
sem p' ev s1 c' s2 /\ wf_env envi' s2 (p_globs p').

Let Pc s1 (c: seq (@instr asm_op_spec1 asmOp_spec1)) s2 :=
forall (envi : env) envi' c',
wf_env envi s1 (p_globs p) ->
c_spec1_to_spec2 (i_spec1_to_spec2) envi c = ok (envi', c') ->
sem p' ev s1 c' s2 /\ wf_env envi' s2 (p_globs p').

Let Pfor (i:var_i) vs s1 c s2 :=
forall (envi envi': env) c',
wf_env envi s1 (p_globs p) ->
c_spec1_to_spec2 (i_spec1_to_spec2) (update_cond_env (vrv i) envi.1, Sv.remove i envi.2) c =  ok (envi', c') ->
sub_env envi envi' ->
sem_for p' ev i vs s1 c' s2 /\ wf_env envi s2 (p_globs p').

Let Pfun scs m fn vargs scs' m' vres :=
forall vargs', List.Forall2 value_uincl vargs vargs' ->
exists2 vres', List.Forall2 value_uincl vres vres' & sem_call p' ev scs m fn vargs' scs' m' vres'.

Lemma eq_globs : p_globs p = p_globs p'.
Proof.
have := prog_spec1_spec2_ok. rewrite /prog_spec1_to_spec2.
by t_xrbindP=> -[envp' fns] /= hm henv hp /=; subst.
Qed.

Lemma sem_pexpr_not_mem_eq gd s1 s2 e v:
sem_pexpr gd s1 e = ok v ->
(*escs s1 = escs s2 ->*)
evm s1 =[read_e e]  evm s2 ->
use_mem e = false ->
sem_pexpr gd s2 e = ok v.
Proof.
(*move=> he hescs hevm hmem. Print estate.
have heeq := eq_on_sem_pexpr gd (s := s1) (s' := with_vm s1 s2.(evm)) erefl erefl hevm. 
move: gd s1 s2 v. elim: e=> //=.
+ move=> x gd s1 s2 v hg hevm _.
  have hsub : Sv.Subset (read_gvar x) (read_e x).
  + rewrite /read_e /read_gvar /=. case: ifP=> //=.
    + move=> hl. rewrite /read_gvar /=. case: ifP=> //=.
      + move=> _. admit. (* doable *)
      admit. (* doable *)
    move=>  hl'. admit. (* doable *)
  have heq := get_gvar_eq_on gd hsub hevm. admit. (* doable *)
+ admit. 
+ admit. 
(* Papp1 *)
+ move=> op e he gd s1 s2 v /=. t_xrbindP=> z hesem hop hevm hmem. 
  have hevm' : evm s1 =[read_e e] evm s2.
  + by case: (op) hevm=> //=.
  by move: (he gd s1 s2 z hesem hevm' hmem)=> -> /=.
(* Papp2 *)
+ move=> op e1 he1 e2 he2 gd s1 s2 v. 
  t_xrbindP=> z he1sem z' he2sem hop2 hevm hmem.
  have [hmem1 hmem2] := Bool.orb_false_elim (use_mem e1) (use_mem e2) hmem.
  rewrite /read_e /= in hevm.
  have hevm1 : evm s1 =[read_e e1] evm s2.
  + admit. (* doable *)
  have hevm2 : evm s1 =[read_e e2] evm s2.
  + admit. (* doable *)
  move: (he1 gd s1 s2 z he1sem hevm1 hmem1)=> -> /=.
  by move: (he2 gd s1 s2 z' he2sem hevm2 hmem2)=> -> /=.
(* PopN *)
+ move=> op es he gd s1 s2 v. t_xrbindP=> vs hm hop hevm hmem.
  admit.
(* if *)
admit.*)
Admitted.

Search write_lval.
Lemma write_lval_get_var s1 s2 m x gd:
Sv.In m (vrvs [:: x]) -> 
write_lval gd x (Vword (wrepr Uptr 0)) s1 = ok s2 ->
get_var (evm s2) m = ok (Vword (wrepr Uptr 0)).
Proof.
move=> hin hw.
have hevm := vrvP hw. case: x hw hin hevm=> //=.
+ move=> vi ty hw hin. have [h1 h2] := SvD.F.empty_iff m. by move: (h1 hin).
+ move=> x hw hin. have h := SvD.F.add_iff Sv.empty x m. case: h=> //= h1 h2.
  move: (h1 hin)=> h1'. case: h1'=> //=.
  + move=> hx; subst. move: hw. rewrite /write_var. t_xrbindP=> vm hset hs /=; subst; rewrite /=.
    have := get_set_var x hset. case: ifP=> //=.
    + move=> /eqP _ hvm hevm. rewrite /get_var /= hvm /=. admit.
    by move=> /eqP //.
  move=> hine. have [] := SvD.F.empty_iff m. move=> h h'. by move: (h hine).
+ move=> sz vi i. t_xrbindP=> z z' hg hp z1 z2 hi hp' z3. 
  rewrite /truncate_word /=. case: ifP=>//= _ [] hz3; subst.
  move=> mem /= hw hs hin. have [h1 h2] := SvD.F.empty_iff m. by move: (h1 hin).
+ move=> arr wsz vi i. rewrite /on_arr_var /=. t_xrbindP=> z hg. case: z hg=> //=.
  move=> len a hg. t_xrbindP=> z z' hi hint z1. rewrite /truncate_word. case: ifP=> //= _. 
  move=> [] hz1; subst. move=> z2 /=.  admit.
move=> arr wsz pos vi i /=. rewrite /on_arr_var /=. t_xrbindP=> z hg. case: z hg=> //=.
move=> len a hg. by t_xrbindP=> z z' hi /= _ //=.
Admitted.

Lemma sub_inter_1 env1 env2 env3:
sub_env env1 (merge_env env2 env3) ->
sub_env env1 env2.
Proof.
Admitted.

Lemma sub_env_refl env:
sub_env env env.
Proof.
case: (env)=> //=. move=> a b. rewrite /sub_env /=.
case: a=> //=.
+ move=> -[ea s]. rewrite /andb /=. case: ifP=> //=.
  + move=> heq. by rewrite SvP.subset_refl.
move=> hneq. have heq := eq_expr_refl ea. by rewrite heq in hneq.
by rewrite SvP.subset_refl.
Qed.

Lemma Hskip : sem_Ind_nil (spp := spp_of_asm_op_spec1) Pc.
Proof.
move=> s1 envi' envi'' c' hwf [] henv hc; subst. have heg := eq_globs. split=> //=. 
+ by constructor. by rewrite -heg.
Qed.

Lemma Hcons : sem_Ind_cons (spp := spp_of_asm_op_spec1) p ev Pc Pi.
Proof.
move=> s1 s2 s3 i c hi. rewrite /Pi /Pc /=. have heg := eq_globs.
move=> hit hc hct envi envi' c' hwf /=. 
t_xrbindP=> -[envi1 c1] hi' -[envi2 c2] hi'' heq heq' /=; subst. rewrite /=.
move: (hit envi envi1 c1 hwf hi')=> [] hc' hwf'.
rewrite -heg in hwf'. move: (hct envi1 envi2 c2 hwf' hi'')=> [] hc'' hwf''. 
split=> //=. by have happ := sem_app (spp := spp_of_asm_op_spec2) hc' hc''. 
Qed.

Lemma HmkI : sem_Ind_mkI (spp := spp_of_asm_op_spec1) p ev Pi_r Pi.
Proof.
move=> ii i s1 s2 hi hpi. rewrite /Pi_r in hpi. rewrite /Pi /=.
move=> envi hwf /=. by move: (hpi ii envi hwf)=> //=.
Qed. 

Lemma Hassgn : sem_Ind_assgn (spp := spp_of_asm_op_spec1) p Pi_r.
Proof.
move=> s1 s2 x tag ty e v v' he ht hw. rewrite /Pi_r /=.
move=> ii envi envi' c' hwf /= [] hu hc'; subst.
have heg := eq_globs. split=> //=. 
+ apply (Eseq (spp := spp_of_asm_op_spec2) (s2 := s2)). 
  + apply (EmkI (spp := spp_of_asm_op_spec2)). apply @Eassgn with v v'.
    + rewrite -heg /=.  admit.  (* doable *)
    + by apply ht.
    rewrite -heg /=. admit. (* doable *)
  by constructor.
rewrite /wf_env. case: hwf=> hwf1 hwf2.
split=> //=. 
+ move=> m hin. have hin1 := SvP.MP.FM.diff_1 hin.
  move: (hwf1 m hin1)=> {hwf1} hwf1. 
  have hwf1' := SvP.MP.FM.diff_2 hin. 
  have hdisj': disjoint (Sv.singleton m) (vrv x).
  + have [] //=:= disjointP (Sv.singleton m) (vrv x). move=> h.
    case: h. move=> a ha. by have heq := SvP.MP.FM.singleton_1 ha; subst.
  have hevm:= disjoint_eq_on hdisj' hw. rewrite /eq_on in hevm. 
  have hs : Sv.In m (Sv.singleton m). + by have := SvP.MP.Dec.F.singleton_2 erefl.
  move: (hevm m hs)=> /= {hevm} hevm. 
  by rewrite /get_var /= -hevm.
move=> e0 fv. rewrite /update_cond_env /=.
case: envi.1 hwf2=> //=. move=> -[oe ofv] hwf2.
case: ifP=> //= hdisj [] heq hfv; subst.
move: (hwf2 e0 fv erefl)=> [] hfv [] hmem hb. split=> //=.
split=> //=. rewrite hfv in hdisj. 
have hdisj' : disjoint (read_e e0) (vrv x).
+ by apply disjoint_sym.
have hevm := disjoint_eq_on hdisj' hw. rewrite -heg. 
by have := sem_pexpr_not_mem_eq hb hevm hmem.
Admitted.

Lemma Hopn : sem_Ind_opn (spp := spp_of_asm_op_spec1) p Pi_r.
Proof.
move=> s1 s2 t [].
(* Ocopy *) (* done *)
+ move=> w pos xs es /= hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi envi' c' hwf /= [] hu hc; subst.  
  rewrite /sem_sopn in hop. move: hop.
  t_xrbindP=> vs vs' hes hexec hws. 
  split=> //=. econstructor.
  econstructor. + econstructor. rewrite -heg /=. admit. (* doable *)
  + by constructor. 
  rewrite /wf_env in hwf. case: hwf=> hwf1 hwf2. rewrite /wf_env /=.
  split=> //=.
  + move=> m hin. have hin' := SvP.MP.FM.diff_1 hin.
    have hin'' := SvP.MP.FM.diff_2 hin.
    move: (hwf1 m hin')=> {hwf1} hwf1.
    have hdisj': disjoint (Sv.singleton m) (vrvs xs).
    + rewrite /disjoint /=. admit. (* doable *)
    have hevm := disjoint_eq_ons (spp := spp_of_asm_op_spec1) hdisj' hws. 
    rewrite /eq_on in hevm. 
    have hs : Sv.In m (Sv.singleton m). 
    + by have := SvD.F.singleton_2 erefl. 
    move: (hevm m hs)=> /= {hevm} hevm.
    by rewrite /get_var /= -hevm.
  move=> e fv. rewrite /update_cond_env /=. 
  case: envi.1 hwf2=> //= -[e1 fv1] hwf2.
  move: (hwf2 e1 fv1 erefl). move=> [] hfv1 [] hmem he.
  case: ifP=> //= hdisj [] heq hfveq; subst. split=> //=. split=> //=.
  have hdisj' : disjoint (read_e e) (vrvs xs).
  + by apply disjoint_sym.
  have hevm := disjoint_eq_ons (spp := spp_of_asm_op_spec1) hdisj' hws. rewrite -heg.
  by have := sem_pexpr_not_mem_eq he hevm hmem.
(* Onop *) (* done *)
+ move=> xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi envi' c' hwf /= [] hu hc; subst. rewrite /sem_sopn in hop.
  move: hop. t_xrbindP=> vs vs' hes. rewrite /exec_sopn /=. 
  case: vs' hes=> //=. move=> hes [] heq hws; subst. split=> //=. 
  + econstructor. 
    + econstructor. econstructor. rewrite -heg. admit. (* doable *)
    by constructor.
  rewrite /wf_env /=. case: hwf=> hwf1 hwf2.
  split=> //=.
  + move=> m hin. case: xs hws hin=> //= hws hin. case: hws=> <-.
    have hin' := SvP.MP.FM.diff_1 hin.
    by move: (hwf1 m hin')=> {hwf1} hwf1. 
  move=> e fv. rewrite /update_cond_env /=. 
  case: envi.1 hwf2=> //= -[e1 fv1] hwf2. case: ifP=> //= hdisj [] heeq hfveq; subst.
  move: (hwf2 e fv erefl)=> [] hfv [] hmem he. split=> //=. split=> //=.
  case: xs hws hdisj=> //=. rewrite -heg. by move=> [] /= hs hdisj; subst.
(* Omul *) (* done *)
+ move=> w xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi envi' c' hwf /= [] hu hc'; subst. split=> //=.
  + econstructor.
    + econstructor. econstructor. admit. (* doable *)
    by constructor.
  rewrite /wf_env in hwf. case: hwf=> hwf1 hwf2.
  rewrite /sem_sopn in hop. move: hop.
  t_xrbindP=> vs vs' hes hex hws.
  split=> //=.
  + move=> m hin. have hin' := SvP.MP.FM.diff_1 hin.
    have hin'' := SvP.MP.FM.diff_2 hin. move: (hwf1 m hin')=> {hwf1} hwf1.
    have hdisj' : disjoint (Sv.singleton m) (vrvs xs).
    + admit. (* doable *)
    have hevm := disjoint_eq_ons hdisj' hws. rewrite /eq_on in hevm. 
    have hs : Sv.In m (Sv.singleton m). 
    + by have := SvD.F.singleton_2 erefl. 
    move: (hevm m hs)=> /= {hevm} hevm.
    by rewrite /get_var /= -hevm.
  move=> e fv. rewrite /update_cond_env /=. 
  case: envi.1 hwf2=> //= -[e1 fv1] hwf2. case: ifP=> //= hdisj [] heeq hfveq; subst.
  move: (hwf2 e fv erefl)=> [] hfv [] hmem he. split=> //=. split=> //=.
  rewrite hfv in hdisj. have hdisj' : disjoint (read_e e) (vrvs xs).
  + by apply disjoint_sym.
  have hevm := disjoint_eq_ons (spp := spp_of_asm_op_spec1) hdisj' hws. rewrite -heg.
  by have := sem_pexpr_not_mem_eq he hevm hmem.
(* Oaddcarry *) (* done *)
+  move=> w xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi envi' c hwf /= [] hu hc; subst. split=> //=.
  + econstructor.
    + econstructor. econstructor. admit. (* doable *)
    by constructor.
  rewrite /wf_env in hwf. case: hwf=> hwf1 hwf2.
  rewrite /sem_sopn in hop. move: hop.
  t_xrbindP=> vs vs' hes hex hws.
  split=> //=.
  + move=> m hin. have hin' := SvP.MP.FM.diff_1 hin.
    have hin'' := SvP.MP.FM.diff_2 hin. move: (hwf1 m hin')=> {hwf1} hwf1.
    have hdisj' : disjoint (Sv.singleton m) (vrvs xs).
    + admit. (* doable *)
    have hevm := disjoint_eq_ons hdisj' hws. rewrite /eq_on in hevm. 
    have hs : Sv.In m (Sv.singleton m). 
    + by have := SvD.F.singleton_2 erefl. 
    move: (hevm m hs)=> /= {hevm} hevm.
    by rewrite /get_var /= -hevm.
  move=> e fv. rewrite /update_cond_env /=. 
  case: envi.1 hwf2=> //= -[e1 fv1] hwf2. case: ifP=> //= hdisj [] heeq hfveq; subst.
  move: (hwf2 e fv erefl)=> [] hfv [] hmem he. split=> //=. split=> //=. rewrite hfv in hdisj.
  have hdisj' : disjoint (read_e e) (vrvs xs).
  + by apply disjoint_sym.
  have hevm := disjoint_eq_ons (spp := spp_of_asm_op_spec1) hdisj' hws. rewrite -heg.
  by have := sem_pexpr_not_mem_eq he hevm hmem.
(* Osubcarry *) (* done *)
+ move=> w xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi envi' c hwf [] hu hc; subst. split=> //=.
  + econstructor.
    + econstructor. econstructor. admit. (* doable *)
    by constructor.
  rewrite /wf_env in hwf. case: hwf=> hwf1 hwf2.
  rewrite /sem_sopn in hop. move: hop.
  t_xrbindP=> vs vs' hes hex hws.
  split=> //=.
  + move=> m hin. have hin' := SvP.MP.FM.diff_1 hin.
    have hin'' := SvP.MP.FM.diff_2 hin. move: (hwf1 m hin')=> {hwf1} hwf1.
    have hdisj' : disjoint (Sv.singleton m) (vrvs xs).
    + admit. (* doable *)
    have hevm := disjoint_eq_ons hdisj' hws. rewrite /eq_on in hevm. 
    have hs : Sv.In m (Sv.singleton m). 
    + by have := SvD.F.singleton_2 erefl. 
    move: (hevm m hs)=> /= {hevm} hevm.
    by rewrite /get_var /= -hevm.
  move=> e fv. rewrite /update_cond_env /=. 
  case: envi.1 hwf2=> //= -[e1 fv1] hwf2. case: ifP=> //= hdisj [] heeq hfveq; subst.
  move: (hwf2 e fv erefl)=> [] hfv [] hmem he. split=> //=. split=> //=. rewrite hfv in hdisj.
  have hdisj' : disjoint (read_e e) (vrvs xs).
  + by apply disjoint_sym.
  have hevm := disjoint_eq_ons (spp := spp_of_asm_op_spec1) hdisj' hws. rewrite -heg.
  by have := sem_pexpr_not_mem_eq he hevm hmem.
move=> [].
(* protect *) (* done *)
+ move=> w xs es. rewrite /Pi_r /=. have heg := eq_globs.
  case: es=> //= e es. case: es=> //= e' es'. case: es'=> //=.
  move=> hop ii envi envi' c hwf; subst. case: e' hop=> //= x hop. 
  case: ifP=> //= hdisj [] hu hc; subst. split=> //=.
  + econstructor. 
    + econstructor. econstructor. admit. (* doable *)
    by constructor.
  case: hwf=> hwf1 hwf2. split=> //=.
  + move=> m hin. have hin' := SvP.MP.FM.diff_1 hin.
    have hin'' := SvP.MP.FM.diff_2 hin. move: (hwf1 m hin')=> {hwf1} hwf1.
    rewrite /sem_sopn in hop. move: hop.
    t_xrbindP=> vs vs' hes hexec hws. 
    have hdisj' : disjoint (Sv.singleton m) (vrvs xs).
    + admit. (* doable *)
    have hevm := disjoint_eq_ons (spp := spp_of_asm_op_spec1) hdisj' hws. 
    rewrite /eq_on in hevm. 
    have hs : Sv.In m (Sv.singleton m). 
    + by have := SvD.F.singleton_2 erefl. 
    move: (hevm m hs)=> /= {hevm} hevm.
    by rewrite /get_var /= -hevm.
  move=> e0 fv. rewrite /update_cond_env /=. case: envi.1 hwf2=> //=.
  move=> -[e1 fv1] hwf2 /=. case: ifP=> //= hdisj' [] heeq hfveq; subst.
  move: (hwf2 e0 fv erefl)=> [] hfv [] hmem hee. split=> //=. split=> //=.
  rewrite /sem_sopn /= in hop. move: hop.
  t_xrbindP=> vs vs' v he vs'' v' hx hvs hvs'; subst. rewrite /exec_sopn /=.
  t_xrbindP=> z zw hw z1 hp /=. rewrite /sopn.sopn_sem /= /asm_op_spec1.protect /=.
  move=> [] hz hvs; subst. case: xs hdisj'=> //= l ls hdisj'.
  t_xrbindP=> s hwl. case: ls hdisj'=> //= hdisj'. move=> [] hs; subst.  
   have hdisj'' : disjoint (read_e e0) (vrv l).
  + by apply disjoint_sym.
  have hevm := disjoint_eq_on (spp := spp_of_asm_op_spec1) hdisj'' hwl.
  have heq := read_e_eq_on (p_globs p') hevm. rewrite /with_vm /= in heq. rewrite -heg.
  by have -> := sem_pexpr_not_mem_eq hee hevm hmem.
(* set_msf e e' *) (* done *)
+ move=> xs es. rewrite /Pi_r /=. have heg := eq_globs. 
  case: es=> //= e es. case: es=> //= e' es'. case: es'=> //=.
  move=> hop ii envi envi' c hwf /=. rewrite /sem_sopn in hop. move: hop.
  t_xrbindP=> vs vs' hes. rewrite /exec_sopn /=. case: vs' hes=> //=. 
  t_xrbindP=> v vs' v' he ves ve he' hves hv hvs'; subst. move=> /= tu b hb.
  rewrite /sopn.sopn_sem /=. t_xrbindP=> wp hp hop hvs hws /=; subst.
  rewrite /get_guard /=. case: hwf=> hwf1 hwf2. case: e' he'=> //= x hg.
  rewrite /asm_op_spec1.set_msf in hop. move: hop. move=> [] htu; subst.
  case: xs hws=> //=.
  move=> x' xs. t_xrbindP=> s hw. case: xs=> //=. move=> [] hs; subst. 
  case: envi.1 hwf1 hwf2=> //= -[e0 fv0] hwf1 hwf2 e' /= [] heeq; subst. case: ifP=> //=.
  move=> /andP [] /andP [] hd1 heq hvar [] henveq hc; subst. split=> //=.
  + econstructor.
    + econstructor. econstructor. admit. (* doable *)
    by constructor.
  rewrite /wf_env /=. split=> //=.
  move=> m hin. rewrite /negb in hd1.
  move: hd1. case: ifP=> //= hd1 _.
  move: (hwf2 e' fv0 erefl)=> [] hfv [] hmem hetrue.
  have heeq := eq_exprP (p_globs p) s1 heq. have hveq : v = true. 
  + rewrite -heeq in he. admit. (* doable (will go after we remove dependency) *)
  rewrite hveq /= in he hb. case: hb=> hb; subst.
  rewrite /negb in hw. rewrite /disjoint /= in hd1. 
  have [] := SvP.choose_mem_3 (Sv.inter (Sv.add (gv x) Sv.empty) envi.2) hd1.
  move=> m' [] hm' hm''. have heq' := SvP.MP.FM.inter_b (Sv.add (gv x) Sv.empty) envi.2 m'. 
  rewrite hm'' in heq'. symmetry in heq'.
  have [h1 h2] := Bool.andb_true_iff (Sv.mem m' (Sv.add (gv x) Sv.empty)) (Sv.mem m' envi.2). 
  move: (h1 heq')=> [] h3 h4. have hin1 := SvP.MP.Dec.F.mem_2 h4.
  move: (hwf1 m' hin1)=> hg'. have hin2 := SvP.MP.Dec.F.mem_2 h3.
  move: (hwf1 m' hin1)=> hget. have heqx := SvP.MP.singleton_equal_add (gv x).
  rewrite /Sv.Equal /= in heqx. move: (heqx m')=> [] hinm hinm'. 
  move: (hinm' hin2)=> hinm''. have heqxm' := SvP.MP.FM.singleton_1 hinm''; subst.
  move: (hwf1 (gv x) hin1)=> hget'. rewrite /gv /get_gvar /= in hg. rewrite hget' in hg.
  move=> {h4} {h3} {h2} {h1} {heq'} {hm''} {hm'} {heqx} {hinm''} {hinm'} {hinm}.
  rewrite hvar /= in hg. case: hg=> hg; subst. rewrite /to_pointer /truncate_word in hp.
  move: hp. case: ifP=> //= _ [] hwp; subst. rewrite zero_extend_u in hw. by have := write_lval_get_var hin hw.
(* init_msf *) (* done *)
+ move=> xs [] //= hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi envi' c hwf /= [] hu hc; subst. rewrite /sem_sopn in hop. move: hop.
  t_xrbindP=> vs vs' /= [] hes /=; subst. rewrite /exec_sopn /=.
  move=> [] <- /= hws. split=> //=.
  + econstructor.
    + econstructor. econstructor. rewrite -heg. admit. (* doable *)
    by constructor.
  rewrite /wf_env in hwf. case: hwf=> hwf1 hwf2. rewrite /wf_env /update_cond_env /=.
  split=> //=.
  move=> m hin. case: xs hws hin=> //=.
  move=> x xs. t_xrbindP=> s hw /=. case: xs=> //=.
  move=> [] <- hin. rewrite /vrvs /= /vrv_rec in hin. case: x hin hw=> //=.
  + move=> vi ty hin. have [h1 h2] := SvP.MP.FM.empty_iff m. by move: (h1 hin)=> //=.
  + move=> vi hin hw. have [h1 h2] := Sv.add_spec Sv.empty vi m. move: (h1 hin)=> [] h; subst.
    + rewrite /write_var /= in hw. move: hw. t_xrbindP=> vm' hw hs. rewrite /with_vm /= in hs.
      rewrite -hs /=. have := get_var_set_var vi hw. case: ifP=> //=.
      + move=> /eqP _ -> /=. admit. (* doable *)
      by move=> /eqP [].
    have [hf hf'] := SvD.F.empty_iff m. by move: (hf h).
  move=> sz vi e h. have [hf hf'] := SvD.F.empty_iff m. by move: (hf h).
  move=> aa sz vi e hin. have [h1 h2] := Sv.add_spec Sv.empty vi m. move: (h1 hin)=> [].
  + move=> -> /=. rewrite /on_arr_var /=. t_xrbindP=> z hg. case: z hg=> //= len w hg /=.
    t_xrbindP=> z z0 he /= hi zw hw a /= ha hwr. rewrite /write_var in hwr. move: hwr.
    t_xrbindP=> vm' /= hset <- /=. rewrite /truncate_word /= in hw. move: hw. case: ifP=> //= hsz.
    move=> [] hz; subst. admit. (* doable *)
    have [hf hf'] := SvD.F.empty_iff m. move=> h. by move: (hf h).
  move=> aa wsz pos vi e hin /=. rewrite /on_arr_var /=. t_xrbindP=> z /=. case: z=> //=.
  move=> len a hg. by t_xrbindP=> z z0 he hi //=.
(* mov_msf *)
+ move=> xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
  case: es hop=> //= e es. case: es=> //= hop ii envi envi' c hwf; subst.
  rewrite /sem_sopn in hop. move: hop. t_xrbindP=> vs vs' hes.
  rewrite /exec_sopn /=. case: vs' hes=> //= v vs'. t_xrbindP=> v' he hv hvs'; subst.
  move=> tu wp hp /=. rewrite /sopn.sopn_sem /=. move=> htu hvs; subst. move=> hws.
  case: xs hws=> //= x xs. t_xrbindP=> s hw. case: xs=> //=. move=> [] hs; subst.
  rewrite /asm_op_spec1.mov_msf /= in htu. case: htu=> h; subst. case: e he=> //= xe hg.
  case: ifP=> //=. move=> /andP [] /negP hdisj hvar [] hu hc; subst. split=> //=.
  + econstructor.
    + econstructor. econstructor. rewrite -heg /=. admit. (* doable *)
    by constructor.
  rewrite /wf_env in hwf. rewrite /wf_env /update_cond_env /=.
  case: hwf=> hwf1 hwf2. split=> //=.
  + move=> m hin. have hin' := SvP.MP.FM.union_1 hin. case: hin'=> hin'.
    + have hin'' : Sv.In (gv xe) envi.2. 
      + rewrite /not in hdisj. rewrite /disjoint in hdisj. admit. (* doable *)
    move: (hwf1 (gv xe) hin'')=> hgxe. move: (hwf1 m hin')=> hgm. 
    rewrite /get_gvar in hg. rewrite hvar /= in hg.
    rewrite hgxe /= in hg. case: hg=> hg; subst.
    rewrite /to_pointer /truncate_word in hp. move: hp.
    case: ifP=> //= _ [] hu; subst. admit. (* ask ??? *)
  have hin'' : Sv.In (gv xe) envi.2. 
  + rewrite /not in hdisj. rewrite /disjoint in hdisj. admit. (* doable *)
  move: (hwf1 (gv xe) hin'')=> hgxe. rewrite /gv /get_gvar hvar /= in hg. 
  rewrite hg in hgxe. case: hgxe=> hgxe; subst.
  rewrite /to_pointer /truncate_word in hp. move: hp.
  case: ifP=> //= _ [] hu; subst. by have := write_lval_get_var hin' hw.
 move=> e fv. case: envi.1 hwf2=>//=. move=> -[e1 fv1] hwf2. 
 case: ifP=> //= hdisj' [] heeq hfveq; subst. move: (hwf2 e fv erefl)=> [] hfv [] hmem he.
 split=> //=. split=> //=. rewrite -heg. rewrite hfv in hdisj'.
 have hdisj'' : disjoint (read_e e) (vrvs [:: x]).
 + by apply disjoint_sym.
 have hevm := disjoint_eq_on (spp := spp_of_asm_op_spec1) hdisj'' hw. 
 by have := sem_pexpr_not_mem_eq he hevm hmem.
(* oasm *) (* done *)
move=> a xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
move=> ii envi envi' c hwf [] hu hc; subst. rewrite /sem_sopn in hop. move: hop.
t_xrbindP=> vs vs' hes hexec hws. split=> //=.
+ econstructor.
  + econstructor.
    + econstructor. rewrite -heg. admit. (* doable *)
  by constructor.
rewrite /wf_env /=. case: hwf=> hwf1 hwf2. split=> //=.
+ move=> m hin. have hin' := SvP.MP.FM.diff_1 hin.
  have hin'' := SvP.MP.FM.diff_2 hin. move: (hwf1 m hin')=> {hwf1} hwf1.
  have hdisj' : disjoint (Sv.singleton m) (vrvs xs).
  + admit. (* doable *)
  have hevm := disjoint_eq_ons hdisj' hws. rewrite /eq_on in hevm. 
  have hs : Sv.In m (Sv.singleton m). 
  + by have := SvD.F.singleton_2 erefl. 
  move: (hevm m hs)=> /= {hevm} hevm.
  by rewrite /get_var /= -hevm.
move=> e fv. rewrite /update_cond_env /=. 
case: envi.1 hwf2=> //= -[e1 fv1] hwf2. case: ifP=> //= hdisj [] heeq hfveq; subst.
move: (hwf2 e fv erefl)=> [] hfv [] hmem he. split=> //=. split=> //=.
rewrite hfv in hdisj. have hdisj' : disjoint (read_e e) (vrvs xs).
+ by apply disjoint_sym.
have hevm := disjoint_eq_ons (spp := spp_of_asm_op_spec1) hdisj' hws. rewrite -heg.
by have := sem_pexpr_not_mem_eq he hevm hmem.
Admitted.

Lemma Hif_true : sem_Ind_if_true (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Proof.
move=> s1 s2 e c1 c2 he hc1 hpc. rewrite /Pc in hpc.  
move=> ii -[envi1 env2] envi' c hwf; subst.
have heg := eq_globs.
rewrite -/i_spec1_to_spec2 /=. 
case: ifP=> //= hmem.
case: envi1 hwf=> //=.
(* some case *)
+ move=> -[e1 fv1] /= hwf. 
  t_xrbindP=> -[envc1 c1'] /= hbc1 -[envc2 c2'] hbc2 /= henv' hc'; subst. 
  have hwfe : wf_env (None, Sv.empty) s1 (p_globs p).
  + rewrite /wf_env /=. split=> //=.
    move=> m hin. have [h1 h2] := SvD.F.empty_iff m. by move: (h1 hin).
  move: (hpc (None, Sv.empty) envc1 c1' hwfe hbc1)=> [] hc1' hwf1.
  split=> //=.
  + econstructor.
    + econstructor. econstructor.
      + by rewrite -heg.
      by apply hc1'.
    by constructor.
  rewrite /wf_env in hwf1. case: hwf1=> hwf11 /= hwf12.
  rewrite /wf_env /=. split=> //=.
  move=> m hin. have hin1 := SvP.MP.FM.inter_1 hin.
  by move: (hwf11 m hin1).
(* none case *)
move=> hwf.
t_xrbindP=> -[envc1 c1'] hbc /= -[envc2 c2'] hbc' /= henv hc; subst.
have hwf' : wf_env (Some (e, read_e e), env2) s1 (p_globs p).
+ rewrite /wf_env. case: hwf=> hwf1 hwf2. split=> //=.
  move=> e1 fv1 [] he1 hfv1; subst. split=> //=. 
  move: (hwf2 e1 (read_e e1))=> hwf2'. split=> //=. rewrite /negb in hmem.
  move: hmem. by case: ifP=> //=.
move: (hpc (Some (e, read_e e), env2) envc1 c1' hwf' hbc). 
move=> [] hc1' hwf1. split=> //=.
+ econstructor. 
  + econstructor. econstructor.
    + by rewrite -heg.
    by apply hc1'.
  by constructor.
rewrite /wf_env in hwf1. case: hwf1=> hwf11 hwf12.
rewrite /wf_env /=. split=> //=.
move=> m hin. have hin1 := SvP.MP.FM.inter_1 hin.
by move: (hwf11 m hin1).
Qed.

Lemma Hif_false : sem_Ind_if_false (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Proof.
move=> s1 s2 e c1 c2 he hc1 hpc. rewrite /Pc in hpc.  
move=> ii -[envi1 env2] hwf.
have heg := eq_globs.
rewrite -/i_spec1_to_spec2 /=. case: ifP=> //= hmem.
case: envi1 hwf=> //=.
(* some case *)
+ move=> -[e1 fv1] /= envi c hwf. 
  t_xrbindP=> -[envc1 c1'] /= hbc1 -[envc2 c2'] /= hbc2 henv hc; subst. 
  have hwfe : wf_env (None, Sv.empty) s1 (p_globs p).
  + rewrite /wf_env /=. split=> //=.
    move=> m hin. have [h1 h2] := SvD.F.empty_iff m. by move: (h1 hin).
  move: (hpc (None, Sv.empty) envc2 c2' hwfe hbc2)=> [] hc2' hwf1. 
  split=> //=.
  + apply (Eseq (spp := spp_of_asm_op_spec2) (s2 := s2)). 
    + apply (EmkI (spp := spp_of_asm_op_spec2)). apply @Eif_false. 
      + by rewrite -heg /=.
      by apply hc2'.
    by constructor.
  rewrite /wf_env in hwf1. case: hwf1=> hwf11 /= hwf12.
  rewrite /wf_env /=. split=> //=.
  move=> m hin. have hin1 := SvP.MP.FM.inter_2 hin.
  by move: (hwf11 m hin1).
(* none case *)
move=> envi c' hwf. 
t_xrbindP=> -[envc1 c1'] hbc1 -[envc2 c2'] hbc2 /= henv hc'; subst. 
have hwf' : wf_env (Some ((enot e), read_e (enot e)), env2) s1 (p_globs p).
+ rewrite /wf_env. case: hwf=> hwf1 hwf2. split=> //=.
  move=> e1 fv1 [] he1 hfv1; subst. split=> //=. 
  split=> //=.
  + rewrite /negb in hmem. move: hmem. by case: ifP=> //=.
  admit. (* doable *)
move: (hpc (Some ((enot e), read_e (enot e)), env2) envc2 c2' hwf' hbc2)=>[] hc2' hwf1. 
split=> //=.
+ apply (Eseq (spp := spp_of_asm_op_spec2) (s2 := s2)). 
    + apply (EmkI (spp := spp_of_asm_op_spec2)). apply @Eif_false. 
      + by rewrite -heg /=.
      by apply hc2'.
    by constructor.
rewrite /wf_env in hwf1. case: hwf1=> hwf11 hwf12.
rewrite /wf_env /=. split=> //=.
move=> m hin. have hin1 := SvP.MP.FM.inter_2 hin.
by move: (hwf11 m hin1).
Admitted.

Lemma loop_whileP_spec c1 e c2 c1' c2' n envi1 (envi2: env):
loop_while i_spec1_to_spec2 c1 e c2 n envi1 = 
ok (envi2, c1', c2') ->
exists envi envi21 envi3, 
[/\ c_spec1_to_spec2 i_spec1_to_spec2 envi c1 = 
    ok ((envi21, envi2.2), c1'), 
    c_spec1_to_spec2 i_spec1_to_spec2 (update_cond_env envi2.2 (Some (e, read_e e)), envi2.2) c2 = ok (envi3, c2')
    & sub_env envi envi3 /\ sub_env envi envi1 /\
    envi2.1 = (update_cond_env envi2.2 (Some ((enot e), read_e (enot e))))].
Proof.
elim: n envi1=> //= n hrec envi1.
t_xrbindP=> -[[envi21 envi22] c1''] hc1 -[envi3' c2''] hc2. case: ifP=> //= hsub.
+ move=> [] hif hceq hceq'; subst. move: hc2. case: ifP=> //=.
  + move=> hdisj hc2. exists envi1. exists envi21. exists envi3'.
    split=> //=. split=> //=. split=> //=. by apply sub_env_refl.
  move=> hdisj hc2. exists envi1. exists envi21. exists envi3'.
  split=> //=. split=> //=. split=> //=. by apply sub_env_refl.
move=> hloop. move: (hrec (merge_env envi1 envi3') hloop)=> 
[] envi [] envc [] envi3 [] hc1' hc2' [] hsub1 [] hsub2 henveq.
exists envi. exists envc. exists envi3. split=> //=. split=> //=. split=> //=. 
+ by have := sub_inter_1 hsub2.
Qed.

Lemma whileP_prop_spec (ii: instr_info) a c1 e c2 envi1 (envi2: env) cr:
i_spec1_to_spec2 envi1 (MkI ii (Cwhile a c1 e c2)) = ok (envi2, cr)->
exists envi envi21 envi3 c1' c2',
[ /\ c_spec1_to_spec2 i_spec1_to_spec2 envi c1 = ok ((envi21, envi2.2), c1'),
     c_spec1_to_spec2 i_spec1_to_spec2 (update_cond_env envi2.2 (Some (e, read_e e)), envi2.2) c2 = ok (envi3, c2'),
     i_spec1_to_spec2 envi (MkI ii (Cwhile a c1 e c2)) = ok ((update_cond_env envi2.2 (Some ((enot e), read_e (enot e))), envi2.2), cr),
     cr = [:: MkI ii (Cwhile a c1' e c2')] 
  &  sub_env envi envi3 /\ sub_env envi envi1 /\ envi2.1 = (update_cond_env envi2.2 (Some ((enot e), read_e (enot e))))].
Proof.
rewrite /=. case: ifP=> //= hmem. t_xrbindP=> -[[[e1 fv] c1'] c2'] hloop [] he1 hc; subst.
have [envi [envi21 [envi3 [hc1] hc2 [hsub1 hsub2]]]] := loop_whileP_spec hloop.  
exists envi, envi21, envi3, c1', c2'. split=> //=.  
by rewrite compiler_util.Loop.nbP /= hc1 /= hc2 /= hsub1 /=. 
Qed.

Lemma wf_sub_env s1 gd envi envi':
sub_env envi envi' ->
wf_env envi' s1 gd ->
wf_env envi s1 gd.
Proof.
(*case: envi=> //= envi1 envi2. case: envi'=> envi1' envi2'. rewrite /sub_env /=.
move=> /andP. rewrite /sub_cond_env. case: envi1=> //=.
+ move=> -[se fv]. case: envi1'=> //= -[se' fv'].
  + move=> [] /= heq hsub. move=> [] hwf1 hwf2.
    split=> //=.
    +*)
Admitted.

Lemma Hwhile_true : sem_Ind_while_true (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Proof.
move=> s1 s2 s3 s4 a c e c' hc hpc he hc' hpc' hi hw ii envi envc c1 hwf hic.
have [env1 [envi21 [envi3 [c1' [c2' [hc1' hc2' hi' hc1eq [hsub1 [hsub2 henv]]]]]]]] := whileP_prop_spec hic; subst.
have hwf' := wf_sub_env hsub2 hwf. 
move: (hpc env1 (envi21, envc.2) c1' hwf' hc1')=> [] hc1'' hwf''.
have hwfu : wf_env (update_cond_env envc.2 (Some (e, read_e e)),
           envc.2) s2 (p_globs p).
+ rewrite /update_cond_env /=. case: ifP=> //=.
  + move=> hdisj. move: henv. rewrite /update_cond_env /=. case: ifP=> //=.
    + move=> hdisj' heq; subst. rewrite /wf_env in hwf''. case: hwf''=> hwf1 /= hwf2.
      split=> //=. move=> e1 fv [] heeq hfveq; subst. split=> //=. split=> //=.
      rewrite /i_spec1_to_spec2 in hic. move: hic. case: ifP=> //= hmem.
      rewrite /negb in hmem. move: hmem. by case: ifP=> //=. 
    move=> hdisj'. 
    have hdisj'' : disjoint envc.2 (read_e (enot e)).
    + by case: (e) hdisj=> //=.
    by rewrite hdisj'' in hdisj'.
  move=> hdisj''. rewrite /wf_env /=. split=> //=.
  move=> m hin. case: hwf''=> /= hwf1 hwf2.
  by move: (hwf1 m hin).
move: (hpc' (update_cond_env envc.2 (Some (e, read_e e)), envc.2) envi3 c2' hwfu hc2')=> [] hc2'' hwf2. have heg := eq_globs.
rewrite /Pi_r in hw. 
move: (hw ii env1 (update_cond_env envc.2 (Some (enot e, read_e (enot e))), envc.2) [:: MkI ii (Cwhile a c1' e c2')]) => {hw} hw. rewrite hi' /= in hw; subst.
have hwf3 := wf_sub_env hsub1 hwf2. rewrite heg in hw. move: (hw hwf3 erefl)=> [] hw' hwf4.
split=> //=.
+ econstructor.
  + econstructor. eapply (Ewhile_true (spp := spp_of_asm_op_spec2)). 
    + by apply hc1''.
    + by rewrite -heg.
    + by apply hc2''.
    have [si [hsi hem]] := semE hw'. have hsi' := sem_IE hsi. admit. (* doable *)
  by constructor.
move: hwf4. case: ifP=> //=.
+ move=> hdisj [] hwf4 /= hwf4'. split=> //=.
  rewrite henv /= hdisj /=. move=> e0 fv0 [] heeq hfveq; subst.
  by move: (hwf4' (enot e) (read_e (enot e)) erefl).
move=> hdisj [] hwf4 /= hwf4'. split=> //=.
rewrite henv /= hdisj /=. move=> e0 fv0. by move: (hwf4' e0 fv0).
Admitted.

Lemma Hwhile_false : sem_Ind_while_false (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Proof.
move=> s1 s2 a c e c' hc hpc he ii envi envi' c1 hwf hic.
have [env1 [envi21 [envi3 [c1' [c2' [hc1' hc2' hi' hc1eq [hsub1 [hsub2 henv]]]]]]]] := whileP_prop_spec hic; subst.
have hwf' := wf_sub_env hsub2 hwf. move: (hpc env1 (envi21, envi'.2) c1' hwf' hc1')=> /= [] hc1'' hwf''. have heg := eq_globs.
split=> //=.
+ econstructor.
  + econstructor. eapply (Ewhile_false (spp := spp_of_asm_op_spec2)). 
    + by apply hc1''.
    + by rewrite -heg.
  by constructor.
case: hwf''=> hwf1 /= hwf2. split=> //=. rewrite henv /=. case: ifP=> //= hdisj.
move=> e0 fv0 [] heeq hfveq; subst. split=> //=. rewrite /i_spec1_to_spec2 in hi'.
move: hi'. case: ifP=> //= hmem _. rewrite /negb in hmem. move: hmem. case: ifP=> //= hmem _.
split=> //=. rewrite -heg. admit. (* doable *)
Admitted.

Lemma merge_envP s gd env1 env2 env3 e fv: 
wf_env env1 s gd ->
merge_env env1 env2 = (Some (e, fv), env3) ->
env1.1 = Some (e, fv) /\ env3 = Sv.inter env1.2 env2.2.
Proof.
rewrite /merge_env /= /wf_env. case: env1.1=> //= -[se fv1].
case: env2.1=> //= -[se' fv2] /=. case: ifP=> //= heq.
by move=> [] h1 h2 [] heeq hfveq henv; subst. 
Qed.

Lemma merge_cond_envP s gd env1 env12 env2 e fv:
wf_env (env1, env12) s gd ->
merge_cond_env env1 env2 = (Some (e, fv)) ->
env1 = Some (e, fv).
Proof.
move=> [] hwf1 hwf2. rewrite /merge_cond_env.
case: env1 hwf1 hwf2=> //=. case: env2=> //=.
move=> -[se1 fv1] -[se2 fv2] hwf1 hwf2 /=. case: ifP=> //= he [] h1 h2; subst.
Qed.

Lemma sub_envP env1 env2:
sub_env env1 env2 ->
Sv.subset env1.2 env2.2.
Proof.
case: env1=> //=. case: env2=> //=.
move=> a b a' b'. rewrite /sub_env /=.
case: a'=> //=. case: a=> //=. by move=> a1 a2 /andP [] he hs.
Qed.

Lemma sub_trans env1 env2 env3: 
sub_env env1 env2 -> sub_env env2 env3 -> sub_env env1 env3.
Proof.
Admitted.

Lemma sub_merge_l env1 env2: 
sub_env (merge_env env1 env2) env1.
Proof. 
Admitted.

Lemma wf_mergeP s gd env1 env2:
wf_env env1 s gd ->
wf_env (merge_env env1 env2) s gd. 
Proof.
move=> hwf. split=> //=.
+ case: hwf=> hwf1 hwf2. move=> m hin. have hin' := SvP.MP.FM.inter_1 hin.
  by move: (hwf1 m hin').
move=> e fv henv. have henveq := merge_cond_envP hwf henv.
case: hwf=> hwf1 hwf2. by move: (hwf2 e fv henveq).
Qed.

Lemma loop_forP x c n envi1 envi c' : 
loop_for i_spec1_to_spec2 x c n envi1 = ok (envi, c') ->
exists envi3, 
[/\ c_spec1_to_spec2 i_spec1_to_spec2 (update_cond_env (vrv x) envi.1, Sv.remove x envi.2) c = ok (envi3, c'),
    sub_env envi envi3
    & sub_env envi envi1].
Proof.
elim: n envi1 => //= n hrec envi1.
t_xrbindP => -[envi3 c''] /= hc; case: ifP => hincl.
+ move=> [??]; subst envi c''; exists envi3; split => //. apply sub_env_refl.
move=> /hrec [envi3' [h1 h2 h3]]; exists envi3'; split => //=.
by apply/(sub_trans h3)/sub_merge_l.
Qed.

Lemma Hfor : sem_Ind_for (spp := spp_of_asm_op_spec1) p ev Pi_r Pfor.
Proof.
move=> s1 s2 i d lo hi c vlo vhi hlo hhi hsem hfor ii envi envi' c' hwf. have heg := eq_globs.
rewrite /i_spec1_to_spec2 /=. rewrite -/i_spec1_to_spec2 /=.
t_xrbindP=> -[envc c1] /= /loop_forP [envi3] [hpic hsub1 hsub2] henv hc; subst.
have hwf' : wf_env envi' s1 (p_globs p).
+ by have := wf_sub_env hsub2 hwf.
move: (hfor envi' envi3 c1 hwf' hpic hsub1)=> [] hfor' hwf''.
split=> //=.
+ econstructor. 
  + econstructor. econstructor.
    + rewrite -heg. admit. (* doable *)
    + rewrite -heg. admit. (* doable *)
    + by apply hfor'.
  by constructor.
Admitted.

Lemma Hfor_nil : sem_Ind_for_nil (spp := spp_of_asm_op_spec1) Pfor.
Proof.
move=> s1 i c envi envi' c' hwf hc hsub. have heg := eq_globs. 
split=> //=. 
+ by constructor. by rewrite -heg.
Qed.

Lemma write_var_valid_env s s' gd envi x v : 
wf_env envi s gd ->
write_var x v s = ok s' ->
wf_env (update_cond_env (vrv x) envi.1, Sv.remove x envi.2) s' gd.
Proof.
move=> hwf hw; split=> //=.
+ move=> m hin. case: hwf=> hwf1 hwf2.
  have h := SvP.MP.Dec.F.remove_iff. move: (h envi.2 x m)=> [] h1 h2.
  move: (h1 hin)=> [] h1' hneq. move: (hwf1 m h1')=> hg. move: hw; rewrite /write_var /=; t_xrbindP.
  move=> vm1 hset1 ?; subst s'; rewrite /= in hg; rewrite /=. 
  have := get_set_var m hset1. case: ifP=> //=.
  + move=> /eqP hx. by rewrite hx in hneq.
  move=> /eqP _ hvm. by rewrite /get_var /= hvm. 
rewrite /update_cond_env /=. case: envi hwf=> //= envi1 envi2.
case: envi1=> //=. move=> [] se fv [] /= hwf1 /= hwf2 se' fv'.
case: ifP=> //= hdisj [] hse hfv; subst.
move: (hwf2 se' fv' erefl)=> [] hfv [] hmem he. split=> //=.
split=> //=. rewrite hfv in hdisj. have hescs := write_var_scsP hw.
have hemem := write_var_memP hw. move: hw; rewrite /write_var /=; t_xrbindP.
move=> vm1 hset1 ?; subst s'; rewrite /=. rewrite -he.
have h := eq_on_sem_pexpr gd hescs hemem. symmetry. apply h=> //=.
move=> z hz. have hnez : x.(v_var) != z.
+ apply/eqP => ?; subst z. have hdisj' := disjointP (Sv.add x Sv.empty) (read_e se') hdisj. 
  have hin' : Sv.In x (Sv.add x Sv.empty). + by apply SvD.F.add_1.
  move: (hdisj' x hin'). rewrite /not. move=> hnot. by move: (hnot hz). 
have := get_set_var z hset1. case: ifP=> //=.
move=> /eqP hneq hvm. rewrite hneq in hnez. rewrite /negb in hnez. 
move: hnez. case: ifP=> //=. by move=> /eqP //.
Qed.

Lemma Hfor_cons : sem_Ind_for_cons (spp := spp_of_asm_op_spec1) p ev Pc Pfor.
Proof.
move=> s1 s2 s3 s4 i w ws c hw hc hpc hfor hpc'. move=> envi envi' c' hwf hc' hsub.
have heg := eq_globs.
have hwf' := write_var_valid_env hwf hw.
move: (hpc (update_cond_env (vrv i) envi.1,
          Sv.remove i envi.2) envi' c' hwf' hc')=> [] hsem hwf''.
rewrite -heg in hwf''.
have hwf1 :=  wf_sub_env hsub hwf''.
move: (hpc' envi envi' c' hwf1 hc' hsub)=> [] hfor' hwf2. 
split=> //=. econstructor.
+ by apply hw.
+ by apply hsem.
by apply hfor'.
Qed.

End PROOF.

