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

Section Section.

Context `{asmop : asmOp}.
Context {pd : PointerData}.
Context {T} {pT:progT T}.

Definition fun_spec1_to_spec2 (f:@fundef asm_op_spec1 asmOp_spec1 _ _)
: cexec (env * @fundef asm_op_spec2 asmOp_spec2 _ _) :=
  let 'MkFun ii si p c so r ev := f in
  Let c := c_spec1_to_spec2 i_spec1_to_spec2 empty_env c in
  ok (c.1, MkFun ii si p c.2 so r ev).

Variable map_spec1_to_spec2 : 
(@fundef asm_op_spec1 asmOp_spec1 _ _ -> 
cexec (env * @fundef asm_op_spec2 asmOp_spec2 _ _)) -> 
@prog asm_op_spec1 asmOp_spec1 _ _ -> 
(@prog asm_op_spec2 asmOp_spec2 _ _).

Definition prog_spec1_to_spec2 (p:@prog asm_op_spec1 asmOp_spec1 _ _) : 
(@prog asm_op_spec2 asmOp_spec2 _ _) := 
map_spec1_to_spec2 fun_spec1_to_spec2 p.
About map_prog.
End Section.

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

(*Context {T:eqType} {pT:progT T} `{sCP: semCallParams}.
Variable (ev:extra_val_t).
Variable (p: @prog asm_op_spec1 asmOp_spec1 _ _).
Variable (sppe: SemPexprParams asm_op syscall_state).*)

Variable map_spec1_to_spec2 : 
(@fundef asm_op_spec1 asmOp_spec1 _ _ -> 
cexec (env * @fundef asm_op_spec2 asmOp_spec2 _ _)) -> 
@prog asm_op_spec1 asmOp_spec1 _ _ -> 
@prog asm_op_spec2 asmOp_spec2 _ _.

Definition wf_env (envi : env) (s: estate) :=
(forall m, Sv.In m envi.2 -> get_var s.(evm) m = ok (Vword (wrepr Uptr (0)))) /\
(forall e fv gd,
envi.1 = Some (e, fv) ->
fv = read_e e /\
use_mem e = false /\
sem_pexpr gd s e = ok (Vbool true)).

Let p' := prog_spec1_to_spec2 map_spec1_to_spec2 p.

Let Pi_r s1 (i: @instr_r asm_op_spec1 asmOp_spec1) s2 :=
forall ii (envi : env), 
wf_env envi s1 ->
match (ir_spec1_to_spec2 envi ii i) with
 | Ok (envi', c') => sem p' ev s1 c' s2 /\ wf_env envi' s2
 | _ => True
end.

Let Pi s1 (i: @instr asm_op_spec1 asmOp_spec1) s2 :=
forall (envi : env),
wf_env envi s1 ->
match (i_spec1_to_spec2 envi i) with
 | Ok (envi', c') => sem p' ev s1 c' s2 /\ wf_env envi' s2
 | _ => True
end.

Let Pc s1 (c: seq (@instr asm_op_spec1 asmOp_spec1)) s2 :=
forall (envi : env),
wf_env envi s1 ->
match (c_spec1_to_spec2 (i_spec1_to_spec2) envi c) with
 | Ok (envi', c') => sem p' ev s1 c' s2 /\ wf_env envi' s2
 | _ => True
end.

Let Pfor i vs s1 c s2 :=
forall (envi : env),
wf_env envi s1 ->
match (c_spec1_to_spec2 (i_spec1_to_spec2) envi c) with
 | Ok (envi', c') => sem_for p' ev i vs s1 c' s2 /\ wf_env envi' s2
 | _ => True
end.

(*Set Printing Implicit.
Set Printing All.
About sem_Ind_nil. About estate. Print estate. Print sem_Ind_nil.
Print Instances SemPexprParams. 
Print Pc.
Print Estate.*)

Lemma eq_globs : p_globs p = p_globs p'.
Proof.
rewrite /p' /=. case: p=> /=. 
move=> pf pg pe /=. rewrite /prog_spec1_to_spec2 /= /fun_spec1_to_spec2 /=. 
Admitted.

Lemma Hskip : sem_Ind_nil (spp := spp_of_asm_op_spec1) Pc.
Proof.
move=> s1 envi hwf /=. split=> //=.
by constructor.
Qed.

Lemma Hcons : sem_Ind_cons (spp := spp_of_asm_op_spec1) p ev Pc Pi.
Proof.
move=> s1 s2 s3 i c hi. rewrite /Pi /Pc /=. have heg := eq_globs.
move=> hit hc hct envi hwf /=. move: (hit envi hwf)=> {hit} hit.
move: hit. case: (i_spec1_to_spec2 envi i)=> //= -[env1 c'] -[hc' hwf'].
move: (hct env1 hwf')=> {hct} hct. move: hct. 
case: (c_spec1_to_spec2 i_spec1_to_spec2 env1 c) => //= -[env2 c''] -[hc'' hwf''].
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
move=> ii envi hwf /=.
have heg := eq_globs. split=> //=. 
+ apply (Eseq (spp := spp_of_asm_op_spec2) (s2 := s2)). 
  + apply (EmkI (spp := spp_of_asm_op_spec2)). apply @Eassgn with v v'.
    + rewrite -heg /=.  admit. 
    + by apply ht.
    rewrite -heg /=. admit.
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
move=> e0 fv gd. rewrite /update_cond_env /=.
case: envi.1 hwf2=> //=. move=> -[oe ofv] hwf2.
case: ifP=> //= hdisj [] heq hfv; subst.
move: (hwf2 e0 fv gd erefl)=> [] hfv [] hmem hb. split=> //=.
split=> //=. have hescs := lv_write_scsP hw.
admit.
Admitted.

Lemma not_disjoint s s':
disjoint s s' = false ->
exists (x : Sv.elt),
Sv.In x s /\ Sv.In x s'.
Admitted.

Lemma Hopn : sem_Ind_opn (spp := spp_of_asm_op_spec1) p Pi_r.
Proof.
move=> s1 s2 t [].
(* Ocopy *)
+ move=> w pos xs es /= hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi hwf /=. rewrite /ir_spec1_to_spec2 /=. 
  rewrite /sem_sopn in hop. move: hop.
  t_xrbindP=> vs vs' hes hexec hws. 
  split=> //=. econstructor.
  econstructor. + econstructor. rewrite -heg /=. admit.
  + by constructor. 
  rewrite /wf_env in hwf. case: hwf=> hwf1 hwf2. rewrite /wf_env /=.
  split=> //=.
  + move=> m hin. have hin' := SvP.MP.FM.diff_1 hin.
    have hin'' := SvP.MP.FM.diff_2 hin.
    move: (hwf1 m hin')=> {hwf1} hwf1.
    have hdisj': disjoint (Sv.singleton m) (vrvs xs).
    + admit. (* doable *)
    have hevm := disjoint_eq_ons (spp := spp_of_asm_op_spec1) hdisj' hws. 
    rewrite /eq_on in hevm. 
    have hs : Sv.In m (Sv.singleton m). 
    + by have := SvD.F.singleton_2 erefl. 
    move: (hevm m hs)=> /= {hevm} hevm.
    by rewrite /get_var /= -hevm.
  move=> e fv gd. rewrite /update_cond_env /=. 
  case: envi.1 hwf2=> //= -[e1 fv1] hwf2.
  move: (hwf2 e1 fv1 gd erefl). move=> [] hfv1 [] hmem he.
  case: ifP=> //= hdisj [] heq hfveq; subst. split=> //=. split=> //=.
  admit.
(* Onop *) (* done *)
+ move=> xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi hwf /=. rewrite /sem_sopn in hop.
  move: hop. t_xrbindP=> vs vs' hes. rewrite /exec_sopn /=. 
  case: vs' hes=> //=. move=> hes [] heq hws; subst. split=> //=. 
  + econstructor. 
    + econstructor. econstructor. rewrite -heg. admit.
    by constructor.
  rewrite /wf_env /=. case: hwf=> hwf1 hwf2.
  split=> //=.
  + move=> m hin. case: xs hws hin=> //= hws hin. case: hws=> <-.
    have hin' := SvP.MP.FM.diff_1 hin.
    by move: (hwf1 m hin')=> {hwf1} hwf1. 
  move=> e fv gd. rewrite /update_cond_env /=. 
  case: envi.1 hwf2=> //= -[e1 fv1] hwf2. case: ifP=> //= hdisj [] heeq hfveq; subst.
  move: (hwf2 e fv gd erefl)=> [] hfv [] hmem he. split=> //=. split=> //=.
  admit.
(* Omul *)
+ move=> w xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi hwf. split=> //=.
  + econstructor.
    + econstructor. econstructor. admit.
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
  move=> e fv gd. rewrite /update_cond_env /=. 
  case: envi.1 hwf2=> //= -[e1 fv1] hwf2. case: ifP=> //= hdisj [] heeq hfveq; subst.
  move: (hwf2 e fv gd erefl)=> [] hfv [] hmem he. split=> //=. split=> //=.
  admit.
(* Oaddcarry *)
+  move=> w xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi hwf. split=> //=.
  + econstructor.
    + econstructor. econstructor. admit.
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
  move=> e fv gd. rewrite /update_cond_env /=. 
  case: envi.1 hwf2=> //= -[e1 fv1] hwf2. case: ifP=> //= hdisj [] heeq hfveq; subst.
  move: (hwf2 e fv gd erefl)=> [] hfv [] hmem he. split=> //=. split=> //=.
  admit.
(* Osubcarry *)
+ move=> w xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi hwf. split=> //=.
  + econstructor.
    + econstructor. econstructor. admit.
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
  move=> e fv gd. rewrite /update_cond_env /=. 
  case: envi.1 hwf2=> //= -[e1 fv1] hwf2. case: ifP=> //= hdisj [] heeq hfveq; subst.
  move: (hwf2 e fv gd erefl)=> [] hfv [] hmem he. split=> //=. split=> //=.
  admit.
move=> [].
(* protect *)
+ move=> w xs es. rewrite /Pi_r /ir_spec1_to_spec2 /=. have hew := eq_globs.
  case: es=> //= e es. case: es=> //= e' es'. case: es'=> //=.
  move=> hop ii envi hwf. case: ifP=> //= hdisj. split=> //=.
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
  move=> e0 fv gd. rewrite /update_cond_env /=.
  case: envi.1 hwf2=> //=. move=> -[e1 fv1] hwf2.
  case: ifP=> //= hdisj' [] heeq hfveq; subst.
  move: (hwf2 e0 fv gd erefl). move=> [] hfv [] hmem he. split=> //=. split=> //=.
  rewrite /sem_sopn in hop. move: hop. 
  t_xrbindP=> vs vs' hes hexec hws. rewrite /exec_sopn /= in hexec. move: hexec.
  case: vs' hes=> //= v' vs'. t_xrbindP=> vz hesem vs1 v1 he'sem hvs1 hv' hvs'; subst.
  move=> /= tu wt hw. t_xrbindP=> w'' hp /= hop hvs; subst. rewrite /sopn.sopn_sem /= in hop.
  case: xs hdisj' hws=> //=. move=> x xs hdisj'. t_xrbindP=> s' hw' /=. case: xs hdisj'=> //=.
  move=> hdisj' [] hs; subst. 
  have hescs := lv_write_scsP (spp := spp_of_asm_op_spec1) hw'.
  have hlv : ~~ lv_write_mem x.
  + rewrite /negb. case: ifP=> //=.
    case: x hw' hdisj'=> //=. move=> ws vi ex. 
    t_xrbindP=> wp wv hg hwp wp' wv' hex hwp' ww ht m hwm hwm' hdisj' _.
    admit.  (* msf variable must be moved to a register not a memory *)
  have hemem := lv_write_memP (spp := spp_of_asm_op_spec1) hlv hw'.
  have hdisj'' : disjoint (read_e e0) (vrvs [:: x]).
  + by apply disjoint_sym. 
  have hevm := disjoint_eq_on (spp := spp_of_asm_op_spec1) hdisj'' hw'. 
  have heq := eq_on_sem_pexpr gd hescs hemem hevm. by rewrite -he.
(* set_msf *)
+ move=> xs es. rewrite /Pi_r /ir_spec1_to_spec2 /=. have heg := eq_globs. 
  case: es=> //= e es. case: es=> //= e' es'. case: es'=> //=.
  move=> hop ii envi hwf /=. rewrite /sem_sopn in hop. move: hop.
  t_xrbindP=> vs vs' hes. rewrite /exec_sopn /=. case: vs' hes=> //=. 
  t_xrbindP=> v vs' v' he ves ve he' hves hv hvs'; subst. move=> /= tu b hb.
  rewrite /sopn.sopn_sem /=. t_xrbindP=> wp hp hop hvs hws /=; subst.
  rewrite /get_guard /=. case: hwf=> hwf1 hwf2.
  case: envi.1 hwf1 hwf2=> //= -[e0 fv0] hwf1 hwf2. case: ifP=> //=.
  move=> /andP hd. split=> //=.
  + econstructor.
    + econstructor. econstructor. admit. (* doable *)
    by constructor.
  rewrite /wf_env /=. split=> //=.
  move=> m hin. case: hd=> hd1 hd2. rewrite /negb in hd1.
  move: hd1. case: ifP=> //= hd1 _. case: xs hws hin=> //=.
  move=> x xs. t_xrbindP=> s hw. case: xs=> //=. move=> [] hs hin; subst.
  have hin' := SvD.F.union_1 hin. 
  move: (hwf2 e0 fv0 (p_globs p) erefl)=> [] hfv [] hmem hetrue.
  have heeq := eq_exprP (p_globs p) s1 hd2. 
  have hveq : v = true. + admit. (* doable (will go after we remove dependency) *)
  rewrite hveq /= in he hb. case: hb=> hb; subst. rewrite /asm_op_spec1.set_msf in hop.
  move: hop. move=> [] hwp; subst. have heq := read_eE e' Sv.empty.
  rewrite /Sv.Equal /= in heq. case: hin'=> hin1.
  + have hin2 := SvP.MP.FM.diff_1 hin1. have hin3 := SvP.MP.FM.diff_2 hin1.
    admit.
  admit.
(* init_msf *)
+ move=> xs [] //= hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi hwf /=. rewrite /sem_sopn in hop. move: hop.
  t_xrbindP=> vs vs' /= [] hes /=; subst. rewrite /exec_sopn /=.
  move=> [] <- /= hws. split=> //=.
  + econstructor.
    + econstructor. econstructor. rewrite -heg. admit.
    by constructor.
  rewrite /wf_env in hwf. case: hwf=> hwf1 hwf2. rewrite /wf_env /update_cond_env /=.
  split=> //=.
  move=> m hin. case: xs hws hin=> //=.
  move=> x xs. t_xrbindP=> s hw /=. case: xs=> //=.
  move=> [] <- hin. 
  admit. (* doable *)
(* mov_msf *)
+ move=> xs es hop. rewrite /Pi_r /ir_spec1_to_spec2 /=. have heg := eq_globs.
  case: es hop=> //= e es. case: es=> //= hop ii envi hwf.
  rewrite /sem_sopn in hop. move: hop. t_xrbindP=> vs vs' hes.
  rewrite /exec_sopn /=. case: vs' hes=> //= v vs'. t_xrbindP=> v' he hv hvs'; subst.
  move=> tu wp hp /=. rewrite /sopn.sopn_sem /=. move=> htu hvs; subst. move=> hws.
  case: xs hws=> //= x xs. t_xrbindP=> s hw. case: xs=> //=. move=> [] hs; subst.
  case: ifP=> //=.
  move=> hdisj. split=> //=.
  + econstructor.
    + econstructor. econstructor. rewrite -heg /=. admit.
    by constructor.
  rewrite /wf_env in hwf. rewrite /wf_env /update_cond_env /=.
  case: hwf=> hwf1 hwf2. 
  split=> //=.
  + move=> m hin. have heq := read_eE e Sv.empty. 
    have hsub := SvP.MP.subset_equal heq.
    have hin' := SvP.MP.FM.union_1 hin. case: hin'=> hin'.
    + move: (hwf1 m hin')=> hg. rewrite /asm_op_spec1.mov_msf /= in htu.
      case: htu=> htu; subst. 
      admit.
    admit.
  move=> e0 fv gd. case: envi.1 hwf2=> //=. move=> -[e' fv'] hwf2.
  case: ifP=> //= hdisj' [] heeq hfveq; subst. move: (hwf2 e0 fv gd erefl)=> [] hfv [] hmem he'.
  split=> //=. split=> //=. 
  have hescs := lv_write_scsP (spp := spp_of_asm_op_spec1) hw.
  have hlv : ~~ lv_write_mem x. (* msf variable must be moved to a register not a memory *)
  + admit.
  have hemem := lv_write_memP (spp := spp_of_asm_op_spec1) hlv hw. rewrite hfv in hdisj'.
  have hdisj'' : disjoint (read_e e0) (vrvs [:: x]).
  + by apply disjoint_sym. 
  have hevm := disjoint_eq_on (spp := spp_of_asm_op_spec1) hdisj'' hw. 
  have heq := eq_on_sem_pexpr gd hescs hemem hevm. admit. (* doable *) 
(* oasm *)
move=> a xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
move=> ii envi hwf. rewrite /sem_sopn in hop. move: hop.
t_xrbindP=> vs vs' hes hexec hws. split=> //=.
+ econstructor.
  + econstructor.
    + econstructor. rewrite -heg. admit.
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
move=> e fv gd. rewrite /update_cond_env /=. 
case: envi.1 hwf2=> //= -[e1 fv1] hwf2. case: ifP=> //= hdisj [] heeq hfveq; subst.
move: (hwf2 e fv gd erefl)=> [] hfv [] hmem he. split=> //=. split=> //=.
admit.
Admitted.

Lemma Hif_true : sem_Ind_if_true (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Proof.
move=> s1 s2 e c1 c2 he hc2 hpc. move=> ii envi hwf. case: hwf=> hwf1 hwf2.
 have heg := eq_globs.
rewrite /ir_spec1_to_spec2 -/i_spec1_to_spec2 /=. 
case hbc2 : c_spec1_to_spec2=> //= [[envc1 c2'] /=|//]. 
case hbc1 : c_spec1_to_spec2=> //= [[envc1' c1']].
(*+ rewrite /Pc in hpc.
  case: envi.1 hwf2=> //=.
  (* some case *)
  + move=> -[se fv] hwf2. admit.
  (* None *)

have hwf' : wf_env (Some (e, read_e e), envi.2) s1.
+ rewrite /wf_env. case: hwf=> hwf1 hwf2. 
  + split.
    + move=> /= m hin. by move: (hwf1 m hin)=> hg.
  move=> e' fv gd [] heeq hfv; subst. split=> //=.
  case: envi.1 hwf2=> //=.
  (* some e case *)
  + move=> -[e'' fv''] hwf2. move:(hwf2 e'' fv'' gd erefl)=> [] hfv [] hmem he''.
    admit.
  (* none case *)
  move=> hwf2.
move: (hwf2 
move: (hpc (Some (e, read_e e), envi.2)). hwf).
case heq' : c_spec1_to_spec2=> //= [[envc2 c1''] /=|//].
move=> [] hc1'' hwf'. split=> //=.
apply (Eseq (spp := spp_of_asm_op_spec2) (s2 := s2)).
apply (EmkI (spp := spp_of_asm_op_spec2)). 
+ apply (Eif_true (spp := spp_of_asm_op_spec2)).
  + by rewrite -heg.
  admit.
by constructor.*)
Admitted.

Lemma Hif_false : sem_Ind_if_false (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Proof.
(*move=> s1 s2 e c1 c2 he hc2 hpc. move=> ii envi hwf. have heg := eq_globs.
rewrite /ir_spec1_to_spec2 -/i_spec1_to_spec2 /=.
move: (hpc envi hwf). case: envi hwf=> //= [env1 env2] hwf.
case heq : c_spec1_to_spec2=> //= [[envc1 c2'] /=|//]. move=> [hc1' hwf1].
case heq' : c_spec1_to_spec2=> //= [[envc2 c2''] /=|//].
case heq'' : c_spec1_to_spec2=> //= [[envc1' c1']].
split=> //=.
+ apply (Eseq (spp := spp_of_asm_op_spec2) (s2 := s2)).
  + apply (EmkI (spp := spp_of_asm_op_spec2)). 
    apply (Eif_false (spp := spp_of_asm_op_spec2)).
    + by rewrite -heg.
    admit.
  by constructor.*)
(*rewrite /wf_env /update_cond_env /=. rewrite /wf_env in hwf hwf1.
case: env1 heq heq' heq'' hwf hwf1 => //= -[b fv] heq heq' heq'' hwf hwf1.
move=> e0 fv0 s gd. case: ifP=> //=.
move=> hsub [] h1 h2; subst. move: (hwf e0 fv0 s gd erefl)=> [] hfv0 [] hmem [] he0 hmsf.
split=> //=. split=> //=. split=> //=. rewrite /= in heq''.
move=> m hsub'. move: (hwf1 e0 fv0 s gd)=> {hwf1} hwf1. apply hwf1.*)
Admitted.

Lemma Hwhile_true : sem_Ind_while_true (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Admitted.

Lemma Hwhile_false : sem_Ind_while_false (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Admitted.

Lemma Hfor : sem_Ind_for (spp := spp_of_asm_op_spec1) p ev Pi_r Pfor.
Admitted.

End PROOF.

