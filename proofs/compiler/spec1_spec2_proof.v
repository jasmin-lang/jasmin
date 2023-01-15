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

Definition wf_env (envi : env) (s: estate) (gd : glob_decls) :=
(forall m, Sv.In m envi.2 -> get_var s.(evm) m = ok (Vword (wrepr Uptr (0)))) /\
(forall e fv,
envi.1 = Some (e, fv) ->
fv = read_e e /\
use_mem e = false /\
sem_pexpr gd s e = ok (Vbool true)).

Let p' := prog_spec1_to_spec2 map_spec1_to_spec2 p.

Let Pi_r s1 (i: @instr_r asm_op_spec1 asmOp_spec1) s2 :=
forall ii (envi : env), 
wf_env envi s1 (p_globs p) ->
match (ir_spec1_to_spec2 envi ii i) with
 | Ok (envi', c') => sem p' ev s1 c' s2 /\ wf_env envi' s2 (p_globs p')
 | _ => True
end.

Let Pi s1 (i: @instr asm_op_spec1 asmOp_spec1) s2 :=
forall (envi : env),
wf_env envi s1 (p_globs p) ->
match (i_spec1_to_spec2 envi i) with
 | Ok (envi', c') => sem p' ev s1 c' s2 /\ wf_env envi' s2 (p_globs p')
 | _ => True
end.

Let Pc s1 (c: seq (@instr asm_op_spec1 asmOp_spec1)) s2 :=
forall (envi : env),
wf_env envi s1 (p_globs p) ->
match (c_spec1_to_spec2 (i_spec1_to_spec2) envi c) with
 | Ok (envi', c') => sem p' ev s1 c' s2 /\ wf_env envi' s2 (p_globs p')
 | _ => True
end.

Let Pfor i vs s1 c s2 :=
forall (envi : env),
wf_env envi s1 (p_globs p) ->
match (c_spec1_to_spec2 (i_spec1_to_spec2) envi c) with
 | Ok (envi', c') => sem_for p' ev i vs s1 c' s2 /\ wf_env envi' s2 (p_globs p')
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

Lemma sem_pexpr_not_mem_eq gd s1 s2 e v:
sem_pexpr gd s1 e = ok v ->
evm s1 =[read_e e]  evm s2 ->
use_mem e = false ->
sem_pexpr gd s2 e = ok v.
Proof.
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
admit.
Admitted.

Lemma write_lval_get_var s1 s2 m x gd:
Sv.In m (vrvs [:: x]) -> 
write_lval gd x (Vword (zero_extend Uptr (wrepr Uptr 0))) s1 = ok s2 ->
get_var (evm s2) m = ok (Vword (wrepr Uptr 0)).
Proof.
move=> hin hw. rewrite /vrvs /vrvs_rec in hin. case: x hw hin=> //=.
+ move=> vi ty hw hin. have [h1 h2] := SvD.F.empty_iff m. by move: (h1 hin).
+ move=> vi hw hin. have [h1 h2] := Sv.add_spec Sv.empty vi m. move: (h1 hin).
  move=> {h1} h1. case: h1=> //=.
  + move=> hmeq; subst. rewrite /write_var /= in hw. move: hw.
    t_xrbindP=> vm hset hvm; subst; rewrite /=. have := get_var_set_var vi hset.
    case: ifP=> //=.
    + move=> /eqP _ -> /=. admit. (* doable *) 
    by move=> /eqP [].
  move=> hin'. have [h1' h2'] := SvD.F.empty_iff m. by move: (h1' hin').
+ move=> sz vi i. t_xrbindP=> z z' hg hp z1 z2 hi hp' z3. 
  rewrite /truncate_word /=. case: ifP=>//= _ [] hz3; subst.
  move=> mem /= hw hs hin. have [h1 h2] := SvD.F.empty_iff m. by move: (h1 hin).
+ move=> arr wsz vi i. rewrite /on_arr_var /=. t_xrbindP=> z hg. case: z hg=> //=.
  move=> len a hg. t_xrbindP=> z z' hi hint z1. rewrite /truncate_word. case: ifP=> //= _.
  move=> [] hz1; subst. move=> z2 /=.  admit.
move=> arr wsz pos vi i /=. rewrite /on_arr_var /=. t_xrbindP=> z hg. case: z hg=> //=.
move=> len a hg. by t_xrbindP=> z z' hi /= _ //=.
Admitted.

Lemma Hskip : sem_Ind_nil (spp := spp_of_asm_op_spec1) Pc.
Proof.
move=> s1 envi hwf /=. have heg := eq_globs. split=> //=. 
+ by constructor. by rewrite -heg.
Qed.

Lemma Hcons : sem_Ind_cons (spp := spp_of_asm_op_spec1) p ev Pc Pi.
Proof.
move=> s1 s2 s3 i c hi. rewrite /Pi /Pc /=. have heg := eq_globs.
move=> hit hc hct envi hwf /=. move: (hit envi hwf)=> {hit} hit.
move: hit. case: (i_spec1_to_spec2 envi i)=> //= -[env1 c'] -[hc' hwf'].
rewrite -heg in hwf'. move: (hct env1 hwf')=> {hct} hct. move: hct. 
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
  move=> ii envi hwf /=. rewrite /ir_spec1_to_spec2 /=. 
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
  move=> ii envi hwf /=. rewrite /sem_sopn in hop.
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
  move=> ii envi hwf. split=> //=.
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
  move=> ii envi hwf. split=> //=.
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
  move=> ii envi hwf. split=> //=.
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
+ move=> w xs es. rewrite /Pi_r /ir_spec1_to_spec2 /=. have heg := eq_globs.
  case: es=> //= e es. case: es=> //= e' es'. case: es'=> //=.
  move=> hop ii envi hwf. case: e' hop=> //= x hop. case: ifP=> //= hdisj. split=> //=.
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
+ move=> xs es. rewrite /Pi_r /ir_spec1_to_spec2 /=. have heg := eq_globs. 
  case: es=> //= e es. case: es=> //= e' es'. case: es'=> //=.
  move=> hop ii envi hwf /=. rewrite /sem_sopn in hop. move: hop.
  t_xrbindP=> vs vs' hes. rewrite /exec_sopn /=. case: vs' hes=> //=. 
  t_xrbindP=> v vs' v' he ves ve he' hves hv hvs'; subst. move=> /= tu b hb.
  rewrite /sopn.sopn_sem /=. t_xrbindP=> wp hp hop hvs hws /=; subst.
  rewrite /get_guard /=. case: hwf=> hwf1 hwf2. case: e' he'=> //= x hg.
  rewrite /asm_op_spec1.set_msf in hop. move: hop. move=> [] htu; subst.
  case: xs hws=> //=.
  move=> x' xs. t_xrbindP=> s hw. case: xs=> //=. move=> [] hs; subst. 
  case: envi.1 hwf1 hwf2=> //= -[e0 fv0] hwf1 hwf2. case: ifP=> //=.
  move=> /andP hd. split=> //=.
  + econstructor.
    + econstructor. econstructor. admit. (* doable *)
    by constructor.
  rewrite /wf_env /=. split=> //=.
  move=> m hin. case: hd=> /andP [] hd1 heq hvar. rewrite /negb in hd1.
  move: hd1. case: ifP=> //= hd1 _.
  move: (hwf2 e0 fv0 erefl)=> [] hfv [] hmem hetrue.
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
  move: hp. case: ifP=> //= _ [] hwp; subst. by have := write_lval_get_var hin hw.
(* init_msf *) (* done *)
+ move=> xs [] //= hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi hwf /=. rewrite /sem_sopn in hop. move: hop.
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
+ move=> xs es hop. rewrite /Pi_r /ir_spec1_to_spec2 /=. have heg := eq_globs.
  case: es hop=> //= e es. case: es=> //= hop ii envi hwf.
  rewrite /sem_sopn in hop. move: hop. t_xrbindP=> vs vs' hes.
  rewrite /exec_sopn /=. case: vs' hes=> //= v vs'. t_xrbindP=> v' he hv hvs'; subst.
  move=> tu wp hp /=. rewrite /sopn.sopn_sem /=. move=> htu hvs; subst. move=> hws.
  case: xs hws=> //= x xs. t_xrbindP=> s hw. case: xs=> //=. move=> [] hs; subst.
  rewrite /asm_op_spec1.mov_msf /= in htu. case: htu=> h; subst. case: e he=> //= xe hg.
  case: ifP=> //=. move=> /andP [] /negP hdisj hvar. split=> //=.
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
move=> ii envi hwf. rewrite /sem_sopn in hop. move: hop.
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
move=> ii -[envi1 env2] hwf.
have heg := eq_globs.
rewrite /ir_spec1_to_spec2 -/i_spec1_to_spec2 /=. 
case: envi1 hwf=> //=.
(* some case *)
+ move=> -[e1 fv1] /= hwf.
  case hbc1 : (c_spec1_to_spec2 i_spec1_to_spec2 (None, Sv.empty) c1)
  => [[envc1 c1'] /=|//].
  case hbc2 : (c_spec1_to_spec2 i_spec1_to_spec2 (None, Sv.empty) c2)
  => [[envc2 c2'] /=|//].
  have hwfe : wf_env (None, Sv.empty) s1 (p_globs p).
  + rewrite /wf_env /=. split=> //=.
    move=> m hin. have [h1 h2] := SvD.F.empty_iff m. by move: (h1 hin).
  move: (hpc (None, Sv.empty) hwfe). rewrite hbc1 /=. move=> [] hc1' hwf1.
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
case hbc1 : (c_spec1_to_spec2 i_spec1_to_spec2 (Some (e, read_e e), env2) c1)=> [[envc1 c1'] /=|//].
case hbc2 : (c_spec1_to_spec2 i_spec1_to_spec2 (Some (enot e, read_e (enot e)), env2) c2)=> [[envc2 c2'] /=|//].
have hwf' : wf_env (Some (e, read_e e), env2) s1 (p_globs p).
+ rewrite /wf_env. case: hwf=> hwf1 hwf2. split=> //=.
  move=> e1 fv1 [] he1 hfv1; subst. split=> //=. 
  move: (hwf2 e1 (read_e e1))=> hwf2'. split=> //=.
  admit. (* How to show that condition is not dependent on memory *)
move: (hpc (Some (e, read_e e), env2) hwf'). rewrite hbc1 /=.
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
Admitted.

Lemma Hif_false : sem_Ind_if_false (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Proof.
move=> s1 s2 e c1 c2 he hc1 hpc. rewrite /Pc in hpc.  
move=> ii -[envi1 env2] hwf.
have heg := eq_globs.
rewrite /ir_spec1_to_spec2 -/i_spec1_to_spec2 /=. 
case: envi1 hwf=> //=.
(* some case *)
+ move=> -[e1 fv1] /= hwf.
  case hbc1 : (c_spec1_to_spec2 i_spec1_to_spec2 (None, Sv.empty) c1)
  => [[envc1 c1'] /=|//].
  case hbc2 : (c_spec1_to_spec2 i_spec1_to_spec2 (None, Sv.empty) c2)
  => [[envc2 c2'] /=|//].
  have hwfe : wf_env (None, Sv.empty) s1 (p_globs p).
  + rewrite /wf_env /=. split=> //=.
    move=> m hin. have [h1 h2] := SvD.F.empty_iff m. by move: (h1 hin).
  move: (hpc (None, Sv.empty) hwfe). rewrite hbc2 /=. move=> [] hc2' hwf1.
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
move=> hwf. 
case hbc1 : (c_spec1_to_spec2 i_spec1_to_spec2 (Some (e, read_e e), env2) c1)=> [[envc1 c1'] /=|//].
case hbc2 : (c_spec1_to_spec2 i_spec1_to_spec2 (Some (enot e, read_e (enot e)), env2) c2)=> [[envc2 c2'] /=|//].
have hwf' : wf_env (Some ((enot e), read_e (enot e)), env2) s1 (p_globs p).
+ rewrite /wf_env. case: hwf=> hwf1 hwf2. split=> //=.
  move=> e1 fv1 [] he1 hfv1; subst. split=> //=. 
  split=> //=.
  + admit. (* How to show that condition is not dependent on memory *)
  admit. (* doable *)
move: (hpc (Some ((enot e), read_e (enot e)), env2) hwf'). rewrite hbc2 /=.
move=> [] hc2' hwf1. split=> //=.
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

Lemma Hwhile_true : sem_Ind_while_true (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Proof.
move=> s1 s2 s3 s4 a c e c' hc hpc he hc' hpc' hi hpi. move=> ii envi hwf.
rewrite /ir_spec1_to_spec2 -/i_spec1_to_spec2 /=. have heg := eq_globs.
case hbc : (c_spec1_to_spec2 i_spec1_to_spec2 envi c)=> [[envc c1] /=|//].
case hbc' : (c_spec1_to_spec2 i_spec1_to_spec2 (enter_msf envc e) c')=> [[envc' c2] /=|//].
have hwfe : wf_env (None, Sv.empty) s3 (p_globs p).
+ rewrite /wf_env /=. split=> //=.
  move=> m hin. have [h1 h2] := SvD.F.empty_iff m. by move: (h1 hin).
move: (hpc envi hwf). rewrite hbc /=. move=> [] hc1 hwf1.
have hwf' : wf_env (enter_msf envc e) s2 (p_globs p).
+ rewrite /wf_env /enter_msf. case: envc hbc hbc' hwf1=> //=. move=> ec1 msf hbc hbc'.
  case: ec1 hbc hbc'=> //=.
  (* some *)
  + move=> -[ec1' fvc1'] hbc hbc' hwf1. case: hwf1=> hwf11 hwf12.
    split=> //=. move=> m hin. have [h1 h2] := SvD.F.empty_iff m. by move: (h1 hin).
  (* none *)
  move=> hbc hbc' hwf1. case: hwf1=> hwf11 hwf12. split=> //=.
  move=> e1 fv1 [] hee hfv; subst. split=> //=. split=> //=.
  admit. (* how to show that condition doesn't depend on memory *)
move: (hpc' (enter_msf envc e) hwf'). rewrite hbc' /=. move=> [] hc2 hwf''.   
rewrite /Pi_r in hpi. rewrite -heg in hwf''. move: (hpi ii envc' hwf'').
rewrite /ir_spec1_to_spec2 -/i_spec1_to_spec2 /=. move=> hpi'.
split=> //=.
+ econstructor. 
  + econstructor. eapply (Ewhile_true (spp := spp_of_asm_op_spec2)).  
  + by apply hc1.
  + by rewrite -heg.
  + by apply hc2.
  + admit.
  by constructor.
rewrite /wf_env /=. split=> //=. case: hwf1=> hwf11 hwf12.
case: hwf''=> hwf1'' hwf2''. move=> m hin.
have hin1 := SvP.MP.FM.inter_2 hin.
admit.
Admitted.

Lemma Hwhile_false : sem_Ind_while_false (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Proof.
move=> s1 s2 a c e c' hc hpc he. move=> ii envi hwf.
rewrite /ir_spec1_to_spec2 -/i_spec1_to_spec2 /=. have heg := eq_globs.
case hbc : (c_spec1_to_spec2 i_spec1_to_spec2 envi c)=> [[envc c1] /=|//].
case hbc' : (c_spec1_to_spec2 i_spec1_to_spec2 (enter_msf envc e) c')=> [[envc' c2] /=|//].
rewrite /Pc in hpc. move: (hpc envi hwf). rewrite hbc /=. move=> [] hc1 hwf'.
have hwf'' : wf_env (enter_msf envc e) s2 (p_globs p).
+ rewrite /wf_env /enter_msf. case: envc hbc hbc' hwf'=> //=. move=> ec1 msf hbc hbc'. 
  case: ec1 hbc hbc'=> //=.
  (* some *)
  + move=> -[ec1' fvc1'] hbc hbc' hwf1. case: hwf1=> hwf11 hwf12.
    split=> //=. move=> m hin. have [h1 h2] := SvD.F.empty_iff m. by move: (h1 hin).
  (* none *)
  move=> hbc hbc' hwf1. case: hwf1=> hwf11 hwf12. split=> //=.
  move=> e1 fv1 [] hee hfv; subst. split=> //=. split=> //=.
  + admit. (* how to show that condition doesn't depend on memory *)
  admit. (* doable *)
split=> //=.
+ apply (Eseq (spp := spp_of_asm_op_spec2) (s2 := s2)). 
  + apply (EmkI (spp := spp_of_asm_op_spec2)). apply @Ewhile_false. 
    + by apply hc1.
    + by rewrite -heg /=.
    by constructor.
rewrite /wf_env /=. split=> //=. case: hwf'=> hwf11 hwf12.
move=> m hin. have hin1 := SvP.MP.FM.inter_1 hin.
by move: (hwf11 m hin1).
Admitted.

Lemma Hfor : sem_Ind_for (spp := spp_of_asm_op_spec1) p ev Pi_r Pfor.
Proof.
move=> s1 s2 i d lo hi c vlo vhi hlo hhi.
Admitted.

Lemma Hfor_nil : sem_Ind_for_nil (spp := spp_of_asm_op_spec1) Pfor.
Proof.
move=> s1 i c envi hwf. 
case hbc : (c_spec1_to_spec2 i_spec1_to_spec2 envi c)=> [[envc c1] /=|//].
split=> //=.
+ by constructor. 
rewrite /wf_env. case: hwf=> hwf1 hwf2. split=> //=. 
move=> m hin.
Admitted.

Lemma Hfor_cons : sem_Ind_for_cons (spp := spp_of_asm_op_spec1) p ev Pc Pfor.
Proof.
move=> s1 s2 s3 s4 i w ws c hw hc hpc hfor hpc'. move=> envi hwf.
case hbc : (c_spec1_to_spec2 i_spec1_to_spec2 envi c)=> [[envc c1] /=|//].
have hwf' : wf_env envi s2 (p_globs p).
+ rewrite /wf_env. case: hwf=> hwf1 hwf2. split=> //=. 
  + move=> m hin. move: (hwf1 m hin)=> hg. have hevm := vrvP_var hw.
    rewrite /vmap_eq_except in hevm. admit.
  admit.
split=> //=.
+ econstructor.
  + by apply hw.
  + rewrite /Pc in hpc.
Admitted.

End PROOF.

