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

Definition wf_env (envi : env) :=
forall e fv s gd,
envi.1 = Some (e, fv) ->
fv = read_e e /\
use_mem e = false /\
sem_pexpr gd s e = ok (Vbool true) /\
(forall m, Sv.In m envi.2 -> get_var s.(evm) m = ok (Vword (wrepr Uptr (0)))).

(*Inductive wf_env (*(s: estate)*) (envi : env) : Prop :=
| wf_cond_env : forall e fv msf gd s,
                envi = (Some (e, fv), msf)  ->
                fv = read_e e ->
                use_mem e = false ->
                sem_pexpr gd s e = ok (Vbool true) ->
                (forall m, Sv.Subset (read_gvar m) msf -> get_gvar gd s.(evm) m = ok (Vword (wrepr Uptr (0)))) ->
                wf_env envi
| wf_none_env : forall msf,
                envi = (None, msf) ->
                wf_env envi.*)

(*Definition estate_spec1_spec2 (s1 : @estate (@asm_op_spec1 asm_op0 asmop) syscall_state
                  (@spp_of_asm_op_spec1 asm_op0 asmop pd syscall_state fcp sc_sem)) :
@estate (@asm_op_spec2 asm_op0 asmop) syscall_state
                  (@spp_of_asm_op_spec2 asm_op0 asmop pd syscall_state fcp sc_sem) :=
match s1 with 
| Estate ss m f => @Estate (@asm_op_spec2 asm_op0 asmop) syscall_state
                   (@spp_of_asm_op_spec2 asm_op0 asmop pd syscall_state fcp sc_sem) ss m f
end. *)

Let p' := prog_spec1_to_spec2 map_spec1_to_spec2 p.

Let Pi_r s1 (i: @instr_r asm_op_spec1 asmOp_spec1) s2 :=
forall ii (envi : env), 
wf_env envi ->
match (ir_spec1_to_spec2 envi ii i) with
 | Ok (envi', c') => sem p' ev s1 c' s2 /\ wf_env envi'
 | _ => True
end.

Let Pi s1 (i: @instr asm_op_spec1 asmOp_spec1) s2 :=
forall (envi : env),
wf_env envi ->
match (i_spec1_to_spec2 envi i) with
 | Ok (envi', c') => sem p' ev s1 c' s2 /\ wf_env envi'
 | _ => True
end.

Let Pc s1 (c: seq (@instr asm_op_spec1 asmOp_spec1)) s2 :=
forall (envi : env),
wf_env envi ->
match (c_spec1_to_spec2 (i_spec1_to_spec2) envi c) with
 | Ok (envi', c') => sem p' ev s1 c' s2 /\ wf_env envi'
 | _ => True
end.

Let Pfor i vs s1 c s2 :=
forall (envi : env),
wf_env envi ->
match (c_spec1_to_spec2 (i_spec1_to_spec2) envi c) with
 | Ok (envi', c') => sem_for p' ev i vs s1 c' s2 /\ wf_env envi'
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
  move=> ii envi hwf /=. split=> //=. case: s1 hop hwf=> //= ss m vm hop hwf.
  case: s2 hop=>//= ss' m' vm' hop'. econstructor.
  econstructor. + econstructor. rewrite -heg /=. admit.
  + by constructor.   
(* Onop *)
+ move=> xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi hwf /=. split=> //=. econstructor. 
  + econstructor. econstructor. rewrite -heg. admit.
  by constructor.
(* Omul *)
+ move=> w xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi hwf. split=> //=.
  + econstructor.
    + econstructor. econstructor. admit.
    by constructor.
(* Oaddcarry *)
+ move=> w xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi hwf. split=> //=.
  + econstructor.
    + econstructor. econstructor. admit.
    by constructor.
(* Osubcarry *)
+ move=> w xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi hwf. split=> //=.
  + econstructor.
    + econstructor. econstructor. admit.
    by constructor.
move=> [].
(* protect *)
+ move=> w xs es. rewrite /Pi_r /ir_spec1_to_spec2 /=. have hew := eq_globs.
  case: es=> //= e es. case: es=> //= e' es'. case: es'=> //=.
  move=> hop ii envi hwf. case: ifP=> //= hdisj. split=> //=.
  + econstructor. 
    + econstructor. econstructor. admit.
    by constructor.
  rewrite /wf_env in hwf. rewrite /wf_env /=.
  move=> e0 fv s gd henv. move: (hwf e0 fv s gd)=> henvi.
  rewrite /update_cond_env in henv. case: envi.1 henv henvi=> //= -[env1 env2].
  case: ifP=> //= hsub [] h1 h2 []; subst; auto.
(* set_msf *)
+ move=> xs es. rewrite /Pi_r /ir_spec1_to_spec2 /=. have heg := eq_globs. 
  case: es=> //= e es. case: es=> //= e' es'. case: es'=> //=.
  move=> hop ii envi hwf /=. case: ifP=> //=.
  (* e' is not present in msf variables *)
  move=> hdisj. split=> //=.
  + econstructor.
    + econstructor. econstructor. admit.
      by constructor.
    rewrite /wf_env in hwf. rewrite /wf_env /update_cond_env /=.
  move=> e0 fv s gd /=. case: envi.1 hwf=> //= -[env1 env2] hwf. 
  case: ifP=> //= hsub [] h1 h2; subst. 
  move: (hwf e0 fv s gd erefl)=> [] hfv [] hmem [] he hmsf. by split=> //=; auto.
  (* e' is present in msf variables *)
  + move=> hdisj. split=> //=.
    + econstructor. 
      + econstructor. econstructor. rewrite -heg.
        rewrite /sem_sopn /=. rewrite /sem_sopn /= in hop.
        move: hop. t_xrbindP=> vs vs' v he vs1 vs1' he' <- <- /= hop hw. admit.
      by constructor.
    rewrite /wf_env /= in hwf. rewrite /wf_env /=.
    move=> e0 fv s gd. rewrite /update_cond_env /=. case: envi.1 hwf=> //=.
    move=> -[e1 fv1] hwf. case: ifP=> //=.
    move=> hsub [] h1 h2; subst. move: (hwf e0 fv s gd erefl)=> [] hfv [] hmem [] he hmsf; 
    split=> //=; auto. split=> //=. split=> //=. 
    have /= heqe := read_eE e' Sv.empty. have [elm [hd hd']]:= not_disjoint hdisj.
    move: (hmsf elm hd')=> hg'. move=> m hin. have heq := vrvs_recE envi.2 xs.
    rewrite /Sv.Equal in heq. move: (heq m)=> [] heq' heq''. move: (heq' hin)=> {heq'} heq'.
    move: (hmsf m)=> ->. + reflexivity.
    have := SvD.F.union_1 heq'. move=> hdes. case: hdes=> //= hdes.
    admit.
(* init_msf *)
+ move=> xs [] //= hop. rewrite /Pi_r /=. have heg := eq_globs.
  case: s1 hop=> //=. case: s2=> //=.
  move=> ss' m' vm' ss m vm /= hop ii envi hwf /=.
  split=> //=.
  + econstructor.
    + econstructor. econstructor. rewrite -heg. admit.
    by constructor.
  rewrite /wf_env in hwf. rewrite /wf_env /update_cond_env /=.
  case: envi.1 hwf=> //= -[env1 env2] hwf. 
  move=> e fv s gd. case: ifP=> //=.
  move=> hsub [] h1 h2; subst. 
  move: (hwf e fv s gd erefl)=> [] hfv [] hmem [] he hmsf. split=> //=; auto.
  split=> //=. split=> //=. move=> ms hsub'. admit.
(* mov_msf *)
+ move=> xs es hop. rewrite /Pi_r /ir_spec1_to_spec2 /=. have heg := eq_globs.
  case: s1 hop=> //=. case: s2=> //=. move=> ss' m' vm' ss m vm /= hop.
  case: es hop=> //= e es. case: es=> //= hop ii envi hwf.
  case: ifP=> //=.
  (* e not present in X ==> X = X*)
  + move=> hdisj. split=> //=.
    + econstructor.
      + econstructor. econstructor. rewrite -heg /=. admit.
      by constructor.
    rewrite /wf_env in hwf. rewrite /wf_env /update_cond_env /=.
    case: envi.1 hwf=> //= -[env1 env2] hwf. 
    move=> e0 fv s gd. case: ifP=> //=.
    move=> hsub [] h1 h2; subst. move: (hwf e0 fv s gd erefl)=> [] hfv [] hmem [] he hmsf. 
    by split=> //=; auto.
  (* e is present in X ==> X = xs U X *)
  move=> hdisj. split=> //=.
  + econstructor.
    + econstructor. econstructor. rewrite -heg /=. admit.
    by constructor.
  rewrite /wf_env in hwf. rewrite /wf_env /update_cond_env /=.
  case: envi.1 hwf=> //= -[env1 env2] hwf. 
  move=> e0 fv s gd. case: ifP=> //=.
  move=> hsub [] h1 h2; subst. move: (hwf e0 fv s gd erefl)=> [] hfv [] hmem [] he hmsf. 
  split=> //=; auto. split=> //=. split=> //=. move=> m1 hsub'. apply hmsf. admit.
(* oasm *)
move=> a xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
move=> ii envi hwf. econstructor.
+ econstructor.
  + econstructor. econstructor. rewrite -heg. admit.
  by constructor.
by apply hwf.
Admitted.

Lemma env_sem_instr env env' env1 env2 i c c':
i_spec1_to_spec2 env i = ok (env1, c) ->
i_spec1_to_spec2 env' i = ok (env2, c') ->
c = c'.
Proof.
case: i=> //= ii ir. case: ir=> //=.
(* assgn *)
+ move=> l a s e. rewrite /i_spec1_to_spec2 /=.
  by move=> [] henv <- [] _ <-.
(* opn *)
+ move=> l a sop es. rewrite /i_spec1_to_spec2 /=.
  case: sop=> //=.
  + by move=> w pos [] _ <- [] _ <-.
  + by move=> [] _ <- [] _ <-.
  + by move=> w [] _ <- [] _ <-.
  + by move=> w [] _ <- [] _ <-.
  + by move=> w [] _ <- [] _ <-.
  move=> [].
  + move=> w. case: es=> //= e es. case: es=> //= e' es'. case: es'=> //=.
    case: ifP=> //= hdisj [] _ <-. by case: ifP=> //= hdisj' [] _ <-.
  + case: es=> //= e es'. case: es'=> //= e' es'. case: es'=> //=.
    case: ifP=> //= hdisj. move=> [] _ <-. by case: ifP=> //= hdisj' [] _ <-.
  + move=> [] _ <-. by case: ifP=> //= hdisj' [] _ <-.
  + by case: es=> //= [] [] _ <- [] _ <-.
  + case: es=> //= e es. case: es=> //=. case: ifP=> _ [] _ <-. 
    + case: ifP=> //= _. + by move=> [] _ <-. + by move=> [] _ <-.
    by case: ifP=> //= _ [] _ <-.
  + by move=> a0 [] _ <- [] _ <-.
(* syscall *)
+ move=> l s es. rewrite /i_spec1_to_spec2. by move=> [] _ <- [] _ <-.
(* if *)
+ move=> e c1 c2. rewrite /i_spec1_to_spec2 /=. 
  t_xrbindP=> -[env1' c1'] /= hc1 -[env2' c2'] hc2 /= h h1 -[env3 c3'] hc3 -[envc4 c4'] hc4 /= h' h1' /=; subst.
  admit.
(* for *)
+ move=> x [] []. rewrite /i_spec1_to_spec2 /=. 
  t_xrbindP=> d e e' c1 -[env1' c1'] hc /= h h1 -[env1'' c1''] hc' /= h' h1'; subst. admit.
(* while *)
+ move=> a l e es. rewrite /i_spec1_to_spec2. admit.
(* call *)
admit.
Admitted. 

Lemma env_sem_cmd env env' env1 env2 c c1 c1':
c_spec1_to_spec2 i_spec1_to_spec2 env c = ok (env1, c1) ->
c_spec1_to_spec2 i_spec1_to_spec2 env' c = ok (env2, c1') ->
c1 = c1'.
Proof.
move: env env' env1 env2 c1 c1'. elim: c=> //=.
+ by move=> env env' env1 env2 c1' c2' [] _ <- [] _ <-.
move=> i c hrec env env' env1 env2 c1 c1'. 
t_xrbindP=> -[envi ci] hi -[envc cc] /= hc /= h hceq -[envi' ci'] hi' -[envc' cc'] /= hc' h' hceq' /=; subst.
move: (hrec envi envi' env1 env2 cc cc' hc hc')=> ->.
by have -> := env_sem_instr hi hi'.
Qed.

Lemma Hif_true : sem_Ind_if_true (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Proof.
move=> s1 s2 e c1 c2 he hc2 hpc. move=> ii envi hwf. have heg := eq_globs.
rewrite /ir_spec1_to_spec2 -/i_spec1_to_spec2 /=.
move: (hpc envi hwf). case: envi hwf=> //= [env1 env2] hwf.
case heq : c_spec1_to_spec2=> //= [[envc1 c1'] /=|//]. move=> [hc1' hwf1].
case heq' : c_spec1_to_spec2=> //= [[envc2 c2'] /=|//].
case heq'' : c_spec1_to_spec2=> //= [[envc1' c1'']].
rewrite /= in heq''. split=> //=.
+ econstructor. + econstructor. econstructor. by rewrite -heg.
  + admit.
  by econstructor.
rewrite /wf_env /update_cond_env /=. rewrite /wf_env in hwf hwf1.
case: env1 heq heq' heq'' hwf hwf1 => //= -[b fv] heq heq' heq'' hwf hwf1.
move=> e0 fv0 s gd. case: ifP=> //=.
move=> hsub [] h1 h2; subst. move: (hwf e0 fv0 s gd erefl)=> [] hfv0 [] hmem [] he0 hmsf.
split=> //=. split=> //=. split=> //=. rewrite /= in heq''.
move=> m hsub'. move: (hwf1 e0 fv0 s gd)=> {hwf1} hwf1. apply hwf1.
Admitted.

Lemma Hif_false : sem_Ind_if_false (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Proof.
move=> s1 s2 e c1 c2 he hc2 hpc. move=> ii envi hwf. have heg := eq_globs.
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
  by constructor.
rewrite /wf_env /update_cond_env /=. rewrite /wf_env in hwf hwf1.
case: env1 heq heq' heq'' hwf hwf1 => //= -[b fv] heq heq' heq'' hwf hwf1.
move=> e0 fv0 s gd. case: ifP=> //=.
move=> hsub [] h1 h2; subst. move: (hwf e0 fv0 s gd erefl)=> [] hfv0 [] hmem [] he0 hmsf.
split=> //=. split=> //=. split=> //=. rewrite /= in heq''.
move=> m hsub'. move: (hwf1 e0 fv0 s gd)=> {hwf1} hwf1. apply hwf1.
Admitted.

Lemma Hwhile_true : sem_Ind_while_true (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Admitted.

Lemma Hwhile_false : sem_Ind_while_false (spp := spp_of_asm_op_spec1) p ev Pc Pi_r.
Admitted.

Lemma Hfor : sem_Ind_for (spp := spp_of_asm_op_spec1) p ev Pi_r Pfor.
Admitted.

