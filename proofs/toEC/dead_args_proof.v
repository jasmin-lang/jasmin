(* * Correctness of the pass dead_args.

   The pass removes dead code, the parameters that a body does not read and
   the results that no caller uses. [dead_args_info] gives, for each function
   of the source, the positions of its parameters and of its results that are
   kept ([keep_only]). The transformed program computes the same results as
   the source, but those removed, from the same arguments, but those removed:
   the removed arguments are not read, and the removed results are not used.

   The correctness is stated from the transformed program to the source, the
   direction the extraction for safety needs. As for [dead_code]
   ([dead_code_total_proof]), it needs the removed code not to fail
   ([total_ok], the well-typedness of the source), and the source to accept
   the removed arguments: they have the types of the parameters. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import compiler_util psem psem_facts.
Require Import dead_code dead_args dead_code_total_proof.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Section DEFS.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}.

Context (info : keep_info).

(* The positions kept; all for a function absent from [info]. *)
Definition kparams (fn : funname) : seq bool :=
  if get_fundef info fn is Some k then k.1 else [::].

Definition kres (fn : funname) : seq bool :=
  if get_fundef info fn is Some k then k.2 else [::].

Definition fs_keep (k : seq bool) (fs : fstate) : fstate :=
  {| fscs := fscs fs; fmem := fmem fs; fvals := keep_only (fvals fs) k |}.

(* The arguments given to the source are those given to the transformed
   program, the removed ones being values of the types of the parameters. *)
Definition dead_args_tgt_src_spec (p : uprog) : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 =>
       [/\ fn1 = fn2, fs1 = fs_keep (kparams fn1) fs2 &
           forall fd, get_fundef (p_funcs p) fn1 = Some fd ->
             is_ok (mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) (fvals fs2))];
     rpostF_ := fun fn1 _ _ _ fr1 fr2 => fr1 = fs_keep (kres fn1) fr2 |}.

End DEFS.

Section COMMON.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}.

(* ** The positions kept *)

Lemma keep_only_nseq {T : Type} (l : seq T) n : size l <= n -> keep_only l (nseq n true) = l.
Proof.
elim: n l => [ | n ih] [ | x l] //= hs.
by rewrite ih.
Qed.

Lemma size_keep_compose k k' : size (keep_compose k k') = size k.
Proof.
elim: k k' => [ | [] k ih] [ | b k'] //=; by rewrite ih.
Qed.

Lemma keep_only_compose {T : Type} (l : seq T) k k' :
  size l <= size k -> keep_only (keep_only l k) k' = keep_only l (keep_compose k k').
Proof.
have h0 : forall m, keep_only (@nil T) m = [::] by case.
elim: k k' l => [ | b k ih] k' [ | x l] //=; rewrite ?h0 //.
rewrite ltnS => hs; case: b; last by rewrite /= ih.
case: k' => [ | b' k'] /=; first by rewrite -ih.
by case: b'; rewrite ih.
Qed.

Lemma Forall2_keep_only {A B : Type} (R : A -> B -> Prop) xs ys k :
  List.Forall2 R xs ys -> List.Forall2 R (keep_only xs k) (keep_only ys k).
Proof.
elim: k xs ys => // b k ih xs ys [ | x y {}xs {}ys hxy hxys] /=; first by constructor.
by case: b; [constructor => //; apply: ih | apply: ih].
Qed.

Lemma mapM_keep_only {A B E : Type} (f : A -> result E B) l vs k :
  mapM f l = ok vs -> mapM f (keep_only l k) = ok (keep_only vs k).
Proof.
elim: k l vs => // b k ih [ | x l] vs /=; first by move=> [<-].
t_xrbindP => v hv vs1 /ih{}ih <-.
by case: b => //=; rewrite hv /= ih.
Qed.

(* The source writes all the parameters, the transformed program those kept:
   the states agree on the variables [I] that contain no removed one. *)
Lemma write_vars_keep_only wdb I (xs : seq var_i) k vs t s t' s' :
  (forall b x, List.In (b, x) (zip k xs) -> ~~ b -> ~ Sv.In (v_var x) I) ->
  [/\ escs t = escs s, emem t = emem s & evm t =[I] evm s] ->
  write_vars wdb (keep_only xs k) (keep_only vs k) t = ok t' ->
  write_vars wdb xs vs s = ok s' ->
  [/\ escs t' = escs s', emem t' = emem s' & evm t' =[I] evm s'].
Proof.
have hset : forall vm1 vm2 (y : var) w, vm1 =[I] vm2 -> vm1.[y <- w] =[I] vm2.[y <- w].
+ by move=> vm1 vm2 y w h z hz; rewrite !Vm.setP; case: eqP => // _; apply: h.
have hdead : forall vm1 vm2 (y : var) w, ~ Sv.In y I -> vm1 =[I] vm2 -> vm1 =[I] vm2.[y <- w].
+ by move=> vm1 vm2 y w hy h z hz; rewrite Vm.setP_neq; [apply: h | apply/eqP => ?; subst z].
elim: xs k vs t s => [ | x xs ih] [ | b k] [ | v vs] t s //=.
1,2: by move=> _ ? [<-] [<-].
+ move=> _ [h1 h2 h3]; t_xrbindP => t1 /write_varP [-> _ _] ht s1 /write_varP [-> _ _] hs.
  apply: (ih [::] vs _ _ _ _ ht hs) => //=.
  + by case: (xs) => [ | ??] ?? /=.
  by split => //; apply: hset.
move=> hX [h1 h2 h3]; case: b hX => hX /=; t_xrbindP.
+ move=> _ /write_varP [-> _ _] ht _ /write_varP [-> _ _] hs.
  apply: (ih k vs _ _ _ _ ht hs); first by move=> b y hy; apply: hX; right.
  by split => //; apply: hset.
move=> ht _ /write_varP [-> _ _] hs.
apply: (ih k vs _ _ _ _ ht hs); first by move=> b y hy; apply: hX; right.
by split => //; apply: hdead h3; apply: (hX false) => //; left.
Qed.

(* Parameters that each accept the values of their types, on every state,
   accept them in sequence. *)
Lemma total_ok_write_vars (xs : seq var_i) tys vs vs' :
  List.Forall2 (fun x ty =>
      forall s v v', dc_truncate_val ty v = ok v' -> is_ok (write_var true x v' s)) xs tys ->
  mapM2 ErrType dc_truncate_val tys vs = ok vs' ->
  forall s, is_ok (write_vars true xs vs' s).
Proof.
move=> h; elim: h vs vs' => {xs tys} [ | x ty xs tys hx _ ih] [ | v vs] vs' //=; first by move=> [<-].
t_xrbindP => v' hv vs1 /ih{}ih <- s.
case: (write_var _ _ _ s) (hx s _ _ hv) => //= s1 _; apply: ih.
Qed.

(* The destinations that [check_keep_only] keeps. *)
Lemma check_keep_only_keep xs tokeep O I xs' :
  check_keep_only xs tokeep O = ok (I, xs') -> xs' = keep_only xs tokeep.
Proof.
elim: tokeep xs I xs' => [ | b tokeep ih] [ | x xs] I xs' //=; first by move=> [_ <-].
case heq: check_keep_only => [[s1 xs1] | ] //=; rewrite (ih _ _ _ heq).
by case: b => [[_ <-] | ]; [ | case: ifP => // _ [_ <-]].
Qed.

Lemma total_ok_cP' (pp : uprog) c :
  (forall i, List.In i c -> total_ok_i pp i) ->
  (fix total_ok_c (c : cmd) : Prop :=
     if c is i :: c then total_ok_i pp i /\ total_ok_c c else True) c.
Proof. by elim: c => //= i c ih h; split; [apply: h; left | apply: ih => j hj; apply: h; right]. Qed.

End COMMON.

(* ** A round

   A round removes, from [q], the parameters that [kp] tells dead and the
   matching arguments, then runs [dead_code] with the results that [kr] tells
   dead. When it checks that the removed parameters are not live at the entry
   of the bodies, the transformed program [p2] runs as [q], from the same
   arguments but those removed, with the same results but those removed. The
   proof is that of [dead_code] ([dc_tgt_src_body]), where the source passes
   more arguments at the calls; the removed parameters, written by the source
   only, are not live. *)

Section ROUND.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
  {LC : LoopCounter} {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

#[local] Existing Instance withassert_nocontract.

Context (kp kr : funname -> option (seq bool)) (q p2 : uprog) (ev : extra_val_t).

Hypothesis hdc :
  dead_code_prog_tokeep (fun _ => false) (fun _ fi => fi) false kr
    (map_prog_name (rm_params_fd kp) q) = ok p2.

Notation dc_i := (dead_code_i (fun _ => false) false kr).
Notation dc_fd := (dead_code_fd (fun _ => false) (fun _ fi => fi) false kr).
Notation rm_i := (rm_args_i kp).

Lemma da_globs : p_globs p2 = p_globs q.
Proof using hdc. by rewrite (dc_globs hdc). Qed.

Lemma da_get fn fd2 :
  get_fundef (p_funcs p2) fn = Some fd2 ->
  exists2 fd, get_fundef (p_funcs q) fn = Some fd & dc_fd fn (rm_params_fd kp fn fd) = ok fd2.
Proof using hdc.
move=> /(get_map_cfprog_name_gen' (dc_funcs hdc)) [fd1 hfd1].
by rewrite get_map_prog_name; case: get_fundef => // fd [?]; subst fd1; exists fd.
Qed.

Lemma da_get_src fn fd :
  get_fundef (p_funcs q) fn = Some fd ->
  exists2 fd2, get_fundef (p_funcs p2) fn = Some fd2 & dc_fd fn (rm_params_fd kp fn fd) = ok fd2.
Proof using hdc.
move=> hget; have := get_map_cfprog_name_gen (dc_funcs hdc) (fn := fn) (f := rm_params_fd kp fn fd).
by rewrite get_map_prog_name hget => /(_ erefl) [fd2 ??]; exists fd2.
Qed.

(* The arguments given to the source are those given to the transformed
   program, plus those of the removed parameters, of their types; the results
   are as for [dead_code] ([dc_ts_spec]). *)
Definition da_round_spec : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 =>
       [/\ fn1 = fn2, fs1 = dc_keep_res kp fn1 fs2 &
           forall fd, get_fundef (p_funcs q) fn1 = Some fd ->
             is_ok (mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) (fvals fs2))];
     rpostF_ := fun fn1 _ _ _ fr1 fr2 =>
       fr1 = dc_keep_res kr fn1 fr2 /\
       exists2 fd, get_fundef (p_funcs q) fn1 = Some fd &
         exists vs,
           mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyout)) vs = ok (fvals fr2) |}.

Section TGT_SRC.

Context {sm : SemMode} (hsm : is_total (sm := sm)) (hok : total_ok q).

Let Qi (i : instr) :=
  total_ok_i q i ->
  forall I c' O, dc_i (rm_i i) O = ok (I, c') ->
  wequiv_rec (sm1 := sm) (sm2 := sm) p2 q ev ev da_round_spec (st_dc I) c' [:: i] (st_dc O).

Let Qi_r (i : instr_r) := forall ii, Qi (MkI ii i).

Let Qc (c : cmd) :=
  (forall i, List.In i c -> total_ok_i q i) ->
  forall I c' O, dead_code_c dc_i (map rm_i c) O = ok (I, c') ->
  wequiv_rec (sm1 := sm) (sm2 := sm) p2 q ev ev da_round_spec (st_dc I) c' c (st_dc O).

Lemma da_tgt_src_body c : Qc c.
Proof using hdc hsm.
have hg := da_globs.
have hcu := checker_st_dcP hsm hg.
move: c; apply (cmd_rect (Pr := Qi_r) (Pi := Qi) (Pc := Qc)) => //; rewrite /Qi_r /Qi /Qc.
+ by move=> _ _ _ O [<- <-]; apply wequiv_nil.
+ move=> i c hi hc hok' I c_ O /=.
  t_xrbindP => -[R c'] /(hc (fun j hj => hok' j (or_intror hj))){}hc [I' i'].
  move=> /(hi (hok' i (or_introl erefl))){}hi /= ??; subst I' c_.
  by rewrite -cat1s; apply wequiv_cat with (st_dc R).
+ move=> x tg ty e ii /= hoki I c' O.
  have hkeep : wequiv_rec (sm1 := sm) (sm2 := sm) p2 q ev ev da_round_spec
    (st_dc (read_rv_rec (read_e_rec (Sv.diff O (vrv x)) e) x))
    [:: MkI ii (Cassgn x tg ty e)] [:: MkI ii (Cassgn x tg ty e)] (st_dc O).
  + apply wequiv_assgn_rel_eq with checker_st_dc
      (read_rv_rec (read_e_rec (Sv.diff O (vrv x)) e) x) => //=.
    + by split => //; rewrite /read_es /= read_rvE !read_eE; SvD.fsetdec.
    by split => //; rewrite /read_rvs /vrvs /= !read_rvE ?read_eE; SvD.fsetdec.
  rewrite write_i_assgn; case: ifP => _; last by move=> [<- <-].
  case: ifP => hrm; last by move=> [<- <-].
  move=> [<- <-]; apply wequiv_assign_right => t s hts.
  case hs: (sem_assgn (sm := sm) q x tg ty e s) => [s' | err]; last first.
  + by have := hoki s; rewrite -(sem_assgn_total_sm _ _ _ _ _ _ hsm) hs.
  exists s' => //.
  case/orP: hrm => [/andP [hd hnm] | /andP [_ hnop]]; last exact: st_dc_nop hsm hnop hts hs.
  by move: hs; rewrite /sem_assgn; t_xrbindP => v _ v' _; apply: st_dc_dead hd hnm hts.
+ move=> xs tg o es ii /= hoki I c' O.
  have hkeep : wequiv_rec (sm1 := sm) (sm2 := sm) p2 q ev ev da_round_spec
    (st_dc (read_es_rec (read_rvs_rec (Sv.diff O (vrvs xs)) xs) es))
    [:: MkI ii (Copn xs tg o es)] [:: MkI ii (Copn xs tg o es)] (st_dc O).
  + apply wequiv_opn_rel_eq with checker_st_dc
      (read_es_rec (read_rvs_rec (Sv.diff O (vrvs xs)) xs) es) => //=.
    + by split => //; rewrite read_esE read_rvsE; SvD.fsetdec.
    by split => //; rewrite read_esE read_rvsE; SvD.fsetdec.
  have -> : check_nop_opn (fun _ => false) xs o es = false.
  + by move: (xs) (o) (es) => [ | x [ | ??]] [] // ? [ | ? [ | ??]].
  case: ifP => _; last by move=> [<- <-].
  case: ifP => hrm; last by move=> [<- <-].
  move=> [<- <-]; apply wequiv_opn_right => t s hts.
  case hs: (sem_sopn (sm := sm) (p_globs q) o s xs es) => [s' | err]; last first.
  + by have := sem_sopn_total_ok hsm (hoki s); rewrite hs.
  exists s' => //; move: hs hrm; rewrite /sem_sopn; t_xrbindP => vs vs' _ _ hw /andP [hd hnm].
  exact: st_dc_deads hd hnm hts hw.
+ move=> xs o es ii _ I c' O /= [<- <-].
  set X := read_es_rec _ es.
  apply wequiv_syscall_rel_eq_core with checker_st_dc X => //=.
  + by split => //; rewrite /X read_esE read_rvsE; SvD.fsetdec.
  + by split => //; rewrite /X read_esE read_rvsE; SvD.fsetdec.
  exact: wrequiv_eq.
+ move=> a ii _ I c' O /= [<- <-].
  apply wequiv_assert => _; split => // t s hts; rewrite hg => ha; split.
  + by apply: st_dc_eassert hts ha; rewrite read_eassertE; SvD.fsetdec.
  by apply: st_dc_sub hts; rewrite read_eassertE; SvD.fsetdec.
+ move=> e c1 c2 hc1 hc2 ii /= [/total_ok_cP /hc1{}hc1 /total_ok_cP /hc2{}hc2] I c' O; t_xrbindP.
  move=> [I1 c1'] /hc1{}hc1 [I2 c2'] /hc2{}hc2 [??]; subst I c'.
  apply wequiv_if_rel_eq with checker_st_dc (read_e_rec (Sv.union I1 I2) e) O O => //=.
  + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
  + apply wequiv_weaken with (st_dc I1) (st_dc O) => //.
    by move=> ??; apply: st_dc_sub; rewrite read_eE; SvD.fsetdec.
  apply wequiv_weaken with (st_dc I2) (st_dc O) => //.
  by move=> ??; apply: st_dc_sub; rewrite read_eE; SvD.fsetdec.
+ move=> x dir lo hi c hc ii /= /total_ok_cP /hc{}hc I c_ O.
  case Hloop: loop => [[sv1 sc1] /=|//] [??]; subst I c_.
  have [H1 [sv2 [/hc{}hc H2']]] := dead_code_proof.loopP Hloop.
  apply wequiv_weaken with (st_dc (read_e_rec (read_e_rec sv1 hi) lo)) (st_dc sv1) => //.
  + by move=> ??; apply: st_dc_sub.
  apply wequiv_for_rel_eq with checker_st_dc (read_e_rec (read_e_rec sv1 hi) lo) sv2 => //.
  + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
  + by move=> ??; apply: vm_dc_sub; rewrite !read_eE; SvD.fsetdec.
  by split => //; rewrite /vrvs /read_rvs /=; SvD.fsetdec.
+ move=> a c1 e ii' c2 hc1 hc2 ii /= [/total_ok_cP /hc1{}hc1 /total_ok_cP /hc2{}hc2] I c_ O.
  set dobody := (X in wloop X).
  case Hloop: wloop => [[sv1 [c1' c2']] /=|//] [??]; subst sv1 c_.
  have [sv2 [sv2' [H1 [heq H2]]]] := dead_code_proof.wloopP Hloop.
  move: (heq); rewrite /dobody; t_xrbindP.
  move=> [Ic1 c1_] /hc1{}hc1.
  case heq1 : dead_code_c => [[Ic2 c2_]/= | //] [????]; subst sv2' Ic1 c1_ c2_.
  have {}hc2 := hc2 _ _ _ heq1.
  apply wequiv_weaken with (st_dc I) (st_dc (read_e_rec sv2 e)) => //.
  + by move=> ??; apply: st_dc_sub; rewrite read_eE; SvD.fsetdec.
  apply wequiv_while_rel_eq with checker_st_dc (read_e_rec sv2 e) => //.
  + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
  apply wequiv_weaken with (st_dc Ic2) (st_dc I) => //.
  by move=> ??; apply: st_dc_sub; rewrite read_eE; SvD.fsetdec.
move=> xs f es ii hoki I_ c_ O /=.
set sxs := (X in Let sxs := X in _).
case heq: sxs => [[I xs'] | ] //= [??]; subst c_ I_.
(* The source evaluates all the arguments, of the types of the parameters. *)
have hes : forall s, exists2 vs, sem_pexprs (sm := sm) true (p_globs q) s es = ok vs &
  forall fd, get_fundef (p_funcs q) f = Some fd ->
    is_ok (mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) vs).
+ move=> s; rewrite (sem_pexprs_is_totalE _ (sm1 := sm) (sm2 := total)) ?hsm //.
  move: hoki => /=; case: get_fundef => [fd [/(_ s) + _] | /(_ s)].
  + by case: sem_pexprs => //= vs h; exists vs => // _ [<-].
  by case: sem_pexprs => // vs _; exists vs.
apply wequiv_call_wa with (Pf := rpreF (eS := da_round_spec)) (Qf := rpostF (eS := da_round_spec))
  (Rv := fun vs1 vs2 => vs1 = fn_keep_only kp f vs2 /\
     forall fd, get_fundef (p_funcs q) f = Some fd ->
       is_ok (mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) vs2)).
+ rewrite hg => t s vs1 [_ hmem [heq' _]] h.
  have [vs2 hvs2 htr] := hes s; exists vs2 => //; split => //.
  have : sem_pexprs (sm := sm) true (p_globs q) s (fn_keep_only kp f es) = ok vs1.
  + rewrite -h; symmetry; apply: eq_on_sem_pexprs => //; apply: eq_on_total_sm hsm (eq_onI _ heq').
    by rewrite read_esE; SvD.fsetdec.
  rewrite /fn_keep_only; case: (kp f) => [k | ]; last by rewrite hvs2 => -[].
  by rewrite /sem_pexprs (mapM_keep_only _ hvs2) => -[].
+ by [].
+ by move=> t s vs1 vs2 [hscs hmem _] [-> htr]; split => //; rewrite /mk_fstate /dc_keep_res hscs hmem.
+ by [].
+ exact: (@wequiv_fun_rec _ _ _ _ _ _ _ _ _ _ p2 q ev ev da_round_spec ii ii f f).
move=> fs1 fs2 fr1 fr2 _ /= [-> [fd hfd [vs htr]]].
rewrite hg /upd_estate => t s t' [hscs hmem hvm] /= hw.
set t1 := with_scs (with_mem t (fmem fr2)) (fscs fr2).
set s1 := with_scs (with_mem s (fmem fr2)) (fscs fr2).
have hts : st_dc I t1 s1.
+ by split => //=; apply: vm_dc_sub hvm; rewrite read_esE; SvD.fsetdec.
move: heq hw; rewrite /sxs /fn_keep_only; case: (kr f) => [tokeep | [??]]; last first.
+ subst I xs' => hw.
  have [ | s' -> hst'] := st_dc_writes hsm _ hts hw; first by rewrite read_rvsE; SvD.fsetdec.
  by exists s' => //; apply: st_dc_sub hst'; rewrite read_rvsE; SvD.fsetdec.
move=> hc hw.
have {}hc : check_keep_only xs tokeep O = ok (I, xs').
+ by move: hc; rewrite /add_iinfo; case: check_keep_only => // ? [->].
move: hoki; rewrite /= hfd => -[_ /total_ok_writes /(_ htr s1)].
rewrite -(write_lvals_is_totalE _ _ _ _ _ (sm1 := sm) (sm2 := total)) ?hsm //.
case hws: write_lvals => [s' | ] // _; exists s' => //.
have [ | | | t'' hw' hR] := check_keep_onlyP (R := fun X a b => st_dc X b a) _ _ _ hc hts hws.
+ by move=> X X' a b hsub; apply: st_dc_sub.
+ by move=> X x v a b a' hsub h1 h2; apply: st_dc_write_rev hsm hsub h1 h2.
+ by move=> X x v a b a' hd hnm h1 h2; apply: st_dc_dead hd hnm h1 h2.
by move: hw'; rewrite /t1 hw => -[->].
Qed.
Hypothesis hcheck :
  forall fn fd, get_fundef (p_funcs q) fn = Some fd -> check_params kp kr fn fd = ok tt.

Lemma da_tgt_src_callP fn :
  wiequiv_f (sm1 := sm) (sm2 := sm) p2 q ev ev (rpreF (eS := da_round_spec)) fn fn
    (rpostF (eS := da_round_spec)).
Proof using hcheck hdc hok hsm.
apply wequiv_fun_ind_wa => {}fn _ fs1 fs [<- -> htr] fd2 hget2.
have [fd hget hfd] := da_get hget2.
exists fd => // _; split => // t hinit.
have [[hpar hres] hokb] := hok hget.
move: hfd hinit; rewrite /dead_code_fd; t_xrbindP => -[I c'] hc ? hinit; subst fd2.
move: hinit; rewrite /initialize_funcall; t_xrbindP => vargs1 htr1 s0 hs0 hw1.
move: htr1 hs0 hw1 => /= htr1 hs0 hw1.
move: (htr _ hget); case htrs: mapM2 => [vargs | ] // _.
case: hs0 => ?; subst s0.
have := total_ok_write_vars hpar htrs (estate0 fs); case hws: write_vars => [s | ] // _.
exists s; first exact: hws.
have hk : forall T (l : seq T), fn_keep_only kp fn l = keep_only l (odflt [::] (kp fn)).
+ by move=> T l; rewrite /fn_keep_only; case: (kp fn).
rewrite !hk map_keep_only (mapM2_keep_only _ htrs) in htr1.
case: htr1 => ?; subst vargs1.
(* The removed parameters are not live at the entry of the body. *)
have hrm : forall b x, List.In (b, x) (zip (odflt [::] (kp fn)) (f_params fd)) ->
  ~~ b -> ~ Sv.In (v_var x) I.
+ move: (hcheck hget); rewrite /check_params; case: (kp fn) => [k | ] /=; last by case: (f_params fd).
  move: hc => /= -> /=; t_xrbindP.
  elim: zip => //= -[b' y] l ih /andP [h1 h2] b x [[<- <-] | /(ih h2)] // hb.
  by move: h1; rewrite (negbTE hb) /= => /Sv_memP.
rewrite hk in hw1.
have [hscs hmem heqI] := write_vars_keep_only hrm (And3 erefl erefl (fun _ _ => erefl)) hw1 hws.
exists (st_dc I), (st_dc (read_es [seq Plvar i | i <- fn_keep_only kr fn (f_res fd)])).
split => //=.
+ split => //; split => y hy; first by apply: (Vm.get_eq_mode erefl); apply: heqI.
  by rewrite /is_var_init heqI.
+ exact: da_tgt_src_body hokb _ _ _ hc.
move=> t' s' fr1 [hscs' hmem' [heq _]]; rewrite /finalize_funcall /=.
t_xrbindP => vres1 hget1 vres1' htr1 <-.
have hgv : forall vm (xs : seq var_i),
  get_var_is (sm := sm) true vm xs = get_var_is (sm := total) true vm xs.
+ move=> vm; elim => //= x xs ->.
  by rewrite (get_var_is_totalE (sm1 := sm) (sm2 := total)) ?hsm.
move: (hres s'); rewrite -hgv.
case hgs: get_var_is => [vres | ] //=; case htrs': mapM2 => [vres' | ] //= _.
eexists; first reflexivity.
split; last by exists fd => //; exists vres.
rewrite (get_var_is_eq_on _ _ (eq_on_total_sm hsm heq)) in hget1; last by rewrite vars_l_read_es.
rewrite /dc_keep_res /= hscs' hmem'; move: hget1 htr1; rewrite /fn_keep_only.
case: (kr fn) => [tokeep | ]; last by rewrite hgs => -[<-]; rewrite htrs' => -[<-].
rewrite (get_var_is_keep_only _ hgs) => -[<-].
by rewrite map_keep_only (mapM2_keep_only _ htrs') => -[<-].
Qed.

End TGT_SRC.

(* [dead_args] keeps the well-typedness. *)

Let Ti (i : instr) :=
  total_ok_i q i ->
  forall I c' O, dc_i (rm_i i) O = ok (I, c') -> forall j, List.In j c' -> total_ok_i p2 j.

Let Ti_r (i : instr_r) := forall ii, Ti (MkI ii i).

Let Tc (c : cmd) :=
  (forall i, List.In i c -> total_ok_i q i) ->
  forall I c' O, dead_code_c dc_i (map rm_i c) O = ok (I, c') ->
  forall j, List.In j c' -> total_ok_i p2 j.

Lemma da_total_ok_body c : Tc c.
Proof using hdc.
have hg := da_globs.
move: c; apply (cmd_rect (Pr := Ti_r) (Pi := Ti) (Pc := Tc)) => //; rewrite /Ti_r /Ti /Tc.
+ by move=> _ _ _ O [_ <-].
+ move=> i c hi hc hok' I c_ O /=.
  t_xrbindP => -[R c'] /(hc (fun j hj => hok' j (or_intror hj))){}hc [I' i'].
  move=> /(hi (hok' i (or_introl erefl))){}hi /= ??; subst I' c_.
  by move=> j /(@List.in_app_or _ _ _ j) [/hi | /hc].
+ move=> x tg ty e ii /= hoki I c' O.
  have h : total_ok_i p2 (MkI ii (Cassgn x tg ty e)).
  + by move=> s /=; have := hoki s; rewrite /sem_assgn hg.
  by repeat case: ifP => _; move=> [_ <-] j //= [<- | []].
+ move=> xs tg o es ii /= hoki I c' O.
  have h : total_ok_i p2 (MkI ii (Copn xs tg o es)) by move=> s /=; rewrite hg.
  by repeat case: ifP => _; move=> [_ <-] j //= [<- | []].
+ by move=> xs o es ii _ I c' O /= [_ <-] j [<- | []].
+ by move=> a ii _ I c' O /= [_ <-] j [<- | []].
+ move=> e c1 c2 hc1 hc2 ii /= [/total_ok_cP /hc1{}hc1 /total_ok_cP /hc2{}hc2] I c' O; t_xrbindP.
  move=> [I1 c1'] /hc1{}hc1 [I2 c2'] /hc2{}hc2 [_ <-] j [<- | []] //=.
  by split; apply: total_ok_cP'.
+ move=> x dir lo hi c hc ii /= /total_ok_cP /hc{}hc I c_ O.
  case Hloop: loop => [[sv1 sc1] /=|//] [_ <-] j [<- | []] //=.
  have [_ [sv2 [/hc{}hc _]]] := dead_code_proof.loopP Hloop.
  exact: total_ok_cP'.
+ move=> a c1 e ii' c2 hc1 hc2 ii /= [/total_ok_cP /hc1{}hc1 /total_ok_cP /hc2{}hc2] I c_ O.
  set dobody := (X in wloop X).
  case Hloop: wloop => [[sv1 [c1' c2']] /=|//] [_ <-] j [<- | []] //=.
  have [sv2 [sv2' [_ [heq _]]]] := dead_code_proof.wloopP Hloop.
  move: heq; rewrite /dobody; t_xrbindP => -[Ic1 c1_] /hc1{}hc1.
  case heq1 : dead_code_c => [[Ic2 c2_]/= | //] [????]; subst sv2' Ic1 c1_ c2_.
  by split; apply: total_ok_cP' => //; apply: hc2 heq1.
move=> xs f es ii hoki I_ c_ O /=.
set sxs := (X in Let sxs := X in _).
case heq: sxs => [[I xs'] | ] //= [_ <-] j [<- | []] //=.
have -> : xs' = fn_keep_only kr f xs.
+ move: heq; rewrite /sxs /fn_keep_only; case: (kr f) => [tokeep | [_ ->]] //.
  rewrite /add_iinfo; case h: check_keep_only => [[??] | ] // [??]; subst.
  exact: check_keep_only_keep h.
have hk : forall T (l : seq T) (g : funname -> option (seq bool)),
  fn_keep_only g f l = keep_only l (odflt [::] (g f)).
+ by move=> T l g; rewrite /fn_keep_only; case: (g f).
rewrite hg !hk; move: hoki => /=; case hq: get_fundef => [fd | ].
+ have [fd2 -> hfd2] := da_get_src hq.
  move: hfd2; rewrite /dead_code_fd; t_xrbindP => _ _ <- /= [hargs hdst]; rewrite !hk.
  rewrite !map_keep_only; split; last exact: Forall2_keep_only.
  move=> s; have := hargs s; case hes: sem_pexprs => [vs | ] //=.
  case htr: mapM2 => [vs' | ] //= _.
  by rewrite /sem_pexprs (mapM_keep_only _ hes) /= (mapM2_keep_only _ htr).
case hp2: get_fundef => [fd2 | ]; first by have [? ] := da_get hp2; rewrite hq.
move=> h s; have := h s; case hes: sem_pexprs => [vs | ] // _.
by rewrite /sem_pexprs (mapM_keep_only _ hes).
Qed.

Lemma da_total_ok : total_ok q -> total_ok p2.
Proof using hdc.
move=> hok fn fd2 /da_get [fd hget]; rewrite /dead_code_fd; t_xrbindP => -[I c'] hc <-.
have [[hpar hres] hokb] := hok _ _ hget.
have hk : forall T (l : seq T) g, fn_keep_only g fn l = keep_only l (odflt [::] (g fn)).
+ by move=> T l g; rewrite /fn_keep_only; case: (g fn).
split; [split | ] => /=.
+ by rewrite !hk map_keep_only; apply: Forall2_keep_only.
+ move=> s; have := hres s; case hgs: get_var_is => [vres | ] //=.
  case htr: mapM2 => [vres' | ] //= _.
  by rewrite !hk (get_var_is_keep_only _ hgs) /= map_keep_only (mapM2_keep_only _ htr).
exact: da_total_ok_body hokb _ _ _ hc.
Qed.

End ROUND.

(* ** The rounds

   The rounds compose by transitivity: the source of each round is related to
   [p], with the positions that [info] keeps, composed with [keep_compose]. *)

Section COMPOSE.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
  {LC : LoopCounter} {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
  {rE_trans : EventRels_trans rE rE rE}.

#[local] Existing Instance withassert_nocontract.

Context (protect : funname -> var -> bool)
  (dead_info : _uprog -> funname -> option (seq bool) * option (seq bool))
  (p : uprog) (ev : extra_val_t) (hok : total_ok p).

Lemma kparams_update kp kr info fn :
  kparams (update_info kp kr info) fn = keep_update (kparams info fn) (kp fn).
Proof.
rewrite /kparams /update_info /get_fundef assoc_mapE; last by move=> ? [].
by case: assoc => //=; case: (kp fn).
Qed.

Lemma kres_update kp kr info fn :
  kres (update_info kp kr info) fn = keep_update (kres info fn) (kr fn).
Proof.
rewrite /kres /update_info /get_fundef assoc_mapE; last by move=> ? [].
by case: assoc => //=; case: (kr fn).
Qed.

Lemma fs_keep_update K (g : funname -> option (seq bool)) fn fs :
  size (fvals fs) <= size K ->
  fs_keep (keep_update K (g fn)) fs = dc_keep_res g fn (fs_keep K fs).
Proof.
move=> hs; rewrite /fs_keep /dc_keep_res /fn_keep_only /=.
by case: (g fn) => //= k; rewrite keep_only_compose.
Qed.

Lemma fs_keep_nseq n fs : size (fvals fs) <= n -> fs_keep (nseq n true) fs = fs.
Proof. by move=> hs; rewrite /fs_keep keep_only_nseq //; case: fs {hs}. Qed.

(* A well-typed function has as many results as result types. *)
Lemma total_ok_fd_size fd (s : estate) : total_ok_fd fd -> size (f_res fd) = size (f_tyout fd).
Proof.
move=> [_ /(_ s)].
case h: get_var_is => [vs | ] //=; case h2: mapM2 => [vs' | ] //= _.
have [h3 _] := size_mapM2 h2; rewrite size_map in h3.
by rewrite h3 (size_mapM h).
Qed.

(* As [dead_args_tgt_src_spec], and the results of the source have the types
   of the results of its function. *)
Definition da_spec (info : keep_info) : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 =>
       [/\ fn1 = fn2, fs1 = fs_keep (kparams info fn1) fs2 &
           forall fd, get_fundef (p_funcs p) fn1 = Some fd ->
             is_ok (mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) (fvals fs2))];
     rpostF_ := fun fn1 _ _ _ fr1 fr2 =>
       fr1 = fs_keep (kres info fn1) fr2 /\
       exists2 fd, get_fundef (p_funcs p) fn1 = Some fd &
         exists vs,
           mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyout)) vs = ok (fvals fr2) |}.

(* What the rounds keep: [q] has the functions of [p], with the parameters
   that [info] keeps. *)
Definition da_names (q : uprog) :=
  forall fn, get_fundef (p_funcs q) fn = None <-> get_fundef (p_funcs p) fn = None.

Definition da_keep (q : uprog) (info : keep_info) :=
  forall fn fd, get_fundef (p_funcs p) fn = Some fd ->
    exists2 k, get_fundef info fn = Some k &
      [/\ size k.1 = size (f_params fd), size k.2 = size (f_res fd) &
          forall fdq, get_fundef (p_funcs q) fn = Some fdq ->
            f_tyin fdq = keep_only (f_tyin fd) k.1].

Definition da_rel (q : uprog) (info : keep_info) :=
  forall fn,
    wiequiv_f (sm1 := total_init) (sm2 := total_init) q p ev ev
      (rpreF (eS := da_spec info)) fn fn (rpostF (eS := da_spec info)).

Lemma dead_args_roundP (q p2 : uprog) ch kp kr :
  dead_args_round protect dead_info q = ok (p2, ch, kp, kr) ->
  dead_code_prog_tokeep (fun _ => false) (fun _ fi => fi) false kr
    (map_prog_name (rm_params_fd kp) q) = ok p2 /\
  forall fn fd, get_fundef (p_funcs q) fn = Some fd -> check_params kp kr fn fd = ok tt.
Proof.
rewrite /dead_args_round; t_xrbindP.
move=> p2' hdc hall ? _ ? ?; subst; split => // fn fd /get_fundef_in' hin.
have := allMP hin hall; rewrite /add_funname /=.
by case: check_params => // -[].
Qed.

Lemma size_keep_update k o : size (keep_update k o) = size k.
Proof. by case: o => //= k'; rewrite size_keep_compose. Qed.

Lemma da_struct_step q info p2 ch kp kr :
  total_ok q -> da_names q -> da_keep q info ->
  dead_args_round protect dead_info q = ok (p2, ch, kp, kr) ->
  [/\ total_ok p2, da_names p2 & da_keep p2 (update_info kp kr info)].
Proof using hok.
move=> hokq hn hk /dead_args_roundP [hdc _]; split.
+ exact: da_total_ok hdc hokq.
+ move=> fn; rewrite -hn; split.
  + by case hq: (get_fundef (p_funcs q)) => [fd | ] //; have [fd2 -> _] := da_get_src hdc hq.
  by case h2: (get_fundef (p_funcs p2)) => [fd2 | ] //; have [fd -> _] := da_get hdc h2.
move=> fn fd hfd; have [k hk' [h1 h2 h3]] := hk _ _ hfd.
exists (keep_update k.1 (kp fn), keep_update k.2 (kr fn)).
+ by rewrite /update_info /get_fundef assoc_mapE /=; [rewrite -/(get_fundef _ _) hk' | move=> ? []].
rewrite /= !size_keep_update; split => // fdq2 /(da_get hdc) [fdq /h3 hty].
rewrite /dead_code_fd; t_xrbindP => _ _ <- /=; rewrite hty /fn_keep_only.
have [[/Forall2_size hsz _] _] := hok hfd; rewrite size_map in hsz.
by case: (kp fn) => //= k'; rewrite keep_only_compose // h1 hsz.
Qed.

Lemma da_rel_step q info p2 ch kp kr :
  total_ok q -> da_names q -> da_keep q info -> da_rel q info ->
  dead_args_round protect dead_info q = ok (p2, ch, kp, kr) ->
  da_rel p2 (update_info kp kr info).
Proof using hok rE_trans.
move=> hokq hn hk hrel hr fn.
have [hdc hcheck] := dead_args_roundP hr.
have hround := da_tgt_src_callP (wE := wE) (rE := rE) ev hdc (sm := total_init) erefl hokq hcheck (fn := fn).
case hp: (get_fundef (p_funcs p) fn) => [fd | ]; last first.
+ apply: wequiv_fun_get => fd2 /(da_get hdc) [fdq hq _].
  by move: (hn fn); rewrite hq hp => -[_ /(_ erefl)].
apply: (wkequiv_io_trans _ _ hround (hrel fn)).
+ have [k hk' [h1 h2 h3]] := hk _ _ hp.
  have hK : kparams info fn = k.1 by rewrite /kparams hk'.
  have [[/Forall2_size hsz _] _] := hok hp; rewrite size_map in hsz.
  move=> fs1 fs3 /= [_ -> htr]; exists (fs_keep (kparams info fn) fs3) => //.
  have [vs htrs] : exists vs,
    mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) (fvals fs3) = ok vs.
  + by move: (htr _ hp); case: mapM2 => // vs _; exists vs.
  have [hs _] := size_mapM2 htrs; rewrite size_map in hs.
  rewrite kparams_update fs_keep_update; last by rewrite hK h1 hsz hs.
  split => // fdq /h3 ->; rewrite hK map_keep_only.
  by rewrite (mapM2_keep_only _ htrs).
move=> fs1 fs2 fs3 r1 r3 _ _ [r2 [-> _] [-> [fd' hfd' [vs htr]]]].
split; last by exists fd' => //; exists vs.
move: hfd'; rewrite hp => -[?]; subst fd'.
have [k hk' [h1 h2 h3]] := hk _ _ hp.
have hsr := total_ok_fd_size (estate0 r3) (hok hp).1.
have [_ hs] := size_mapM2 htr; rewrite size_map in hs.
by rewrite kres_update fs_keep_update // /kres hk' h2 hsr hs.
Qed.

Definition da_info0 : keep_info :=
  [seq (f.1, (nseq (size f.2.(f_params)) true, nseq (size f.2.(f_res)) true)) | f <- p_funcs p].

Lemma get_info0 fn fd :
  get_fundef (p_funcs p) fn = Some fd ->
  get_fundef da_info0 fn = Some (nseq (size (f_params fd)) true, nseq (size (f_res fd)) true).
Proof.
by rewrite /da_info0 /get_fundef assoc_mapE /=; [move=> -> | move=> ? []].
Qed.

Lemma da_keep0 : da_keep p da_info0.
Proof using hok.
move=> fn fd hp; rewrite (get_info0 hp); eexists; first reflexivity.
rewrite /= !size_nseq; split => // fdq; rewrite hp => -[<-].
have [[/Forall2_size hsz _] _] := hok hp; rewrite size_map in hsz.
by rewrite keep_only_nseq // hsz.
Qed.

(* The first round relates its result to [p] directly. *)
Lemma da_rel_first p2 ch kp kr :
  dead_args_round protect dead_info p = ok (p2, ch, kp, kr) ->
  da_rel p2 (update_info kp kr da_info0).
Proof using hok.
move=> hr fn; have [hdc hcheck] := dead_args_roundP hr.
have hround :=
  da_tgt_src_callP (wE := wE) (rE := rE) ev hdc (sm := total_init) erefl hok hcheck (fn := fn).
case hp: (get_fundef (p_funcs p) fn) => [fd | ]; last first.
+ by apply: wequiv_fun_get => fd2 /(da_get hdc) [fdq]; rewrite hp.
have hK := get_info0 hp.
have [[/Forall2_size hsz _] _] := hok hp; rewrite size_map in hsz.
apply: wkequiv_io_weaken hround => //.
+ move=> fs1 fs3 /= [_ -> htr]; split => //.
  have [vs htrs] : exists vs,
    mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) (fvals fs3) = ok vs.
  + by move: (htr _ hp); case: mapM2 => // vs _; exists vs.
  have [hs _] := size_mapM2 htrs; rewrite size_map in hs.
  have hle : size (fvals fs3) <= size (nseq (size (f_params fd)) true).
  + by rewrite size_nseq hsz hs.
  rewrite kparams_update /kparams hK /= (fs_keep_update _ _ hle) fs_keep_nseq //.
  by rewrite hsz hs.
move=> fs1 fs3 r1 r3 _ /= [-> [fd' hfd' [vs htr]]]; split; last by exists fd' => //; exists vs.
move: hfd'; rewrite hp => -[?]; subst fd'.
have hsr := total_ok_fd_size (estate0 r3) (hok hp).1.
have [_ hs] := size_mapM2 htr; rewrite size_map in hs.
have hle : size (fvals r3) <= size (nseq (size (f_res fd)) true) by rewrite size_nseq hsr hs.
rewrite kres_update /kres hK /= (fs_keep_update _ _ hle) fs_keep_nseq //.
by rewrite hsr hs.
Qed.

Lemma da_loop fuel q info p' info' :
  total_ok q -> da_names q -> da_keep q info -> da_rel q info ->
  dead_args_loop protect dead_info fuel q info = ok (p', info') ->
  da_rel p' info'.
Proof using hok rE_trans.
elim: fuel q info => [ | n ih] q info hokq hn hk hrel /=; first by move=> [<- <-].
t_xrbindP => -[[[p2 ch] kp] kr] hr.
have [hokp2 hn2 hk2] := da_struct_step hokq hn hk hr.
have hrel2 := da_rel_step hokq hn hk hrel hr.
by case: ch hr => _; [apply: ih | move=> [<- <-]].
Qed.

Lemma da_info_rel p' info :
  dead_args_info protect dead_info p = ok (p', info) -> da_rel p' info.
Proof using hok rE_trans.
rewrite /dead_args_info -/da_info0 /=; t_xrbindP => -[[[p2 ch] kp] kr] hr.
have [hokp2 hn2 hk2] := da_struct_step hok (fun _ => conj id id) da_keep0 hr.
have hrel2 := da_rel_first hr.
by case: ch hr => _; [apply: da_loop | move=> [<- <-]].
Qed.

End COMPOSE.

(* When the transformed program runs without failure, in the mode
   [total_init] (the pass runs after [explicit_init]) with its assertions
   evaluated, the source runs, from the same arguments and values of the
   types of the removed parameters, with the same results, but those removed.
   [total_ok] is stated in the mode [total]: the two modes fail alike, but
   for a write of an output that [total] leaves undefined and [total_init]
   defines, which fails in [total] only. *)
Lemma dead_args_tgt_src :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {LC : LoopCounter}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    {rE_trans : EventRels_trans rE rE rE}
    protect dead_info (p p' : uprog) info (ev : extra_val_t),
  total_ok p ->
  dead_args_info protect dead_info p = ok (p', info) ->
  forall fn,
  wiequiv_f (sm1 := total_init) (sm2 := total_init)
    (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    p' p ev ev (rpreF (eS := dead_args_tgt_src_spec info p)) fn fn
    (rpostF (eS := dead_args_tgt_src_spec info p)).
Proof.
move=> asm_op syscall_state ep spp sip LC E E0 wE rE rE_trans protect dead_info p p' info ev
  hok hda fn.
apply: wkequiv_io_weaken
  (da_info_rel (wE := wE) (rE_trans := rE_trans) ev hok hda (fn := fn)) => //.
by move=> > _ [].
Qed.

Section PROTECTED.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
  {LC : LoopCounter}.

(* The parameters and the results of a function whose variables are all
   protected are all kept. *)
Lemma dead_args_info_protected (protect : funname -> var -> bool) dead_info
  (p p' : uprog) info fn :
  (forall x, protect fn x) ->
  dead_args_info protect dead_info p = ok (p', info) ->
  all id (kparams info fn) /\ all id (kres info fn).
Proof.
move=> hpr; rewrite /dead_args_info.
move: (sumn _).+1 => fuel.
set info0 := [seq _ | f <- p_funcs p].
have : forall k, get_fundef info0 fn = Some k -> all id k.1 && all id k.2.
- rewrite /info0 /get_fundef assoc_mapE; last by move=> ? [].
  move=> k; case: assoc => //= fd [<-] /=.
  by rewrite !all_nseq !orbT.
elim: fuel p info0 => [|n ih] p0 i0 hi /=.
- move=> [_ <-]; rewrite /kparams /kres.
  by case: get_fundef hi => // k /(_ _ erefl) /andP.
have hupd : forall kp kr, kp = params_keep protect dead_info p0 ->
  kr = res_keep protect dead_info p0 ->
  forall k, get_fundef (update_info kp kr i0) fn = Some k -> all id k.1 && all id k.2.
- move=> kp kr -> -> k; rewrite /update_info /get_fundef assoc_mapE; last by move=> ? [].
  have hk : forall o xs, keep_vars protect fn o xs = None.
  + move=> [k'|] xs //=; rewrite /keep_vars; case: ifP => // /negP [].
    by rewrite all_map; elim: zip => //= b l ->; rewrite hpr orbT.
  rewrite /= /params_keep /res_keep; case: get_fundef => [fd|]; rewrite ?hk /=.
  1,2: by move: (hi k); rewrite /get_fundef; case: assoc => //= -[k1 k2] h [?]; subst k; apply: h.
t_xrbindP => -[[[p2 ch] kp] kr] hr.
have [-> ->] : kp = params_keep protect dead_info p0 /\ kr = res_keep protect dead_info p0.
- by move: hr; rewrite /dead_args_round; t_xrbindP => ?? _ _ _ <- <-.
have hi' := hupd _ _ erefl erefl.
case: ch hr => _; first by apply: ih.
move=> [_ <-]; rewrite /kparams /kres.
by case: get_fundef hi' => // k /(_ _ erefl) /andP.
Qed.

End PROTECTED.
