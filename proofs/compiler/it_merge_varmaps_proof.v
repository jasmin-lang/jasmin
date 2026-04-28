(*
*)

From ITree Require Import
  ITree
  ITreeFacts
  Basics.HeterogeneousRelations
  Interp.Recursion
  Eq.Rutt
  Eq.RuttFacts.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
Require Import sem_one_varmap it_sems_one_varmap merge_varmaps psem_facts core_logics relational_logic.
Require sem_one_varmap_facts.
Require Import seq_extra.
Import Utf8.
Import word_ssrZ.
Import psem.
Import merge_varmaps.
Import compiler_util.
Require Import xrutt xrutt_facts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

#[local] Existing Instance withsubword.
#[local] Existing Instance direct_c.

Section WITH_PARAMS.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Lemma init_stk_stateI fex pex gd s s' :
  pex.(sp_rip) != pex.(sp_rsp) →
  init_stk_state fex pex gd s = ok s' →
  [/\
    escs s = escs s',
    (evm s').[vid pex.(sp_rip)] = Vword gd,
    alloc_stack s.(emem) fex.(sf_align) fex.(sf_stk_sz) fex.(sf_stk_ioff) fex.(sf_stk_extra_sz) = ok (emem s'),
    (evm s').[vid pex.(sp_rsp)] = Vword (top_stack (emem s')) &
    forall (x:var), x <> vid pex.(sp_rip) -> x <> vid pex.(sp_rsp) ->
              (evm s').[x] = Vm.init.[x]].
Proof.
  move => /eqP checked_sp_rip.
  apply: rbindP => m ok_m [<-] /=; split => //.
  + by rewrite Vm.setP_eq vm_truncate_val_eq.
  + rewrite Vm.setP_neq.
    * by rewrite Vm.setP_eq vm_truncate_val_eq.
    by apply /eqP; congruence.
  by move=> x /eqP ? /eqP ?; rewrite !Vm.setP_neq // eq_sym.
Qed.

Lemma orbX (P Q: bool):
  P || Q = (P && ~~ Q) || Q.
Proof. by case: Q; rewrite !(orbT, orbF, andbT). Qed.

(* TODO: move *)
Definition is_export (p: sprog) (fn: funname) : Prop :=
  exists2 fd, get_fundef p.(p_funcs) fn = Some fd & fd.(f_extra).(sf_return_address) = RAnone.

Section PROG.

Context
  {ovm_i : one_varmap_info}
  (p : sprog)
  (id_tmp id_tmp2: Ident.ident)
  (global_data : pointer)
  {LC : LoopCounter}.

Let var_tmp  : var := vid id_tmp.
Let var_tmp2 : var := vid id_tmp2.
Let var_tmps : Sv.t := Sv.add var_tmp2 (Sv.singleton var_tmp).

Definition valid_writefun (w: funname → Sv.t) (f: sfun_decl) : bool :=
  Sv.subset (write_fd p var_tmps w f.2) (w f.1).

Lemma check_wmapP (wm: Mf.t Sv.t) (fn: funname) (fd: sfundef) :
  get_fundef (p_funcs p) fn = Some fd →
  check_wmap p var_tmps wm →
  valid_writefun (get_wmap wm) (fn, fd).
Proof. by move /get_fundef_in' => h /allE/List.Forall_forall /(_ _ h). Qed.

Let wmap := mk_wmap p var_tmps.
Notation wrf := (get_wmap wmap).

Lemma checkP u (fn: funname) (fd: sfundef) :
  check p var_tmps = ok u →
  get_fundef (p_funcs p) fn = Some fd →
  valid_writefun wrf (fn, fd) ∧ check_fd p var_tmps wrf fn fd = ok tt.
Proof.
  rewrite /check; t_xrbindP => ok_wmap _ _ ? ok_prog _ ok_fd; split.
  - exact: check_wmapP ok_fd ok_wmap.
  by have [ [] ] := get_map_cfprog_name_gen ok_prog ok_fd.
Qed.

Hypothesis ok_p : check p var_tmps = ok tt.

Let vgd : var := vid p.(p_extra).(sp_rip).
Let vrsp : var := vid p.(p_extra).(sp_rsp).

Lemma rip_neq_rsp : p.(p_extra).(sp_rip) != p.(p_extra).(sp_rsp).
Proof. by move: ok_p; rewrite /check; t_xrbindP. Qed.

Lemma vgd_neq_vrsp : vgd != vrsp.
Proof.
  have := rip_neq_rsp.
  rewrite /vgd /vrsp /=.
  by move=> /eqP ?; apply /eqP; congruence.
Qed.

Lemma var_tmp_not_magic :
  disjoint var_tmps (magic_variables p).
Proof. by move: ok_p; rewrite /check; t_xrbindP. Qed.

Lemma not_written_magic W :
  disjoint W (magic_variables p) →
  ¬ Sv.In vgd W ∧ ¬ Sv.In vrsp W.
Proof. rewrite /disjoint /magic_variables /is_true Sv.is_empty_spec; SvD.fsetdec. Qed.

Lemma disjoint_tmp_call_magic f :
  disjoint (fd_tmp_call p f) (magic_variables p).
Proof.
  move: ok_p; rewrite /fd_tmp_call /check; t_xrbindP => _ _ _ ? ok_prog.
  have /(_ f) := get_map_cfprog_name_gen ok_prog.
  case: get_fundef => // fd /(_ _ erefl) [? ].
  by rewrite /check_fd /=; t_xrbindP => ? _ _ _ _ _ _ /disjoint_sym.
Qed.

Lemma kill_vars_tmp_call_rsp fn vm :
  (kill_vars (fd_tmp_call p fn) vm).[vrsp] = vm.[vrsp].
Proof.
  rewrite kill_varsE; case: ifP => // /Sv_memP.
  have := disjoint_tmp_call_magic fn.
  rewrite /disjoint => /Sv.is_empty_spec.
  rewrite /magic_variables /vrsp /=; SvD.fsetdec.
Qed.

Lemma kill_vars_tmp_call_rip fn vm :
  (kill_vars (fd_tmp_call p fn) vm).[vgd] = vm.[vgd].
Proof.
  rewrite kill_varsE; case: ifP => // /Sv_memP.
  have := disjoint_tmp_call_magic fn.
  rewrite /disjoint => /Sv.is_empty_spec.
  rewrite /magic_variables /vgd /=; SvD.fsetdec.
Qed.

Notation write_c_rec := (merge_varmaps.write_c_rec p var_tmps wrf).
Notation write_c := (merge_varmaps.write_c p var_tmps wrf).
Notation write_I_rec := (merge_varmaps.write_I_rec p var_tmps wrf).
Notation write_I := (merge_varmaps.write_I p var_tmps wrf).
Notation write_i_rec := (merge_varmaps.write_i_rec p var_tmps wrf).
Notation write_i := (merge_varmaps.write_i p var_tmps wrf).

Section WRITE.

Let Pr i := forall s, Sv.Equal (write_i_rec s i) (Sv.union s (write_i i)).
Let Pi i := forall s, Sv.Equal (write_I_rec s i) (Sv.union s (write_I i)).
Let Pc c := forall s, Sv.Equal (write_c_rec s c) (Sv.union s (write_c c)).

Lemma write_c_recE c : ∀ s, Sv.Equal (write_c_rec s c) (Sv.union s (write_c c)).
Proof.
  apply: (cmd_rect (Pr := Pr) (Pi := Pi) (Pc := Pc)).
  - by move => i ii ih s; rewrite /write_I /write_I_rec -/write_i_rec !ih; SvD.fsetdec.
  - rewrite /Pc. by SvD.fsetdec.
  - by move => i c' hi hc' s; rewrite /write_c /= !hc' -/write_I hi; SvD.fsetdec.
  - by move => x tg ty e s; rewrite /write_i /write_i_rec -vrv_recE.
  - by move => xs tg op es s; rewrite /write_i /write_i_rec -vrvs_recE.
  - by move => xs op es s; rewrite /write_i /write_i_rec !vrvs_recE; SvD.fsetdec.
  - by move=> a s; rewrite /write_i /write_i_rec; SvD.fsetdec.
  - by move => e c1 c2 h1 h2 s; rewrite /write_i /write_i_rec -!/write_c_rec -/write_c !h1 h2; SvD.fsetdec.
  - by move => v d lo hi body h s; rewrite /write_i /write_i_rec -!/write_c_rec !h; SvD.fsetdec.
  - by move => a c1 e ei c2  h1 h2 s; rewrite /write_i /write_i_rec -!/write_c_rec -/write_c !h1 h2; SvD.fsetdec.
  by move=> xs fn es s; rewrite /write_i /write_i_rec; SvD.fsetdec.
Qed.

Lemma write_I_recE ii i s :
  Sv.Equal (write_I_rec s (MkI ii i))
           (write_i_rec s i).
Proof. by []. Qed.

Lemma write_c_cons i c :
  Sv.Equal (write_c (i :: c)) (Sv.union (write_I i) (write_c c)).
Proof. by rewrite /write_c /= write_c_recE. Qed.

Lemma write_i_if e c1 c2 :
  Sv.Equal (write_i (Cif e c1 c2)) (Sv.union (write_c c1) (write_c c2)).
Proof.
  rewrite /write_i /write_i_rec -/write_c_rec !write_c_recE.
  move: (write_c c2) (write_c c1). (* SvD.fsetdec faster *)
  SvD.fsetdec.
Qed.

Lemma write_i_while aa c1 e ei c2 :
  Sv.Equal (write_i (Cwhile aa c1 e ei c2)) (Sv.union (write_c c1) (write_c c2)).
Proof. etransitivity; last exact: (write_i_if e c1 c2). reflexivity. Qed.

End WRITE.

Notation check_instr := (check_i p var_tmps wrf).
Notation check_instr_r := (check_ir p var_tmps wrf).
Notation check_cmd sz := (check_c (check_instr sz)).

Lemma check_instr_r_CwhileP sz ii aa c e ei c' D D' :
  check_instr_r sz ii D (Cwhile aa c e ei c') = ok D' →
  ∃ D1,
   [/\ Sv.Subset D D1
     , check_cmd sz D1 c = ok D'
     , check_e ii D' e = ok tt
     , check_instr_r sz ii D1 (Cwhile aa c e ei c') = ok D'
     & ~is_false e -> exists2 D2, Sv.Subset D2 D1 & check_cmd sz D' c' = ok D2].
Proof.
  rewrite /check_instr_r -/check_instr; case: is_falseP => //.
  + move=> ->; exists D; split => //=. rewrite /check_e /read_e /check_fv /=.
    have -> // : Sv.is_empty (Sv.inter D' Sv.empty).
    by apply Sv.is_empty_spec; clear; SvD.fsetdec.
  move=> _.
  elim: loop_counter D => // n ih /=; t_xrbindP => D D1 h1 he D2 h2.
  case: (equivP idP (Sv.subset_spec _ _)) => d.
  - case => ?; subst D1; exists D.
    rewrite h1 /= /check_e he /= h2 /=; split => //; last by exists D2.
    by move /Sv.subset_spec : d => ->.
  move => /ih{ih} [D4]; rewrite /check_e /= => -[hsub hc he' heq [] // D3 hle hc'].
  exists D4. rewrite hc /= he' /= hc' /=; split => //; last by eauto.
  + by move: hsub; clear; SvD.fsetdec.
  by move /Sv.subset_spec: hle => ->.
Qed.

Lemma check_instrP sz ii i D D' :
  check_instr sz D (MkI ii i) = ok D' →
  check_instr_r sz ii D i = ok D'.
Proof. by []. Qed.

Remark vrvs_vars vs xs :
  mapM get_lvar vs = ok (map v_var xs) →
  vrvs vs = sv_of_list v_var xs.
Proof.
  rewrite /vrvs /sv_of_list.
  elim: vs xs Sv.empty => [ | v vs ih ] [ | x xs ] //= acc; t_xrbindP => // ? ok_x ? ok_xs ??; subst.
  case: v ok_x => //= _ [->].
  exact: ih ok_xs.
Qed.

Record match_estate (D: Sv.t) (s t: estate) : Prop :=
  MVM {
    mvm_scs  : escs s = escs t;
    mvm_mem  : emem s = emem t;
    mvm_vmap : s.(evm) <=[\D] t.(evm);
  }.

Instance match_estate_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) match_estate.
Proof.
  by move => x y x_eq_y s _ <- t _ <-; split => - [] ?; rewrite ?x_eq_y => ?; constructor => //; rewrite x_eq_y.
Qed.

Lemma match_estateI X X' s t :
  Sv.Subset X X' →
  match_estate X s t →
  match_estate X' s t.
Proof. by move => hle [?? hvm]; split => //; apply: uincl_exI hle hvm. Qed.

(* Precondition for function *)
Definition preF (fn1 fn2 : funname) (fs:fstate) (s:estate) :=
  [/\ fn1 = fn2
    , fscs fs = escs s
    , fmem fs = emem s
    & let m := fmem fs in
      let tvm1 := evm s in
      let args := fvals fs in
      match get_fundef (p_funcs p) fn1 with
      | Some fd =>
        exists args',
         [/\ top_stack_aligned fd m
           , tvm1.[vrsp] = Vword (top_stack m)
           , tvm1.[ vgd ] = Vword global_data
           , get_var_is false tvm1 fd.(f_params) = ok args'
           & List.Forall2 value_uincl args args']
      | None => false
      end].

(* Postcondition for function *)
Definition postF (fn1 fn2 : funname) (fs:fstate) (s:estate) (fs':fstate) (ks:Sv.t * estate) :=
   let (k, s') := (ks.1, ks.2) in
   [/\ fscs fs' = escs s'
     , fmem fs' = emem s'
     & let m' := fmem fs' in
       let res := fvals fs' in
       let tvm1 := evm s in
       let tvm2 := evm s' in
       match get_fundef (p_funcs p) fn1 with
       | Some fd =>
         exists res',
          [/\ Sv.Subset k (writefun_ra p var_tmps wrf fn1)
            , Sv.Subset (writefun_RA var_tmps p fn1) k
            , get_var_is false tvm2 fd.(f_res) = ok res'
            , tvm1 =[\ writefun_ra p var_tmps wrf fn1 ] tvm2
            , stack_stable (emem s) (emem s')
            , tvm2.[vrsp] = Vword (top_stack m')
            , tvm2.[ vgd ] = Vword global_data
            & List.Forall2 value_uincl res res']
       | _ => True
       end].

Definition PreF {T1 T2} (d1 : recCall T1) (d2 : recCallK T2) : Prop :=
  match d1, d2 with
  | RecCall _ fn1 fs1, RecCallK fn2 s2 => preF fn1 fn2 fs1 s2
  end.

Definition PostF {T1 T2} (d1 : recCall T1) (t1: T1) (d2 : recCallK T2) (t2: T2) : Prop :=
  match d1 in recCall T1_ return T1_ -> T2 -> Prop with
  | RecCall _ fn1 fs1 =>
    match d2 in recCallK T2_ return fstate -> T2_ -> Prop with
    | RecCallK fn2 s2 => postF fn1 fn2 fs1 s2
    end
  end t1 t2.

#[local] Instance relEvent_recCall {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0} :
    EventRels2 (Sum.sum1 recCall E0) (Sum.sum1 recCallK E0) :=
  {| EPreRel0_  := sum_prerelF (@PreF) EPreRel0
   ; EPostRel0_ := sum_postrelF (@PostF) EPostRel0
  |}.

Section CMD.

Context {E_l E0_l : Type -> Type} {wE_l: with_Error E_l E0_l}
  {E_r E0_r : Type -> Type} {wE_r: with_Error E_r E0_r}
  {rndE0_l : RndEvent syscall_state -< E0_l}
  {rndE0_r : RndEvent syscall_state -< E0_r}
  {rE0 : EventRels2 E0_l E0_r}
  {rndE0_refl : RndE0_refl2 rE0}
.

Context (sem_F1 : sem_Fun (pT:= progStack) E_l)
        (sem_F2 : sem_FunK E_r).

Context (hcall : forall ii1 fn1 fn2,
    wkequiv_io
      (preF fn1 fn2)
      (sem_fun (sem_Fun := sem_F1) p global_data ii1 fn1)
      (sem_funK (sem_FunK := sem_F2) p fn2)
      (postF fn1 fn2)).

Context (m0:mem)
        (sz: wsize)
        (W:Sv.t)
        (mvp_not_written: disjoint W (magic_variables p)).

Record merge_vmap_stable (t:estate) :=
  { mvs_stable: stack_stable m0 (emem t)
  ; mvs_top_stack: (evm t).[vrsp] = Vword (top_stack (emem t))
  ; mvs_global_data : (evm t).[ vgd ] = Vword global_data
  ; mvs_stack_aligned : is_align (top_stack (emem t)) sz
  }.

Record merged_vmap_inv (X:Sv.t) (s:estate) (t:estate) :=
  { mvi_match : match_estate X s t
  ; mvi_stable: merge_vmap_stable (t:estate)
  }.

Definition Pc (c:cmd) :=
  ∀ I O,
    Sv.Subset (write_c c) W →
    check_cmd sz I c = ok O →
    wkequiv_io
      (fun s1 kt1 => merged_vmap_inv I s1 kt1.2)
      (it_sems_core.isem_cmd_ (sem_F:=sem_F1) p global_data c)
      (it_sems_one_varmap.isem_cmd_ (it_sems_one_varmap.isem_i var_tmps (sem_F:=sem_F2)) p c)
      (fun s1 kt1 s2 kt2 =>
         [/\ merged_vmap_inv O s2 kt2.2
           , evm kt1.2 =[\ write_c c] evm kt2.2
           & Sv.Subset kt2.1 (Sv.union (write_c c) kt1.1)]).

Definition Pi (i:instr) :=
  ∀ I O,
    Sv.Subset (write_I i) W →
    check_instr sz I i = ok O →
    wkequiv_io
      (merged_vmap_inv I)
      (it_sems_core.isem_i_body (sem_F:=sem_F1) p global_data i)
      (it_sems_one_varmap.isem_i var_tmps (sem_F:=sem_F2) p i)
      (fun s1 t1 s2 kt2 =>
         [/\ merged_vmap_inv O s2 kt2.2
           , evm t1 =[\ write_I i] evm kt2.2
           & Sv.Subset kt2.1 (write_I i)]).

Definition Pi_r (i:instr_r) :=
 ∀ ii I O,
    Sv.Subset (write_i i) W →
    check_instr_r sz ii I i = ok O →
    wkequiv_io
      (merged_vmap_inv I)
      (it_sems_core.isem_i_body (sem_F:=sem_F1) p global_data (MkI ii i))
      (it_sems_one_varmap.isem_ir var_tmps (sem_F:=sem_F2) p i)
      (fun s1 t1 s2 kt2 =>
         [/\ merged_vmap_inv O s2 kt2.2
           , evm t1 =[\ write_i i] evm kt2.2
           & Sv.Subset kt2.1 (write_i i)]).

(* TODO: move this *)
Lemma with_vm_m x y :
  escs x = escs y →
  emem x = emem y →
  forall vm, with_vm x vm = with_vm y vm.
Proof. by case: x y => scs m vm [] scs' m' vm' /= -> ->. Qed.

Lemma check_eP wdb ii I e s t v u : check_e ii I e = ok u ->
  match_estate I s t ->
  sem_pexpr wdb (p_globs p) s e = ok v ->
  exists2 v', sem_pexpr wdb (p_globs p) t e = ok v' & value_uincl v v'.
Proof.
  rewrite /check_e/check_fv => /assertP/Sv.is_empty_spec hd sim sem.
  have := sem_pexpr_uincl_on (vm2 := evm t) _ sem.
  rewrite (with_vm_m (mvm_scs sim) (mvm_mem sim)) with_vm_same; apply.
  by move=> x hx; apply (mvm_vmap sim); SvD.fsetdec.
Qed.

Lemma check_esP wdb ii I es s t vs u : check_es ii I es = ok u ->
  match_estate I s t ->
  sem_pexprs wdb (p_globs p) s es = ok vs ->
  exists2 vs', sem_pexprs wdb (p_globs p) t es = ok vs' & List.Forall2 value_uincl vs vs'.
Proof.
  rewrite /check_es => hc hsim; elim: es tt hc vs => [ | e es hrec] /=.
  + by move=> _ _ _ [<-]; exists [::].
  t_xrbindP => hce hces _ v hv vs hvs <-.
  have [v' -> /= uv']:= check_eP hce hsim hv.
  have [vs' -> /= uvs'] := hrec _ hces _ hvs.
  by eexists; first reflexivity; constructor.
Qed.

Lemma check_lvP_match_estate ii I x O s1 s2 t1 v v': check_lv ii I x = ok O ->
  match_estate I s1 t1 ->
  write_lval true (p_globs p) x v s1 = ok s2 ->
  value_uincl v v' ->
  exists2 t2, write_lval true (p_globs p) x v' t1 = ok t2 & match_estate O s2 t2.
Proof.
  rewrite /check_lv /check_fv; t_xrbindP => /Sv.is_empty_spec hd <- hsim hw hu.
  have []:= write_uincl_on (vm1 := evm t1) _ hu hw.
  + move=> z hz; apply (mvm_vmap hsim); SvD.fsetdec.
  move=> vm2; rewrite (with_vm_m (mvm_scs hsim) (mvm_mem hsim)) with_vm_same => hw' hs.
  exists (with_vm s2 vm2) => //;split => // z hz.
  case: (Sv_memP z (vrv x)) => hin; first by apply hs.
  rewrite -(vrvP hw); last by SvD.fsetdec.
  rewrite -(vrvP hw'); last by SvD.fsetdec.
  by apply (mvm_vmap hsim); SvD.fsetdec.
Qed.

Lemma check_lvsP_match_estate ii I xs O s1 s2 t1 vs vs': check_lvs ii I xs = ok O ->
  match_estate I s1 t1 ->
  write_lvals true (p_globs p) s1 xs vs = ok s2 ->
  List.Forall2 value_uincl vs vs' ->
  exists2 t2, write_lvals true (p_globs p) t1 xs vs' = ok t2 & match_estate O s2 t2.
Proof.
  rewrite /check_lvs.
  elim: xs I s1 s2 t1 vs vs' => /= [ | x xs hrec] I s1 s2 t1 [ | v vs] // vs'_.
  + by move=> [<-] hsim [<-] /List_Forall2_inv_l ->; exists t1.
  t_xrbindP => I' hx hxs hsim s3 hw hws /List_Forall2_inv_l [v' [vs' [-> [uv uvs]]]].
  have [t3 -> /= hsim']:= check_lvP_match_estate hx hsim hw uv.
  by have [t2 -> /= ?] := hrec _ _ _ _ _ _ hxs hsim' hws uvs; exists t2.
Qed.

Lemma merge_vmap_stable_trans (t1 t2:estate) X:
  Sv.Subset X W ->
  merge_vmap_stable t1 ->
  stack_stable (emem t1) (emem t2) ->
  evm t1 =[\X] evm t2 ->
  merge_vmap_stable t2.
Proof.
  move=> hsub [] hstable hrsp hgd hal hstable' heqex.
  have /not_written_magic [??] := disjoint_w hsub mvp_not_written.
  have heq1 := ss_top_stack hstable'.
  split; rewrite -?heq1 -?heqex //.
  by apply: stack_stable_trans hstable hstable'.
Qed.

Lemma check_lvP ii I x O s1 s2 t1 v v':
  Sv.Subset (vrv x) W ->
  check_lv ii I x = ok O ->
  merged_vmap_inv I s1 t1 ->
  write_lval true (p_globs p) x v s1 = ok s2 ->
  value_uincl v v' ->
  exists2 t2, write_lval true (p_globs p) x v' t1 = ok t2 & merged_vmap_inv O s2 t2.
Proof.
  move=> hsub hch [] hmatch hstable hw hu.
  have [t2 hw' hmatch'] := check_lvP_match_estate hch hmatch hw hu.
  exists t2 => //; split => //.
  apply: (merge_vmap_stable_trans hsub hstable).
  + by apply: write_lval_stack_stable hw'.
  by apply: vrvP hw'.
Qed.

Lemma check_lvsP ii I xs O s1 s2 t1 vs vs':
  Sv.Subset (vrvs xs) W ->
  check_lvs ii I xs = ok O ->
  merged_vmap_inv I s1 t1 ->
  write_lvals true (p_globs p) s1 xs vs = ok s2 ->
  List.Forall2 value_uincl vs vs' ->
  exists2 t2, write_lvals true (p_globs p) t1 xs vs' = ok t2 & merged_vmap_inv O s2 t2.
Proof.
  move=> hsub hch [] hmatch hstable hw hu.
  have [t2 hw' hmatch'] := check_lvsP_match_estate hch hmatch hw hu.
  exists t2 => //; split => //.
  apply: (merge_vmap_stable_trans hsub hstable).
  + by apply: write_lvals_stack_stable hw'.
  by apply: vrvsP hw'.
Qed.

Lemma all2_get_pvar args xs :
  all2
    (λ (e : pexpr) (a : var),
      match e with
      | Pvar {| gv := v; gs := Slocal |} => v_var v == a
      | Pvar {| gv := v; gs := Sglob |} => false
      | _ => false
      end) args xs ->
   mapM get_pvar args = ok xs.
Proof.
  elim: args xs => [ | a args hrec] [ | x xs] //= /andP [].
  by case: a => // -[y [] // /eqP /= <-] /hrec ->.
Qed.

Lemma all2_get_lvar xs res :
  all2
   (λ (x : lval) (r : var),
    match x with
    | Lvar v => v_var v == r
    | _ => false
    end) xs res ->
  mapM get_lvar xs = ok res.
Proof.
  elim: xs res => [ | x xs hrec] [ | r res] //= /andP [].
  by case: x => // y /eqP /= <- /hrec ->.
Qed.

Lemma match_estate_kill I s1 t1 K:
   match_estate I s1 t1 -> match_estate (Sv.union I K) s1 (with_vm t1 (kill_vars K (evm t1))).
Proof.
  move=> [h1 h2 h3]; constructor => // x hx.
  rewrite /with_vm /= kill_varsE; case: Sv_memP => //; first by SvD.fsetdec.
  move=> hni; apply h3; SvD.fsetdec.
Qed.

Lemma sem_pexprs_get_vars s es xs vs wdb :
  mapM get_pvar es = ok xs →
  sem_pexprs wdb (p_globs p) s es = ok vs →
  get_vars wdb (evm s) xs = ok vs.
Proof.
  elim: es xs vs => //= [ | e es hes] [ | x xs] // vs; t_xrbindP => //.
  move=> x'; case: e => //= -[ x'' []] // [<-] ? /hes{}hes <- ?; subst.
  by rewrite /get_gvar /= => ? -> /= ? /hes -> <-.
Qed.

Lemma get_lvar_write_lvals wdb s1 s2 xs xs' vs:
  mapM get_lvar xs = ok xs' ->
  write_lvals wdb (p_globs p) s1 xs vs = ok s2 ->
  write_lvals wdb (p_globs p) s1 (to_lvals xs') vs = ok s2.
Proof.
  elim: xs xs' vs s1 => [ | x xs hrec] /=.
  + by move=> _ [] // s1 [<-] [<-].
  t_xrbindP => ? [] // v vs s1 ? hx ? hxs <-.
  case: x hx => //= x' [<-]. rewrite /mk_var_i /write_var /=; t_xrbindP.
  by move=> > -> /= <-; apply hrec.
Qed.

Lemma get_lvar_check_lvs ii X xs xs':
  mapM get_lvar xs = ok xs' ->
  exists2 X', check_lvs ii X (to_lvals xs') = ok X' & Sv.Equal X' (Sv.diff X (vrvs (to_lvals xs'))).
Proof.
  elim: xs xs' X => [ | x xs hrec] /=.
  + by move=> _ X [<-] /=; exists X => //; rewrite /vrvs /=; clear; SvD.fsetdec.
  t_xrbindP => ? X x' hx ? hxs <- /=.
  rewrite /check_lv /= /check_fv.
  have -> /= : Sv.is_empty (Sv.inter X Sv.empty).
  + by apply Sv.is_empty_spec; clear; SvD.fsetdec.
  have [X' -> heq]:= hrec _ (Sv.diff X (Sv.add x' Sv.empty)) hxs.
  exists X' => //; move: heq; clear.
  rewrite vrvs_cons /=; SvD.fsetdec.
Qed.

Lemma subset_merged_vmap_inv X X' s t:
  Sv.Subset X X' -> merged_vmap_inv X s t -> merged_vmap_inv X' s t.
Proof.
  move=> heq [h1 h2]; split => //.
  case: h1 => ?? h; split => //.
  by move=> x hx; apply h; SvD.fsetdec.
Qed.

Lemma SvSubset_and s1 s2 s : Sv.Subset (Sv.union s1 s2) s -> Sv.Subset s1 s /\ Sv.Subset s2 s.
Proof. split; SvD.fsetdec. Qed.

Lemma merge_varmaps_cmdP c : Pc c.
Proof.
  apply (cmd_rect (Pr:=Pi_r) (Pi:=Pi) (Pc:=Pc)) => // {c}.
  (* instr_r -> instr *)
  + move=> i ii hi I O hsub /= hck s1 t1 hinv1.
    set sem := (sem in xrutt.xrutt _ _ _ _ _ sem _).
    have hsem : sem ≈ (s' <- isem_i_body (sem_F:=sem_F1) p global_data (MkI ii i) s1;; Ret s').
    + setoid_rewrite bind_ret_r; reflexivity.
    rewrite hsem => {sem hsem}.
    have {}hi:= hi ii _ _ hsub hck s1 t1 hinv1.
    apply (xrutt_facts.xrutt_bind hi).
    move=> s2 kt2 [hinv2 hex2 hsub2].
    have {}hsub : Sv.Subset kt2.1 W by apply: SvD.F.Subset_trans hsub2 hsub.
    have /stack_stableP -> :=
      stack_stable_trans (stack_stable_sym (mvs_stable (mvi_stable hinv1)))
                   (mvs_stable (mvi_stable hinv2)).
    rewrite (disjoint_w hsub mvp_not_written) /=.
    rewrite /valid_RSP (mvs_top_stack (mvi_stable hinv2)) value_eqb_refl //= bind_ret_l.
    by apply xrutt.xrutt_Ret.
  (* nil *)
  + by move=> I O hsub [<-] s t hinv; apply xrutt.xrutt_Ret; split.
  (* cons *)
  + move=> i c hi hc I O; rewrite {1}write_c_cons => hsub /=; t_xrbindP => I' hchi hchc.
    have [hsubi hsubc] := SvSubset_and hsub.
    move=> s1 kt1 hinv1.
    apply: (xrutt_facts.xrutt_bind (hi _ _ hsubi hchi s1 kt1.2 hinv1)).
    move=> s2 kt2 [hinv2 hex2 hsub2].
    have {}hinv2 : merged_vmap_inv I' s2 (Sv.union kt1.1 kt2.1, kt2.2).2 := hinv2.
    have := hc _ _ hsubc hchc _ _ hinv2.
    apply xrutt_facts.xrutt_weaken => // s3 kt3 [/= hinv3 hex3 hsub3]; split => //.
    + rewrite write_c_cons.
      apply eq_exT with (evm kt2.2).
      + by apply: eq_exI hex2; apply Sv_Subset_union_left.
      by apply: eq_exI hex3; apply Sv_Subset_union_right.
    by rewrite write_c_cons; move: hsub2 hsub3; clear; SvD.fsetdec.
  (* assgn *)
  + move=> x tg ty e ii I O.
    rewrite /write_i /= => hsub; t_xrbindP => he hx s1 t1 hinv1.
    apply xrutt_iresult => s2; rewrite /sem_assgn.
    t_xrbindP => v ok_v v' ok_v' ok_s2.
    have [w -> /= vw] := check_eP he (mvi_match hinv1) ok_v.
    have [w' -> /= vw'] := value_uincl_truncate vw ok_v'.
    have [t2 hw /= hinv'] := check_lvP hsub hx hinv1 ok_s2 vw'.
    rewrite hw; exists (vrv x, t2) => //=; split => //.
    by apply: (vrvP hw).
  (* opn *)
  + move=> xs t o es ii I O.
    rewrite /write_i /= => hsub; t_xrbindP => he hx s1 t1 hinv1.
    apply xrutt_iresult => s2; rewrite /sem_sopn.
    t_xrbindP => ws vs ok_v ok_ws ok_s2.
    have [w -> /= vw] := check_esP he (mvi_match hinv1) ok_v.
    have [ws' -> /= vw'] := vuincl_exec_opn vw ok_ws.
    have [t2 hw /= hinv'] := check_lvsP hsub hx hinv1 ok_s2 vw'.
    rewrite hw; exists (vrvs xs, t2) => //=; split => //.
    by apply: (vrvsP hw).

  (* syscall *)
  + move=> xs o es ii I O.
    rewrite /write_i /= => hsub; t_xrbindP => he halles hallxs <- s1 t1 hinv1.
    rewrite /it_sems_one_varmap.sem_syscall.
    rewrite bind_bind.
    apply: (xrutt_bind (RR := List.Forall2 value_uincl)).
    - apply xrutt_iresult  => vs ok_v.
      have [ves' hves' uves]:= check_esP he (mvi_match hinv1) ok_v.
      have -> /= := sem_pexprs_get_vars (all2_get_pvar halles) hves'.
      exists ves' => //=.
    move=> vs ves' uves //=.
    rewrite bind_bind.
    apply : (xrutt_bind (RR := fun fs fs' =>  stack_stable (emem t1) (fmem fs) /\ fs_uincl fs fs')).
    -        (* apply: xrutt_weaken; cycle 5. *)
      (* apply lutt_xrutt_trans_r. *)
      (* admit. *)
      (* Arguments fexec_syscall: clear implicits. *)
      (* have truc := (fs_uincl_syscall o s1 t1 (i1 :=mk_fstate vs s1) (i2 := (mk_fstate ves' t1)) (rndE0_refl:=rndE0_refl)). *)
      (* apply truc. *)

      rewrite /fexec_syscall //=.
      apply : (xrutt_bind (RR := eq)).
      apply xrutt_iresult.
       - move => v1 hv1.
         exists v1 => //.
         by apply: (exec_syscall_argPs uves).
      move => _ len ->.
      apply : (xrutt_bind (RR := eq)).
       - apply xrutt_trigger. admit. admit.
      move =>  _ scb ->.
      apply : (xrutt_bind (RR := eq)).
       - apply xrutt_iresult.
         move => [] [] a b c hv1.
         exists (a,b,c) => //=.
         move : hinv1 => [] [] _ <- _ _.
         apply (exec_syscall_storePs uves hv1).
      move =>  _ scm ->.
      apply xrutt_Ret.
      split;[ | apply fs_uinclR ].
      
      admit.
   move => fs fs' [hu h].
   rewrite -(bind_ret_r (iresult s1 (upd_estate true (p_globs p) xs fs s1))).
   apply : (xrutt_bind (RR := fun a b => exists X': Sv.t, merged_vmap_inv X' a b /\
      Sv.Equal X' (Sv.diff (Sv.union I syscall_kill) (vrvs (to_lvals (scs_vout (syscall_sig o))))) /\
      evm t1 =[\Sv.union syscall_kill (vrvs (to_lvals (scs_vout (syscall_sig o))))] evm b
          (* evm t1 =[\syscall_kill] evm b  *))) => //=.
     - apply xrutt_iresult.
       move => s2 ok_s2.
       case: hu => /= hfscs hfmem hu.
       move: hsub; rewrite {1}vrvs_recE {1}Sv_union_empty => hsub.
       have [hkill {}hsub] := SvSubset_and hsub.
       have hinv' : merged_vmap_inv (Sv.union I syscall_kill)
                      (with_scs (with_mem s1 (fmem fs)) (fscs fs))
                      (with_scs (with_mem (with_vm t1 (vm_after_syscall (evm t1))) (fmem fs)) (fscs fs)).
         + case: hinv1 => hst1 hmerge; split.
         + case: hst1 => ?? hvmap; split => //= z hz.
        rewrite /vm_after_syscall kill_varsE.
         case: Sv_memP.
          + by move=> ?; exfalso; apply hz; SvD.fsetdec.
          by move=> hz'; apply: hvmap; SvD.fsetdec.
         apply: (merge_vmap_stable_trans hkill hmerge) => //=.
         move=> x hx; rewrite /vm_after_syscall kill_varsE.
         by case: Sv_memP.
       have ok_s2':= get_lvar_write_lvals (all2_get_lvar hallxs) ok_s2.
       have [X' hch heq]:= [elaborate get_lvar_check_lvs ii (Sv.union I syscall_kill) (all2_get_lvar hallxs)].
       have [t2 hw /= hinv''] := check_lvsP hsub hch hinv' ok_s2' hu.
       exists t2 => //=.
       - by rewrite /upd_estate -hw hfmem hfscs.
       exists X'; split => //=.
       split => //=.
       have /= h1 := vrvsP hw.
       apply: eq_exT; last by apply: eq_exI h1; SvD.fsetdec.
       apply: (eq_exI (s2:= syscall_kill));first by SvD.fsetdec.
       by move=> y /= /Sv_memP /negPf; rewrite /vm_after_syscall kill_varsE => ->.
   move => s2' s2 [X' [hinv'' [heq h1]]].
   apply xrutt_Ret => //=.
    split => //=.
    + by apply: subset_merged_vmap_inv hinv''; rewrite heq.
    + by rewrite vrvs_recE Sv_union_empty.
      by rewrite vrvs_recE Sv_union_empty /=; apply SvD.F.Subset_refl.
      (* if *)
  + move=> e c1 c2 hc1 hc2 ii I O.
    rewrite {1}write_i_if /=; t_xrbindP => hsub hche O1 hch1 O2 hch2 <- s1 t1 hinv1 /=.
    apply xrutt_facts.xrutt_bind with eq.
    + apply xrutt_iresult => b; rewrite /sem_cond; t_xrbindP => v he.
      have [v' -> /= hu hto]:= check_eP hche (mvi_match hinv1) he.
      by have [? -> <-] := wrequiv_to_bool hu hto; eexists; eauto.
    have [hsub1 hsub2] := SvSubset_and hsub.
    have {}hinv1 : merged_vmap_inv I s1 (Sv.empty, t1).2 := hinv1.
    move=> b _ <-; case: b.
    + have := hc1 _ _ hsub1 hch1 s1 (Sv.empty, t1) hinv1.
      apply xrutt_facts.xrutt_weaken => // s2 kt2 [hinv' hex' hsub']; split.
      + by apply: subset_merged_vmap_inv hinv'; clear; SvD.fsetdec.
      + by rewrite write_i_if; apply: eq_exI hex'; clear; SvD.fsetdec.
      rewrite write_i_if; move: hsub'; clear; SvD.fsetdec.
    have := hc2 _ _ hsub2 hch2 s1 (Sv.empty, t1) hinv1.
    apply xrutt_facts.xrutt_weaken => // s2 kt2 [hinv' hex' hsub']; split.
    + by apply: subset_merged_vmap_inv hinv'; clear; SvD.fsetdec.
    + by rewrite write_i_if; apply: eq_exI hex'; clear; SvD.fsetdec.
    by rewrite write_i_if; move: hsub'; clear; SvD.fsetdec.
  (* while *)
  + move=> a c e iiw c' hc hc' ii I O.
  rewrite {1}write_i_while; t_xrbindP => hsub /check_instr_r_CwhileP [D1 [leID1 hchc hche _ hchc']].
  have [{}hsub hsub'] := SvSubset_and hsub.
  move=> s1 t1 hinv1.
  rewrite /isem_ir_rec /isem_i_rec /= /isem_while_loop /it_sems_one_varmap.isem_while_loop.
  apply xrutt_facts.xrutt_iter with
    (RI:= fun s1 kt1 =>
       [/\ merged_vmap_inv D1 s1 kt1.2
         , evm t1 =[\write_i (Cwhile a c e iiw c')] evm kt1.2
         & Sv.Subset kt1.1 (write_i (Cwhile a c e iiw c'))]);last first.
  + split => //=; last by clear; SvD.fsetdec.
    by apply: subset_merged_vmap_inv hinv1.
    move=> {hinv1} {}s1 kt1 [hinv1 hex1 hsubk].
    rewrite /isem_while_round /it_sems_one_varmap.isem_while_round.
    apply (xrutt_facts.xrutt_bind (hc _ _ hsub hchc _ _ hinv1)).
    move=> s2 kt2 [hinv2 hex2 hsub2].
    have hsubw : Sv.Subset kt2.1 (write_i (Cwhile a c false iiw c')).
    + by move: hsubk hsub2; rewrite !write_i_while; clear; SvD.fsetdec.
    case: is_falseP hchc' => [? _ | _ [] // D2 hsubD hchc'].
    + subst e; rewrite /isem_cond /sem_cond /= 2!bind_ret_l.
      apply xrutt.xrutt_Ret; constructor; split => //.
      apply: (eq_exT hex1); apply: eq_exI hex2.
      by rewrite write_i_while; clear; SvD.fsetdec.
    apply xrutt_facts.xrutt_bind with eq.
    + apply xrutt_iresult => b; rewrite /sem_cond; t_xrbindP => v he.
      have [v' -> /= hu hto]:= check_eP hche (mvi_match hinv2) he.
      by have [? -> <-] := wrequiv_to_bool hu hto; eexists; eauto.
    move=> + _ <- => -[]; last first.
    + apply xrutt.xrutt_Ret; constructor; split => //.
      by apply (eq_exT hex1); apply: eq_exI hex2; rewrite write_i_while; clear; SvD.fsetdec.
    apply (xrutt_facts.xrutt_bind (hc' _ _ hsub' hchc' _ _ hinv2)).
    move=> s3 rt3 [hinv3 hex3 hsub3]; apply xrutt.xrutt_Ret; constructor; split => //.
    + by apply: subset_merged_vmap_inv hinv3.
    + apply: (eq_exT hex1); rewrite write_i_while.
      apply eq_exT with (evm kt2.2).
      + by apply: eq_exI hex2; clear; SvD.fsetdec.
      by apply: eq_exI hex3; clear; SvD.fsetdec.
    by move: hsubw hsub3; rewrite !write_i_while; clear; SvD.fsetdec.
  (* call *)
  move=> xs f es ii I O.
  rewrite /write_i /= => /SvSubset_and [_] /SvSubset_and [] hsubra hsubtmp.
  case hget : get_fundef => [ fd | //].
  t_xrbindP => hches hal halles hallxs hdisj <-.
  rewrite /isem_i_rec /isem_ir_rec /= => s1 t1 hinv1.
  rewrite /isem_pexprs.
  case hes : sem_pexprs => [vs | e]; last first.
  + rewrite /= bind_throw; apply xrutt.xrutt_CutL.
    by rewrite /errcutoff /is_error /subevent /resum /fromErr mid12.
  have hinvu : merged_vmap_inv (Sv.union I (tmp_call (f_extra fd))) s1 (kill_tmp_call p f t1).
  + case: hinv1 => sim hstable; split.
    + rewrite /kill_tmp_call /fd_tmp_call hget.
      by apply: match_estate_kill sim.
    case: hstable=> hsta hrsp hvgd hali; split => //=.
    + by rewrite kill_vars_tmp_call_rsp.
    by rewrite kill_vars_tmp_call_rip.
  have [ves' hves' uves]:= check_esP hches (mvi_match hinvu) hes.
  have hgetv := sem_pexprs_get_vars (all2_get_pvar halles) hves'.
  rewrite /iresult /isem_pre /isem_post /= !bind_ret_l.
  setoid_rewrite bind_ret_l.
  have [htop hval /(hcall ii) hf /=] :
     [/\ top_stack_aligned fd (emem s1)
       , valid_RSP p (emem s1) (kill_vars (fd_tmp_call p f) (evm t1))
       & preF f f (mk_fstate vs s1) (kill_tmp_call p f t1)].
  + rewrite /preF /valid_RSP /=.
    case: hinvu => -[] <- /= hmem heqex []; rewrite -hmem hget.
    move=> hstable -> ->.
    rewrite /kill_tmp_call /fd_tmp_call hget -hmem value_eqb_refl // => hali.
    have -> : top_stack_aligned fd (emem s1).
    + by rewrite /top_stack_aligned (is_align_m hal hali) orbT.
    split => //; split => //.
    exists ves'; split => //.
    elim: (f_params fd) (ves') hgetv => //=.
    move=> x xs' hrec ?; t_xrbindP => ? /hrec -> <- /=.
    by rewrite /fd_tmp_call hget.

  rewrite /is_disjoint_magic hget.
  have -> /= : disjoint (ra_vm (f_extra fd) Sv.empty) (magic_variables p).
  + have [_] := checkP ok_p hget.
    rewrite /check_fd; t_xrbindP => k _ _ _ _ + _ _ _.
    move=> /disjoint_union [_]; rewrite hget.
    move=> /disjoint_union [] /disjoint_union [] + _ _.
    rewrite /ra_vm; case: sf_return_address => //.
    by apply: disjoint_w; clear;SvD.fsetdec.
  rewrite !bind_ret_l; apply (xrutt_facts.xrutt_bind hf).
  move=> s2 kt2 [] /= hscs hmem; rewrite hget => -[res'] [hsub' /Sv.subset_spec hsubk hget' heqex hstable hrsp hgd hu].
  rewrite /upd_estate.
  case hws : write_lvals => [s3 | e] /=; last first.
  + apply xrutt.xrutt_CutL.
    by rewrite /errcutoff /is_error /subevent /resum /fromErr mid12.
  rewrite /valid_RSP hrsp (ss_top_stack hstable) hmem value_eqb_refl // hsubk /= bind_ret_l.
  apply xrutt.xrutt_Ret => /=; split; last first.
  + by rewrite /writefun_ra_call; move: hsub'; clear; SvD.fsetdec.
  + rewrite /writefun_ra_call => x hx.
    have /Sv_memP/negbTE hn : ¬ Sv.In x (fd_tmp_call p f) by SvD.fsetdec.
    rewrite kill_varsE hn.
    have ? : ¬ Sv.In x (writefun_ra p var_tmps wrf f).
    + by move: hx; clear; SvD.fsetdec.
    by rewrite -heqex // kill_varsE hn.
  split.
  + split.
    + by rewrite (write_lvals_escs hws).
    + by rewrite (write_lvals_emem (all2_get_lvar hallxs) hws).
    move=> y hin; rewrite /kill_tmp_call /= kill_varsE /fd_tmp_call hget /=; case: Sv_memP.
    + by SvD.fsetdec.
    move=> /Sv_memP /negbTE hntc; case: (Sv_memP y (sv_of_list v_var (f_res fd))); last first.
    + move=> hx; rewrite -(vrvsP hws) /=; last by rewrite (vrvs_vars (all2_get_lvar hallxs)).
      rewrite -heqex; last by SvD.fsetdec.
      rewrite kill_varsE /fd_tmp_call hget hntc.
      by apply (mvm_vmap (mvi_match hinv1)); SvD.fsetdec.
    rewrite -Sv.mem_spec sv_of_listE => /= x_result.
    move: hu (f_res fd) x_result (all2_get_lvar hallxs) hget' (hallxs) (with_scs (with_mem s1 (fmem s2)) (fscs s2)) hws; clear.
    elim: xs (fvals s2) res' => [ | d ds ih ] [] //.
    + by move => _ /List_Forall2_inv_l -> [] // d ds _ /=; t_xrbindP.
    move => v vs _ /List_Forall2_inv_l [v'] [vs'] [->] [vv' vs_vs'] [] // q qs /= hx /=.
    t_xrbindP => xd hxd xds hxds ??; subst xd xds => ws hqs ??; subst v' ws.
    case: d hxd => // d hxd /andP [] /= /eqP hxq hall2 s3' s4 w ws.
    move: hx; rewrite /= inE orbX; case/orP; last first.
    + by move => hx; exact: ih _ _ vs_vs' _ hx hxds hqs hall2 _ ws.
    case/andP => /eqP hyq /negbTE x_not_in_ys.
    have <- := vrvsP ws; last by rewrite (vrvs_vars hxds) -Sv.mem_spec sv_of_listE /= x_not_in_ys.
    move/write_varP: w vv' => [-> ? /vm_truncate_value_uincl].
    by rewrite hxq -hyq Vm.setP_eq; apply: value_uincl_trans.
  case: hinvu => ? [hstable1 hrsp1 hgd1 hal1]; split.
  + by apply: stack_stable_trans hstable.
  + by rewrite /kill_tmp_call /= kill_vars_tmp_call_rsp -hmem.
  + by rewrite /kill_tmp_call /= kill_vars_tmp_call_rip.
  by rewrite /= -(ss_top_stack hstable).
Admitted.

End CMD.

Context {E E0 : Type -> Type} {wE: with_Error E E0}
  {rndE0 : RndEvent syscall_state -< E0} {rE0 : EventRels E0}.

Lemma merge_varmaps_funP fn1 fn2 :
  wkequiv_io
    (preF fn1 fn2)
    (sem_fun (sem_Fun := sem_fun_full) p global_data dummy_instr_info fn1)
    (it_sems_one_varmap.isem_fun var_tmps p fn2)
    (postF fn1 fn2).
Proof.
  move=> fs1 t1 hpre /=.
  rewrite /isem_fun /isem_fun_def /it_sems_one_varmap.isem_fun /it_sems_one_varmap.isem_fun_def.
  have {}hpre : PreF (RecCall dummy_instr_info fn1 fs1) (RecCallK fn2 t1) by done.
  apply: (xrutt_facts.mrec_xrutt (RPreInv:= @PreF) (RPostInv := @PostF) _ hpre).
  move=> {fn1 fn2 fs1 t1 hpre} _ _ [ii fn fs1] [_ t1] [<-] /= hscs hmem.
  case hget: get_fundef => [fd | //] [vs] [hal hrsp hgd hgetvs hu].
  rewrite /isem_fun_body /it_sems_one_varmap.isem_fun_body.
  rewrite /kget_fundef hget /= /isem_pre /isem_post /= !bind_ret_l.
  have [hvalra ]:= checkP ok_p hget.
  rewrite /check_fd; t_xrbindP => D.
  set ID := (ID in check_cmd _ ID _).
  set DF := Sv.union _ D.
  set res := sv_of_list v_var (f_res fd).
  set params := sv_of_list v_var (f_params fd).
  move => checked_body hdisj
    checked_params RSP_not_result preserved_magic
    checked_save_stack htmp_call_magic checked_ra.
  rewrite /iresult.
  case hinit: (initialize_funcall p global_data fd fs1) => [s1 | e] /=; last first.
  + rewrite bind_throw;apply xrutt.xrutt_CutL.
    by rewrite /xrutt_facts.EE_MR /errcutoff /is_error /subevent /resum /fromErr /= mid12.
  rewrite bind_ret_l.
  move: hinit; rewrite /initialize_funcall /init_state /=.
  t_xrbindP.
  move=> vargs ok_vargs s0' /init_stk_stateI -/(_ rip_neq_rsp) [hscs0 vgd_v ok_m' vrsp_v hvmap0] ok_s1.
  have {}checked_ra :
    match sf_return_address (f_extra fd) with
    | RAreg ra _ =>
      [/\ convertible (vtype ra) (aword Uptr),
       ~Sv.In ra (wrf fn),
       ~Sv.In ra (magic_variables p) &
       ~Sv.In ra params
      ]
    | RAstack ra_call ra_return _ _ =>
      (if ra_call is Some r then [/\ convertible (vtype r) (aword Uptr) & ~Sv.In r (magic_variables p)] else True) /\
      (if ra_return is Some r then [/\ convertible (vtype r) (aword Uptr) & ~Sv.In r (magic_variables p)] else True)
    | RAnone =>
        let to_save := sv_of_list fst (sf_to_save (f_extra fd)) in
      [/\ disjoint to_save res,
       Sv.subset (Sv.inter callee_saved (writefun_ra p var_tmps wrf fn)) to_save &
       all
         (λ x : var_i, if vtype x is aword _ then true else false)
         (f_params fd)
        ]
    end.
  - case heq : sf_return_address checked_ra => [ | ra ? | ra_call ra_return ofs ?].
    + by t_xrbindP => ??.
    + t_xrbindP => -> /Sv_memP ra_not_written.
      by rewrite SvP.union_mem negb_or => /andP[] /Sv_memP ra_not_magic /Sv_memP ra_not_param.
    t_xrbindP=> hcall hreturn.
    move: preserved_magic;
      rewrite /writefun_ra hget /ra_undef /ra_vm /ra_vm_return heq /disjoint => hempty.
    split.
    + case: ra_call heq hempty hcall => [ r | ] // heq.
      by t_xrbindP => /Sv.is_empty_spec /= h ->; split => //; SvD.fsetdec.
    case: ra_return heq hempty hreturn => [ r | ] // heq.
    by t_xrbindP => /Sv.is_empty_spec /= h ->; split => //; SvD.fsetdec.
  have ra_neq_magic :
    match sf_return_address (f_extra fd) with
    | RAreg ra _ => [&& ra != vgd, ra != vrsp & convertible (vtype ra) (aword Uptr)]
    | RAstack ra_call ra_return _ _ =>
      (if ra_call is Some ra then [&& ra != vgd, ra != vrsp & convertible (vtype ra) (aword Uptr)] else true) &&
      (if ra_return is Some ra then [&& ra != vgd, ra != vrsp & convertible (vtype ra) (aword Uptr)] else true)
    | _ => True
    end.
  - case: sf_return_address checked_ra => // [ ra _ | ra_call ra_return _ _].
    + rewrite /magic_variables -/vgd -/vrsp /= => -[].
      rewrite Sv.add_spec Sv.singleton_spec => -> ra_not_written.
      by case/Decidable.not_or => /eqP -> /eqP -> _.
    rewrite /magic_variables -/vgd -/vrsp /= => -[].
    move=> hcall hreturn.
    apply /andP; split.
    + case: ra_call hcall => [ra_call|//].
      rewrite /magic_variables -/vgd -/vrsp /= => -[].
      rewrite Sv.add_spec Sv.singleton_spec => ->.
      by case/Decidable.not_or => /eqP -> /eqP ->.
    case: ra_return hreturn => [ra_return|//].
    rewrite /magic_variables -/vgd -/vrsp /= => -[].
    rewrite Sv.add_spec Sv.singleton_spec => ->.
    by case/Decidable.not_or => /eqP -> /eqP ->.
  rewrite /it_sems_one_varmap.initialize_funcall.
  rewrite -hmem hal /valid_RSP hrsp value_eqb_refl //=.
  have -> /= : saved_stack_valid_init p fd.
  + rewrite /saved_stack_valid_init; move: hvalra.
    rewrite /valid_writefun /write_fd /saved_stack_valid /=.
    case: sf_save_stack checked_save_stack => // r; t_xrbindP => _ /Sv_memP r_not_written.
    rewrite /magic_variables /= => /Sv_memP.
    rewrite Sv.union_spec Sv.add_spec Sv.singleton_spec => ? /Sv.subset_spec ?.
    apply/andP; split; [apply/eqP | apply/eqP ]; intuition.
  rewrite ok_m' /= !bind_ret_l.
  set t1' := (t1' in it_sems_one_varmap.isem_cmd _ _ _ t1').
  have hfun : ∀ (ii1 : instr_info) (fn1 fn2 : funname),
      wkequiv_io (preF fn1 fn2)
        (sem_fun (sem_Fun:= sem_fun_rec _) p global_data ii1 fn1)
        (sem_funK (sem_FunK :=  it_sems_one_varmap.sem_funK_rec _) p fn2)
        (postF fn1 fn2).
  + move=> ii1 fn1 fn2 s t hpre /=.
    apply xrutt.xrutt_Vis => // s' t' /= hpost.
    by apply xrutt.xrutt_Ret.
  have hdisj_w : disjoint (write_c (f_body fd)) (magic_variables p).
  + apply: disjoint_w; last exact: preserved_magic.
    etransitivity; first by rewrite -Sv.subset_spec; exact: hvalra.
    rewrite /writefun_ra hget; exact: Sv_Subset_union_left.
  have hsub : Sv.Subset (write_c (f_body fd)) (write_c (f_body fd)) by done.
  have hpre : merged_vmap_inv (emem s0') (sf_align (f_extra fd)) ID s1 (Sv.empty, t1').2.
  + subst t1'; constructor.
    - split.
      + move: ok_s1; rewrite /= (write_vars_lvals _ [::]) => /write_lvals_escs ->.
        by rewrite -hscs -hscs0.
      + by rewrite /= -(write_vars_memP ok_s1).
      rewrite /set_RSP => z.
      case: (z =P vrsp) => [-> _ | /eqP hzrsp hnin].
      + rewrite Vm.setP_eq -(write_vars_eq_ex ok_s1) ?vrsp_v ?vm_truncate_val_eq //.
        by case: (not_written_magic checked_params).
      rewrite /= Vm.setP_neq; last by rewrite eq_sym.
      have huninit : ¬ Sv.In z params → z ≠ vgd → (evm s1).[z] = undef_addr (eval_atype (vtype z)).
      + move => h zgd; rewrite -(write_vars_eq_ex ok_s1) // hvmap0 //; last by apply/eqP.
        by apply Vm.initP.
      have hz : value_uincl (evm s1).[z] (evm t1).[z].
      + case: (Sv_memP z (sv_of_list v_var (f_params fd))) => hinp.
        + have : List.Forall2 value_uincl vargs vs.
          + apply: Forall2_trans hu; first by apply: value_uincl_trans.
            by apply: mapM2_dc_truncate_value_uincl ok_vargs.
          move/Sv_memP: hinp; rewrite sv_of_listE /=.
          elim: (f_params fd) (vargs) (vs) (s0') ok_s1 hgetvs => [ | x xs hrec] [ | v vs1] vs_ s //=.
          t_xrbindP => s' hx hxs vs' hmap <-; rewrite inE => hin /List_Forall2_inv[] ? H0.
          case: (@idP (z \in [seq v_var i | i <- xs])) hin => [hin _ | hnin'].
          + by apply: hrec hxs hmap hin H0.
          rewrite orbF => /eqP heq; rewrite -(write_vars_eq_ex hxs); last first.
          + by apply/Sv_memP; rewrite sv_of_listE /=;apply/negP.
          move/write_varP: hx => [-> _ /vm_truncate_value_uincl htr].
          by rewrite heq Vm.setP_eq; apply: (value_uincl_trans htr).
        rewrite -(write_vars_eq_ex ok_s1) //.
        case: (z =P vgd) => [-> | /eqP hzvgd]; first by rewrite vgd_v hgd.
        rewrite hvmap0 //. 2-3: by apply/eqP.
        rewrite Vm.initP.
        apply/compat_value_uincl_undef/Vm.getP.

      rewrite /ra_undef_vm kill_varsE; case:Sv_memP; last by [].
      move: hnin preserved_magic; rewrite /ID /writefun_ra hget -/(ra_undef _ _) -/params Sv.inter_spec => hnin no_magic hin.
      have {} hnin : ¬ Sv.In z params by intuition.
      have { no_magic } [ not_GD _ ] := not_written_magic no_magic.
      have {not_GD} z_not_GD : z ≠ vgd.
      + move: vgd (ra_undef _ _) (wrf _) hin not_GD; clear; SvD.fsetdec.
      rewrite huninit //.
    constructor => //=.
    + by rewrite /set_RSP Vm.setP_eq /= cmp_le_refl.
    + rewrite Vm.setP_neq; last by rewrite eq_sym vgd_neq_vrsp.
      rewrite /ra_undef_vm kill_varsE.
      have := not_written_magic preserved_magic.
      rewrite /writefun_ra hget /ra_undef.
      by case: Sv_memP => // h [[] ]; SvD.fsetdec.
    rewrite (alloc_stack_top_stack ok_m').
    exact: do_align_is_align.
    have := merge_varmaps_cmdP hfun (m0:=emem s0') (sz:=sf_align (f_extra fd)) hdisj_w hsub checked_body.
    Admitted.
(*   move=> /(_ s1 (Sv.empty, t1') hpre). *)
(*   set post := (post in xrutt.xrutt _ _ _ _ post _ _) => hbody. *)
(*   apply (xrutt_facts.xrutt_bind (RR:=post)). *)
(*   + apply: xrutt_facts.xrutt_weaken hbody => //. *)
(*     + move=> t e1; rewrite /errcutoff /xrutt_facts.EE_MR /= /is_error; case: e1 => // /= e. *)
(*       by case: mfun1 => //. *)
(*     + move=> T1 T2 [e1 | e1] [e2 | e2]; rewrite /EPreRel //= => h; apply sum_prerelP => //=. *)
(*       + by move: h; case: mfun1. *)
(*       + by move: h; case: mfun1. *)
(*       by move: h; case: mfun1 => // ?; case: mfun1. *)
(*     rewrite /errcutoff /nocutoff /is_error. *)
(*     move=> ?? [] // ? ? [] // ? /=?. *)
(*     + by move=> _ _ hpre_ /sum_postrelP //=. *)
(*     + by move=> _ _ hpre_ /sum_postrelP //=. *)
(*     + by move=> _ _ hpre_ /sum_postrelP /=. *)
(*     move=> hh _ hpre_ /sum_postrelP /=. *)
(*     rewrite /EPostRel /=; case: mfun1 hh => //; case: mfun1 => //. *)
(*   move=> s2 kt2 hpost. setoid_rewrite bind_ret_l. rewrite bind_ret_r. *)
(*   case hfin: finalize_funcall => [s3 | e ] /=; last first. *)
(*   + apply xrutt.xrutt_CutL. *)
(*     by rewrite /xrutt_facts.EE_MR /errcutoff /is_error /subevent /resum /fromErr /= mid12. *)
(*   rewrite /it_sems_one_varmap.finalize_funcall. *)
(*   case: hpost => hmerge hex hk. *)
(*   have -> /= : ra_valid p fd kt2.1. *)
(*   + move: hvalra. *)
(*     rewrite /valid_writefun /write_fd /ra_valid /=. *)
(*     case: sf_return_address ra_neq_magic checked_ra => //. *)
(*     + move => ra _ /and3P [] -> -> -> /= [] _ hra ?? /Sv.subset_spec ok_wrf. *)
(*       apply/Sv_memP => hin; apply: hra; apply: ok_wrf. *)
(*       by move: hk hin; clear; SvD.fsetdec. *)
(*     move=> ra_call ra_return _ _ /andP [hcall hreturn] _ _. *)
(*     apply /andP; split. *)
(*     + by case: ra_call hcall => [ra_call|//] /and3P[] -> -> _. *)
(*     by case: ra_return hreturn => [ra_return|//] /and3P[] -> -> _. *)
(*   have -> /= : saved_stack_valid_final p fd kt2.1. *)
(*   + move: hvalra. *)
(*     rewrite /valid_writefun /write_fd /saved_stack_valid_final /=. *)
(*     case: sf_save_stack checked_save_stack => // r; t_xrbindP => _ /Sv_memP r_not_written /Sv_memP. *)
(*     rewrite Sv.union_spec => ? /Sv.subset_spec ?; apply/Sv_memP. *)
(*     SvD.fsetdec. *)
(*   have -> /= : valid_RSP p (emem kt2.2) (evm kt2.2). *)
(*   + by rewrite /valid_RSP; case: hmerge => ? [] _ -> _ _; apply value_eqb_refl. *)
(*   rewrite bind_ret_l /=. *)
(*   case: hmerge => -[hscs' hmem' hvm'] [hstable hrsp' hgd' hal']. *)
(*   have hstable1 : stack_stable (emem t1) (free_stack (emem kt2.2)). *)
(*   + rewrite -hmem. *)
(*     have A := Memory.alloc_stackP ok_m'. *)
(*     have B := hstable. *)
(*     have C := Memory.free_stackP (emem kt2.2). *)
(*     split. *)
(*     - by rewrite -(ass_root A) (ss_root B) (fss_root C). *)
(*     - by rewrite -(ass_limit A) (ss_limit B) (fss_limit C). *)
(*     by rewrite (fss_frames C) -(ss_frames B) (ass_frames A). *)
(*   move/stack_stableP: (hstable1); rewrite -hmem => -> /=. *)
(*   rewrite bind_ret_l. *)
(*   apply xrutt.xrutt_Ret; rewrite /postF /=. *)
(*   move: hfin; rewrite /finalize_funcall; t_xrbindP. *)
(*   move=> vres ok_vres vres' ok_vres' ?; subst s3 => /=. *)
(*   split => //. *)
(*   + by rewrite /finalize_stk_mem hmem'. *)
(*   have [tres ok_tres res_uincl] : *)
(*     let: vm := (set_RSP p (free_stack (emem kt2.2)) (kill_vars (ra_vm_return (f_extra fd)) (evm kt2.2))) in *)
(*     exists2 tres, *)
(*       get_var_is false vm (f_res fd) = ok tres & List.Forall2 value_uincl vres' tres. *)
(*   - have : forall x, (x \in [seq (v_var i) | i <- f_res fd]) -> ~ Sv.In x DF. *)
(*     + move=> x hx; have /Sv_memP: Sv.mem x res by rewrite /res sv_of_listE. *)
(*       by move /Sv.is_empty_spec: hdisj; SvD.fsetdec. *)
(*     move: ok_vres'; rewrite /dc_truncate_val /= => /mapM2_id ?; subst vres'. *)
(*     move: hvm' ok_vres RSP_not_result. *)
(*     rewrite /res sv_of_listE /=; clear. *)
(*     move: (evm s2) (evm kt2.2) (free_stack _) => vm vm' m {s2 kt2} hvm. *)
(*     elim: vres (f_res fd) => [ | v vres ih ] [] //=; t_xrbindP => //. *)
(*     + by move => _ _ _; exists [::]. *)
(*     move => x xs vx hvxs <- ?; rewrite inE negb_or => /andP [ hne hnin] h; subst vx. *)
(*     have {ih} [ | tres -> /= res_uincl ] := ih _ hvxs hnin. *)
(*     + by move=> ? h1; apply h; rewrite inE h1 orbT. *)
(*     have ex : value_uincl vm.[x] (set_RSP p m (kill_vars (ra_vm_return fd.(f_extra)) vm')).[x]. *)
(*     + rewrite /set_RSP Vm.setP_neq //. *)
(*       have := h x; rewrite inE eqxx => /(_ erefl). *)
(*       rewrite Sv.union_spec => /Decidable.not_or [hra hD]. *)
(*       rewrite kill_varsE; case: Sv_memP => // _. *)
(*       by apply: hvm. *)
(*     by eexists; first reflexivity; constructor. *)
(*   rewrite hget; exists tres. *)
(*   split => //. *)
(*   + rewrite /writefun_ra hget. *)
(*     move: hvalra; rewrite /valid_writefun /write_fd /= => /Sv.subset_spec. *)
(*     by move: hk; clear; SvD.fsetdec. *)
(*   + by rewrite /writefun_RA hget; clear; SvD.fsetdec. *)
(*   + rewrite /writefun_ra hget => r hr; rewrite /set_RSP Vm.setP. *)
(*     case: eqP. *)
(*     - move => ?; subst. *)
(*       have ok_free := Memory.free_stackP (emem kt2.2). *)
(*       rewrite /top_stack (fss_root ok_free) -(ss_root hstable) (fss_frames ok_free) -(ss_frames hstable) /=. *)
(*       have ok_alloc:= Memory.alloc_stackP ok_m'. *)
(*       rewrite (ass_frames ok_alloc) (ass_root ok_alloc) /= -/(top_stack (emem s1)) cmp_le_refl. *)
(*       exact: hrsp. *)
(*     move => /eqP r_neq_rsp. *)
(*     rewrite kill_varsE. *)
(*     case: Sv_memP; first by SvD.fsetdec. *)
(*     move=> _; rewrite -(hex r). *)
(*     + rewrite /= /set_RSP Vm.setP_neq // /ra_undef_vm kill_varsE. *)
(*       by case: Sv_memP => //; SvD.fsetdec. *)
(*     move: hvalra hr; rewrite /valid_writefun /= /write_fd /= => /Sv.subset_spec. *)
(*     by clear; SvD.fsetdec. *)
(*   + by rewrite Vm.setP_eq /= cmp_le_refl hmem'. *)
(*   rewrite Vm.setP_neq; last by rewrite eq_sym vgd_neq_vrsp. *)
(*   rewrite kill_varsE; case: Sv_memP => //. *)
(*   have := not_written_magic preserved_magic. *)
(*   by rewrite /writefun_ra hget => -[+ _]; clear; SvD.fsetdec. *)
(* Qed. *)

Lemma merge_varmaps_export_callP fn:
  is_export p fn →
  wkequiv
    (fun fs t =>
      [/\ fscs fs = escs t
        , fmem fs = emem t
        & let m := fmem fs in
          let tvm1 := evm t in
          let args := fvals fs in
          match get_fundef (p_funcs p) fn with
          | Some fd =>
             ∃ (args' : seq value),
               [/\ tvm1.[vrsp] = Vword (top_stack m)
                 , tvm1.[vgd] = Vword global_data
                 , get_var_is false tvm1 (f_params fd) = ok args'
                 & List.Forall2 value_uincl args args']
          | None => true
          end])
    (isem_fun p global_data fn)
    (it_sems_one_varmap.isem_exportcall var_tmps p global_data fn)
    (fun fs' t' =>
      [/\ fscs fs' = escs t'
        , fmem fs' = emem t'
        & let m' := fmem fs' in
          let res := fvals fs' in
          let tvm2 := evm t' in
          match get_fundef (p_funcs p) fn with
          | Some fd =>
            ∃ (res' : seq value),
              get_var_is false tvm2 (f_res fd) = ok res' /\
              List.Forall2 value_uincl res res'
          | None => false
          end]).
Proof.
  case => fd ok_fd Export fs t; rewrite ok_fd /= => -[] hscs hmem /= [args'] [ hrsp hvgd hargs huargs].
  rewrite /isem_exportcall.
  case: (checkP ok_p ok_fd)=> _ok_wrf.
  rewrite /check_fd; t_xrbindP => D.
  rewrite /top_stack_aligned Export.
  set ID := (ID in check_c _ ID _).
  set DF := Sv.union _ D.
  set results := sv_of_list v_var (f_res fd).
  set params := sv_of_list v_var (f_params fd).
  move => checked_body hdisj checked_params RSP_not_result preserved_magic checked_save_stack tmp_call_magic.
  t_xrbindP => to_save_not_result ok_callee_saved ok_params.
  have /merge_varmaps_funP hsem : preF fn fn fs t.
  + rewrite /preF ok_fd; split => //.
    exists args'; split => //.
    by rewrite /top_stack_aligned Export.
  rewrite ok_fd /= bind_ret_l.
  rewrite RSP_not_result Export to_save_not_result hvgd value_eqb_refl //= bind_ret_l.
  rewrite -(bind_ret_r (isem_fun p global_data fn fs)).
  apply (xrutt_facts.xrutt_bind hsem).
  move=> s rt [hscs' hmem']; rewrite ok_fd => /= -[vres'] [hsub hsubk hget' hex hstable hrsp' hvgd' hures].
  have -> : Sv.subset (Sv.inter callee_saved (Sv.union rt.1 (ra_undef fd var_tmps)))
              (sv_of_list fst (sf_to_save (f_extra fd))).
  + apply /Sv.subset_spec.
    move/Sv.subset_spec: ok_callee_saved hsub.
    rewrite /writefun_ra ok_fd.
    move: (ra_vm_return _) => W.
    move: (sv_of_list _ _) => C.
    move: (ra_undef _ _) => X.
    by clear; SvD.fsetdec.
  by rewrite /= bind_ret_l; apply xrutt.xrutt_Ret; split => //; exists vres'; split.
Qed.

Lemma merge_varmaps_export_call_checkP fn:
  is_export p fn →
  wkequiv
    (fun fs t =>
      [/\ fscs fs = escs t
        , fmem fs = emem t
        & let m := fmem fs in
          let tvm1 := evm t in
          let args := fvals fs in
          match get_fundef (p_funcs p) fn with
          | Some fd =>
             ∃ (args' : seq value),
               [/\ tvm1.[vrsp] = Vword (top_stack m)
                 , tvm1.[vgd] = Vword global_data
                 , get_var_is false tvm1 (f_params fd) = ok args'
                 & List.Forall2 value_uincl args args']
          | None => true
          end])
    (isem_fun p global_data fn)
    (it_sems_one_varmap.isem_exportcall_check var_tmps p global_data fn)
    (fun fs' t' =>
      [/\ fscs fs' = escs t'
        , fmem fs' = emem t'
        & let m' := fmem fs' in
          let res := fvals fs' in
          let tvm2 := evm t' in
          match get_fundef (p_funcs p) fn with
          | Some fd =>
            ∃ (res' : seq value),
              get_var_is false tvm2 (f_res fd) = ok res' /\
              List.Forall2 value_uincl res res'
          | None => false
          end]).
Proof.
  move=> /merge_varmaps_export_callP => h fs s /h.
  have -> // : isem_exportcall var_tmps p global_data fn s ≈ isem_exportcall_check var_tmps p global_data fn s.
  rewrite /isem_exportcall /isem_exportcall_check.
  case ok_fd : (get_fundef (p_funcs p) fn) => [fd | ] /=; last first.
  + rewrite !bind_throw; reflexivity.
  rewrite !bind_ret_l.
  apply eqit_bind => [|_]; first reflexivity.
  rewrite isem_fun_isem_fun_check.
  rewrite /isem_fun_check /it_sems_one_varmap.isem_fun_def.
  setoid_rewrite mrec_as_interp.
  rewrite /= /it_sems_one_varmap.isem_fun_body.
  rewrite /it_sems_one_varmap.initialize_funcall ok_fd /=.
  setoid_rewrite bind_ret_l.
  case: alloc_stack => [m | err] /=.
  + rewrite bind_ret_l; reflexivity.
  rewrite bind_throw.
  set F := (mrecursive _ ).
  have interp_throw : forall T e, interp F (Exception.throw (X:=T) e) ≈ Exception.throw e.
  + by move=> T e; rewrite interp_vis bind_trigger; apply eqit_Vis => -[].
  case: saved_stack_valid_init => /=; last first.
  + rewrite bind_throw interp_throw bind_throw; reflexivity.
  rewrite bind_ret_l.
  case: top_stack_aligned => /=; last first.
  + rewrite bind_throw interp_throw bind_throw; reflexivity.
  case: valid_RSP => /=; rewrite bind_throw interp_throw bind_throw; reflexivity.
Qed.

End PROG.

End WITH_PARAMS.
