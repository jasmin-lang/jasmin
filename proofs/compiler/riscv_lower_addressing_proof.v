(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import ssralg.

Require Import psem psem_facts compiler_util lea_proof.

Require Import
  arch_decl
  arch_extra
  sem_params_of_arch_extra
  riscv_instr_decl
  riscv_decl
  riscv
  riscv_extra.

Require Export riscv_lower_addressing.

(* ** proofs
 * -------------------------------------------------------------------- *)

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {atoI : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {pT : progT}
  {sCP : semCallParams}.

Context (fresh_reg : string -> atype -> Ident.ident).

Context (p p' : prog).

Hypothesis ok_p' : lower_addressing_prog fresh_reg p = ok p'.

Context (ev : extra_val_t).

Lemma lower_addressing_prog_invariants :
  p.(p_globs) = p'.(p_globs) /\ p.(p_extra) = p'.(p_extra).
Proof.
  move: ok_p'; rewrite /lower_addressing_prog.
  by t_xrbindP=> _ _ <- /=.
Qed.

(* For convenience in this file, we prove this trivial corollary. *)
#[local]
Lemma eq_globs :
  p.(p_globs) = p'.(p_globs).
Proof. by have [? _] := lower_addressing_prog_invariants. Qed.

Lemma lower_addressing_fd_invariants :
  forall fn fd,
  get_fundef p.(p_funcs) fn = Some fd ->
  exists2 fd',
    get_fundef p'.(p_funcs) fn = Some fd' &
    [/\ fd.(f_info) = fd'.(f_info),
        fd.(f_tyin) = fd'.(f_tyin),
        fd.(f_params) = fd'.(f_params),
        fd.(f_tyout) = fd'.(f_tyout),
        fd.(f_res) = fd'.(f_res) &
        fd.(f_extra) = fd'.(f_extra)].
Proof.
  move=> fn fd get_fd.
  move: ok_p'; rewrite /lower_addressing_prog.
  t_xrbindP=> funcs ok_funcs <-.
  have [fd' ok_fd' get_fd'] := get_map_cfprog_gen ok_funcs get_fd.
  exists fd' => //.
  move: ok_fd'; rewrite /lower_addressing_fd.
  by t_xrbindP=> _ _ <- /=.
Qed.

Lemma shift_of_scaleP scale shift w :
  shift_of_scale scale = Some shift ->
  riscv_sll_semi w (wrepr U8 (Z.of_nat shift)) = (wrepr Uptr scale * w)%R.
Proof.
  by case: scale => // -[|[|[|[]|]|]|] //= [<-]; rewrite /riscv_sll_semi wshl_sem.
Qed.

Lemma compute_addrP ii (tmp : var_i) e prelude ep s1 we :
  sem_pexpr true p'.(p_globs) s1 e >>= to_pointer = ok we ->
  vtype tmp = aword Uptr ->
  compute_addr tmp e = Some (prelude, ep) ->
  exists vm1, [/\
    esem p' ev (map (MkI ii) prelude) s1 = ok (with_vm s1 vm1),
    evm s1 =[\Sv.singleton tmp] vm1 &
    sem_pexpr true p'.(p_globs) (with_vm s1 vm1) ep >>= to_pointer = ok we ].
Proof.
  move=> ok_we tmp_ty.
  rewrite /compute_addr.
  case hlea: mk_lea => [[disp base scale offset]|//] /=.
  case: base hlea => [base|//] hlea.
  case: offset hlea => [offset|//] hlea.
  case: eqP => [//|hneq] /=.
  case hshift: shift_of_scale => [shift|//] /=.
  move=> [<- <-] {prelude ep}.
  move: ok_we; t_xrbindP=> ve ok_ve /to_wordI' [ws] [w] [hle1 ??]. subst ve we.
  have /(_ (cmp_le_refl _) hle1) := mk_leaP _ _ hlea ok_ve.
  rewrite /sem_lea /=.
  (* t_xrbindP too aggressive *)
  apply: rbindP => wb.
  apply: rbindP => vb ok_vb ok_wb.
  apply: rbindP => wo.
  apply: rbindP => vo ok_vo ok_wo.
  move=> /ok_inj; rewrite GRing.addrC => {}lea_sem.

  eexists _; split.
  + rewrite /sem_sopn /= wrepr_unsigned.
    rewrite /get_gvar /= ok_vo /=.
    rewrite /exec_sopn /= ok_wo /=.
    Local Opaque riscv_sll_semi.
    rewrite truncate_word_le //= zero_extend_wrepr //.
    rewrite /sopn_sem /= (shift_of_scaleP _ hshift) /=.
    Local Transparent riscv_sll_semi.
    rewrite write_var_eq_type //=; last by rewrite tmp_ty.
    rewrite /get_gvar /= get_var_eq tmp_ty /= cmp_le_refl orbT //.
    rewrite get_var_neq // ok_vb /=.
    rewrite ok_wb /= truncate_word_u /=.
    by rewrite write_var_eq_type /with_vm //= tmp_ty.
  + do 2 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by move=> /Sv.singleton_spec).
    by apply eq_ex_refl.
  rewrite /get_gvar /= get_var_eq /= tmp_ty /= cmp_le_refl orbT //=.
  by rewrite /sem_sop2 /= !truncate_word_u /= truncate_word_u -lea_sem wrepr_unsigned.
Qed.

Lemma is_one_LmemP xs al ws x e :
  is_one_Lmem xs = Some (al, ws, x, e) ->
  xs = [:: Lmem al ws x e].
Proof. by case: xs => [//|] [] // _ _ _ _ [] //= [-> -> -> ->]. Qed.

Lemma is_one_PloadP es al ws e :
  is_one_Pload es = Some (al, ws, e) ->
  es = [:: Pload al ws e].
Proof. by case: es => [//|] [] // _ _ _ [] //= [-> -> ->]. Qed.

Let sip := sip_of_asm_e.

Lemma Hopn_aux (s1 s2 : estate) (t : assgn_tag) (o : sopn) (xs : lvals) (es : pexprs) (ii : instr_info) (tmp : var_i) (vm1 : Vm.t) X:
  sem_sopn (p_globs p) o s1 xs es = ok s2 ->
  vtype tmp = aword Uptr ->
  ~ Sv.In tmp X -> Sv.Subset (read_I (MkI ii (Copn xs t o es))) X ->
  evm s1 =[X] vm1 ->
  exists2 vm2 : Vm.t,
    esem p' ev (lower_addressing_i tmp (MkI ii (Copn xs t o es)))  (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    evm s2 =[X] vm2.
Proof.
  rewrite !read_writeE => ok_s2 tmp_ty tmp_nin hsub eq_vm1 /=.
  have [vm2 hsem eq_vm2] :
     exists2 vm2 : Vm.t, sem_sopn (p_globs p) o (with_vm s1 vm1) xs es = ok (with_vm s2 vm2) & evm s2 =[X] vm2.
    move: ok_s2; rewrite /sem_sopn; t_xrbindP => vs vr hes hex hw.
    have [|vm2 hw2 heq2] := write_lvals_eq_on _ hw eq_vm1; first by SvD.fsetdec.
    exists vm2; last by apply: eq_onI heq2; SvD.fsetdec.
    rewrite  -(read_es_eq_on _ _ (s := X)) //; last first.
    + by move=> z;rewrite read_esE => hz;apply eq_vm1; SvD.fsetdec.
    by rewrite hes /= hex /= hw2.
  rewrite eq_globs in hsem.
  have: [elaborate exists2 vm2,
    esem p' ev [:: MkI ii (Copn xs t o es)] (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    evm s2 =[X] vm2].
  + by exists vm2 => //=; rewrite LetK.

  case hxs: is_one_Lmem => [[[[al ws] x] e]|].
  + move: hxs => /is_one_LmemP ?; subst xs.
    case hcompute: compute_addr => [[prelude ep]|//] _.
    move: hsem; rewrite /sem_sopn.
    t_xrbindP => -[] // v [] /=; last by t_xrbindP.
    t_xrbindP=> vs ok_vs ok_v ? we ve ok_ve ok_we w ok_w
      m2 ok_m2 <- /= [eq_scs ??]; subst vm2 m2.
    have /(_ (with_vm s1 vm1) we) := compute_addrP ii _ tmp_ty hcompute.
    rewrite ok_ve /= ok_we.
    move=> /(_ erefl) [vm1' [hsem1' eq_vm1' ok_ep]].
    exists vm1'.
    + rewrite map_cat esem_cat hsem1' /= LetK.
      rewrite /sem_sopn /=.
      rewrite -(eq_on_sem_pexprs _ _ (s:=with_vm s1 vm1)) //=; last first.
      + apply: (eq_ex_disjoint_eq_on eq_vm1').
        by apply/disjointP => ?; SvD.fsetdec.
      rewrite ok_vs /= ok_v /= ok_ep /= ok_w /= ok_m2 /=.
      by rewrite /with_mem /with_vm /= eq_scs.
    move=> z hz; rewrite eq_vm2 // eq_vm1' //; SvD.fsetdec.

  case hes: is_one_Pload => [[[al ws] e]|//].
  move: hes => /is_one_PloadP ?; subst es.
  case hcompute: compute_addr => [[prelude ep]|//] _.
  move: hsem; rewrite /sem_sopn /=.
  t_xrbindP=> /= vs _ _ we ve ok_ve ok_we w ok_w <- <- ok_vs ok_vm2.
  have /(_ (with_vm s1 vm1) we) := compute_addrP ii _ tmp_ty hcompute.
  rewrite ok_ve /= ok_we.
  move=> /(_ erefl) [vm1' [hsem1' eq_vm1' ok_ep]].
  have [|vm1'' ok_vm1'' eq_vm1''] := write_lvals_eq_ex _ ok_vm2 eq_vm1'.
  + by apply/disjointP => ?; SvD.fsetdec.
  exists vm1''.
  + rewrite map_cat esem_cat hsem1' /= LetK.
    by rewrite /sem_sopn /= ok_ep /= ok_w /= ok_vs /= ok_vm1''.
  move=> z hz; rewrite eq_vm2 // -eq_vm1'' //=; SvD.fsetdec.
Qed.

Section SEM.

Let Pi s1 i s2 :=
  forall X (tmp : var_i) vm1,
    vtype tmp = aword Uptr ->
    ~ Sv.In tmp X -> Sv.Subset (read_I i) X ->
    evm s1 =[X] vm1 ->
    exists2 vm2,
      sem p' ev (with_vm s1 vm1) (lower_addressing_i tmp i) (with_vm s2 vm2)
      & evm s2 =[X] vm2.

Let Pi_r s1 i s2 :=
  forall ii,
    Pi s1 (MkI ii i) s2.

Let Pc s1 c s2 :=
  forall X (tmp : var_i) vm1,
    vtype tmp = aword Uptr ->
    ~ Sv.In tmp X -> Sv.Subset (read_c c) X ->
    evm s1 =[X] vm1 ->
    exists2 vm2,
      sem p' ev (with_vm s1 vm1) (lower_addressing_c tmp c) (with_vm s2 vm2)
      & evm s2 =[X] vm2.

Let Pfor (i:var_i) zs s1 c s2 :=
  forall X (tmp : var_i) vm1,
    vtype tmp = aword Uptr ->
    ~ Sv.In tmp X -> Sv.Subset (read_c c) X ->
    evm s1 =[X] vm1 ->
    exists2 vm2,
      sem_for p' ev i zs (with_vm s1 vm1) (lower_addressing_c tmp c) (with_vm s2 vm2)
      & evm s2 =[X] vm2.

Let Pfun scs1 m1 fn vargs scs2 m2 vres :=
  sem_call p' ev scs1 m1 fn vargs scs2 m2 vres.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move=> s X tmp vm1 _ _ _ eq_vm1; exists vm1 => //.
  by apply: Eskip.
Qed.

Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ Hu _ Hc X tmp vm1 tmp_ty tmp_nin; rewrite read_writeE => hsub eq_vm1.
  have [|vm2 hsem2 eq_vm2] := Hu X tmp vm1 tmp_ty tmp_nin _ eq_vm1; first SvD.fsetdec.
  have [|vm3 hsem3 eq_vm3] := Hc X tmp vm2 tmp_ty tmp_nin _ eq_vm2; first SvD.fsetdec.
  exists vm3 => //.
  by apply (sem_app hsem2 hsem3).
Qed.

Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof. done. Qed.

Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s1 s2 x tag ty e v v' He htr Hw ii X tmp vm1 _ _; rewrite !read_writeE => hsub eq_vm1 /=.
  have [|vm2 Hw2 eq_vm2] := write_lval_eq_on _ Hw eq_vm1; first SvD.fsetdec.
  rewrite eq_globs in Hw2.
  exists vm2 => //; last by apply: eq_onI eq_vm2; SvD.fsetdec.
  apply: sem_seq_ir; apply: Eassgn htr _ => //.
  rewrite -eq_globs -(eq_on_sem_pexpr _ _ (s:=s1)) //=.
  by apply: eq_onI eq_vm1; SvD.fsetdec.
Qed.

Local Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  rewrite /sem_Ind_opn /Pi_r /Pi.
  move=> s1 s2 t o xs es hopn ii X tmp vm1 htytmp hnin hsub heq.
  have [vm2 /esem_sem ??]:= Hopn_aux hopn htytmp hnin hsub heq.
  by exists vm2.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> s1 scs mem s2 o xs es ves vs hes ho hw ii X tmp vm1 tmp_ty tmp_nin hsub eq_vm1.
  rewrite !read_writeE in hsub.
  have [|vm2 hw2 eq_vm2] := write_lvals_eq_on _ hw eq_vm1; first SvD.fsetdec.
  rewrite eq_globs in hw2.
  exists vm2 => //; last by apply: eq_onI eq_vm2; SvD.fsetdec.
  apply: sem_seq_ir; apply: (Esyscall _ (s1:=with_vm _ _) _ ho hw2).
  rewrite -eq_globs -(eq_on_sem_pexprs _ _ (s:=s1)) //=.
  by apply: eq_onI eq_vm1; SvD.fsetdec.
Qed.

Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 He _ Hc1 ii X tmp vm1 tmp_ty tmp_nin; rewrite !read_writeE => hsub eq_vm1 /=.
  have [|vm2 hsem2 eq_vm2] := Hc1 X tmp vm1 tmp_ty tmp_nin _ eq_vm1; first SvD.fsetdec.
  exists vm2 => //.
  apply: sem_seq_ir; apply: Eif_true => //.
  rewrite -eq_globs.
  rewrite -(eq_on_sem_pexpr _ _ (s:=s1)) //=.
  apply: eq_onI eq_vm1; SvD.fsetdec.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 He _ Hc2 ii X tmp vm1 tmp_ty tmp_nin; rewrite !read_writeE => hsub eq_vm1 /=.
  have [|vm2 hsem2 eq_vm2] := Hc2 X tmp vm1 tmp_ty tmp_nin _ eq_vm1; first SvD.fsetdec.
  exists vm2 => //.
  apply: sem_seq_ir; apply: Eif_false => //.
  rewrite -eq_globs.
  rewrite -(eq_on_sem_pexpr _ _ (s:=s1)) //=.
  apply: eq_onI eq_vm1; SvD.fsetdec.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 s3 s4 a c e info c' _ Hc He _ Hc' Hw1 Hw ii X tmp vm1 tmp_ty tmp_nin hsub eq_vm1 /=.
  have hsub' := hsub; rewrite !read_writeE in hsub'.
  have [|vm2 hsem2 eq_vm2] := Hc X tmp vm1 tmp_ty tmp_nin _ eq_vm1; first SvD.fsetdec.
  have [|vm3 hsem3 eq_vm3] := Hc' X tmp vm2 tmp_ty tmp_nin _ eq_vm2; first SvD.fsetdec.
  have [vm4 hsem4 eq_vm4] := Hw ii X tmp vm3 tmp_ty tmp_nin hsub eq_vm3.
  exists vm4 => //=.
  apply: sem_seq_ir; apply: Ewhile_true.
  + by apply hsem2.
  + rewrite -eq_globs.
    rewrite -(eq_on_sem_pexpr _ _ (s:=s2)) //=.
    by apply: eq_onI eq_vm2; SvD.fsetdec.
  + by apply hsem3.
  by move: hsem4 => /= /sem_seq1_iff /sem_IE.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 a c e info c' _ Hc He ii X tmp vm1 tmp_ty tmp_nin; rewrite !read_writeE => hsub eq_vm1.
  have [|vm2 hsem2 eq_vm2] := Hc X tmp vm1 tmp_ty tmp_nin _ eq_vm1; first SvD.fsetdec.
  exists vm2 => //=.
  apply: sem_seq_ir; apply: Ewhile_false => //.
  rewrite -eq_globs.
  rewrite -(eq_on_sem_pexpr _ _ (s:=s2)) //=.
  by apply: eq_onI eq_vm2; SvD.fsetdec.
Qed.

Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s1 s2 i d lo hi c vlo vhi Hlo Hhi _ Hfor ii X tmp vm1 tmp_ty tmp_nin; rewrite !read_writeE => hsub eq_vm1.
  have [|vm2 hsem2 eq_vm2] := Hfor X tmp vm1 tmp_ty tmp_nin _ eq_vm1; first SvD.fsetdec.
  exists vm2 => //=.
  apply: sem_seq_ir; apply: Efor hsem2.
  + rewrite -eq_globs.
    rewrite -(eq_on_sem_pexpr _ _ (s:=s1)) //=.
    by apply: eq_onI eq_vm1; SvD.fsetdec.
  rewrite -eq_globs.
  rewrite -(eq_on_sem_pexpr _ _ (s:=s1)) //=.
  by apply: eq_onI eq_vm1; SvD.fsetdec.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof.
  by move=> s i c X tmp vm1 tmp_ty tmp_nin hsub eq_vm1; exists vm1 => //; constructor.
Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move => s1 s1' s2 s3 i w ws c Hw _ Hc _ Hf X tmp vm1 tmp_ty tmp_nin hsub eq_vm1.
  have [vm2 Hw2 eq_vm2] := write_var_eq_on Hw eq_vm1.
  have {}eq_vm2: evm s1' =[X] vm2 by apply: eq_onI eq_vm2; SvD.fsetdec.
  have [vm3 hsem3 eq_vm3] := Hc X tmp vm2 tmp_ty tmp_nin hsub eq_vm2.
  have [vm4 hsem4 eq_vm4] := Hf X tmp vm3 tmp_ty tmp_nin hsub eq_vm3.
  by exists vm4 => //; apply: EForOne Hw2 hsem3 hsem4.
Qed.

Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s1 scs2 m2 s2 xs fn args vargs vs Hargs Hcall Hfun Hvs
    ii X tmp vm1 tmp_ty tmp_nin; rewrite !read_writeE => hsub eq_vm1.
  have [|vm2 Hvs2 eq_vm2] := write_lvals_eq_on _ Hvs eq_vm1; first SvD.fsetdec.
  rewrite eq_globs in Hvs2.
  exists vm2 => //; last by apply: eq_onI eq_vm2; SvD.fsetdec.
  apply: sem_seq_ir; apply: (Ecall (s1:=with_vm _ _) _ Hfun Hvs2).
  rewrite -eq_globs.
  rewrite -(eq_on_sem_pexprs _ _ (s:=s1)) //=.
  apply:eq_onI eq_vm1; SvD.fsetdec.
Qed.

Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> scs1 m1 sc2 m2 fn f vargs vargs' s0 s1 s2 vres vres'
    Hget Hargs Hi Hw _ Hc Hres Hfull Hscs Hfi.
  rewrite /Pfun.
  move: ok_p'; rewrite /lower_addressing_prog.
  set tmp := {| v_var := _; v_info := _ |}.
  t_xrbindP=> funcs ok_funcs ?; subst p'.
  have [f' ok_f' Hget'] := get_map_cfprog_gen ok_funcs Hget.
  move: ok_f'; rewrite /lower_addressing_fd.
  t_xrbindP=> /Sv_memP tmp_nin1 /Sv_memP tmp_nin2 ?; subst f'.
  set X := Sv.union (read_c (f_body f)) (vars_l (f_res f)).
  have tmp_nin : ~Sv.In tmp X by rewrite /X; SvD.fsetdec.
  have [|vm2 hsem2 eq_vm2] := Hc X tmp (evm s1) erefl tmp_nin _ (eq_on_refl _); first SvD.fsetdec.
  rewrite with_vm_same in hsem2.
  move: Hres.
  rewrite -(sem_pexprs_get_var _ p.(p_globs)).
  rewrite (eq_on_sem_pexprs _ (s' := with_vm s2 vm2)) //=; last first.
  + apply: eq_onI eq_vm2.
    by rewrite vars_l_read_es; SvD.fsetdec.
  rewrite sem_pexprs_get_var => Hres.
  by apply: EcallRun; eassumption.
Qed.

Lemma lower_addressing_progP scs mem f va scs' mem' vr:
  sem_call p ev scs mem f va scs' mem' vr ->
  sem_call p' ev scs mem f va scs' mem' vr.
Proof.
  exact:
    (sem_call_Ind
       Hskip
       Hcons
       HmkI
       Hassgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hfor
       Hfor_nil
       Hfor_cons
       Hcall
       Hproc).
Qed.

End SEM.

Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE0 : EventRels E0}.

#[ local ]
Lemma checker_st_eq_onP_ : Checker_eq p p' checker_st_eq_on.
Proof. apply checker_st_eq_onP; apply eq_globs. Qed.
#[local] Hint Resolve checker_st_eq_onP_ : core.

Lemma it_lower_addressing_progP fn:
  wiequiv_f p p' ev ev (rpreF (eS:=eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  apply wequiv_fun_ind => {}fn _ fs _ [<-] <- fd hget.
  move: ok_p'; rewrite /lower_addressing_prog.
  set tmp := {| v_var := _; v_info := _ |}.
  t_xrbindP=> funcs ok_funcs hp'.
  have [f' ok_f' hget'] := get_map_cfprog_gen ok_funcs hget.
  move: ok_f'; rewrite /lower_addressing_fd.
  t_xrbindP=> /Sv_memP tmp_nin1 /Sv_memP tmp_nin2 ?; subst f'.
  set X := Sv.union (read_c (f_body fd)) (vars_l (f_res fd)).
  have tmp_nin : ~Sv.In tmp X by rewrite /X; SvD.fsetdec.
  have htytmp : vtype tmp = aword Uptr by [].
  rewrite -{1}hp' /=; eexists; first by eauto.
  move => s.
  set c' := lower_addressing_c tmp (f_body fd).
  move=> /(eq_initialize (sip:= sip) (p':=p') (fd':=with_body fd c')) -> //; last by rewrite -hp'.
  exists s; first reflexivity.
  exists (st_eq_on X), (st_eq_on X).
  split => //=; last first.
  + apply wrequiv_weaken with (st_eq_on (vars_l (f_res fd))) eq => //.
    + by apply st_rel_weaken => ??; apply eq_onI; rewrite /= /X; clear; SvD.fsetdec.
    by apply: (st_eq_on_finalize (fd':=with_body fd c')).
  clear ok_funcs funcs fs fn hget' tmp_nin1 tmp_nin2 s hp' hget; subst c'.
  have : Sv.Subset (read_c (f_body fd)) X by rewrite /X; clear; SvD.fsetdec.
  move: tmp X tmp_nin htytmp (f_body fd) => tmp X tmp_nin htytmp {fd}.
  set Pi := fun i =>
    Sv.Subset (read_I i) X ->
    wequiv_rec (sip:=sip) p p' ev ev eq_spec (st_eq_on X) [::i] (lower_addressing_i tmp i) (st_eq_on X).
  set Pi_r := fun i => forall ii, Pi (MkI ii i).
  set Pc := fun c =>
    Sv.Subset (read_c c) X ->
    wequiv_rec (sip:=sip) p p' ev ev eq_spec (st_eq_on X) c (lower_addressing_c tmp c) (st_eq_on X).
  apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => //; subst Pi_r Pi Pc => /=.
  + by move=> hsub /=; apply (wequiv_nil (sip:=sip)).
  + move=> i c hi hc; rewrite read_writeE => hsub.
    rewrite /lower_addressing_c /conc_map /= -cat1s.
    apply (wequiv_cat (sip:=sip)) with (st_eq_on X).
    + by apply hi => //; SvD.fsetdec.
    apply hc; last by SvD.fsetdec.
  + move=> x tg ty e ii; rewrite !read_writeE => hsub.
    apply (wequiv_assgn_rel_eq (sip:=sip)) with checker_st_eq_on X => //.
    + by split => //; rewrite /read_es /= read_eE; SvD.fsetdec.
    split => //; first by SvD.fsetdec.
    by rewrite /read_rvs /= read_rvE; SvD.fsetdec.
  + move=> xs tg o es ii hsub.
    apply (wequiv_opn_esem (sip:=sip)) => s t s' /st_relP [-> /= heq] hopn.
    have [vm2 h ?]:= Hopn_aux hopn htytmp tmp_nin hsub heq.
    by eexists; first apply h.
  + move=> xs sc es ii; rewrite !read_writeE => hsub.
    by apply (wequiv_syscall_rel_eq (sip:=sip)) with checker_st_eq_on X => //=; split=> //; SvD.fsetdec.
  + by move=> ? ii ?; apply wequiv_noassert with (ev1:=ev) (ii:=ii).
  + move=> e c1 c2 hc1 hc2 ii; rewrite !read_writeE => hsub.
    apply (wequiv_if_rel_eq (sip:=sip)) with checker_st_eq_on X X X => //.
    + by split => //; rewrite /read_es /= read_eE; SvD.fsetdec.
    + by apply hc1; SvD.fsetdec.
    by apply hc2; SvD.fsetdec.
  + move=> x dir lo hi c hc ii; rewrite !read_writeE => hsub.
    apply (wequiv_for_rel_eq (sip:=sip)) with checker_st_eq_on X X => //.
    + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
    + by split => //; rewrite /read_rvs /=; SvD.fsetdec.
    by apply hc => //; SvD.fsetdec.
  + move=> a c1 e ii' c2 hc1 hc2 ii; rewrite !read_writeE => hsub.
    apply (wequiv_while_rel_eq (sip:=sip)) with checker_st_eq_on X => //.
    + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
    + by apply hc1 => //; SvD.fsetdec.
    by apply hc2 => //; SvD.fsetdec.
  move=> xs fn es ii; rewrite !read_writeE => hsub.
  apply (wequiv_call_rel_eq (sip:=sip)) with checker_st_eq_on X => //.
  + by split => //; SvD.fsetdec.
  + by split => //; SvD.fsetdec.
  by move=> ???; apply: (wequiv_fun_rec (spec := eq_spec)).
Qed.

End IT.

End WITH_PARAMS.
