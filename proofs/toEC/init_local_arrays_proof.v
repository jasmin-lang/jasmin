From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem compiler_util.
Require Export init_local_arrays.

Section INIT_LOCAL_ARRAYS_PROOF.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.

Context
  (p p' : uprog)
  (ev : extra_val_t)
  (init_local_arrays_ok : init_local_arrays_prog p = p')
.

Lemma init_local_arrays_eq_globs : p_globs p = p_globs p'.
Proof using init_local_arrays_ok.
  by move: init_local_arrays_ok; rewrite /init_local_arrays_prog => <-.
Qed.

Lemma get_fundef_init_local_arrays fn :
  get_fundef (p_funcs (init_local_arrays_prog p)) fn =
    omap init_local_arrays_fd (get_fundef (p_funcs p) fn).
Proof.
rewrite /get_fundef /init_local_arrays_prog /=.
by elim: (p_funcs p) => [ | [fn' fd'] pfuns ih] //=; case: eqP.
Qed.

Lemma vrvs_map_Lvar (xs : seq var_i) :
  Sv.Equal (vrvs [seq Lvar i | i <- xs]) (vars_l xs).
Proof using E E0 dc ep rE0 spp syscall_state wE wsw.
elim: xs => [ | x xs ih] /=; first by SvD.fsetdec.
by rewrite vrvs_cons vrv_var ih; SvD.fsetdec.
Qed.

Lemma local_arraysP fd x :
  x \in local_arrays fd ->
  is_local_array_var x /\ ~ Sv.In x (vars_l (f_params fd)).
Proof.
rewrite /local_arrays mem_filter => /andP [] harr /Sv_elemsP hin.
split=> //.
by move: hin; rewrite Sv.diff_spec => -[_].
Qed.

Lemma init_local_arrays_init_locals fd fs s :
  initialize_funcall p ev fd fs = ok s ->
  forall x, x \in local_arrays fd -> (evm s).[x] = Vm.init.[x].
Proof using E E0 asm_op dc ep ev p rE0 sip spp syscall_state wE wsw.
rewrite /initialize_funcall; t_xrbindP => vs hargs s0 hini hw x hx.
have [_ hnotin] := local_arraysP hx.
move: hw; rewrite (write_vars_lvals _ (p_globs p)) => hw.
rewrite -(disjoint_eq_ons (s := Sv.singleton x) _ hw).
- by move: hini => [<-] /=; rewrite Vm.initP.
- rewrite /disjoint; apply/Sv.is_empty_spec; rewrite vrvs_map_Lvar.
  by SvD.fsetdec.
by SvD.fsetdec.
Qed.

Lemma init_local_array_instrP (ii : instr_info) x s1 s2 :
  is_local_array_var x ->
  (evm s1).[x] = Vm.init.[x] ->
  st_eq tt s1 s2 ->
  exists2 s2',
    sem_assgn p' (Lvar {| v_var := x; v_info := dummy_var_info |})
      AT_none (vtype x)
      (match vtype x with
       | aarr ws n => Parr_init ws n
       | _ => Parr_init U8 0
       end) s2 = ok s2'
    & st_eq tt s1 s2'.
Proof.
move=> harr hx [hscs hmem hvm].
move: harr; rewrite /is_local_array_var.
case hty: (vtype x) => [ | | ws n | ] // _.
rewrite /sem_assgn /=.
rewrite /truncate_val /= WArray.castK /=.
eexists.
- apply/write_varP; split=> //; rewrite hty /= eqxx //.
split=> //=.
move: hvm; rewrite !vm_eq_vm_rel => hu1.
apply: (vm_rel_set_r (P := PredT)) => //.
move=> _ /=.
rewrite hty /=.
by rewrite if_same hx Vm.initP hty.
by apply: (vm_relI _ hu1).
Qed.

Let Rprefix (xs : seq var) (s1 s2 : estate) : Prop :=
  st_eq tt s1 s2 /\
  forall x, x \in xs -> is_local_array_var x /\ (evm s1).[x] = Vm.init.[x].

Lemma init_local_arrays_prefixP ii (xs : seq var) :
  wequiv_rec p p' ev ev eq_spec (Rprefix xs)
    [::] (map (init_local_array_instr ii) xs) (st_eq tt).
Proof.
elim: xs => [ | x xs ih] /=.
- apply wequiv_nil.
  by move=> s1 s2 [].
apply (wequiv_cat (R := Rprefix xs)
  (c1 := [::]) (c1' := [::])
  (c2 := [:: init_local_array_instr ii x])
  (c2' := map (init_local_array_instr ii) xs)).
- apply wequiv_assign_right => s1 s2 [heq hloc].
  have [harr hx] := hloc x (mem_head _ _).
  have [s2' heq1 heq2] := init_local_array_instrP ii harr hx heq.
  exists s2'; first exact: heq1.
  split=> //.
  by move=> y hy; apply: hloc; rewrite in_cons hy orbT.
exact: ih.
Qed.

Lemma init_local_arrays_proof fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using init_local_arrays_ok.
apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hget.
exists (init_local_arrays_fd fd).
- by rewrite -init_local_arrays_ok get_fundef_init_local_arrays hget.
move=> s11 hinit.
exists s11.
- by apply: (eq_initialize _ _ _ _ hinit) => //; rewrite -init_local_arrays_ok.
exists (Rprefix (local_arrays fd)), (st_eq tt); split.
- split=> //.
  move=> x hx; split; [case: (local_arraysP hx) => // |
    exact (init_local_arrays_init_locals hinit hx)].
- rewrite /init_local_arrays_fd /init_local_arrays_body /=.
  rewrite -{1}(cat0s (f_body fd)).
  apply (wequiv_cat (R := st_eq tt)
    (c1 := [::]) (c1' := f_body fd)
    (c2 := map (init_local_array_instr (entry_info_of_fun_info (f_info fd)))
             (local_arrays fd))
    (c2' := f_body fd)).
  + exact: init_local_arrays_prefixP.
  by apply/wequiv_rec_st_eq/init_local_arrays_eq_globs.
exact: (st_eq_finalize erefl erefl erefl).
Qed.

End INIT_LOCAL_ARRAYS_PROOF.
