From mathcomp
Require Import all_ssreflect all_algebra.
Require Import compiler_util psem.
Require Import x86_gen x86_variables_proofs asmgen_proof.

Import Utf8.
Import Relation_Operators.
Import linear linear_sem x86_sem x86_decl x86_variables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma assemble_progP p p' :
  assemble_prog p = ok p' →
  let rip := mk_rip p.(lp_rip) in
  [/\ disj_rip rip,
   xp_globs p' = lp_globs p &
   map_cfprog (assemble_fd RSP rip) p.(lp_funcs) = ok (xp_funcs p') ].
Proof.
  apply: rbindP => _ /assertP /eqP h.
  apply: rbindP => fds ok_fds [<-].
  split => //.
  split => r heq //.
  by move: h; rewrite -heq register_of_var_of_register.
Qed.

(* Assembling preserves labels *)

Lemma assemble_c_labels rip a b :
  assemble_c rip a = ok b →
  label_in_lcmd a = label_in_asm b.
Proof.
  move => /mapM_Forall2; elim => // { a b }.
  move => x y a b ok_y _ ih.
  rewrite /label_in_lcmd -cat1s pmap_cat.
  rewrite /label_in_asm -(cat1s y) pmap_cat.
  congr (_ ++ _); last exact: ih.
  case: x ok_y { ih } => ii [] /=; t_xrbindP => *.
  all: try match goal with H : ciok _ = ok _ |- _ => case: H  => ? end.
  all: by subst.
Qed.

Lemma assemble_fd_labels rsp rip (fn: funname) fd fd' :
  assemble_fd rsp rip fd = ok fd' →
  [seq (fn, lbl) | lbl <- label_in_lcmd (lfd_body fd)] = [seq (fn, lbl) | lbl <- label_in_asm (xfd_body fd')].
Proof.
  rewrite /assemble_fd; t_xrbindP => c ok_c ?? [] <- {fd'} /=.
  by rewrite (assemble_c_labels ok_c).
Qed.

Lemma assemble_prog_labels p p' :
  assemble_prog p = ok p' →
  label_in_lprog p = label_in_xprog p'.
Proof.
  case/assemble_progP => _ _ /mapM_Forall2.
  rewrite /label_in_lprog /label_in_xprog.
  elim => //; t_xrbindP => - [] fn lfd fn' lfds xfds xfd.
  apply: add_finfoP => /= ok_xfd [] <- {fn'} _ ih.
  congr (_ ++ _); last exact: ih.
  exact: assemble_fd_labels ok_xfd.
Qed.
Variant match_state rip (ls: lstate) (lc : lcmd) (xs: x86_state) : Prop :=
| MS
  `(lom_eqv rip (to_estate ls) (xm xs))
  `(lfn ls = xfn xs)
  `(assemble_c rip lc = ok (xc xs))
  `(lpc ls = xip xs)
.

Lemma assemble_i_is_label rip a b lbl :
  assemble_i rip a = ok b →
  linear.is_label lbl a = x86_sem.is_label lbl b.
Proof.
by (rewrite /assemble_i /linear.is_label ; case a =>  ii []; t_xrbindP) => /=
  [????? <- | [<-] | ? [<-] | ? [<-] | _ ? _ [<-] | _ ?? _ [<-] | ???? [<-]].
Qed.

Lemma assemble_c_find_is_label rip c i lbl:
  assemble_c rip c = ok i →
  find (linear.is_label lbl) c = find (x86_sem.is_label lbl) i.
Proof.
rewrite /assemble_c.
elim: c i.
- by move => i [<-].
move => a c ih i' /=; t_xrbindP => b ok_b i ok_i <- {i'} /=.
by rewrite (ih i ok_i) (assemble_i_is_label lbl ok_b).
Qed.

Lemma assemble_c_find_label rip c i lbl:
  assemble_c rip c = ok i →
  linear.find_label lbl c = x86_sem.find_label lbl i.
Proof.
rewrite /assemble_c /linear.find_label /x86_sem.find_label => ok_i.
by rewrite (mapM_size ok_i) (assemble_c_find_is_label lbl ok_i).
Qed.

(* -------------------------------------------------------------------- *)

Lemma eval_assemble_word rip ii sz e a s xs v :
  lom_eqv rip s xs →
  assemble_word_mem rip ii sz None e = ok a →
  sem_pexpr [::] s e = ok v →
  exists2 v', eval_asm_arg AK_mem xs a (sword sz) = ok v' & value_uincl v v'.
Proof.
  rewrite /assemble_word /eval_asm_arg => eqm.
  case: e => //=; t_xrbindP.
  - move => x _ /assertP ok_x /xreg_of_varI h.
    rewrite /get_gvar ok_x => ok_v.
    case: a h => // r ok_r; (eexists; first reflexivity).
    + exact: (xgetreg_ex eqm ok_r ok_v).
    exact: (xxgetreg_ex eqm ok_r ok_v).
  - move => sz' ??; case: eqP => // <-{sz'}; t_xrbindP => d ok_d <- ptr w ok_w ok_ptr uptr u ok_u ok_uptr ? ok_rd ?; subst v => /=.
    case: (eqm) => eqmem _ _ _ _ _.
    rewrite (addr_of_xpexprP eqm ok_d ok_w ok_ptr ok_u ok_uptr) -eqmem ok_rd.
    eexists; first reflexivity.
    exact: word_uincl_refl.
  by case => // ? [].
Qed.

Section PROG.

Context (p: lprog) (p': xprog) (ok_p': assemble_prog p = ok p').

Lemma ok_get_fundef fn fd :
  get_fundef (lp_funcs p) fn = Some fd →
  exists2 fd', get_fundef (xp_funcs p') fn = Some fd' & assemble_fd RSP (mk_rip p.(lp_rip)) fd = ok fd'.
Proof.
  have [_ _ x y ] := assemble_progP ok_p'.
  have [fd' ??] := get_map_cfprog x y.
  by exists fd'.
Qed.

Lemma lom_eqv_write_var f rip s xs (x: var_i) sz (w: word sz) s' r :
  lom_eqv rip s xs →
  write_var x (Vword w) s = ok s' →
  var_of_register r = x →
  lom_eqv rip s' (mem_write_reg f r w xs).
Proof.
  case => eqm ok_rip [ dr dx df ] eqr eqx eqf.
  rewrite /mem_write_reg /write_var; t_xrbindP.
  case: s' => m _ vm ok_vm [] <- <- hx.
  constructor => //=.
  2-4: move => r' v'.
  all: rewrite (get_var_set_var _ ok_vm) -hx.
  3: exact: eqx.
  3: exact: eqf.
  - by move: dr => /(_ r) /eqP /negbTE ->.
  rewrite /RegMap.set ffunE.
  case: eqP (@var_of_register_inj r r') => h; last first.
  - move => _; case: eqP => [ ? | _ ]; last exact: eqr.
    by elim h; congr var_of_register.
  move => /(_ h) ->; rewrite eqxx; t_xrbindP => /= w' ok_w' <- /=.
  case: Sumbool.sumbool_of_bool ok_w' => hsz [] <-{w'} /=.
  + by apply word_uincl_word_extend.
  by rewrite word_extend_big // hsz.
Qed.

Lemma assemble_iP i j ls ls' lc xs :
  let: rip := mk_rip (lp_rip p) in
  omap lfd_body (get_fundef (lp_funcs p) (lfn ls)) = Some lc ->
  match_state rip ls lc xs →
  assemble_i rip i = ok j →
  linear_sem.eval_instr p i ls = ok ls' →
  exists2 xs': x86_state,
    x86_sem.eval_instr p' j xs = ok xs'  &
    exists2 lc',
        omap lfd_body (get_fundef (lp_funcs p) (lfn ls')) = Some lc' &
        match_state rip ls' lc' xs'.
Proof.
move => omap_lc.
rewrite /linear_sem.eval_instr /x86_sem.eval_instr; case => eqm eqfn eqc eqpc.
case: i => ii [] /=.
- move => lvs op pes; t_xrbindP => -[op' asm_args] hass <- m hsem ?; subst ls'.
  have [s [-> eqm' /=]]:= assemble_sopnP hsem hass eqm.
  eexists; first reflexivity.
  eexists; first exact: omap_lc.
  by constructor => //=; rewrite ?to_estate_of_estate ?eqpc.
- move => [<-] [?]; subst ls'.
  eexists; first reflexivity.
  eexists; first eassumption.
  by constructor => //; rewrite /setpc eqpc.
- move => lbl [<-] [?]; subst ls'.
  eexists; first reflexivity.
  eexists; first eassumption.
  constructor => //.
  by rewrite /setpc /= eqpc.
- case => fn lbl [<-] /=; t_xrbindP => body.
  case ok_fd: get_fundef => [ fd | // ] [ ] <-{body} pc ok_pc <-{ls'}.
  case/ok_get_fundef: (ok_fd) => fd' ->.
  rewrite /assemble_fd; t_xrbindP => xc ok_xc _ /assertP rsp_not_in_args [] <-{fd'} /=.
  rewrite -(assemble_c_find_label lbl ok_xc) ok_pc /=.
  rewrite ok_fd /=.
  do 2 (eexists; first reflexivity).
  by constructor.
- t_xrbindP => e d ok_d [<-] ptr v ok_v ok_ptr.
  have [v' ok_v' hvv'] := eval_assemble_word eqm ok_d ok_v.
  rewrite ok_v' /= (value_uincl_word hvv' ok_ptr) /=.
  case ptr_eq: decode_label => [ [] fn lbl | // ] /=.
  replace (decode_label _ ptr) with (Some (fn, lbl));
    last by rewrite -(assemble_prog_labels ok_p').
  rewrite /=.
  case get_fd: (get_fundef _) => [ fd | // ].
  have [fd' -> ] := ok_get_fundef get_fd.
  rewrite /assemble_fd /=; t_xrbindP => xc ok_xc _ /assertP rsp_not_in_args [] <-{fd'} /=.
  move => pc ok_pc <-{ls'}.
  rewrite -(assemble_c_find_label lbl ok_xc) ok_pc.
  rewrite get_fd /=.
  do 2 (eexists; first reflexivity).
  by constructor.
- case => // x lbl.
  case: (register_of_var _) (@var_of_register_of_var x) => //= r /(_ _ erefl) ok_r_x [<-]{j}.
  rewrite eqfn.
  case ptr_eq: encode_label => [ ptr | ] //.
  replace (encode_label _ _) with (Some ptr);
    last by rewrite -(assemble_prog_labels ok_p').
  rewrite /=.
  rewrite /sem_sopn /=.
  t_xrbindP => s' q ok_s' ? ?; subst ls' q.
  eexists; first reflexivity.
  rewrite /= -eqfn.
  exists lc; first exact: omap_lc.
  constructor => //=; last by congr _.+1.
  move: ok_s' ok_r_x.
  rewrite to_estate_of_estate !zero_extend_u sign_extend_u wrepr_unsigned.
  exact: lom_eqv_write_var.
- t_xrbindP => cnd lbl cndt ok_c [<-] b v ok_v ok_b.
  case: eqm => eqm hrip hd eqr eqx eqf.
  have [v' [ok_v' hvv']] := eval_assemble_cond eqf ok_c ok_v.
  case: v ok_v ok_b hvv' => // [ b' | [] // ] ok_b [?]; subst b'.
  rewrite /eval_Jcc.
  case: b ok_b => ok_b; case: v' ok_v' => // b ok_v' /= ?; subst b;
    (case: (eval_cond _ _) ok_v' => // [ b | [] // ] [->] {b}).
  + t_xrbindP => lc'' ok_lc'' pc ok_pc ?; subst ls' => /=.
    move: omap_lc ok_lc''; rewrite /omap /obind /oapp => /=.
    case: get_fundef => // lfu [->]  [?]; subst lc''; clear lfu.
    rewrite /eval_JMP -(assemble_c_find_label lbl eqc) ok_pc /=.
    do 2 (eexists; first reflexivity).
    by constructor.
  case => ?; subst ls' => /=.
  eexists; first reflexivity.
  exists lc; first exact: omap_lc.
  by constructor => //; rewrite /setpc /= eqpc.
Qed.

Lemma match_state_step ls ls' lc xs :
  let: rip := mk_rip (lp_rip p) in
  omap lfd_body (get_fundef (lp_funcs p) (lfn ls)) = Some lc ->
  match_state rip ls lc xs →
  step p ls = ok ls' →
  exists2 xs',
    fetch_and_eval p' xs = ok xs' &
    exists2 lc',
      omap lfd_body (get_fundef (lp_funcs p) (lfn ls')) = Some lc' &
      match_state rip ls' lc' xs'.
Proof.
move => omap_lc.
move => ms; rewrite /step /find_instr /fetch_and_eval; case: (ms)=> _ _ eqc ->.
case ok_fd: get_fundef omap_lc => [fd|] //= [?]; subst lc.
case ok_i : (oseq.onth (lfd_body _) _) => [ i | // ].
have [j [-> ok_j]] := mapM_onth eqc ok_i.
apply: assemble_iP => //; last eassumption.
by rewrite ok_fd.
Qed.

Lemma match_state_sem ls ls' lc xs :
  let: rip := mk_rip (lp_rip p) in
  omap lfd_body (get_fundef (lp_funcs p) (lfn ls)) = Some lc ->
  lsem p ls ls' →
  match_state rip ls lc xs →
  ∃ xs' lc',
    [/\ x86sem p' xs xs' ,
        omap lfd_body (get_fundef (lp_funcs p) (lfn ls')) = Some lc' &
        match_state rip ls' lc' xs'].
Proof.
move => omap_lc.
move => h; elim/lsem_ind: h xs lc omap_lc => {ls ls'}.
- move => ls xs lc omap_lc h; exists xs; exists lc; split => //; exact: rt_refl.
move => ls1 ls2 ls3 h1 h ih xs1 lc omap_lc m1.
have [ xs2 x [ lc' omap_lc' m2 ] ] := match_state_step omap_lc m1 h1.
have [xs3 [lc''] [y omap_lc'' m3]] := ih _ _ omap_lc' m2.
exists xs3; exists lc''; split => //.
apply: x86sem_trans; last by eauto.
exact: rt_step.
Qed.

Local Notation rip := (mk_rip p.(lp_rip)).

Lemma write_vars_uincl ii xs vs s1 s2 rs xm1 :
  write_vars xs vs s1 = ok s2 →
  mapM (xreg_of_var ii \o v_var) xs = ok rs →
  lom_eqv rip s1 xm1 →
  List.Forall2 value_uincl vs (get_arg_values xm1 rs) →
  lom_eqv rip s2 xm1.
Proof.
elim: xs vs s1 s2 rs.
+ by case => // s1 _ _ [<-] [<-].
move => x xs ih /= [] // v vs s1 s3 rs';
  t_xrbindP => s2 ok_s2 ok_s3 r /xreg_of_varI ok_r rs ok_rs <- {rs'} h /List_Forall2_inv_l [v'] [vs'] [/=] /seq_eq_injL [<- {v'} <- {vs'}] [hv rec].
apply: ih.
+ exact: ok_s3.
+ exact: ok_rs.
2: exact: rec.
case: h => h1 hrip hd h2 h3 h4 {ok_s3 ok_rs rec}.
case: r ok_r hv => // r => [ /var_of_register_of_var | /xmm_register_of_varI ] rx /=.
all: move: ok_s2; rewrite /write_var/set_var -rx /=; t_xrbindP => vm; apply: on_vuP => // w hw <-{vm} <-{s2}.
all: constructor => //=; (only 2-4, 6-8: move => r' v'); rewrite /get_var /on_vu.
1, 8: by rewrite Fv.setP_neq; first exact: hrip; apply/eqP; case: hd.
2-4, 6: rewrite Fv.setP_neq //.
2: exact: h3.
2, 4: exact: h4.
2: exact: h2.
+ case: (r =P r').
  * move => <-{r'}; rewrite Fv.setP_eq => -[<-]{v'}.
    apply: value_uincl_trans; last exact: h5.
    have [sz [w' [-> -> /=]]]:= to_pwordI hw.
    case: Sumbool.sumbool_of_bool => hle //=.
    by apply word_uincl_zero_ext; apply cmp_nle_le; rewrite hle.
  move => hne; rewrite Fv.setP_neq; first exact: h2.
  apply/eqP => /var_of_register_inj ?; exact: hne.
case: (r =P r').
* move => <-{r'}; rewrite Fv.setP_eq => -[<-]{v'}.
  apply: value_uincl_trans; last exact: h5.
  have [sz [w' [-> -> /=]]]:= to_pwordI hw.
  case: Sumbool.sumbool_of_bool => hle //=.
  by apply word_uincl_zero_ext; apply cmp_nle_le; rewrite hle.
move => hne; rewrite Fv.setP_neq; first exact: h3.
apply/eqP => /var_of_xmm_register_inj ?; exact: hne.
Qed.

Lemma get_xreg_of_vars_uincl ii xs rs vm vs (rm: regmap) (xrm: xregmap) :
  (∀ r v, get_var vm (var_of_register r) = ok v → value_uincl v (Vword (rm r))) →
  (∀ r v, get_var vm (var_of_xmm_register r) = ok v → value_uincl v (Vword (xrm r))) →
  mapM (xreg_of_var ii \o v_var) xs = ok rs →
  mapM (λ x : var_i, get_var vm x) xs = ok vs →
  List.Forall2 value_uincl vs 
     (map (λ a, match a with Reg r => Vword (rm r) | XMM r => Vword (xrm r) | _ => undef_w U64 end) rs).
Proof.
move => hr hxr; elim: xs rs vs.
+ by move => _ _ [<-] [<-]; constructor.
move => x xs ih rs' vs' /=; t_xrbindP => r /xreg_of_varI ok_r rs ok_rs <- {rs'} v ok_v vs ok_vs <- {vs'} /=.
constructor; last exact: ih.
case: r ok_r => // r => [ /var_of_register_of_var | /xmm_register_of_varI ] rx.
+ by apply: hr; rewrite rx.
by apply: hxr; rewrite rx.
Qed.

(*
Lemma assemble_fdP wrip m1 fn va m2 vr :
  lsem_fd p wrip m1 fn va m2 vr →
  ∃ fd va',
    get_fundef p.(lp_funcs) fn = Some fd ∧
    mapM2 ErrType truncate_val (lfd_tyin fd) va = ok va' ∧
  ∃ fd', get_fundef p'.(xp_funcs) fn = Some fd' ∧
    ∀ st1,
      List.Forall2 value_uincl va' (get_arg_values st1 fd'.(xfd_arg)) →
      st1.(xmem) = m1 →
      ∃ st2,
        x86sem_fd p' wrip fn st1 st2 ∧
        List.Forall2 value_uincl vr (get_arg_values st2 fd'.(xfd_res)) ∧
        st2.(xmem) = m2.
Proof.
case => m1' fd va' vm2 m2' s1 s2 vr' ok_fd ok_m1' /= [<-] {s1} ok_va'.
rewrite /with_vm /=.
set vm1 := (vm in {| evm := vm |}). 
move => ok_s2 hexec ok_vr' ok_vr -> {m2}.
exists fd, va'. split; first exact: ok_fd. split; first exact: ok_va'.
have [ hrip _ ok_sp ok_fds ] := assemble_progP ok_p'.
have [fd' [h ok_fd']] := get_map_cfprog ok_fds ok_fd.
exists fd'; split => //. 
move => s1 hargs ?; subst m1.
move: h; rewrite /assemble_fd; t_xrbindP => body ok_body.
t_xrbindP => args ok_args dsts ok_dsts _ /assertP hsp tosave ? savedstk ? [?]; subst fd'.
set xr1 := mem_write_reg RSP (top_stack m1') {| xmem := m1' ; xreg := s1.(xreg) ; xrip := wrip; xxreg := s1.(xxreg) ; xrf := rflagmap0 |}.
have eqm1 : lom_eqv rip {| emem := m1' ; evm := vm1 |} xr1.
+ constructor => //.
  - by rewrite /get_var /= /vm1 /= Fv.setP_eq.
  - rewrite /vm1 /= => r v.
    rewrite (inj_reg_of_string ok_sp (reg_of_stringK RSP)).
    rewrite /get_var /var_of_register /RegMap.set ffunE; case: eqP.
    * move => -> {r} /=.
      rewrite Fv.setP_neq; last first.
      + by apply /eqP => -[] heq; case: hrip => /(_ RSP); rewrite /var_of_register /= -heq.
      rewrite Fv.setP_eq word_extend_reg_id // zero_extend_u => -[<-];
      exact: word_uincl_refl.
    move => ne; rewrite /= Fv.setP_neq; last first.
    + by apply /eqP => -[] heq; case: hrip => /(_ r); rewrite /var_of_register -heq.
    rewrite Fv.setP_neq /vmap0 ?Fv.get0 //.
    by apply/eqP => -[] /(@inj_string_of_register RSP) ?; apply: ne.
  - by move => r v; rewrite /vm1 /= /get_var !Fv.setP_neq // /vmap0 Fv.get0.
  move => f v /=; rewrite /vm1 /rflagmap0 ffunE /=.
  by rewrite /var_of_flag /get_var /= !Fv.setP_neq // /vmap0 Fv.get0.
have h1 : get_arg_values xr1 args = get_arg_values s1 args.
+ rewrite /get_arg_values /get_arg_value /xr1 /=.
  apply: map_ext => // r /xseq.InP hr; f_equal.
  case: r hr => // r hr.
  rewrite ffunE; case: eqP => // e.
  by elim: (elimN idP hsp); rewrite -e.
rewrite -h1 in hargs => {h1}.
have eqm2 : lom_eqv rip s2 xr1.
+ by apply: write_vars_uincl; eauto.
have ms : match_state rip (of_estate s2 fn fd.(lfd_body) 0) {| xm := xr1 ; xfn := fn ; xc := body ; xip := 0 |}.
+ by constructor => //=; rewrite to_estate_of_estate.
have [[[om or orip oxr orf] ofn oc opc] [xexec]] := match_state_sem hexec ms.
rewrite (mapM_size ok_body).
case => eqm' /= ?.
rewrite ok_body => -[?] ?; subst ofn oc opc.
eexists; split; first by econstructor; eauto.
case: eqm' => /= ?; subst om => eqr' _; split => //.
rewrite /get_arg_values /get_arg_value /=.
apply: (Forall2_trans value_uincl_trans).
+ apply: (mapM2_Forall2 _ ok_vr) => a b r _; exact: truncate_val_uincl.
apply: get_xreg_of_vars_uincl; eassumption.
Qed.
*)

End PROG.
