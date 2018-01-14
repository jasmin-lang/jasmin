Require Import x86_instr linear_sem.
Import Utf8 Relation_Operators.
Import all_ssreflect.
Import compiler_util expr sem x86_sem linear x86_variables x86_variables_proofs asmgen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Definition assemble_i (i: linstr) : ciexec asm :=
  let '{| li_ii := ii ; li_i := ir |} := i in
  match ir with
  | Lassgn d _ e => assemble_sopn ii [:: d] Ox86_MOV [:: e ]

  | Lopn ds op es => assemble_sopn ii ds op es

  | Llabel lbl => ciok (LABEL lbl)

  | Lgoto lbl => ciok (JMP lbl)

  | Lcond e l =>
      Let cond := assemble_cond ii e in
      ciok (Jcc l cond)
  end.

(* -------------------------------------------------------------------- *)
Definition assemble_c (lc: lcmd) : ciexec (seq asm) :=
  mapM assemble_i lc.

(* -------------------------------------------------------------------- *)
Definition assemble_fd (fd: lfundef) :=
  Let fd' := assemble_c (lfd_body fd) in

  match (reg_of_string (lfd_nstk fd)) with
  | Some sp =>
      Let arg := reg_of_vars xH (lfd_arg fd) in
      Let res := reg_of_vars xH (lfd_res fd) in
      ciok (XFundef (lfd_stk_size fd) sp arg fd' res)

  | None =>
      cierror xH (Cerr_assembler (AsmErr_string "Invalid stack pointer"))
  end.

(* -------------------------------------------------------------------- *)
Definition assemble_prog (p: lprog) : cfexec xprog :=
  map_cfprog assemble_fd p.

(* -------------------------------------------------------------------- *)
Variant match_state (ls: lstate) (xs: x86_state) : Prop :=
| MS
  `(lom_eqv (to_estate ls) (xm xs))
  `(assemble_c (lc ls) = ok (xc xs))
  `(lpc ls = xip xs)
.

Lemma assemble_i_is_label a b lbl :
  assemble_i a = ok b →
  linear.is_label lbl a = x86_sem.is_label lbl b.
Proof.
rewrite /assemble_i /linear.is_label ; case a =>  ii [] /=.
- move => lv _ e h.
  have := assemble_sopn_is_sopn h => {h}.
  by case b.
- move => lvs op es h.
  have := assemble_sopn_is_sopn h => {h}.
  by case b.
- by move => lbl' [<-].
- by move => lbl' [<-].
by t_xrbindP => ? ? ? _ [<-].
Qed.

Lemma assemble_c_find_is_label c i lbl:
  assemble_c c = ok i →
  find (linear.is_label lbl) c = find (x86_sem.is_label lbl) i.
Proof.
rewrite /assemble_c.
elim: c i.
- by move => i [<-].
move => a c ih i' /=; t_xrbindP => b ok_b i ok_i <- {i'} /=.
by rewrite (ih i ok_i) (assemble_i_is_label lbl ok_b).
Qed.

Lemma assemble_c_find_label c i lbl:
  assemble_c c = ok i →
  linear.find_label lbl c = x86_sem.find_label lbl i.
Proof.
rewrite /assemble_c /linear.find_label /x86_sem.find_label => ok_i.
by rewrite (mapM_size ok_i) (assemble_c_find_is_label lbl ok_i).
Qed.

Lemma write_oprd_of_lval ii gd lv x y es xs es' v (w: word) :
  lom_eqv es xs →
  pexpr_of_lval ii lv = ok x →
  oprd_of_pexpr ii x = ok y →
  write_lval gd lv v es = ok es' →
  value_uincl v w →
  ∃ xs',
    write_oprd y w xs = ok xs' ∧
    lom_eqv es' xs'.
Proof.
move => eqm; case: lv => //.
- case => x' xi [<-] {x} /=; t_xrbindP => r ok_r [<-] ok_es' hvw.
  case: x' ok_es' ok_r => -[] // x ok_es' /=.
  have := write_var_compile_var ok_es' hvw eqm.
  rewrite /compile_var /register_of_var /=.
  by case: reg_of_string => // r' /(_ _ erefl) [xs' [?] eqm'] [?]; subst r' xs'; eauto.
case => x' xi e [<-] {x} /=; t_xrbindP => r ok_r a ok_a [<-] w' v' ok_v' ok_w' u u' ok_u' ok_u z ok_z m' ok_m' <- {es'} hvw.
case: v ok_z hvw => // [ v | [] // ] [?]; subst v => /= ?; subst z.
have ha : decode_addr xs a = I64.add w' u.
- have ? := xgetreg eqm ok_r ok_v' ok_w'; subst w'.
- move: ok_a; rewrite /addr_of_pexpr /decode_addr.
  have := addr_ofsP ok_u' ok_u.
  case: (addr_ofs e) => //=.
  + by move => z /(_ erefl) [<-] [<-] /=; rewrite !rw64 I64.add_commut.
  + by move => v /(_ erefl); t_xrbindP => v1 ok_v1 hv1u vr ok_vr [<-] /=; rewrite !rw64 (xgetreg eqm ok_vr ok_v1 hv1u).
  + by move => z v /(_ erefl); t_xrbindP => q q' ok_q' ok_q ? vr ok_vr sc /xscale_ok ok_sc [<-] /=; subst u; rewrite !rw64 ok_sc (xgetreg eqm ok_vr ok_q' ok_q).
  move => z v z' /(_ erefl); t_xrbindP => q q' ok_q' ok_q ? vr ok_vr sc /xscale_ok ok_sc [<-] /=; subst u.
  by rewrite ok_sc (xgetreg eqm ok_vr ok_q' ok_q) I64.add_commut I64.add_assoc.
case: eqm => eqm eqr eqf.
rewrite /= /mem_write_mem ha -eqm ok_m' /=.
eexists; split; first by reflexivity.
by constructor.
Qed.

Lemma assemble_iP gd i j ls ls' xs :
  match_state ls xs →
  assemble_i i = ok j →
  linear_sem.eval_instr gd i ls = ok ls' →
  ∃ xs' : x86_state,
    x86_sem.eval_instr gd j xs = ok xs' ∧
    match_state ls' xs'.
Proof.
rewrite /linear_sem.eval_instr /x86_sem.eval_instr; case => eqm eqc eqpc.
case: i => ii [] /=.
- move => lv _ e. rewrite /assemble_sopn /= /compile_hi_sopn /= /compile_low_args /=.
  t_xrbindP => ?? x ok_x <- [] ok_args <- /=; t_xrbindP => ?? y ok_y <- ?? f ok_f <- <- <- /= [<-] v ok_v es ok_es <- {ls'}.
  rewrite /= /eval_MOV.
  have [w -> ok_w /=] := eval_oprd_of_pexpr eqm ok_f ok_v.
  have [xs' [-> eqm'] /=] := write_oprd_of_lval eqm ok_x ok_y ok_es ok_w.
  eexists; split; first by reflexivity.
  by constructor => //=; rewrite ?to_estate_of_estate ?eqpc.
- move => lvs op pes ok_j; t_xrbindP => es ok_es <- {ls'} /=.
  have [m2 [-> eqm2 /=]] := assemble_sopnP eqm ok_j ok_es.
  have := assemble_sopn_is_sopn ok_j.
  by case: j {ok_j} => //; (eexists; split; first by reflexivity); constructor => //=;
    rewrite ?to_estate_of_estate ?eqpc.
- move => lbl [<-] [<-]; eexists; split; first by reflexivity.
  constructor => //.
  by rewrite /setpc /= eqpc.
- move => lbl [<-]; t_xrbindP => pc ok_pc <- {ls'}.
  rewrite /eval_JMP -(assemble_c_find_label lbl eqc) ok_pc /=.
  by eexists; split; eauto; constructor.
- t_xrbindP => cnd lbl cndt ok_c [<-] b v ok_v ok_b.
  case: eqm => eqm eqr eqf.
  have [v' [ok_v' hvv']] := eval_assemble_cond eqf ok_c ok_v.
  case: v ok_v ok_b hvv' => // [ b' | [] // ] ok_b [?]; subst b'.
  rewrite /eval_Jcc.
  case: b ok_b => ok_b; case: v' ok_v' => // b ok_v' /= ?; subst b;
    (case: (eval_cond _ _) ok_v' => // [ b | [] // ] [->] {b}).
  + t_xrbindP => pc ok_pc <- {ls'} /=.
    rewrite /eval_JMP -(assemble_c_find_label lbl eqc) ok_pc /=.
    by eexists; split; eauto; constructor.
  case => <- /=; eexists; split; first by reflexivity.
  by constructor => //; rewrite /setpc /= eqpc.
Qed.

Lemma mapM_onth eT aT bT (f: aT → result eT bT) (xs: seq aT) ys n x :
  mapM f xs = ok ys →
  oseq.onth xs n = Some x →
  ∃ y, oseq.onth ys n = Some y ∧ f x = ok y.
Proof.
move => ok_ys.
case: (leqP (size xs) n) => hsz; first by rewrite (oseq.onth_default hsz).
elim: xs ys ok_ys n hsz.
- by move => ys [<-].
move => y xs ih ys' /=; t_xrbindP => z ok_z ys ok_ys <- [| n ] hsz /= ok_y.
- by exists z; case: ok_y => <-.
exact: (ih _ ok_ys n hsz ok_y).
Qed.

Lemma mapM_onth' eT aT bT (f: aT → result eT bT) (xs: seq aT) ys n y :
  mapM f xs = ok ys →
  oseq.onth ys n = Some y →
  ∃ x, oseq.onth xs n = Some x ∧ f x = ok y.
Proof.
move => ok_ys.
case: (leqP (size ys) n) => hsz; first by rewrite (oseq.onth_default hsz).
elim: xs ys ok_ys n hsz.
- by move => ys [<-].
move => x xs ih ys' /=; t_xrbindP => z ok_z ys ok_ys <- [| n ] hsz /= ok_y.
- by exists x; case: ok_y => <-.
exact: (ih _ ok_ys n hsz ok_y).
Qed.

Lemma match_state_step gd ls ls' xs :
  match_state ls xs →
  step gd ls = ok ls' →
  ∃ xs',
  fetch_and_eval gd xs = ok xs' ∧
  match_state ls' xs'.
Proof.
move => ms; rewrite /step /find_instr /fetch_and_eval; case: (ms)=> _ eqc ->.
case ok_i : (oseq.onth) => [ i | // ].
have [j [-> ok_j]] := mapM_onth eqc ok_i.
exact: assemble_iP.
Qed.

Lemma match_state_sem gd ls ls' xs :
  lsem gd ls ls' →
  match_state ls xs →
  ∃ xs',
    x86sem gd xs xs' ∧
    match_state ls' xs'.
Proof.
move => h; elim/lsem_ind: h xs; clear.
- move => ls xs h; exists xs; split => //; exact: rt_refl.
move => ls1 ls2 ls3 h1 h ih xs1 m1.
have [xs2 [x m2]] := match_state_step m1 h1.
have [xs3 [y m3]] := ih _ m2.
exists xs3; split => //.
apply: x86sem_trans; last by eauto.
exact: rt_step.
Qed.

Section PROG.

Context (p: lprog) (p': xprog) (ok_p': assemble_prog p = ok p') (gd: glob_defs).

Lemma write_vars_mem_write_regs ii xs vs s1 s2 rs m1 :
  write_vars xs vs s1 = ok s2 →
  reg_of_vars ii xs = ok rs →
  lom_eqv s1 m1 →
  ∃ ws, mapM to_word vs = ok ws ∧
        size ws = size rs ∧
        lom_eqv s2 (mem_write_regs m1 rs ws).
Proof.
elim: xs vs rs s1 m1.
+ case => // rs s1 m1 [<-] {s2} [<-] {rs} eqm.
  by exists [::].
rewrite /reg_of_vars.
move => x xs ih [] // v vs rs' /=; t_xrbindP => s0 m0 s1 ok_s1 ok_s2 r ok_r rs ok_rs <- {rs'} eqm.
have := write_var_compile_var ok_s1 _ eqm.
rewrite /compile_var (reg_of_var_register_of_var ok_r).
case/(_ v _ (value_uincl_refl _) erefl) => m1 ok_m1 eqm1.
case: v ok_s1 ok_m1 => //= v ok_s1 [ok_m1].
have [ws [ok_ws [hsz eqm2]]] := ih vs rs s1 m1 ok_s2 ok_rs eqm1.
exists (v :: ws); split; first by rewrite ok_ws.
split; first by rewrite /= hsz.
by rewrite mem_write_regs_cons ok_m1.
Qed.

Lemma get_reg_of_vars ii es m xs vs rs :
  lom_eqv es m →
  mapM (λ x : var_i, get_var es.(evm) x) xs = ok vs →
  List.Forall is_full_array vs →
  reg_of_vars ii xs = ok rs →
  mapM to_word vs = ok (map (λ r, m.(xreg) r) rs).
Proof.
move => eqm.
elim: xs vs rs.
- by case => //= -[].
rewrite /reg_of_vars.
move => x xs ih vs' rs' /=; t_xrbindP => v ok_v vs ok_vs <- {vs'} /List_Forall_inv [wf wfr] r ok_r rs ok_rs <- {rs'}.
have := xgetreg_ex eqm ok_r ok_v.
case: v {ok_v} wf => // v _ /= <-.
by rewrite (ih vs rs ok_vs wfr ok_rs).
Qed.

Lemma assemble_fdP m1 fn va m2 vr :
  lsem_fd p gd m1 fn va m2 vr →
  ∃ va' vr',
    mapM to_word va = ok va' ∧
    mapM to_word vr = ok vr' ∧
    x86sem_fd p' gd m1 fn va' m2 vr'.
Proof.
case => -[] stk m1' fd vm2 m2' s1 s2 ok_fd ok_stk /= [<-] {s1}.
set vm1 := (vm in {| evm := vm |}).
move => ok_s2 hexec ok_vr -> {m2} ok_arr.
have [fd' [h ok_fd']] := get_map_cfprog ok_p' ok_fd.
move: h; rewrite /assemble_fd; t_xrbindP => body ok_body.
case ok_sp: (reg_of_string _) => [ sp | // ]; t_xrbindP => args ok_args dsts ok_dsts [?]; subst fd'.
set xr1 := λ xr0, mem_write_reg sp stk {| xmem := m1' ; xreg := xr0 ; xrf := rflagmap0 |}.
have eqm1 : ∀ xr0, lom_eqv {| emem := m1' ; evm := vm1 |} (xr1 xr0).
+ move => xr0; constructor => //.
  - rewrite /vm1 /= => r v.
    rewrite (inj_reg_of_string ok_sp (reg_of_stringK sp)).
    rewrite /get_var /var_of_register /RegMap.set ffunE; case: eqP.
    * move => -> {r} /=; rewrite Fv.setP_eq => -[<-]; exact: value_uincl_refl.
    move => ne; rewrite /= Fv.setP_neq; first by case => <-.
    by apply/eqP => -[] /inj_string_of_register ?; apply: ne.
  - move => f v /=; rewrite /vm1 /rflagmap0 ffunE /=.
    by rewrite /var_of_flag /get_var /= Fv.setP_neq => // -[<-].
have [wa [ok_wa [hsz]]] := write_vars_mem_write_regs ok_s2 ok_args (eqm1 regmap0).
set m2 := (x in lom_eqv _ x) => eqm2.
have ms : match_state (of_estate s2 fd.(lfd_body) 0) {| xm := m2 ; xc := body ; xip := 0 |}.
- by constructor => //=; rewrite to_estate_of_estate.
have [[[om or orf] oc opc] [xexec]] := match_state_sem hexec ms.
rewrite (mapM_size ok_body).
case => eqm' /=.
rewrite ok_body => -[?] ?; subst oc opc.
have /= ok_wr := get_reg_of_vars eqm' ok_vr ok_arr ok_dsts.
eexists wa, _.
split; first exact: ok_wa.
split; first exact: ok_wr.
econstructor; eauto => /=.
by case: eqm' => /= ->.
Qed.

Lemma assemble_fd_stk_size fd xfd :
  assemble_fd fd = ok xfd →
  lfd_stk_size fd = xfd_stk_size xfd.
Proof.
by rewrite /assemble_fd; t_xrbindP => c _; case: reg_of_string => //; t_xrbindP => ? ? ? ? ? [<-].
Qed.

End PROG.
