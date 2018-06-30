Require Import x86_instr linear_sem.
Import Utf8 Relation_Operators.
Import all_ssreflect all_algebra.
Import compiler_util expr psem x86_sem linear x86_variables x86_variables_proofs asmgen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Definition assemble_i (i: linstr) : ciexec asm :=
  let '{| li_ii := ii ; li_i := ir |} := i in
  match ir with
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
Variant x86_gen_error_t :=
| X86Error_InvalidStackPointer
| X86Error_StackPointerInArguments of register
.

Definition x86_gen_error (e: x86_gen_error_t) : instr_error :=
  (xH, Cerr_assembler (AsmErr_string
  match e with
  | X86Error_InvalidStackPointer => "Invalid stack pointer"
  | X86Error_StackPointerInArguments sp =>
    "Stack pointer (" ++ string_of_register sp ++ ") is also an argument"
  end)).

(* -------------------------------------------------------------------- *)
Definition assemble_fd (fd: lfundef) :=
  Let fd' := assemble_c (lfd_body fd) in

  match (reg_of_string (lfd_nstk fd)) with
  | Some sp =>
      Let arg := reg_of_vars xH (lfd_arg fd) in
      Let res := reg_of_vars xH (lfd_res fd) in
      Let _ := assert (~~ (sp \in arg)) (x86_gen_error (X86Error_StackPointerInArguments sp)) in
      ciok (XFundef (lfd_stk_size fd) sp arg fd' res)

  | None => Error (x86_gen_error X86Error_InvalidStackPointer)
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
  case: eqm => eqm eqr eqx eqf.
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

Context (p: lprog) (p': xprog) (ok_p': assemble_prog p = ok p') (gd: glob_decls).

Definition get_reg_value (st: x86_mem) (r: register) : value :=
  Vword (xreg st r).

Definition get_reg_values st rs : values :=
  map (get_reg_value st) rs.

Lemma write_vars_uincl ii xs vs s1 s2 rs xm1 :
  write_vars xs vs s1 = ok s2 →
  reg_of_vars ii xs = ok rs →
  lom_eqv s1 xm1 →
  List.Forall2 value_uincl vs (get_reg_values xm1 rs) →
  lom_eqv s2 xm1.
Proof.
elim: xs vs s1 s2 rs.
+ by case => // s1 _ _ [<-] [<-].
move => x xs ih /= [] // v vs s1 s3 rs';
  t_xrbindP => s2 ok_s2 ok_s3 r ok_r rs ok_rs <- {rs'} h /List_Forall2_inv_l [v'] [vs'] [/=] /seq_eq_injL [<- {v'} <- {vs'}] [hv rec].
apply: ih; eauto.
have := write_var_compile_var MSB_CLEAR ok_s2 hv h.
rewrite /compile_var (reg_of_var_register_of_var ok_r) => /(_ _ erefl) [_] [<-] /=.
rewrite /mem_write_reg /= word_extend_reg_id // zero_extend_u -RegMap_set_id.
by case: (xm1).
Qed.

Lemma truncate_val_uincl ty v v' :
  truncate_val ty v = ok v' →
  value_uincl v' v.
Proof.
apply: rbindP => z hz [<-].
case: ty z hz => /=.
- by move => b /to_boolI ->.
- by move => z /of_val_int ->.
- by move => sz n t /to_arr_ok ->; split => //; exists erefl.
move => sz w /of_val_word [sz'] [w'] [hle -> ->].
exact: word_uincl_zero_ext.
Qed.

Lemma get_reg_of_vars_uincl ii xs rs vm vs (rm: regmap) :
  (∀ r v, get_var vm (var_of_register r) = ok v → value_uincl v (Vword (rm r))) →
  reg_of_vars ii xs = ok rs →
  mapM (λ x : var_i, get_var vm x) xs = ok vs →
  List.Forall2 value_uincl vs (map (λ r, Vword (rm r)) rs).
Proof.
move => h; elim: xs rs vs.
+ by move => _ _ [<-] [<-]; constructor.
move => x xs ih rs' vs' /=; t_xrbindP => r ok_r rs ok_rs <- {rs'} v ok_v vs ok_vs <- {vs'} /=.
constructor; last exact: ih.
apply: h. rewrite -ok_v {ok_v}; f_equal; apply: var_of_register_of_var.
case: x ok_r => /= x _; exact: reg_of_var_register_of_var.
Qed.

Lemma assemble_fdP m1 fn va m2 vr :
  lsem_fd p gd m1 fn va m2 vr →
  ∃ fd va',
    get_fundef p fn = Some fd ∧
    mapM2 ErrType truncate_val (lfd_tyin fd) va = ok va' ∧
  ∃ fd', get_fundef p' fn = Some fd' ∧
    ∀ st1,
      List.Forall2 value_uincl va' (get_reg_values st1 fd'.(xfd_arg)) →
      st1.(xmem) = m1 →
      ∃ st2,
        x86sem_fd p' gd fn st1 st2 ∧
        List.Forall2 value_uincl vr (get_reg_values st2 fd'.(xfd_res)) ∧
        st2.(xmem) = m2.
Proof.
case => m1' fd va' vm2 m2' s1 s2 vr' ok_fd ok_m1' /= [<-] {s1} ok_va'.
set vm1 := (vm in {| evm := vm |}).
move => ok_s2 hexec ok_vr' ok_vr -> {m2}.
exists fd, va'. split; first exact: ok_fd. split; first exact: ok_va'.
have [fd' [h ok_fd']] := get_map_cfprog ok_p' ok_fd.
exists fd'. split; first exact: ok_fd'.
move => s1 hargs ?; subst m1.
move: h; rewrite /assemble_fd; t_xrbindP => body ok_body.
case ok_sp: (reg_of_string _) => [ sp | // ];
  t_xrbindP => args ok_args dsts ok_dsts _ /assertP hsp [?]; subst fd'.
set xr1 := mem_write_reg sp (Memory.top_stack m1') {| xmem := m1' ; xreg := s1.(xreg) ; xxreg := s1.(xxreg) ; xrf := rflagmap0 |}.
have eqm1 : lom_eqv {| emem := m1' ; evm := vm1 |} xr1.
+ constructor => //.
  - rewrite /vm1 /= => r v.
    rewrite (inj_reg_of_string ok_sp (reg_of_stringK sp)).
    rewrite /get_var /var_of_register /RegMap.set ffunE; case: eqP.
    * move => -> {r} /=; rewrite Fv.setP_eq word_extend_reg_id // zero_extend_u => -[<-];
      exact: word_uincl_refl.
    move => ne; rewrite /= Fv.setP_neq /vmap0 ?Fv.get0; first by case => <-.
    by apply/eqP => -[] /inj_string_of_register ?; apply: ne.
  - by move => r v; rewrite /vm1 /= /get_var /vmap0 Fv.setP_neq // Fv.get0 => - [<-].
  move => f v /=; rewrite /vm1 /rflagmap0 ffunE /=.
  by rewrite /var_of_flag /get_var /= Fv.setP_neq // /vmap0 Fv.get0 => -[<-].
have h1 : get_reg_values xr1 args = get_reg_values s1 args.
+ rewrite /get_reg_values /get_reg_value /xr1 /=.
  apply: map_ext => // r /xseq.InP hr; f_equal.
  rewrite ffunE; case: eqP => // e.
  by elim: (elimN idP hsp); rewrite -e.
rewrite -h1 in hargs => {h1}.
have eqm2 : lom_eqv s2 xr1.
+ by apply: write_vars_uincl; eauto.
have ms : match_state (of_estate s2 fd.(lfd_body) 0) {| xm := xr1 ; xc := body ; xip := 0 |}.
+ by constructor => //=; rewrite to_estate_of_estate.
have [[[om or oxr orf] oc opc] [xexec]] := match_state_sem hexec ms.
rewrite (mapM_size ok_body).
case => eqm' /=.
rewrite ok_body => -[?] ?; subst oc opc.
eexists; split; first by econstructor; eauto.
case: eqm' => /= ?; subst om => eqr' _; split => //.
rewrite /get_reg_values /get_reg_value /=.
apply: (Forall2_trans value_uincl_trans).
+ apply: (mapM2_Forall2 _ ok_vr) => a b r _; exact: truncate_val_uincl.
apply: get_reg_of_vars_uincl; eassumption.
Qed.

Lemma assemble_fd_stk_size fd xfd :
  assemble_fd fd = ok xfd →
  lfd_stk_size fd = xfd_stk_size xfd.
Proof.
by rewrite /assemble_fd; t_xrbindP => c _;
  case: reg_of_string => //; t_xrbindP => ?? _ ? _ _ _ [<-].
Qed.

End PROG.
