(* -------------------------------------------------------------------- *)
Require Import oseq.
Require Import asmgen.
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import xseq expr linear compiler_util.
(* ------- *) Require Import low_memory x86_sem.
Import Utf8 sem.

Lemma lom_eqv_set_register m lom x r i :
  lom_eqv m lom →
  register_of_var x = Some r →
  lom_eqv (set m x (VInt i)) (write_reg lom r i).
Proof.
  case => hr hf hx; rewrite -(var_of_register_of_var hx) => {x hx}.
  split => q; rewrite get_set /=.
  + case: eqP; first by move ->; rewrite eq_refl.
    move => ne; case: eqP => // /var_of_register_inj //.
  case: eqP => // h; elim: (var_of_register_var_of_flag (esym h)).
Qed.

Lemma lom_eqv_set_flag m lom x f b :
  lom_eqv m lom →
  flag_of_var x = Some f →
  lom_eqv (set m x (VBool b)) (write_flag lom f b).
Proof.
  case => hr hf hx; rewrite -(var_of_flag_of_var hx) => {x hx}.
  split => q; rewrite get_set /=.
  + case: eqP => // h; elim: (var_of_register_var_of_flag h).
  case: eqP; first by move ->; rewrite eq_refl.
  move => ne; case: eqP => // /var_of_flag_inj //.
Qed.

Lemma set_lom_eqv m lom x y v lom' :
  lom_eqv m lom →
  compile_var x = Some y →
  set_lo y v lom = Some lom' →
  lom_eqv (set m x v) lom'.
Proof.
  case => hr hf.
  rewrite /compile_var.
  case e1: register_of_var => [ r | ].
  + case => <-; case: v => // i [] <-.
    exact: lom_eqv_set_register.
  case e2: flag_of_var => // [ i ] [] <-; case: v => //= b [] <-.
  exact: lom_eqv_set_flag.
Qed.

Lemma sets_lo_cons m d ds v vs :
  sets_lo m (d :: ds) (v :: vs) = set_lo d v m >>= λ m', sets_lo m' ds vs.
Proof.
  rewrite {1} /sets_lo /=.
  case: set_lo; last by case: eqP => // _; exact: foldl_bind_None.
  case: eqP.
  + move/succn_inj => eq_sz /=.
     by move => m' /=; rewrite /sets_lo; case: eqP.
  move => ne_sz /= m'.
  by rewrite /sets_lo; case: eqP => // k; elim: ne_sz; rewrite k.
Qed.

Lemma toto_out ads vs out irs m1 lom1 outv m2 :
  lom_eqv m1 lom1 →
  all wf_implicit ads →
  omap ireg_of_expr vs = Some irs →
  omap (sem_ad_out vs) ads = Some out →
  sets m1 out outv = Some m2 →
  ∃ outx, omap (sem_lo_ad_out irs) ads = Some outx ∧
  ∃ lom2 : lomem, sets_lo lom1 outx outv = Some lom2 ∧ lom_eqv m2 lom2.
Proof.
  move => eqm hwf hirs.
  elim: ads out outv m1 lom1 eqm hwf.
  - move => out outv m1 lom1 eqm _ [] <- /setsI [hsz ->]; exists [::]; split => //.
    by case: outv hsz => // _; exists lom1.
  move => ad ads ih args' outv' m1 lom1 eqm h; rewrite /= in h; case/andP: h => hwf hwf'.
  case/omap_consI => arg [] args [] -> ha has /sets_consI [v] [outv] [? hm2]; subst outv'.
  case: ad ha hwf.
  + move => x /= [] ?; subst arg.
    case hd: compile_var => [ d | ] // _.
    have : ∃ lom', set_lo d v lom1 = Some lom'.
    admit.
    case => lom' hlom'.
    have eqm' := set_lom_eqv eqm hd hlom'.
    case: (ih args outv (set m1 x v) lom' eqm' hwf' has hm2)
      => dst [hdst] [lom2] [hlom2 eqm2].
    exists (d :: dst); split; first by rewrite hdst.
    exists lom2; split; first by rewrite sets_lo_cons hlom' /=. done.

  move => n /=.
  case eq1: onth => [ [] q | ] // [] ? _; subst q.
  move: eq1 => /onthP - /(_ (EInt 0)) /andP [] hsz /eqP harg.
  case: (onth_omap_size (EInt 0) hirs hsz) => y [hy]; rewrite harg.
  case eqy: register_of_var => [ y' | ] // - [] ?; subst y.
  have eqy' : compile_var arg = Some (DReg y') by rewrite /compile_var eqy.
  have : ∃ i, v = VInt i.
  admit.
  case => i ?; subst v.
  have : ∃ lom', set_lo (DReg y') i lom1 = Some lom' by eexists.
  case => lom' hlom'.
  have eqm' := set_lom_eqv eqm eqy' hlom'.
  have := ih _ _ _ _ eqm' hwf' has hm2.
  case => dst [hdst] [lom2] [hlom2 eqm2].
  rewrite hy hdst /=.
  eexists; split; first by reflexivity.
  case: hlom' => ?; subst lom'.
  by exists lom2.
Admitted.
*)

(* -------------------------------------------------------------------- *)
Lemma compile_lowP ii gd op id m1 lvs pes gargs m2 lom1 :
  sopn_desc ii op = ok id →
  compile_low ii id.(id_tys) pes = ok gargs →
  sem_sopn gd op m1 lvs pes = ok m2 →
  lom_eqv m1 lom1 →
  ∃ lom2,
    low_sem gd lom1 id gargs = ok lom2 ∧
    lom_eqv m2 lom2.
Proof.

Qed.

Definition compile_gen ii (op: sopn) (args : pexprs) : ciexec asm :=
  sopn_desc ii op >>= λ id,
  compile_low ii args id.(id_instr).

Definition compile_low ii (tys: seq arg_ty) (args: pexprs) (op: interp_tys tys) : ciexec asm :=
  mapM (garg_of_pexpr ii) (zip tys args) >>= λ gargs,
  typed_apply_gargs ii gargs op.

Definition compile_gen ii (op: sopn) (args : pexprs) : ciexec asm :=
  sopn_desc ii op >>= λ id,
  compile_low ii args id.(id_instr).

Theorem compile_genP ii gd op id lvs vs m1 m2 instr lom1 :
  sopn_desc ii op = ok id →
  compile_gen ii op vs = ok instr →
  sem_sopn gd op m1 lvs vs = ok m2 →
  lom_eqv m1 lom1 →
  ∃ lom2,
    low_sem gd lom1 id _ = ok lom2 ∧
    lom_eqv m2 lom2.
Proof.
rewrite /compile_gen /sem_id => h.
case E1: (omap _) => [args|//].
case E2: (omap _) => [out|//].
rewrite get_id_ok; set op := (X in sem_cmd X).
rewrite /sem_cmd; case E3: (op _) => [outv|//].
rewrite /sem_lo_gen /sem_lo_gen_aux.
move: h. rewrite /compile_lo. case h: omap => // [irs] hirs.
rewrite (proj2 (id_sem_wf hirs)).
rewrite /sem_lo_cmd.
rewrite get_id_ok -/op.
move => hsets heqm.
have [ inx [ E4 E5 ] ] := toto_in heqm (id_in_wf _) h E1. rewrite E4.
have [ outx [ E6 [ lom2 [ E7 E8 ] ] ] ] := toto_out heqm (id_out_wf _) h E2 hsets.
rewrite E6 E5 E3. eauto.
Qed.

(* -------------------------------------------------------------------- *)
(* From generated ASM semantics to TCB ASM semantics                    *)

Lemma compile_cmd_name c vs loid :
  compile_gen c vs = Some loid →
  cmd_name_of_loid loid = c.
Proof.
  rewrite /compile_gen /compile_lo.
  case: omap => // irs h.
  have := @id_sem_wf (get_id c) irs loid h.
  rewrite get_id_ok.
  by case.
Qed.

Theorem L3 c vs m1 m2 loid lom :
     compile_gen c vs = Some loid
  -> sem_id m1 (get_id c) vs = Some m2
  -> lom_eqv m1 lom
  -> lom_eqv m2 (sem_lo lom loid).
Proof.
  move => hc.
  move/L2: (hc) => h/h{h} h/h{h} [lom'] [].
  rewrite -(compile_cmd_name hc).
  move /obindI : (hc) => [irs [? Hwt]].
  have := (id_gen_sem_wf lom Hwt).  
  by rewrite /sem_lo_gen (compile_cmd_name hc) => -> [<-].
Qed.

(* -------------------------------------------------------------------- *)
(* Putting all together                                                 *)

Definition compile (op: sopn) (outx : lvals) (inx: pexprs) :=
  compile_hi_sopn op outx inx >>= compile_gen op.

Theorem L (c : cmd_name) (outx : seq var) (inx : seq expr) loid (m1 m2 : mem) lom :
     compile c outx inx = Some loid 
  -> semc m1 (c, outx, inx) = Some m2
  -> lom_eqv m1 lom
  -> lom_eqv m2 (sem_lo lom loid).
Proof. 
  by move=> /obindI [lexprs []] /L1 H1 /L3 H3 /H1 /H3 H4 /H4.
Qed.
