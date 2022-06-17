(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ.
Require Import psem.
Require Import compiler_util ZArith.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap_scope.
Local Open Scope seq_scope.

Module E.

Definition pass_name := "allocation"%string.

(* FIXME: are there internal errors? *)
Definition gen_error (internal:bool) (ii:option instr_info) (msg:string) := 
  {| pel_msg      := pp_s msg
   ; pel_fn       := None
   ; pel_fi       := None
   ; pel_ii       := ii
   ; pel_vi       := None
   ; pel_pass     := Some pass_name
   ; pel_internal := internal
  |}.

Definition error msg := gen_error true None msg.

Definition loop_iterator := loop_iterator pass_name.

Definition fold2 := error "fold2".

End E.

Module Type CheckB.

  Module M.
    Parameter t : Type.
    Parameter empty : t.
    Parameter merge : t -> t -> t.
    Parameter incl  : t -> t -> bool.

    Parameter incl_refl : forall r, incl r r.
    Parameter incl_trans: forall r2 r1 r3, incl r1 r2 -> incl r2 r3 -> incl r1 r3.

    Parameter merge_incl_l: forall r1 r2, incl (merge r1 r2) r1.
    Parameter merge_incl_r: forall r1 r2, incl (merge r1 r2) r2.

  End M.

  Parameter check_e    : pexpr -> pexpr -> M.t -> cexec M.t.

  Parameter check_lval : option (stype * pexpr) -> lval -> lval -> M.t -> cexec M.t.

  Parameter eq_alloc : M.t -> Vmap.t -> Vmap.t -> Prop.

  Parameter eq_alloc_empty : eq_alloc M.empty Vmap.empty Vmap.empty.

  Parameter eq_alloc_incl : forall r1 r2 vm vm',
    M.incl r2 r1 ->
    eq_alloc r1 vm vm' ->
    eq_alloc r2 vm vm'.

  Section WITH_POINTER_DATA.
  Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.

  Parameter check_eP : forall gd e1 e2 r re vm1 vm2,
    check_e e1 e2 r = ok re ->
    eq_alloc r vm1 vm2 ->
    eq_alloc re vm1 vm2 /\
    forall scs m v1,  sem_pexpr gd (Estate scs m vm1) e1 = ok v1 ->
    exists2 v2, sem_pexpr gd (Estate scs m vm2) e2 = ok v2 & value_uincl v1 v2.

  Parameter check_lvalP : forall gd r1 r1' x1 x2 e2 s1 s1' vm1 v1 v2,
    check_lval e2 x1 x2 r1 = ok r1' ->
    eq_alloc r1 s1.(evm) vm1 ->
    value_uincl v1 v2 ->
    oapp (fun te2 =>
        sem_pexpr gd (with_vm s1 vm1) te2.2 >>= truncate_val te2.1 = ok v2) true e2 ->
    write_lval gd x1 v1 s1 = ok s1' ->
    exists2 vm1',
      write_lval gd x2 v2 (with_vm s1 vm1) = ok (with_vm s1' vm1') &
      eq_alloc r1' s1'.(evm) vm1'.

  End WITH_POINTER_DATA.
End CheckB.

Module Type CheckBE.
  Include CheckB.

  Section WITH_POINTER_DATA.
  Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.

  Parameter eft : PointerData -> eqType.
  #[ global ] Arguments eft {_}.

  #[ global ] Declare Instance pT  : progT eft.
  #[ global ] Declare Instance sCP : semCallParams.

  Parameter init_alloc :
    extra_fun_t -> extra_prog_t -> extra_prog_t -> cexec M.t.

  Parameter init_allocP :
   forall (ef: extra_fun_t) (ep1 ep2: extra_prog_t) ev s1 scs m r,
     init_alloc ef ep1 ep2 = ok r ->
     init_state ef ep1 ev (Estate scs m Vmap.empty) = ok s1 ->
     exists2 vm2,
       init_state ef ep2 ev (Estate scs m Vmap.empty) = ok (with_vm s1 vm2) &
       eq_alloc r s1.(evm) vm2.

  End WITH_POINTER_DATA.
End CheckBE.

Module CheckBU (C:CheckB) <: CheckBE.

  Include C.

  Section WITH_POINTER_DATA.
  Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.

  Definition eft := fun {_: PointerData} => [eqType of unit].
  #[ global ] Instance pT : progT eft := progUnit.
  #[ global ] Instance sCP : semCallParams := sCP_unit.

  Definition init_alloc (ef: extra_fun_t) (ep1 ep2: extra_prog_t) : cexec M.t :=
    ok M.empty.

  Lemma init_allocP (ef: extra_fun_t) (ep1 ep2: extra_prog_t) ev s1 scs m r :
    init_alloc ef ep1 ep2 = ok r ->
    init_state ef ep1 ev (Estate scs m Vmap.empty) = ok s1 ->
    exists2 vm2,
      init_state ef ep2 ev (Estate scs m Vmap.empty) = ok (with_vm s1 vm2) &
      eq_alloc r s1.(evm) vm2.
  Proof.
    move=> [<-] [<-]; exists Vmap.empty => //; exact: eq_alloc_empty.
  Qed.

  End WITH_POINTER_DATA.
End CheckBU.

Definition alloc_error := pp_internal_error_s "allocation".

Module CheckBS (C:CheckB) <: CheckBE.

  Include C.

  Section WITH_POINTER_DATA.
  Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.

  Definition eft := extra_fun_t (pT:= progStack).
  Instance pT : progT eft := progStack.
  Instance sCP : semCallParams := sCP_stack.
 
  Definition check_lvals :=
    fold2 E.fold2 (check_lval None).

  Definition check_vars xs1 xs2 r := check_lvals (map Lvar xs1) (map Lvar xs2) r.

  Lemma check_lvalsP gd xs1 xs2 vs1 vs2 r1 r2 s1 s2 vm1 :
    check_lvals xs1 xs2 r1 = ok r2 ->
    eq_alloc r1 s1.(evm) vm1 ->
    List.Forall2 value_uincl vs1 vs2 ->
    write_lvals gd s1 xs1 vs1 = ok s2 ->
    exists2 vm2,
      write_lvals gd (with_vm s1 vm1) xs2 vs2 = ok (with_vm s2 vm2) &
      eq_alloc r2 s2.(evm) vm2.
  Proof.
    elim: xs1 xs2 vs1 vs2 r1 r2 s1 s2 vm1 => [ | x1 xs1 Hrec] [ | x2 xs2] //=
      vs1 vs2 r1 r2 s1 s2 vm1.
    + by move=> [<-] Hvm1 [] //= [<-];exists vm1.
    apply: rbindP => r3 Hx Hcxs Hvm1 [] //= {vs1 vs2}.
    move=> v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s3 Hw Hws.
    have [// | vm3 ->/= Hvm3] := check_lvalP (e2:= None) Hx Hvm1 Hv _ Hw.
    apply: Hrec Hcxs Hvm3 Hvs Hws.
  Qed.

  Definition init_alloc (ef: extra_fun_t) (ep1 ep2: extra_prog_t) : cexec M.t :=
    check_vars [:: vid ep1.(sp_rsp); vid ep1.(sp_rip)]
               [:: vid ep2.(sp_rsp); vid ep2.(sp_rip)] M.empty.

  Lemma init_allocP (ef: extra_fun_t) (ep1 ep2: extra_prog_t) ev s1 scs m r :
    init_alloc ef ep1 ep2 = ok r ->
    init_state ef ep1 ev (Estate scs m Vmap.empty) = ok s1 ->
    exists2 vm2,
      init_state ef ep2 ev (Estate scs m Vmap.empty) = ok (with_vm s1 vm2) &
      eq_alloc r s1.(evm) vm2.
  Proof.
    rewrite /init_alloc /init_state /= /init_stk_state /check_vars.
    t_xrbindP => hc m' ha; rewrite (@write_vars_lvals _ _ _ [::]) => hw.
    have [ vm2 ]:= check_lvalsP (s1 := (Estate scs m' Vmap.empty)) hc eq_alloc_empty
                           (List_Forall2_refl _ (@value_uincl_refl)) hw.
    rewrite ha -write_vars_lvals => ??.
    by exists vm2.
  Qed.

  End WITH_POINTER_DATA.
End CheckBS.

Module MakeCheckAlloc (C:CheckBE).

Import C.

Section LOOP.

  Variable check_c : M.t -> cexec M.t.

  Fixpoint loop (n:nat) (m:M.t) :=
    match n with
    | O => Error E.loop_iterator 
    | S n =>
      Let m' := check_c m in
      if M.incl m m' then ok m
      else loop n (M.merge m m')
    end.

  Variable check_c2 : M.t -> cexec (M.t * M.t).

  Fixpoint loop2 (n:nat) (m:M.t) :=
    match n with
    | O => Error E.loop_iterator 
    | S n =>
      Let m' := check_c2 m in
      if M.incl m m'.2 then ok m'.1
      else loop2 n (M.merge m m'.2)
    end.

End LOOP.


Definition check_es es1 es2 r := fold2 E.fold2 check_e es1 es2 r.

Definition check_lvals := fold2 E.fold2 (check_lval None).

Definition check_var x1 x2 r := check_lval None (Lvar x1) (Lvar x2) r.

Definition check_vars xs1 xs2 r := check_lvals (map Lvar xs1) (map Lvar xs2) r.

Section ASM_OP.

Context {pd:PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.
Context `{asmop:asmOp}.

Fixpoint check_i (i1 i2:instr_r) r :=
  match i1, i2 with
  | Cassgn x1 _ ty1 e1, Cassgn x2 _ ty2 e2 =>
    if ty1 == ty2 then
     check_e e1 e2 r >>= check_lval (Some (ty2,e2)) x1 x2
    else Error (alloc_error "bad type in assignment")
  | Copn xs1 _ o1 es1, Copn xs2 _ o2 es2 =>
    if o1 == o2 then
      check_es es1 es2 r >>= check_lvals xs1 xs2
    else Error (alloc_error "operators not equals")
  | Csyscall xs1 o1 es1, Csyscall xs2 o2 es2 =>
    if o1 == o2 then
      check_es es1 es2 r >>= check_lvals xs1 xs2
    else Error (alloc_error "operators not equals")

  | Ccall _ x1 f1 arg1, Ccall _ x2 f2 arg2 =>
    if f1 == f2 then
      check_es arg1 arg2 r >>= check_lvals x1 x2
    else Error (alloc_error "functions not equals")
  | Cif e1 c11 c12, Cif e2 c21 c22 =>
    Let re := check_e e1 e2 r in
    Let r1 := fold2 E.fold2 check_I c11 c21 re in
    Let r2 := fold2 E.fold2 check_I c12 c22 re in
    ok (M.merge r1 r2)
  | Cfor x1 (d1,lo1,hi1) c1, Cfor x2 (d2,lo2,hi2) c2 =>
    if d1 == d2 then
      Let rhi := check_e lo1 lo2 r >>=check_e hi1 hi2 in
      let check_c r :=
          check_var x1 x2 r >>=
          fold2 E.fold2 check_I c1 c2 in
      loop check_c Loop.nb rhi
    else Error (alloc_error "loop directions not equals")
  | Cwhile a1 c1 e1 c1', Cwhile a2 c2 e2 c2' =>
    let check_c r :=
      Let r := fold2 E.fold2 check_I c1 c2 r in
      Let re := check_e e1 e2 r in
      Let r' := fold2 E.fold2 check_I c1' c2' re in
      ok (re, r') in
    Let r := loop2 check_c Loop.nb r in
    ok r

  | _, _ => Error (alloc_error "instructions not equals")
  end

with check_I i1 i2 r :=
  match i1, i2 with
  | MkI _ i1, MkI ii i2 => check_i i1 i2 r
  end.

Definition check_cmd := fold2 E.fold2 check_I.

Definition check_fundef (ep1 ep2 : extra_prog_t) (f1 f2: funname * fundef) (_:Datatypes.unit) :=

  let (f1,fd1) := f1 in
  let (f2,fd2) := f2 in
  add_funname f1 (add_finfo fd1.(f_info) (
  if (f1 == f2) && (fd1.(f_tyin) == fd2.(f_tyin)) && (fd1.(f_tyout) == fd2.(f_tyout)) &&
      (fd1.(f_extra) == fd2.(f_extra)) then
    Let r := init_alloc fd1.(f_extra) ep1 ep2 in
    Let r := check_vars fd1.(f_params) fd2.(f_params) r in
    Let r := check_cmd fd1.(f_body) fd2.(f_body) r in
    let es1 := map Plvar fd1.(f_res) in
    let es2 := map Plvar fd2.(f_res) in
    Let _r := check_es es1 es2 r in
    ok tt
  else Error (E.error "functions not equals"))).

Definition check_prog_error := alloc_error "check_fundef (fold2)".

Lemma check_fundef_meta ep1 ep2 ffd1 ffd2 u u' :
  check_fundef ep1 ep2 ffd1 ffd2 u = ok u' →
  let fd1 := ffd1.2 in
  let fd2 := ffd2.2 in
  [/\
   ffd1.1 = ffd2.1,
   fd1.(f_tyin) = fd2.(f_tyin),
   fd1.(f_tyout) = fd2.(f_tyout) &
   fd1.(f_extra) = fd2.(f_extra)
  ].
Proof.
  case: ffd1 ffd2 => f1 fd1 [] f2 fd2.
  by rewrite /check_fundef; case: andP => // - [] /andP[] /andP[] /eqP -> /eqP -> /eqP -> /eqP -> _.
Qed.

Definition check_prog ep1 p_funcs1 ep2 p_funcs2 := 
  fold2 check_prog_error (check_fundef ep1 ep2) p_funcs1 p_funcs2 tt.

Lemma check_lvalsP gd xs1 xs2 vs1 vs2 r1 r2 s1 s2 vm1 :
  check_lvals xs1 xs2 r1 = ok r2 ->
  eq_alloc r1 s1.(evm) vm1 ->
  List.Forall2 value_uincl vs1 vs2 ->
  write_lvals gd s1 xs1 vs1 = ok s2 ->
  exists2 vm2,
    write_lvals gd (with_vm s1 vm1) xs2 vs2 = ok (with_vm s2 vm2) &
    eq_alloc r2 s2.(evm) vm2.
Proof.
  elim: xs1 xs2 vs1 vs2 r1 r2 s1 s2 vm1 => [ | x1 xs1 Hrec] [ | x2 xs2] //=
    vs1 vs2 r1 r2 s1 s2 vm1.
  + by move=> [<-] Hvm1 [] //= [<-];exists vm1.
  apply: rbindP => r3 Hx Hcxs Hvm1 [] //= {vs1 vs2}.
  move=> v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s3 Hw Hws.
  have [ //| vm3 ->/= Hvm3] := check_lvalP (e2:= None) Hx Hvm1 Hv _ Hw.
  apply: Hrec Hcxs Hvm3 Hvs Hws.
Qed.

Section PROOF.

  Variable p1 p2:prog.
  Variable ev : extra_val_t.

  Local Notation gd := (p_globs p1).
  Local Notation ep1 := (p_extra p1).
  Local Notation ep2 := (p_extra p2). 

  Hypothesis Hcheck: check_prog ep1 p1.(p_funcs) ep2 p2.(p_funcs) = ok tt.
  Hypothesis eq_globs : p_globs p1 = p_globs p2.

  Lemma all_checked : forall fn fd1,
    get_fundef (p_funcs p1) fn = Some fd1 ->
    exists2 fd2, get_fundef (p_funcs p2) fn = Some fd2 &
                check_fundef ep1 ep2 (fn,fd1) (fn,fd2) tt = ok tt.
  Proof.
    move: Hcheck; rewrite /check_prog;clear Hcheck eq_globs.
    move: (p_funcs p1) (p_funcs p2). 
    elim => [ | [fn1' fd1'] pf1 Hrec] [ | [fn2 fd2] pf2] //.
    apply: rbindP => -[] Hc /Hrec {Hrec} Hrec.
    have ? : fn1' = fn2.
    + by move: Hc;rewrite /check_fundef; case:ifP => // /andP[]/andP[]/andP[]/eqP.
    subst=> fn fd1;rewrite !get_fundef_cons.
    case:ifPn => [/eqP -> [] <-| _ /Hrec //].
    by exists fd2.
  Qed.

  Let Pi_r s1 (i1:instr_r) s2:=
    forall r1 i2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_i i1 i2 r1 = ok r2 ->
    exists2 vm2, eq_alloc r2 (evm s2) vm2 &
      sem_i p2 ev (with_vm s1 vm1) i2 (with_vm s2 vm2).

  Let Pi s1 (i1:instr) s2:=
    forall r1 i2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_I i1 i2 r1 = ok r2 ->
    exists2 vm2, eq_alloc r2 (evm s2) vm2 &
      sem_I p2 ev (with_vm s1 vm1) i2 (with_vm s2 vm2).

  Let Pc s1 (c1:cmd) s2:=
    forall r1 c2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_cmd c1 c2 r1 = ok r2 ->
    exists2 vm2, eq_alloc r2 (evm s2) vm2 &
      sem p2 ev (with_vm s1 vm1) c2 (with_vm s2 vm2).

  Let Pfor (i1:var_i) vs s1 c1 s2 :=
    forall i2 r1 r1' c2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_var i1 i2 r1 = ok r1' ->
    check_cmd c1 c2 r1' = ok r2 -> M.incl r1 r2 ->
    exists2 vm2, eq_alloc r1 (evm s2) vm2 &
      sem_for p2 ev i2 vs (with_vm s1 vm1) c2 (with_vm s2 vm2).

  Let Pfun scs m fn vargs1 scs' m' vres :=
    forall vargs2, List.Forall2 value_uincl vargs1 vargs2 ->
    exists2 vres',
       sem_call p2 ev scs m fn vargs2 scs' m' vres' &
       List.Forall2 value_uincl vres vres'.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    move=> s r1 [ | ??] //= r2 vm1 ? [] <-;exists vm1 =>//;constructor.
  Qed.

  Local Lemma Hcons : sem_Ind_cons p1 ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc r1 [ | i2 c2] //= r2 vm1 /Hi Hvm1.
    apply: rbindP => r3 /Hvm1 [vm2 /Hc Hvm2 ?] /Hvm2.
    by move=> [vm3 ??];exists vm3 =>//;econstructor;eauto.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p1 ev Pi_r Pi.
  Proof.
    move=> ii i s1 s2 _ Hi  r1 [? i2] r2 vm1 /Hi Hvm /= /Hvm [vm2 ??].
    by exists vm2 =>//;constructor.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn p1 Pi_r.
  Proof.
    move => s1 s2 x tag ty e v v'.
    case: s1 => scs1 sm1 svm1 He Htr Hw r1 [] //= x2 tag2 ty2 e2 r2 vm1 Hvm1.
    case: eqP => // <- {ty2}; t_xrbindP.
    move=> r1' /check_eP -/(_ (p_globs p1) _ _ Hvm1) [Hr1'] /(_ _ _ _ He) [v2 He2 Hu2] Hcx.
    have [v2' Htr' Hu2']:= value_uincl_truncate Hu2 Htr.
    have  /(_ _ Hr1') [|]:= check_lvalP Hcx _ Hu2' _ Hw.
    + by rewrite /= He2 /= Htr'.
    move=> vm2 Hwv Hvm2.
    by exists vm2 =>//;econstructor;rewrite -?eq_globs;eauto.
  Qed.

  Lemma check_esP e1 e2 r re s vm:
    check_es e1 e2 r = ok re ->
    eq_alloc r s.(evm) vm ->
    eq_alloc re s.(evm) vm /\
    forall v1,  sem_pexprs gd s e1 = ok v1 ->
    exists2 v2, sem_pexprs (p_globs p2) (with_vm s vm) e2 = ok v2 &
               List.Forall2 value_uincl v1 v2.
  Proof.
    rewrite -eq_globs;case: s => sscs sm svm.
    rewrite /check_es; elim: e1 e2 r => [ | e1 es1 Hrec] [ | e2 es2] r //=.
    + by move=> [] <- ?;split=>// -[] //= ?;exists [::].
    move=> H Hea;apply: rbindP H => r' /(check_eP gd) /(_ Hea) [] Hea' He.
    move=> /Hrec /(_ Hea') [] Hre Hes;split=> // v1.
    rewrite /sem_pexprs;apply: rbindP => ve1 h. 
    have [{h}ve2 /= -> Hve]:= He _ _ _ h.
    apply:rbindP => ev2 /Hes [ves2 ];rewrite /sem_pexprs => -> Hves [] <- /=.
    by exists (ve2 :: ves2) => //;constructor.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p1 Pi_r.
  Proof.
    move => s1 s2 t o xs es.
    rewrite /sem_sopn; t_xrbindP => v ves He Ho Hw r1 [] //= xs2 t' o2 es2 r2 vm1 Hvm1.
    case:ifPn => //= /eqP <-.
    t_xrbindP => r1' /check_esP -/(_ _ _ Hvm1) [Hr1'] /(_ _ He) [v2 He2 Hu2].
    have [v' Ho' Hv Hcxs]:= vuincl_exec_opn Hu2 Ho.
    have /(_ _ Hr1') [vm2 Hwv Hvm2]:= check_lvalsP Hcxs _ Hv Hw.
    by exists vm2 =>//;constructor;rewrite /sem_sopn He2 /= Ho' -eq_globs.
  Qed.

  Local Lemma Hsyscall : sem_Ind_syscall p1 Pi_r.
  Proof.
    move => s1 scs m s2 o xs es ves vs hes hsys hw r1 [] //= xs2 o2 es2 r2 vm1 Hvm1.
    case:ifPn => //= /eqP <-.
    t_xrbindP => r1' /check_esP -/(_ _ _ Hvm1) [Hr1'] /(_ _ hes) [v2 He2 Hu2] Hcxs.
    have  [vs' Ho' Hv] := exec_syscallP hsys Hu2.
    have /(_ _ Hr1') [vm2 Hwv Hvm2]:= check_lvalsP Hcxs _ Hv hw.
    by exists vm2 =>//; econstructor; eauto; rewrite -eq_globs.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2.
    case: s1 => scs1 sm1 svm1 Hve _ Hc1 r1 [] //= e' c1' c2' r2 vm1 Hvm1.
    t_xrbindP => r1' /check_eP -/(_ gd _ _ Hvm1) [] Hr1'.
    move=> /(_ _ _ _ Hve) [ve' Hve' /value_uinclE ?];subst ve'.
    move => r3 Hr3 r4 Hr4 <-.
    have [vm2 Hvm2 Hsem]:= Hc1 _ _ _ _ Hr1' Hr3;exists vm2.
    + by eapply eq_alloc_incl;eauto;apply M.merge_incl_l.
    by apply Eif_true => //;rewrite -eq_globs Hve'.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2.
    case: s1 => scs1 sm1 svm1 Hve _ Hc1 r1 [] //= e' c1' c2' r2 vm1 Hvm1.
    t_xrbindP => r1' /check_eP -/(_ gd _ _ Hvm1) [] Hr1'.
    move=> /(_ _ _ _ Hve) [ve' Hve' /value_uinclE ?];subst ve'.
    move => r3 Hr3 r4 Hr4 <-.
    have [vm2 Hvm2 Hsem]:= Hc1 _ _ _ _ Hr1' Hr4;exists vm2.
    + by eapply eq_alloc_incl;eauto;apply M.merge_incl_r.
    by apply Eif_false => //;rewrite -eq_globs Hve'.
  Qed.

  Local Lemma loop2P check_c n r1 r2:
    loop2 check_c n r1 = ok r2 ->
      exists r2' r3,
      [/\ check_c r2' = ok (r2, r3), M.incl r2' r1 & M.incl r2' r3].
  Proof.
    elim: n r1 r2 => //= n Hrec r1 r2.
    apply: rbindP => -[r2_1 r2_2] Hc;case:ifPn => [? [] <- | _ /Hrec].
    + exists r1, r2_2;split=>//;apply M.incl_refl.
    move=> [r2' [r3 [H1 H2 H3]]];exists r2', r3;split=>//.
    apply: (M.incl_trans H2); apply M.merge_incl_l.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 s3 s4 a c e c'.
    case: s2 => scs2 sm2 svm2 _ Hc Hse _ Hc' _ Hw r1 [] //= a2 c2 e2 c2' r2 vm1 Hvm1.
    apply: rbindP => r /loop2P [r2' [r3 [H Hir1 Hir3]]] [?];subst r.
    have Hvmr2' := eq_alloc_incl Hir1 Hvm1.
    move: H; t_xrbindP => r0 Cc2; move /Hc: (Hvmr2') (Cc2) => H /H {H} [vm2 Hvm2 /= Hc2] re Hre.
    have /= [Hrevm2 /(_ _ _ _ Hse) [vb' Hse2 /value_uinclE ?]]:= check_eP gd Hre Hvm2.
    subst vb' => r' Cc2' ??;subst r2 r3.
    move /Hc': (Hrevm2) (Cc2')=> H /H {H} [vm3 Hvm3 /= Hc2'].
    have /Hw {Hw} Hw:= eq_alloc_incl Hir3 Hvm3.
    have : check_i (Cwhile a c e c') (Cwhile a2 c2 e2 c2') r2' = ok re.
    + by rewrite /= Loop.nbP /= Cc2 /= Hre /= Cc2' /= Hir3 /=.
    move=> /Hw [vm4 Hvm4 Hsw];exists vm4 => //.
    by apply: Ewhile_true Hsw;eauto;rewrite -eq_globs Hse2.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 a c e c'.
    case: s2 => scs2 sm2 svm2 _ Hc Hse r1 [] //= a2 c2 e2 c2' r2 vm1 Hvm1.
    t_xrbindP => r /loop2P [r2' [r3 [H Hir1 Hir3]]] ?;subst r.
    have Hvmr2' := eq_alloc_incl Hir1 Hvm1.
    move: H; t_xrbindP=> r0 Cc2; move /Hc: (Hvmr2') (Cc2) => H /H {H} [vm2 Hvm2 /= Hc2] re Hre.
    have /= [Hrevm2 /(_ _ _ _ Hse) [vb' Hse2 /value_uinclE ?]]:= check_eP gd Hre Hvm2.
    subst vb' => r' Cc2' ??;subst r2 r3.
    by exists vm2 => //; apply: Ewhile_false;rewrite // -eq_globs Hse2.
  Qed.

  Local Lemma loopP check_c n r1 r2:
    loop check_c n r1 = ok r2 ->
      exists r2',
      [/\ check_c r2 = ok r2', M.incl r2 r1 & M.incl r2 r2'].
  Proof.
    elim: n r1 r2 => //= n Hrec r1 r2.
    apply: rbindP => r2' Hc;case:ifPn => [? [] <- | _ /Hrec].
    + exists r2';split=>//;apply M.incl_refl.
    move=> [r2'' [H1 H2 H3]];exists r2'';split=>//.
    apply: (M.incl_trans H2); apply M.merge_incl_l.
  Qed.

  Local Lemma Hfor : sem_Ind_for p1 ev Pi_r Pfor.
  Proof.
    move => s1 s2 i d lo hi c vlo vhi.
    case: s1 => scs1 sm1 svm1.
    move=> Hlo Hhi Hc Hfor r1 [] //= i2 [[d2 lo2] hi2] c2 r2 vm1 Hvm1.
    case: eqP => //= ?;subst d2.
    t_xrbindP => r1' r1'' /check_eP -/(_ gd _ _ Hvm1) [Hr1'' Heqlo].
    have [vlo'' Hlo2 /value_uinclE Hvlo'] := Heqlo _ _ _ Hlo.
    subst vlo'' => /check_eP -/(_ gd _ _ Hr1'') [Hr1' Heqhi].
    have [vhi'' Hhi2 /value_uinclE Hhi'] := Heqhi _ _ _ Hhi.
    subst vhi'' => /loopP [r2'] []; t_xrbindP=> r2'' Hcv Hcc Hr2r1 Hr2r2.
    have := Hfor _ _ _ _ _ _ (eq_alloc_incl Hr2r1 Hr1') Hcv Hcc Hr2r2.
    move=> [vm2 Hvm2 Hsem2];exists vm2 => //.
    econstructor; rewrite -?eq_globs ?Hlo2 ?Hhi2 /= ;eauto.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    by move=> s i c i2 r1 r1' c2 r2 vm1 Ha ???;exists vm1 => //;constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p1 ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hwi _ Hc _ Hfor i2 r1 r1' c2 r2 vm2 Heq Hr1' Hcc Hincl.
    have [//|vm3 Hwi2 Hvm3] := check_lvalP (gd := gd) Hr1' Heq (value_uincl_refl _) _ Hwi.
    have [vm4 Hvm4 Hsc] := Hc _ _ _ _ Hvm3 Hcc.
    have [vm5 Hvm5 Hsf] := Hfor _ _ _ _ _ _ (eq_alloc_incl Hincl Hvm4) Hr1' Hcc Hincl.
    by exists vm5 =>//;econstructor;eauto.
  Qed.

  Local Lemma Hcall : sem_Ind_call p1 ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 ii xs fn args vargs vs Hes Hsc Hfun Hw r1 [] //= ii2 xs2 fn2 args2 r2 vm1 Hr1.
    case: eqP => //= ?;subst fn2.
    apply: rbindP => r1' Hca Hcxs.
    have [Hr1' /(_ _ Hes) [vargs2 Hargs2 Hvargs]] := check_esP Hca Hr1.
    have [v' Hs2 Hvs]:= Hfun _ Hvargs.
    have /(_ _ Hr1') [vm2 Hw2 Hr2]:= check_lvalsP Hcxs _ Hvs Hw.
    by exists vm2 =>//; econstructor;eauto;rewrite -?eq_globs.
  Qed.

  Section REFL.

    Hypothesis eq_prog : p1 = p2.

    Local Lemma Hproc_eq scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres :
      get_fundef (p_funcs p1) fn = Some f ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      init_state f.(f_extra) (p_extra p1) ev (Estate scs1 m1 Vmap.empty) = ok s0 ->
      write_vars (f_params f) vargs s0 = ok s1 ->
      sem p1 ev s1 (f_body f) s2 ->
      Pc s1 (f_body f) s2 ->
      mapM2 ErrType (fun ty (x : var_i) => truncate_val ty (evm s2).[x]) f.(f_tyout) (f_res f) = ok vres ->
      scs2 = s2.(escs) ->
      m2 = finalize f.(f_extra) s2.(emem) ->
      Pfun scs1 m1 fn vargs' scs2 m2 vres.
    Proof.
      move=> Hget Hca Hi Hw Hsem _ Hcr hscs Hfi vargs2 Hvargs2; rewrite -eq_prog.
      have: sem_call p1 ev scs1 m1 fn vargs' scs2 m2 vres by econstructor;eauto.
      by apply: sem_call_uincl.
    Qed.

    Lemma alloc_funP_eq_aux fn f f' scs1 m1 scs2 m2 vargs vargs' vres s0 s1 s2 vres':
      check_fundef ep1 ep2 (fn, f) (fn, f') tt = ok tt ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      init_state f.(f_extra) (p_extra p1) ev (Estate scs1 m1 Vmap.empty) = ok s0 ->
      write_vars (f_params f) vargs s0 = ok s1 ->
      sem p1 ev s1 (f_body f) s2 ->
      map (fun x : var_i => Vmap.get_var (evm s2) x) (f_res f) = vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      scs2 = s2.(escs) ->
      m2 = finalize f.(f_extra) s2.(emem) ->
      exists vm0' vm1' vm2' vres1 vres1',
       [ /\ mapM2 ErrType truncate_val f'.(f_tyin) vargs' = ok vargs,
            init_state f'.(f_extra) (p_extra p2) ev (Estate scs1 m1 Vmap.empty) = ok (with_vm s0 vm0') /\
            write_vars (f_params f') vargs (with_vm s0 vm0') = ok (with_vm s1 vm1'),
            sem p2 ev (with_vm s1 vm1') (f_body f') (with_vm s2 vm2'),
            [ /\ map (fun x : var_i => Vmap.get_var (evm (with_vm s2 vm2')) x) (f_res f') = vres1, 
                 List.Forall2 value_uincl vres' vres1' &
                mapM2 ErrType truncate_val f'.(f_tyout) vres1 = ok vres1'] &
            scs2 = s2.(escs) /\ m2 = finalize f'.(f_extra) s2.(emem) ].
    Proof.
      rewrite /check_fundef eq_refl => /=.
      case: ifP => // /andP[]/andP[]/eqP htyin /eqP htyout /eqP hextra.
      t_xrbindP => r0 Hcinit r1 Hcparams r2 Hcc r3 Hcres _ Hca.
      move=> /(init_allocP Hcinit) [vm0 Hi0 Hvm0].
      rewrite (write_vars_lvals gd)=> /(check_lvalsP Hcparams).
      move=> /(_ vargs _ Hvm0) [ | vm3 /= Hw2 Hvm3].
      + by apply: List_Forall2_refl.
      move=> /(sem_Ind Hskip Hcons HmkI Hassgn Hopn Hsyscall Hif_true Hif_false
                Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc_eq) Hc.
      have [vm4 /= Hvm4 Hsc2 Hres Hcr]:= Hc _ _ _ _ Hvm3 Hcc.
      have := check_esP Hcres Hvm4.
      move=> [Hr3];rewrite sem_pexprs_get_var => /(_ _ (f_equal (@ok _) Hres)) [vres1'].
      rewrite sem_pexprs_get_var => -[hmap] huincl ??.
      have [vres2' ??]:= mapM2_truncate_val Hcr huincl.
      do 5 eexists;split;eauto.
      + by rewrite -htyin.
      + rewrite -hextra; split; first by eauto.
        by rewrite (write_vars_lvals gd).
      + by rewrite -htyout;split;eauto.
      by rewrite -hextra.
    Qed.

  End REFL.

  Local Lemma Hproc : sem_Ind_proc p1 ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres Hget Hca Hi Hw _ Hc Hcr Hscs Hfi.
    have [fd2 Hget2 /=]:= all_checked Hget.
    rewrite eq_refl;case: ifP => // /andP[]/andP[] /eqP htyin /eqP htyout /eqP hextra.
    t_xrbindP => r0 Hcinit r1 Hcparams r2 Hcc r3 Hcres _.
    move=> vargs2 Hvargs2.
    have [vm0 Hi0 Hvm0]:= init_allocP Hcinit Hi.
    have [vs2 htr hall2]:= mapM2_truncate_val Hca Hvargs2.
    move: Hw;rewrite (write_vars_lvals gd)=> /(check_lvalsP Hcparams).
    move=> /(_ _ _ Hvm0 hall2) [vm3 /= Hw2 Hvm3].
    have [vm4 /= Hvm4 Hsc2]:= Hc _ _ _ _ Hvm3 Hcc.
    have := check_esP Hcres Hvm4.
    move=> [Hr3];rewrite sem_pexprs_get_var => /(_ _ erefl) [vres1'].
    rewrite sem_pexprs_get_var => -[<-] H2.
    rewrite mapM2_truncate_val_aux in Hcr.
    have [vs3 ??]:= mapM2_truncate_val Hcr H2.
    eexists;eauto;eexists;eauto.
    + by rewrite -htyin; eauto.
    + by rewrite -hextra; eauto.
    + by rewrite (write_vars_lvals gd).
    + by rewrite mapM2_truncate_val_aux -htyout.
    by rewrite -hextra.
  Qed.

  Lemma alloc_callP_aux f scs mem scs' mem' va vr:
    sem_call p1 ev scs mem f va scs' mem' vr ->
    exists2 vr', sem_call p2 ev scs mem f va scs' mem' vr' & List.Forall2 value_uincl vr vr'.
  Proof.
    move=>
      /(@sem_call_Ind _ _ _ _ _ _ _ _ p1 ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn Hsyscall
            Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
    move=> H;apply H.
    by apply List_Forall2_refl.
  Qed.

End PROOF.

Lemma alloc_callP ev gd ep1 p1 ep2 p2 (H: check_prog ep1 p1 ep2 p2 = ok tt) f scs mem scs' mem' va vr:
    sem_call {|p_globs := gd; p_funcs := p1; p_extra := ep1; |} ev scs mem f va scs' mem' vr ->
    exists2 vr', 
     sem_call {|p_globs := gd; p_funcs := p2; p_extra := ep2; |} ev scs mem f va scs' mem' vr' &
                List.Forall2 value_uincl vr vr'.
Proof.
  by apply alloc_callP_aux.
Qed.

Lemma alloc_funP_eq p ev fn f f' scs1 m1 scs2 m2 vargs vargs' vres vres' s0 s1 s2:
  check_fundef (p_extra p) (p_extra p) (fn, f) (fn, f') tt = ok tt ->
  mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
  init_state (f_extra f) (p_extra p) ev (Estate scs1 m1 Vmap.empty) = ok s0 ->
  write_vars (f_params f) vargs s0 = ok s1 ->
  sem p ev s1 (f_body f) s2 ->
  map (fun x : var_i => Vmap.get_var (evm s2) x) (f_res f) = vres ->
  mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
  scs2 = s2.(escs) ->
  m2 = finalize f.(f_extra) s2.(emem) ->
  exists vm0' vm1' vm2' vres1 vres1',
       [ /\ mapM2 ErrType truncate_val f'.(f_tyin) vargs' = ok vargs,
            init_state f'.(f_extra) (p_extra p) ev (Estate scs1 m1 Vmap.empty) = ok (with_vm s0 vm0') /\
            write_vars (f_params f') vargs (with_vm s0 vm0') = ok (with_vm s1 vm1'),
            sem p ev (with_vm s1 vm1') (f_body f') (with_vm s2 vm2'),
            [ /\ map (fun x : var_i => Vmap.get_var (evm (with_vm s2 vm2')) x) (f_res f') = vres1, 
                 List.Forall2 value_uincl vres' vres1' &
                mapM2 ErrType truncate_val f'.(f_tyout) vres1 = ok vres1'] &
            scs2 = s2.(escs) /\ m2 = finalize f'.(f_extra) s2.(emem) ].
  Proof. by apply alloc_funP_eq_aux. Qed.

End ASM_OP.

End MakeCheckAlloc.

Lemma eval_uincl_ok_undefb t1 t2 v1 v2 :
  subtype t1 t2 ->
  eval_uincl v1 v2 ->
  (∃ v' : psem_t t1, v1 = ok v') ∨ v1 = undef_error ∧ t1 = sbool ->
  (∃ v' : psem_t t2, v2 = ok v') ∨ v2 = undef_error ∧ t2 = sbool.
Proof.
  move=> hex hu [[v1' ?] | [? hx1]]; subst v1.
  + by move: hu => /=; case: v2 => //; eauto.
  move: hex v2 hu;rewrite hx1 => /subtypeEl ->.
  by case => /= [ | ? <-]; eauto.
Qed.

Lemma subtype_pof_val_ok t1 t2 v v1 :
  subtype t1 t2 ->
  pof_val t1 v = ok v1 ->
  exists2 v2, pof_val t2 v = ok v2 & value_uincl (pto_val v1) (pto_val v2).
Proof.
  case: t2 => > /subtypeE => [|||[?]] ?; subst; eauto.
  case: v => //=; last by case.
  move=> s' w hle [<-]; eexists; first reflexivity.
  case: Sumbool.sumbool_of_bool => e /=.
  + by rewrite (sumbool_of_boolET (cmp_le_trans e hle)).
  case: Sumbool.sumbool_of_bool => e' /=.
  + move: e => /negbT e.
    by apply/andP; split => //; exact: cmp_nle_le.
  rewrite -(zero_extend_idem _ hle).
  exact: word_uincl_zero_ext.
Qed.

Module CBAreg.

  Module M.

  Module Mv.

  Definition oget (mid: Mvar.t Sv.t) id := odflt Sv.empty (Mvar.get mid id).

  Definition valid (mvar: Mvar.t var) (mid: Mvar.t Sv.t) :=
    forall x id, Mvar.get mvar x = Some id <-> Sv.In x (oget mid id).

  Record t_ := mkT { mvar : Mvar.t var; mid : Mvar.t Sv.t; mvalid : valid mvar mid }.
  Definition t := t_.

  Definition get (m:t) (x:var) := Mvar.get (mvar m) x.

  Definition rm_id (m:t) id :=
     Sv.fold (fun x m => Mvar.remove m x) (oget (mid m) id) (mvar m).

  Definition ms_upd (m:Mvar.t Sv.t) (f:Sv.t -> Sv.t) id :=
    Mvar.set m id (f (oget m id)).

  Definition rm_x (m:t) x :=
    match Mvar.get (mvar m) x with
    | Some id => ms_upd (mid m) (Sv.remove x) id
    | None    => (mid m)
    end.

  Lemma valid_get_in m id x :
    get m x = Some id -> x \in Sv.elements (oget (mid m) id).
  Proof. by move=> /(mvalid) /Sv_elemsP. Qed.

  Lemma rm_idP m id x :
     Mvar.get (rm_id m id) x =
      if Sv.mem x (oget (mid m) id) then None
      else get m x.
  Proof.
    rewrite /rm_id; have := @valid_get_in m id.
    rewrite Sv.fold_spec /get Sv_elems_eq.
    elim: (Sv.elements _) (mvar m) => //= v vs Hrec mv Hget.
    rewrite Hrec ?inE.
    + rewrite Mvar.removeP eq_sym.
      by case: ( _ \in _);[rewrite orbT | case: (_ == _)].
    by move=> z;rewrite Mvar.removeP;case:ifP => //= H /Hget;rewrite inE eq_sym H.
  Qed.

  Lemma rm_id_eq m id x : Mvar.get (rm_id m id) x <> Some id.
  Proof.
    by rewrite rm_idP;case:ifPn => // /negP; rewrite mvalid => H /Sv_memP -/H.
  Qed.

  Lemma rm_idP_neq m x id id' : id != id' ->
    Mvar.get (rm_id m id) x = Some id' <-> Mvar.get (mvar m) x = Some id'.
  Proof.
    rewrite rm_idP => Hneq.
    case:ifP => //= /Sv_memP Hin;split=>// Hg.
    by move: Hin Hg Hneq; rewrite -mvalid => -> [->];rewrite eq_refl.
  Qed.

  Lemma oget_set m id id' s:
    oget (Mvar.set m id' s) id =
     if id' == id then s else oget m id.
  Proof. by rewrite /oget Mvar.setP;case:ifP. Qed.

  Lemma oget_rm m id id':
    oget (Mvar.remove m id') id =
     if id' == id then Sv.empty else oget m id.
  Proof. by rewrite /oget Mvar.removeP;case:ifP. Qed.

  Lemma rm_xP m x id : Sv.Equal (oget (rm_x m x) id) (Sv.remove x (oget (mid m) id)).
  Proof.
    rewrite /rm_x;case Heq: (Mvar.get (mvar m) x) => [id'|];last first.
    + case: (SvP.MP.In_dec x (oget (mid m) id));last by SvD.fsetdec.
      by rewrite -mvalid Heq.
    rewrite /ms_upd oget_set;case:ifPn => [/eqP -> //| /eqP].
    case: (SvP.MP.In_dec x (oget (mid m) id));last by SvD.fsetdec.
    by rewrite -mvalid Heq => -[->].
  Qed.

  Lemma valid_rm m id : valid (rm_id m id) (Mvar.remove (mid m) id).
  Proof.
    move=> x id';rewrite oget_rm;case:ifPn => [/eqP <- | Hne].
    + by split => [/rm_id_eq | ] //;SvD.fsetdec.
    by rewrite rm_idP_neq // mvalid.
  Qed.

  Definition remove m id := @mkT (rm_id m id) (Mvar.remove (mid m) id) (valid_rm m id).

  Lemma removeP m id x' :
    get (remove m id) x' =
      match get m x' with
      | Some id' => if id == id' then None else Some id'
      | None     => None
      end.
  Proof.
    rewrite /remove /get /= rm_idP /get; case: ifPn.
    + by move=> /Sv_memP;rewrite -mvalid => ->;rewrite eq_refl.
    move=> /Sv_memP;case Hg: Mvar.get => [id'|]//=;case:ifP => //= /eqP ?;subst id'.
    by move:Hg; rewrite mvalid => H /(_ H).
  Qed.

  Lemma valid_set m x id :
    valid (Mvar.set (rm_id m id) x id) (Mvar.set (rm_x m x) id (Sv.singleton x)).
  Proof.
    move=> y idy;rewrite Mvar.setP;case:eqP => [<- | Hne].
    + rewrite oget_set;case:eqP => [<- | Hne'];first by split => //;SvD.fsetdec.
      by rewrite rm_xP;split => [[]/Hne' | ] //;SvD.fsetdec.
    rewrite rm_idP oget_set;case:eqP => [<-| Hne'].
    + split;last by SvD.fsetdec.
      by case:ifPn => // /Sv_memP;rewrite -mvalid => H /H.
    rewrite rm_xP;case: ifPn => /Sv_memP H;split => // H1.
    + by move: H1 H Hne'=> /SvD.F.remove_3;rewrite -!mvalid => -> [->].
    + by move:H1;rewrite mvalid;SvD.fsetdec.
    by move: H1 => /SvD.F.remove_3;rewrite mvalid.
  Qed.

  Definition set m x id := mkT (valid_set m x id).

  Lemma valid_add m x id :
    valid (Mvar.set (mvar m) x id) (ms_upd (rm_x m x) (fun s => Sv.add x s) id).
  Proof.
    move=> y idy;rewrite Mvar.setP;case:eqP => Hxy.
    + subst y; rewrite /ms_upd;rewrite oget_set;split => [ [<-]| ].
      + by rewrite eq_refl;SvD.fsetdec.
      by case:eqP => [<- //| ?];rewrite rm_xP;SvD.fsetdec.
    by rewrite /ms_upd oget_set mvalid;case:eqP => [<- | ]; rewrite rm_xP;SvD.fsetdec.
  Qed.

  Definition add m x id := mkT (valid_add m x id).

  Lemma valid_empty : valid (@Mvar.empty _) (@Mvar.empty _).
  Proof. move=> x id;rewrite Mvar.get0 /oget Mvar.get0;split => //=;SvD.fsetdec. Qed.

  Definition empty := mkT valid_empty.

  End Mv.

  Definition mset_valid (mvar: Mvar.t var) (mset:Sv.t) :=
    forall x id, Mvar.get mvar x = Some id ->
    Sv.In x mset /\ subtype (vtype x) (vtype id).

  Record t_ := mkT {
    mv : Mv.t;
    mset : Sv.t;
    svalid: mset_valid (Mv.mvar mv) mset;
  }.

  Definition t := t_.

  Definition get (m:t) (x:var) := Mv.get (mv m) x.

  Lemma mset_valid_set m x id :
    subtype (vtype x) (vtype id) ->
    mset_valid (Mv.mvar (Mv.set (mv m) x id)) (Sv.add x (mset m)).
  Proof.
    move=> hsub y idy;rewrite Mvar.setP;case: eqP => ?.
    + move=> [?];subst; split=> //; SvD.fsetdec.
    by rewrite Mv.rm_idP;case:ifPn => //_ /svalid [??];split => //;SvD.fsetdec.
  Qed.

  Definition set m x id h := mkT (@mset_valid_set m x id h).
  Arguments set m x id h : clear implicits.

  Lemma mset_valid_add m x id :
    subtype (vtype x) (vtype id) ->
    mset_valid (Mv.mvar (Mv.add (mv m) x id)) (Sv.add x (mset m)).
  Proof.
    move=> h y idy;rewrite Mvar.setP;case: eqP => ?.
    + by move=> [?];subst; split=> //;SvD.fsetdec.
    by move=> /svalid [??];split=> //;SvD.fsetdec.
  Qed.

  Definition add m x id h := mkT (@mset_valid_add m x id h).
  Arguments add m x id h : clear implicits.

  Definition addc m x id :=
    if Sumbool.sumbool_of_bool (subtype (vtype x) (vtype id)) is left h then add m x id h
    else m.

  Lemma mset_valid_empty s : mset_valid (Mv.mvar Mv.empty) s.
  Proof. by move=> x id;rewrite Mvar.get0. Qed.

  Definition empty_s s := mkT (mset_valid_empty s).

  Definition empty := empty_s Sv.empty.

  Definition merge_aux m1 m2 :=
    Mvar.map2 (fun x ox ox' =>
      match ox, ox' with
      | Some idx, Some idx' => if idx == idx' then Some idx else None
      | Some idx, None      => if ~~(Sv.mem x (mset m2)) then Some idx else None
      | None, Some idx      => if ~~(Sv.mem x (mset m1)) then Some idx else None
      | None, None          => None
      end) (Mv.mvar m1.(mv)) (Mv.mvar m2.(mv)).

  Definition merge m1 m2 :=
    let mv := merge_aux m1 m2 in
    Mvar.fold (fun x idx m => addc m x idx) mv (empty_s (Sv.union (mset m1) (mset m2))).

  Lemma mset_valid_rm m id : mset_valid (Mv.mvar (Mv.remove (mv m) id)) (mset m).
  Proof.
    move=> y idy.
    have := Mv.removeP (mv m) id y.
    rewrite /Mv.get => ->.
    case: Mvar.get (@svalid m y) => [id'|] //.
    by move=> /(_ _ (refl_equal _));case:eqP => // ?? [<-].
  Qed.

  Definition remove m id :=  mkT (@mset_valid_rm m id).

  Lemma get0_s x s: get (empty_s s) x = None.
  Proof. apply Mvar.get0. Qed.

  Lemma setP m x id y h :
    get (set m x id h) y =
      if x == y then Some id
      else if Sv.mem y (Mv.oget (Mv.mid (mv m)) id) then None
      else get m y.
  Proof. by rewrite /get/set /Mv.get/Mv.set /= Mvar.setP Mv.rm_idP. Qed.

  Lemma setP_mset m x id h : mset (set m x id h) = Sv.add x (mset m).
  Proof. by []. Qed.

  Lemma addP m x id y h :
    get (add m x id h) y = if x == y then Some id else get m y.
  Proof. by rewrite /get/add /Mv.get/Mv.add /= Mvar.setP. Qed.

  Lemma addP_mset m x id h : mset (add m x id h) = Sv.add x (mset m).
  Proof. by []. Qed.

  Lemma addcP m x id y :
    get (addc m x id) y =
     if subtype (vtype x) (vtype id) && (x == y) then Some id else get m y.
  Proof.
    rewrite /addc; case: Sumbool.sumbool_of_bool => [ heq | -> //].
    by rewrite heq addP.
  Qed.

  Lemma merge_auxP m1 m2 x id :
    Mvar.get (merge_aux m1 m2) x = Some id ->
      get m1 x = Some id /\ get m2 x = Some id \/
      get m1 x = Some id /\ ~Sv.In x (mset m2) \/
      get m2 x = Some id /\ ~Sv.In x (mset m1).
  Proof.
    rewrite /merge_aux Mvar.map2P //.
    rewrite /get /Mv.get;case: Mvar.get => [id1 |];case: Mvar.get => [id2 |];
      last by tauto.
    + case:ifPn => // /eqP ->;tauto.
    + case:ifPn => // /Sv_memP;tauto.
    case:ifPn => // /Sv_memP;tauto.
  Qed.

  Lemma mergeP m1 m2 x id :
    get (merge m1 m2) x = Some id ->
      get m1 x = Some id /\ get m2 x = Some id \/
      get m1 x = Some id /\ ~Sv.In x (mset m2) \/
      get m2 x = Some id /\ ~Sv.In x (mset m1).
  Proof.
    rewrite /merge Mvar.foldP. set f := (f in foldl f).
    pose P := fun m =>
      get m x = Some id ->
       get m1 x = Some id /\ get m2 x = Some id \/
       get m1 x = Some id /\ ~Sv.In x (mset m2) \/
       get m2 x = Some id /\ ~Sv.In x (mset m1).
    have H : forall (l:list (var * var)) m,
      (forall p, p \in l -> Mvar.get (merge_aux m1 m2) p.1 = Some p.2) ->
      P m -> P (foldl f m l).
    + elim=> [|p l Hrec] //= m Hl Hm;apply Hrec.
      + by move=> ? H;apply Hl;rewrite in_cons H orbC.
      rewrite /f /P.
      have /Hl -/merge_auxP Hp := mem_head p l.
      have : subtype (vtype p.1) (vtype p.2).
      + have : get m1 p.1 = Some p.2 \/ get m2 p.1 = Some p.2 by intuition.
        by move=> [] /svalid [].
      by rewrite addcP => ->; case:eqP => [<- [<-] //| ne ];apply Hm.
    apply H;first by move=> p /Mvar.elementsP.
    by rewrite /P get0_s.
  Qed.

  Lemma mergeP_mset m1 m2 : Sv.Subset (Sv.union (mset m1) (mset m2)) (mset (merge m1 m2)).
  Proof.
    rewrite /merge Mvar.foldP. set f := (f in foldl f).
    pose P := fun m => Sv.Subset (Sv.union (mset m1) (mset m2)) (mset m).
    have : P (empty_s (Sv.union (mset m1) (mset m2))).
    + by rewrite /P /empty_s.
    have : forall p,
      p \in Mvar.elements (merge_aux m1 m2) -> subtype (vtype p.1) (vtype p.2).
    + move=> p /Mvar.elementsP -/merge_auxP ?.
      have : get m1 p.1 = Some p.2 \/ get m2 p.1 = Some p.2 by intuition.
      by move=> [] /svalid [].
    elim : Mvar.elements (empty_s _) => //= -[x idx] l Hl m Hp Hm.
    apply Hl;first by move=> p hin;apply Hp;rewrite in_cons hin orbT.
    move:Hm;rewrite /f /P /addc /=.
    case: Sumbool.sumbool_of_bool => [? | ].
    + rewrite addP_mset;SvD.fsetdec.
    by have /= -> := Hp _ (mem_head (x, idx) l).
  Qed.

  Lemma removeP m id x :
    get (remove m id) x =
      match get m x with
      | Some id' => if id == id' then None else Some id'
      | None     => None
      end.
  Proof. apply Mv.removeP. Qed.

  Definition incl m1 m2 :=
    Sv.subset (mset m2) (mset m1) &&
    let mv1 := Mv.mvar m1.(mv) in
    let mv2 := Mv.mvar m2.(mv) in
    Sv.for_all (fun x =>
       match Mvar.get mv1 x with
       | Some idx => Mvar.get mv2 x == Some idx
       | None     => true
       end) (mset m2).

  Lemma inclP m1 m2 :
    reflect ((forall x id, Sv.In x (mset m2) -> get m1 x = Some id -> get m2 x = Some id) /\
             Sv.Subset (mset m2) (mset m1))
            (incl m1 m2).
  Proof.
    rewrite /incl andbC; apply (equivP andP).
    match goal with |- (is_true ?A /\ _) <-> (?B /\ _) => have : reflect B A end.
    + apply: (equivP idP).
      rewrite /is_true -SvD.F.for_all_iff;split => [ H x id| H x] /H;
        rewrite /get /Mv.get.
      + by move=> H1 H2;move: H1; rewrite H2 => /eqP.
      by case: Mvar.get => // idx /(_ _ (refl_equal _)) /eqP.
    by move=> /rwP ->;rewrite SvD.F.subset_iff.
  Qed.

  Lemma incl_refl r : incl r r.
  Proof. by apply/inclP;split. Qed.

  Lemma incl_trans r2 r1 r3 : incl r1 r2 -> incl r2 r3 -> incl r1 r3.
  Proof.
    move=> /inclP [H1 H3] /inclP [H2 H4];apply/inclP;split;last by SvD.fsetdec.
    by move=> x id Hin Hget;apply H2 => //;apply H1 => //;SvD.fsetdec.
  Qed.

  Lemma merge_incl_l r1 r2 : incl (merge r1 r2) r1.
  Proof.
    apply/inclP;split;first by move=> x idx Hin /mergeP;tauto.
    by have := @mergeP_mset r1 r2;SvD.fsetdec.
  Qed.

  Lemma merge_incl_r r1 r2 : incl (merge r1 r2) r2.
  Proof.
    apply/inclP;split;first by move=> x idx Hin /mergeP;tauto.
    by have := @mergeP_mset r1 r2;SvD.fsetdec.
  Qed.

  End M.

  Definition cerr_varalloc xi1 xi2 s:=
    pp_internal_error "Variable allocation" (pp_box [:: pp_var xi1; pp_s "and"; pp_var xi2; pp_s ":"; pp_s s]).

  Definition check_v xi1 xi2 (m:M.t) : cexec M.t :=
    let x1 := xi1.(v_var) in
    let x2 := xi2.(v_var) in
    if Sumbool.sumbool_of_bool (subtype (vtype x1) (vtype x2)) is left h then
      match M.get m x1 with
      | None     =>
        if Sv.mem x1 (M.mset m) then 
            Error (cerr_varalloc xi1 xi2 "variable already set")
        else ok (M.set m x1 x2 h)
      | Some x2' =>
        if x2 == x2' then ok m
        else Error (cerr_varalloc xi1 xi2 "variable mismatch")
      end
    else Error (cerr_varalloc xi1 xi2 "type mismatch").

  Definition error_e := pp_internal_error_s "allocation" "expression are not equal".

  Definition check_gv x1 x2 (m:M.t) : cexec M.t :=
    if x1.(gs) == x2.(gs) then
      if is_lvar x1 then check_v x1.(gv) x2.(gv) m 
      else 
        if x1.(gv).(v_var) == x2.(gv).(v_var) then ok m
        else Error error_e
    else Error error_e.
 
  Fixpoint check_e (e1 e2:pexpr) (m:M.t) : cexec M.t :=
    match e1, e2 with
    | Pconst n1, Pconst n2 =>
      if n1 == n2 then ok m else Error error_e
    | Pbool  b1, Pbool  b2 =>
      if b1 == b2 then ok m else Error error_e
    | Parr_init n1, Parr_init n2 =>
      if n1 == n2 then ok m else Error error_e
    | Pvar   x1, Pvar   x2 => check_gv x1 x2 m
    | Pget aa1 w1 x1 e1, Pget aa2 w2 x2 e2 =>
      if (aa1 == aa2) && (w1 == w2) then check_gv x1 x2 m >>= check_e e1 e2 else Error error_e
    | Psub aa1 w1 len1 x1 e1, Psub aa2 w2 len2 x2 e2 =>
      if (aa1 == aa2) && (w1 == w2) && (len1 == len2) then check_gv x1 x2 m >>= check_e e1 e2 
      else Error error_e
    | Pload w1 x1 e1, Pload w2 x2 e2 =>
      if w1 == w2 then check_v x1 x2 m >>= check_e e1 e2 else Error error_e
    | Papp1 o1 e1, Papp1 o2 e2 =>
      if o1 == o2 then check_e e1 e2 m
      else Error error_e
     | Papp2 o1 e11 e12, Papp2 o2 e21 e22 =>
      if o1 == o2 then check_e e11 e21 m >>= check_e e12 e22
      else Error error_e
    | PappN o1 es1, PappN o2 es2 =>
      if o1 == o2
      then fold2 (alloc_error "check_e (appN)") check_e es1 es2 m
      else Error error_e
    | Pif t e e1 e2, Pif t' e' e1' e2' =>
      if t == t' then
        check_e e e' m >>= check_e e1 e1' >>= check_e e2 e2'
      else Error error_e
    | _, _ => Error error_e
    end.

  Definition check_var (x1 x2:var) m h: cexec M.t :=
    ok (M.set m x1 x2 h).

  Definition check_varc (xi1 xi2:var_i) m : cexec M.t :=
    let x1 := xi1.(v_var) in
    let x2 := xi2.(v_var) in
    if Sumbool.sumbool_of_bool (subtype (vtype x1) (vtype x2)) is left h
    then check_var m h else Error (cerr_varalloc xi1 xi2 "type mismatch").

  Definition is_Pvar (e:option (stype * pexpr)) :=
    match e with
    | Some (ty, Pvar x) => if is_lvar x then Some (ty,x.(gv)) else None
    | _ => None
    end.

  Lemma is_PvarP e ty x : is_Pvar e = Some (ty,x) -> e = Some (ty, Plvar x).
  Proof. by case: e => //= -[? []] //= [] v [] // [<- <-]. Qed.

  Definition error_lv := pp_internal_error_s "allocation" "lval not equal".

  Definition check_lval (e2:option (stype * pexpr)) (x1 x2:lval) m : cexec M.t :=
    match x1, x2 with
    | Lnone  _ t1, Lnone _ t2  =>
      if subtype t1 t2 then ok m else Error error_lv
    | Lnone  _ t1, Lvar x      =>
      if subtype t1 x.(v_var).(vtype) then
        ok (M.remove m x.(v_var))
      else Error error_lv
    | Lvar x1    , Lvar x2     =>
      match is_Pvar e2 with
      | Some (ty, x2') =>
        if Sumbool.sumbool_of_bool (subtype (vtype x1) (vtype x2)) is left h then
          if (vtype x1 == ty) && (vtype x1 == vtype x2) && (x2.(v_var) == x2') then ok (M.add m x1 x2 h)
          else check_var m h
        else Error (cerr_varalloc x1 x2 "type mismatch")
      | _               => check_varc x1 x2 m
      end
    | Lmem w1 x1 e1, Lmem w2 x2 e2  =>
      if w1 == w2 then check_v x1 x2 m >>= check_e e1 e2 else Error error_lv
    | Laset aa1 w1 x1 e1, Laset aa2 w2 x2 e2 =>
      if (aa1 == aa2) && (w1 == w2) then check_v x1 x2 m >>= check_e e1 e2 >>= check_varc x1 x2
      else Error error_lv
    | Lasub aa1 w1 len1 x1 e1, Lasub aa2 w2 len2 x2 e2 =>
      if (aa1 == aa2) && (w1 == w2) && (len1 == len2) then check_v x1 x2 m >>= check_e e1 e2 >>= check_varc x1 x2
      else Error error_lv
 
    | _          , _           => Error error_lv
    end.

  Definition eq_alloc (r:M.t) vm1 vm2 :=
    [/\ vm_uincl Vmap.empty vm2,
        (forall x, ~Sv.In x (M.mset r) -> Vmap.get_var vm1 x = undef_addr x.(vtype)) &
        (forall x x', M.get r x = Some x' ->
                      value_uincl (Vmap.get_var vm1 x) (Vmap.get_var vm2 x'))].

  Lemma eq_alloc_empty: eq_alloc M.empty Vmap.empty Vmap.empty.
  Proof. rewrite /vm_uincl; split=> // *; exact: Vmap.get_var0. Qed.

  Lemma eq_alloc_incl r1 r2 vm vm':
    M.incl r2 r1 ->
    eq_alloc r1 vm vm' ->
    eq_alloc r2 vm vm'.
  Proof.
    move=> /M.inclP [Hi Hsub] [ Huincl epa eqa];split=>//.
    + by move=> x Hx;apply epa;SvD.fsetdec.
    move=> x x'; case: (Sv_memP x (M.mset r1)) => [ /Hi H /H /eqa // | /epa -> hget].
    have := Huincl x'.
    have [_ /(_ x') /= heq _ ]:= eq_alloc_empty.
    rewrite heq;last by rewrite SvD.F.empty_iff.
    apply: value_uincl_trans; apply/subtype_eval_uincl_pundef.
    by have []:= M.svalid hget.
  Qed.

  Lemma check_vP x1 x2 r re vm1 vm2 :
    check_v x1 x2 r = ok re ->
    eq_alloc r vm1 vm2 ->
    eq_alloc re vm1 vm2 /\
      value_uincl (Vmap.get_var vm1 x1) (Vmap.get_var vm2 x2).
  Proof.
    rewrite /check_v;case: Sumbool.sumbool_of_bool => // hsub.
    case Hget : M.get => [id | ].
    + case: eqP => //= ? [<-];subst id => Hea;split=>//.
      by case: Hea => _ _; apply.
    case: ifPn => //= /Sv_memP Hnot [] <- [ Hvm0 Hset Huincl];split;first split=>//.
    + by move=> x;rewrite M.setP_mset => ?;apply Hset;SvD.fsetdec.
    + move=> x id;rewrite M.setP;case:eqP => [<- [<-]| Hne].
      + rewrite (Hset _ Hnot) /=.
        apply: (value_uincl_trans (subtype_undef_addr (subtype_compat hsub))).
        by have := Hvm0 x2; rewrite Vmap.get_var0.
      by case:ifP => // _;apply Huincl.
    rewrite (Hset _ Hnot) /undef_addr.
    by case: (vtype x1) hsub (Hvm0 x2) => > /subtypeEl => [|||[?]];
      rewrite Vmap.get_var0 => -> //.
  Qed.

  Lemma check_gvP x1 x2 r re gd vm1 vm2 : 
    check_gv x1 x2 r = ok re ->
    eq_alloc r vm1 vm2 ->
    eq_alloc re vm1 vm2 /\
    (forall v1 : value,
       get_gvar gd vm1 x1 = ok v1 ->
       exists2 v2 : value, get_gvar gd vm2 x2 = ok v2 & value_uincl v1 v2).
  Proof.
    rewrite /check_gv /get_gvar /is_lvar; case: x1 x2 => x1 k1 [x2 k2] /=.
    case: eqP => [-> | //]; case: eqP => [_ /check_vP h/h{h}[]|_].
    + by eexists => // ? [<-]; eexists.
    by case:eqP => [-> [<-] ?| //]; split; eauto.
  Qed.

  Section WITH_POINTER_DATA.
  Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.

  Section CHECK_EP.
    Context (gd: glob_decls) (vm2: Vmap.t).

    Let P e1 : Prop :=
      ∀ e2 r re vm1, check_e e1 e2 r = ok re →
      eq_alloc r vm1 vm2 →
      eq_alloc re vm1 vm2 ∧
      ∀ scs m v1,
        sem_pexpr gd {| escs := scs; emem := m ; evm := vm1 |} e1 = ok v1 →
      exists2 v2, sem_pexpr gd {| escs := scs; emem := m ; evm := vm2 |} e2 = ok v2 &
            value_uincl v1 v2.

    Let Q es1 : Prop :=
      ∀ es2 r re vm1 err,
      fold2 err check_e es1 es2 r = ok re →
      eq_alloc r vm1 vm2 →
      eq_alloc re vm1 vm2 ∧
      ∀ scs m vs1,
        sem_pexprs gd {| escs := scs; emem := m ; evm := vm1 |} es1 = ok vs1 →
      exists2 vs2, sem_pexprs gd {| escs := scs; emem := m ; evm := vm2 |} es2 = ok vs2 &
             List.Forall2 value_uincl vs1 vs2.

    Lemma check_e_esP : (∀ e, P e) ∧ (∀ es, Q es).
    Proof.
      apply: pexprs_ind_pair; split; subst P Q => /=.
      - case => // r _ vm1 _ [<-] h; split => // scs m _ [<-] /=; eauto.
      - move => e1 he1 es1 hes1 [] // e2 es2 r re vm1 err; t_xrbindP => r' ok_r' ok_re h.
        move: he1 => /(_ e2 r r' vm1 ok_r' h) [] h' he1.
        move: hes1 => /(_ es2 r' re vm1 err ok_re h') [] hre hes1.
        apply: (conj hre) => scs m vs1'; t_xrbindP => v1 ok_v1 vs1 ok_vs1 <- {vs1'} /=.
        move: he1 => /(_ _ _ _ ok_v1) [v2 -> hv].
        move: hes1 => /(_ _ _ _ ok_vs1) [vs2 -> hvs].
        eexists; first reflexivity. by constructor.
      - move => z1 [] // z2 r re vm1.
        by case: ifPn => // /eqP <- [->] ?; split=> // ??? [] <-; exists z1.
      - move => b1 [] // b2 r re vm1.
        by case: ifPn => // /eqP <- [->] ?;split=> // ??? [] <-; exists b1.
      - move => n1 [] // n2 r re vm1.
        by case: eqP => //= <- [<-] ?; split => // ??? [<-]; eauto.
      - move => x1 [] // x2 r re vm1.
        by move=> /check_gvP Hv /(Hv gd) [Hea H]; eexists=> // > /H[]; eauto.
      - move => aa1 sz1 x1 e1 He1 [] // aa2 sz2 x2 e2 r re vm1.
        case: andP  => // -[/eqP ? /eqP ?]; subst aa2 sz2.
        apply: rbindP => r' Hcv Hce Hea.
        have [Hea' Hget]:= check_gvP gd Hcv Hea.
        have [Hre Hse1]:= He1 _ _ _ _ Hce Hea';split => //= scs m v1.
        apply: on_arr_gvarP => n t Heqt /Hget [v2 ].
        rewrite /on_arr_var; case: v2 => //= n' t' -> [? /WArray.uincl_get Ht]; subst.
        t_xrbindP=> w ve /Hse1 [v2 -> ] /[swap] /to_intI -> /value_uinclE ->
          ? /= /Ht -> /= <-.
        by eauto.
      - move => aa1 sz1 len1 x1 e1 He1 [] // aa2 sz2 len2 x2 e2 r re vm1.
        case: andP => // -[] /andP[] /eqP ? /eqP ? /eqP ?; subst aa2 sz2 len2.
        apply: rbindP => r' Hcv Hce Hea.
        have [Hea' Hget]:= check_gvP gd Hcv Hea.
        have [Hre Hse1]:= He1 _ _ _ _ Hce Hea';split => //= scs m v1.
        apply: on_arr_gvarP => n t Heqt /Hget [v2 ].
        rewrite /on_arr_var; case: v2 => //= n' t' -> [? /WArray.uincl_get_sub Ht]; subst.
        t_xrbindP => w ve /Hse1 [v2 -> ] /[swap] /to_intI -> /value_uinclE ->
          ? /= /Ht [? -> ?] <- /=.
        by eexists.
      - move => sz1 x1 e1 He1 [] // sz2 x2 e2 r re vm1.
        case: eqP => // ->.
        apply: rbindP => r' Hcv Hce Hea.
        have [Hea' Hvu]:= check_vP Hcv Hea.
        have [Hre Hse1]:= He1 _ _ _ _ Hce Hea'; split => //= scs m v1.
        t_xrbindP=> w1 /to_wordI [? [? H1 /word_uincl_truncate]].
        move: H1 Hvu => -> /value_uinclE[? [? -> h]] /(_ _ _ h){h} /= ->
          > /Hse1{Hse1} [? -> ] /[swap] /to_wordI [? [? -> ]]
          /word_uincl_truncate h /value_uinclE [? [? -> /h{h} /= ->]] ? /= -> /= ->.
        by eauto.
      - move => op1 e1 He1 [] // op2 e2 r re vm1.
        case: eqP => // <-. move=> H /(He1 _ _ _ _ H) [Hea Hse1];split=>//=.
        move=> scs m v1;apply:rbindP => v /Hse1 [v1' -> U1].
        by move=> /(vuincl_sem_sop1 U1);exists v1.
      - move => op1 e11 He11 e12 He12 [] // op2 e21 e22 r re vm1.
        case: eqP => // <-;apply:rbindP => r' Hs1 Hs2 Hea.
        have [Hea' Hse1]:= He11 _ _ _ _ Hs1 Hea.
        have [? Hse2]:= He12 _ _ _ _ Hs2 Hea'; split => //= scs m v.
        apply: rbindP => v1 /Hse1 [v1' -> U1].
        apply: rbindP => v2 /Hse2 [v2' -> U2].
        by move=> /(vuincl_sem_sop2 U1 U2);exists v.
      - move => op1 es1 Hes1 [] // op2 es2 r re vm1.
        case: eqP => // <- {op2} ok_re hr.
        move: Hes1 => /(_ _ _ _ _ _  ok_re hr) [] hre h.
        split => //= scs m v1; t_xrbindP => vs1 ok_vs1 ok_v1.
        rewrite -/(sem_pexprs _ _).
        move: h => /(_ _ _ _ ok_vs1) [vs2 -> hs /=].
        by have [] := vuincl_sem_opN ok_v1 hs; eauto.
      move => t e He e11 He11 e12 He12 [] // t' e2 e21 e22 r re vm1.
      case: eqP => // <-.
      t_xrbindP => r1 r' /He Hr' /He11 Hr1 /He12 Hr2 {He He11 He12}.
      move=> /Hr'{Hr'}[] /Hr1{Hr1}[] /Hr2{Hr2}[] Hre Hs2 Hs1 Hs;split=>// scs m v1.
      t_xrbindP=> b > /Hs [_ /= ->] /= /[swap] /to_boolI -> /value_uinclE ->.
      move=> ?? /Hs1 [? -> /=] /of_val_uincl H/H{H} [? -> ?].
      move=> ?? /Hs2 [? -> /=] /of_val_uincl H/H{H} [? -> ?] <- /=.
      by eexists;eauto;case: (b).
  Qed.

  End CHECK_EP.

  Definition check_eP gd e1 e2 r re vm1 vm2 :=
    (check_e_esP gd vm2).1 e1 e2 r re vm1.

  Lemma set_var_uincl_widen x1 x2 v1 v2 vm1 vm1' vm2 vm2' :
    value_uincl v1 v2 -> subtype (vtype x1) (vtype x2) ->
    vm1 .[ x1 <- v1] = ok vm1' -> vm2 .[ x2 <- v2] = ok vm2' ->
    value_uincl vm1'.[x1] vm2'.[x2].
  Proof.
    move=> ++ /Vmap.set_varP_eq -> /Vmap.set_varP_eq ->.
    (case: v1 => [||||t p] >;
      last by case: (truncate_undefined_val (vtype x1) p) => _ -> /=;
        case: Result.rdfltP => // ? /[dup]/truncate_defined_val_has_type->
        /truncate_defined_val_subtype /[swap] /compat_type_trans H /subtype_compat;
        rewrite compat_typeC => /H)
      => /value_uinclE => [||[? + ?]|[? [? + Hwu]]] => ->;
      case: (vtype x1) => > /subtypeEl => [|||[?]] -> //;
        rewrite /truncate_defined_val /=.
    + case: Sumbool.sumbool_of_bool=> // /[dup]/eqP<- ?.
      by rewrite (Eqdep_dec.UIP_dec Pos.eq_dec (eqP _)).
    case: Result.rmapP => [?/truncate_wordP[h1 ->]|?/truncate_word_errP/proj2];
      case: Result.rmapP => [?/truncate_wordP[h2 ->]|?/truncate_word_errP/proj2] /=;
      have [h3 /eqP -> h4 *] := andP Hwu; rewrite ?zero_extend_idem //
        ?word_uincl_zero_ext // /word_uincl ?zero_extend_idem //;
        try (apply/andP; split=> //).
    + exact: cmp_le_trans h1 h3.
    + exact: cmp_lt_le (cmp_lt_le_trans h4 _).
    exact: cmp_lt_le (cmp_lt_le_trans h4 _).
  Qed.

  Lemma vmap_set_var_widen x1 x2 v1 v2 vm1 vm1' vm2 :
    value_uincl v1 v2 -> subtype (vtype x1) (vtype x2) ->
    vm1 .[ x1 <- v1] = ok vm1' -> exists vm2', vm2 .[ x2 <- v2] = ok vm2'.
  Proof.
    move=> /(set_var_ex_uincl vm1)h+ /[dup]Hsv /h{h}[vm /Vmap.set_varP_eq Hv _].
    move: Hv (Vmap.get_varP vm x1) => -> Htru Hs; apply: (Vmap.set_var_ok vm2).
    move: Htru Hs; rewrite /typerel_undef; case Ht: (truncate_defined_val (vtype x2)).
    + by rewrite (proj2 (truncate_is_defined_val Ht)) (truncate_defined_val_has_type Ht) vm_relxx.
    case: Result.rdfltP => [? /[dup]/truncate_defined_val_subtype Hsub
      /truncate_is_defined_val/proj1 -> _ | _ _] /= H.
      + (case: v2 Hsub H Ht => /= [||||?+ /subtype_compat+ /subtype_compat+ _] >;
          last by rewrite compat_typeC => /is_undef_t_compat_subtype h0 /compat_type_trans h/h/h0)
          => /subtypeE => [|||[?+_]] => -> /subtypeEl => [|||[?+?]] => -> //;
          rewrite /truncate_defined_val /=; first by rewrite sumbool_of_boolET.
      case: Result.rmapP => [// | ?/truncate_word_errP[_ h] *].
      exact: cmp_lt_le h.
    move: H; rewrite /Basics.flip; case: is_defined; first exact: subtype_trans.
    rewrite 2!(compat_typeC _ (_ v2)) => + /subtype_compat.
    exact: compat_type_trans.
  Qed.

  Lemma eq_alloc_set x1 v1 r x2 v2 vm1 vm1' vm2 vm2' h :
    eq_alloc r vm1 vm2 -> value_uincl v1 v2 ->
    Vmap.set_var vm1 x1 v1 = ok vm1' -> Vmap.set_var vm2 x2 v2 = ok vm2' ->
    eq_alloc (M.set r x1 x2 h) vm1' vm2'.
  Proof.
    move=> [Hvm0 Hin Hget] Hu Hvm1 Hvm2.
    split.
    + move=> y; rewrite Vmap.get_var0.
      exact: compat_uincl_undef (typerel_undef_compat vm_subcomp (Vmap.get_varP _ _)).
    + move=> z;rewrite M.setP_mset => Hnin.
      by rewrite (Vmap.set_varP_neq Hvm1);[apply Hin|apply /eqP];SvD.fsetdec.
    move=> x id;rewrite M.setP;case:eqP => [<-[<-] | /eqP Hne];
      first exact: set_var_uincl_widen Hu h Hvm1 Hvm2.
    case: ifPn => //= /Sv_memP Hid Hgetx.
    rewrite (Vmap.set_varP_neq Hvm1 Hne) (Vmap.set_varP_neq Hvm2); first exact: Hget.
    rewrite M.Mv.mvalid in Hgetx.
    by apply/eqP => ?; subst id; apply: Hid.
  Qed.

  Lemma eq_alloc_add x1 v1 r x2 vm1 vm1' vm2 vm2' h :
    eq_alloc r vm1 vm2 -> value_uincl v1 vm2.[x2] ->
    vm1.[x1 <- v1] = ok vm1' -> vm2.[x2 <- vm2.[x2]] = ok vm2' ->
    eq_alloc (M.add r x1 x2 h) vm1' vm2'.
  Proof.
    move=> [Hvm0 Hin Hget] /= Hu Hvm1 Hvm2.
    split.
    + move=> y; rewrite Vmap.get_var0.
      exact: compat_uincl_undef (typerel_undef_compat vm_subcomp (Vmap.get_varP _ _)).
    + move=> z;rewrite M.addP_mset => Hnin.
      by rewrite (Vmap.set_varP_neq Hvm1); [apply Hin|apply /eqP]; SvD.fsetdec.
    move=> x id;rewrite M.addP;case:eqP => [<-[<-] | /eqP Hne /Hget];
      first exact: set_var_uincl_widen Hu h Hvm1 Hvm2.
    rewrite (Vmap.set_varP_neq Hvm1 Hne).
    case: (x2 =P id) => [<-|/eqP hne]; last by rewrite (Vmap.set_varP_neq Hvm2 hne).
    by rewrite (vmap_get_set_get Hvm2).
  Qed.

  Lemma check_varP r1 r1' vm1 vm2 vm1' x1 x2 v1 v2 h :
    eq_alloc r1 vm1 vm2 ->
    @check_var x1 x2 r1 h = ok r1' ->
    Vmap.set_var vm1 x1 v1 = ok vm1' ->
    value_uincl v1 v2 ->
    exists2 vm2',
      Vmap.set_var vm2 x2 v2 = ok vm2' & eq_alloc r1' vm1' vm2'.
  Proof.
    rewrite /check_var => + [<-] Hsv Hvu.
    have [?? Hea] := vmap_set_var_widen vm2 Hvu h Hsv.
    eexists; first by eassumption.
    exact: (eq_alloc_set h Hea Hvu).
  Qed.

  Lemma check_varcP r1 r1' vm1 vm2 vm1' x1 x2 v1 v2 :
    eq_alloc r1 vm1 vm2 ->
    check_varc x1 x2 r1 = ok r1' ->
    Vmap.set_var vm1 x1 v1 = ok vm1' ->
    value_uincl v1 v2 ->
    exists2 vm2',
      Vmap.set_var vm2 x2 v2 = ok vm2' & eq_alloc r1' vm1' vm2'.
  Proof.
    by rewrite /check_varc; case: Sumbool.sumbool_of_bool => // h; exact: check_varP.
  Qed.

  Lemma eq_alloc_rm r x s vm vm' z :
    value_uincl (undef_addr (vtype x)) z ->
    eq_alloc r (evm s) vm ->
    Vmap.set_var vm x z = ok vm' ->
    eq_alloc (M.remove r x) (evm s) vm'.
  Proof.
    move=> Hz [Hmap0 Hinit Halloc];split.
    + move=> y;case:(x =P y) => [<-|/eqP ne].
      + rewrite Vmap.get_var0.
        exact: compat_uincl_undef (typerel_undef_compat vm_subcomp (Vmap.get_varP _ _)).
      by rewrite (Vmap.set_varP_neq H ne).
    + by move=> y /=;apply: Hinit.
    move=> x0 id; rewrite M.removeP.
    case: M.get (Halloc x0) => [id' | ] //.
    move=> /(_ _ (refl_equal _));case:ifPn => //= Hne He [?];subst id'.
    rewrite (Vmap.set_varP_neq H Hne) //;by apply: contra Hne => /eqP ->.
  Qed.

  Lemma check_lvalP gd r1 r1' x1 x2 e2 s1 s1' vm1 v1 v2 :
    check_lval e2 x1 x2 r1 = ok r1' ->
    eq_alloc r1 s1.(evm) vm1 ->
    value_uincl v1 v2 ->
    oapp (fun te2 =>
        sem_pexpr gd (with_vm s1 vm1) te2.2 >>= truncate_val te2.1 = ok v2) true e2 ->
    write_lval gd x1 v1 s1 = ok s1' ->
    exists2 vm1',
      write_lval gd x2 v2 (with_vm s1 vm1) = ok (with_vm s1' vm1') &
      eq_alloc r1' s1'.(evm) vm1'.
  Proof.
    case: x1 x2 => /= [ii1 t1 | x1 | sz1 x1 p1 | aa1 sz1 x1 p1 | aa1 sz1 len1 x1 p1]
                      [ii2 t2 | x2 | sz2 x2 p2 | aa2 sz2 x2 p2 | aa2 sz2 len2 x2 p2] //=.
    + case:ifP => //= hs [] <- ? Hv _; case: ifP => // H [<-].
      have := subtype_compat hs; rewrite compat_typeC => /compat_type_trans
        /(_ (compat_type_trans H (subtype_compat (value_uincl_subtype Hv)))) ->.
      by eexists.
    + case:ifP => //= hs [] <- Heqa Hu Happ; case: ifP => // H [<-].
      pose x1 := Var t1 (vname x2); have Ht : t1 = vtype x1 by done.
      rewrite Ht{Ht} in H hs; have /(Vmap.set_var_ok vm1)[? Hsv] := compat_typerel_undef H.
      rewrite /write_var /=; have [vm1' /[dup]Hsv'-> /=] := vmap_set_var_widen vm1 Hu hs Hsv.
      rewrite with_vm_idem; eexists=> //.
      have := typerel_undef_compat vm_subcomp (Vmap.get_varP vm1' x2).
      rewrite (Vmap.set_varP_eq Hsv').
      by case: Result.rdfltP => [?/truncate_defined_val_subtype/subtype_compat+|?]
        _ => h; exact: (eq_alloc_rm (compat_uincl_undef h) Heqa Hsv').
    + rewrite /write_var=> Hc Hvm1 Hv Happ; apply rbindP => vm1' Hset [<-] /=.
      move: Hc;case: is_Pvar (@is_PvarP e2).
      + move=> [ty x] /(_ _ _ (refl_equal _)) ?;subst e2.
        case: Sumbool.sumbool_of_bool => // ht; case: ifPn;
          last by move=> ? hc; have [vm2' -> /= ?]:= check_varP Hvm1 hc Hset Hv; eexists.
        move=> /andP[]/andP[]/eqP ? /eqP heqt /eqP Hx [<-]; subst.
        have [? /[dup]Hset'-> /=] := vmap_set_var_widen vm1 Hv ht Hset.
        rewrite with_vm_idem; eexists=> //; case: Option.oappP Happ => // _ [<-].
        t_xrbindP=> ? /= [<-]; rewrite -Hx{Hx} heqt.
        move: (truncate_val_u (Vmap.get_varP vm1 x2)) => -> [?]; subst.
        exact: (eq_alloc_add ht Hvm1 Hv Hset Hset').
      by move=> ? hc;have [vm2' -> /= ?]:= check_varcP Hvm1 hc Hset Hv;eexists.
    + case: eqP => // -> /=.
      t_xrbindP => r2 /check_vP h /(check_eP gd) H /h{h} Hvm1 Hv Happ wx vx.
      move: vx Hvm1 => /to_wordI[? [? -> /word_uincl_truncate h]]
        [/H{H} Hvm2 /value_uinclE[? [? -> /h{h}/=->]]] >.
      case: s1 Happ Hvm2 => > Happ [Hr1' H/H{H} [ve' -> ]].
      move=> /[swap] /to_wordI[? [? -> /word_uincl_truncate h]]
        /value_uinclE[? [? -> /h{h}/=->]] ? h.
      move: h Hv => /to_wordI[? [? -> /word_uincl_truncate h]]
        /value_uinclE[? [? -> /h{h}/=->]] ? /= -> <-.
      by eexists.
    + case: andP => // -[/eqP -> /eqP ->] /=.
      t_xrbindP => > /check_vP h /(check_eP gd) H Hcva /h{h} [/H{H} [Hr2 Hr1]] H Hv Happ.
      apply: on_arr_varP => n t Htx h.
      move: h H => -> /value_uinclE[? -> Ht]; t_xrbindP => >.
      case: s1 Hr2 Happ Hr1 => > Hr2 Happ h/h{h}[? ->]
        /[swap]/to_intI->/value_uinclE-> ? /= H.
      move: H Hv => /to_wordI[? [? -> /word_uincl_truncate h]]
        /value_uinclE[? [? -> /h{h} /= ->]] ?
        /(WArray.uincl_set Ht) [? [/= -> Ht2']].
      rewrite /write_var; t_xrbindP=> ? /(check_varcP Hr2 Hcva)-
        /(_ (@Varr n _))/(_ (conj erefl Ht2'))[? /= -> ? <-].
      by eexists.
    case: andP => // -[] /andP[] /eqP -> /eqP -> /eqP -> /=.
    t_xrbindP=> > /check_vP h /(check_eP gd) H Hcva /h{h}[/H{H}[Hr2 Hr1]] H Hv Happ.
    apply: on_arr_varP => n t Htx h.
    move: h H => -> /value_uinclE[? -> Ht]; t_xrbindP => >.
    case: s1 Hr2 Happ Hr1 => > Hr2 Happ h/h{h}[? ->]
      /[swap]/to_intI->/value_uinclE-> ? /= H.
    move: H Hv => /to_arrI-> /value_uinclE[? -> /=].
    rewrite sumbool_of_boolET (Eqdep_dec.UIP_dec Pos.eq_dec (eqP _)) /=.
    move=> /(WArray.uincl_set_sub Ht) h ? /h{h}[? -> Ht2'].
    rewrite /write_var; t_xrbindP=> ? /(check_varcP Hr2 Hcva)-
      /(_ (@Varr n _))/(_ (conj erefl Ht2'))[? /= -> ? <-].
    by eexists.
  Qed.

  End WITH_POINTER_DATA.
End CBAreg.

Module CBAregU := CheckBU CBAreg.
Module CheckAllocRegU :=  MakeCheckAlloc CBAregU.

Module CBAregS := CheckBS CBAreg.
Module CheckAllocRegS := MakeCheckAlloc CBAregS.
