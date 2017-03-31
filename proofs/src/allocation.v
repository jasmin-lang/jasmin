(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* ** Imports and settings *)
Require Import JMeq ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr
               memory dmasm_sem compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

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
  
  Parameter check_lval : lval -> lval -> M.t -> cexec M.t.

  Parameter eq_alloc : M.t -> vmap -> vmap -> Prop.

  Parameter eq_alloc_empty : eq_alloc M.empty vmap0 vmap0.

  Parameter eq_alloc_incl : forall r1 r2 vm vm',
    M.incl r2 r1 -> 
    eq_alloc r1 vm vm' -> 
    eq_alloc r2 vm vm'.

  Parameter check_eP : forall e1 e2 r re vm1 vm2, 
    check_e e1 e2 r = ok re ->
    eq_alloc r vm1 vm2 ->
    eq_alloc re vm1 vm2 /\
    forall m v1,  sem_pexpr (Estate m vm1) e1 = ok v1 ->
    exists v2, sem_pexpr (Estate m vm2) e2 = ok v2 /\ value_uincl v1 v2.

  Parameter check_lvalP : forall r1 r1' x1 x2 s1 s1' vm1 v1 v2,
    check_lval x1 x2 r1 = ok r1' ->
    eq_alloc r1 s1.(evm) vm1 ->
    value_uincl v1 v2 ->
    write_lval x1 v1 s1 = ok s1' ->
    exists vm1', 
      write_lval x2 v2 (Estate s1.(emem) vm1) = ok (Estate s1'.(emem) vm1') /\
      eq_alloc r1' s1'.(evm) vm1'.

End CheckB.

Definition salloc : string := "allocation".

Module MakeCheckAlloc (C:CheckB).

Import C.

Section LOOP.

  Variable ii:instr_info.
  Variable check_c : M.t -> ciexec M.t.
 
  Fixpoint loop (n:nat) (m:M.t) := 
    match n with
    | O => cierror ii (Cerr_Loop "allocation")
    | S n =>
      Let m' := check_c m in
      if M.incl m m' then ok m 
      else loop n (M.merge m m')
    end.

End LOOP.

Definition check_e_error := Cerr_fold2 "allocation:check_e".

Definition cmd2_error := Cerr_fold2 "allocation:check_cmd".

Definition check_es es1 es2 r := fold2 check_e_error check_e es1 es2 r.

Definition check_lvals := 
  fold2 (Cerr_fold2 "allocation:check_lvals") check_lval.

Definition check_var x1 x2 r := check_lval (Lvar x1) (Lvar x2) r.

Definition check_vars xs1 xs2 r := check_lvals (map Lvar xs1) (map Lvar xs2) r.

Fixpoint check_i iinfo i1 i2 r := 
  match i1, i2 with
  | Cassgn x1 _ e1, Cassgn x2 _ e2 => 
    add_iinfo iinfo (check_e e1 e2 r >>= check_lval x1 x2)
  | Copn xs1 o1 es1, Copn xs2 o2 es2 =>
    if o1 == o2 then
      add_iinfo iinfo (check_es es1 es2 r >>= check_lvals xs1 xs2)
    else cierror iinfo (Cerr_neqop o1 o2 salloc)
  | Ccall _ x1 f1 arg1, Ccall _ x2 f2 arg2 => 
    if f1 == f2 then 
      add_iinfo iinfo (check_es arg1 arg2 r >>= check_lvals x1 x2)
    else cierror iinfo (Cerr_neqfun f1 f2 salloc) 
  | Cif e1 c11 c12, Cif e2 c21 c22 =>
    Let re := add_iinfo iinfo (check_e e1 e2 r) in
    Let r1 := fold2 (iinfo,cmd2_error) check_I c11 c21 re in
    Let r2 := fold2 (iinfo,cmd2_error) check_I c12 c22 re in 
    ok (M.merge r1 r2)
  | Cfor x1 (d1,lo1,hi1) c1, Cfor x2 (d2,lo2,hi2) c2 =>
    if d1 == d2 then 
      Let rhi := add_iinfo iinfo (check_e lo1 lo2 r >>=check_e hi1 hi2) in
      let check_c r := 
          add_iinfo iinfo (check_var x1 x2 r) >>= 
          fold2 (iinfo,cmd2_error) check_I c1 c2 in
      loop iinfo check_c Loop.nb rhi 
    else cierror iinfo (Cerr_neqdir salloc)
  | Cwhile e1 c1, Cwhile e2 c2 =>
    let check_c r :=
      add_iinfo iinfo (check_e e1 e2 r) >>= 
      fold2 (iinfo,cmd2_error) check_I c1 c2 in
     loop iinfo check_c Loop.nb r
  | _, _ => cierror iinfo (Cerr_neqinstr i1 i2 salloc)
  end

with check_I i1 i2 r := 
  match i1, i2 with
  | MkI ii i1, MkI _ i2 => check_i ii i1 i2 r
  end.

Definition check_cmd iinfo := fold2 (iinfo,cmd2_error) check_I.

Definition check_fundef (f1 f2: funname * fundef) (_:unit) := 
  let (f1,fd1) := f1 in
  let (f2,fd2) := f2 in
  if f1 == f2 then
    add_finfo f1 f2 (
    Let r := add_iinfo fd1.(f_iinfo) (check_vars fd1.(f_params) fd2.(f_params) M.empty) in
    Let r := check_cmd fd1.(f_iinfo) fd1.(f_body) fd2.(f_body) r in
    let es1 := map Pvar fd1.(f_res) in
    let es2 := map Pvar fd2.(f_res) in
    Let _r := add_iinfo fd1.(f_iinfo) (check_es es1 es2 r) in
    ok tt)    
  else cferror (Ferr_neqfun f1 f2).

Definition check_prog prog1 prog2 :=
  fold2 Ferr_neqprog check_fundef prog1 prog2 tt.
  
Lemma check_lvalsP xs1 xs2 vs1 vs2 r1 r2 s1 s2 vm1 :
  check_lvals xs1 xs2 r1 = ok r2 ->
  eq_alloc r1 s1.(evm) vm1 ->
  List.Forall2 value_uincl vs1 vs2 ->
  write_lvals s1 xs1 vs1 = ok s2 ->
  exists vm2, 
    write_lvals (Estate s1.(emem) vm1) xs2 vs2 = ok (Estate s2.(emem) vm2) /\
    eq_alloc r2 s2.(evm) vm2.
Proof. 
  elim: xs1 xs2 vs1 vs2 r1 r2 s1 s2 vm1 => [ | x1 xs1 Hrec] [ | x2 xs2] //=
    vs1 vs2 r1 r2 s1 s2 vm1.
  + by move=> [<-] Hvm1 [] //= [<-];exists vm1.
  apply: rbindP => r3 Hx Hcxs Hvm1 [] //= {vs1 vs2}.
  move=> v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s3 Hw Hws.
  have [vm3 [->/= Hvm3]] := check_lvalP Hx Hvm1 Hv Hw.
  apply: Hrec Hcxs Hvm3 Hvs Hws. 
Qed.

Section PROOF.

  Variable p1 p2:prog.

  Hypothesis Hcheck: check_prog p1 p2 = ok tt.

  Lemma all_checked : forall fn fd1,
    get_fundef p1 fn = Some fd1 ->
    exists fd2, get_fundef p2 fn = Some fd2 /\ check_fundef (fn,fd1) (fn,fd2) tt = ok tt.
  Proof.    
    move: p1 p2 Hcheck;rewrite /check_prog;clear p1 p2 Hcheck.
    elim => [ | [fn1' fd1'] p1 Hrec] [ | [fn2 fd2] p2] //. 
    apply: rbindP => -[] Hc /Hrec {Hrec} Hrec.
    have ? : fn1' = fn2 by move: Hc;rewrite /check_fundef;case:ifP => /eqP.
    subst=> fn fd1;rewrite !get_fundef_cons;case:ifPn => [/eqP -> [] <-| _ /Hrec //].
    by exists fd2.
  Qed.

  Let Pi_r s1 (i1:instr_r) s2:= 
    forall ii r1 i2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_i ii i1 i2 r1 = ok r2 ->
    exists vm2, eq_alloc r2 (evm s2) vm2 /\ 
      sem_i p2 (Estate (emem s1) vm1) i2 (Estate (emem s2) vm2).

  Let Pi s1 (i1:instr) s2:= 
    forall r1 i2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_I i1 i2 r1 = ok r2 ->
    exists vm2, eq_alloc r2 (evm s2) vm2 /\ 
      sem_I p2 (Estate (emem s1) vm1) i2 (Estate (emem s2) vm2).

  Let Pc s1 (c1:cmd) s2:= 
    forall ii r1 c2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_cmd ii c1 c2 r1 = ok r2 ->
    exists vm2, eq_alloc r2 (evm s2) vm2 /\ 
      sem p2 (Estate (emem s1) vm1) c2 (Estate (emem s2) vm2).

  Let Pfor (i1:var_i) vs s1 c1 s2 :=
    forall i2 ii r1 r1' c2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_var i1 i2 r1 = ok r1' ->  
    check_cmd ii c1 c2 r1' = ok r2 -> M.incl r1 r2 ->
    exists vm2, eq_alloc r1 (evm s2) vm2 /\ 
      sem_for p2 i2 vs (Estate (emem s1) vm1) c2 (Estate (emem s2) vm2).

  Let Pfun (mem:Memory.mem) fn vargs1 (mem':Memory.mem) vres :=
    forall vargs2, List.Forall2 value_uincl vargs1 vargs2 ->
       sem_call p2 mem fn vargs2 mem' vres.

  Local Lemma Hskip s: Pc s [::] s.
  Proof. 
    move=> ii r1 [ | ??] //= r2 vm1 ? [] <-;exists vm1;split=>//;constructor.
  Qed.

  Local Lemma Hcons s1 s2 s3 i c :
    sem_I p1 s1 i s2 ->
    Pi s1 i s2 -> sem p1 s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
  Proof.
    move=> _ Hi _ Hc ? r1 [ | i2 c2] //= r2 vm1 /Hi Hvm1. 
    apply: rbindP => r3 /Hvm1 [vm2 []] /Hc Hvm2 ? /Hvm2.
    by move=> [vm3 [??]];exists vm3;split=>//;econstructor;eauto.
  Qed.

  Local Lemma HmkI ii i s1 s2 :
    sem_i p1 s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
  Proof. 
    move=> _ Hi  r1 [? i2] r2 vm1 /Hi Hvm /= /Hvm [vm2 [??]].
    by exists vm2;split=>//;constructor.
  Qed.

  Local Lemma Hassgn s1 s2 x tag e :
    Let v := sem_pexpr s1 e in write_lval x v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn x tag e) s2.
  Proof.
    case: s1 => sm1 svm1. 
    apply: rbindP => v He Hw ii r1 [] //= x2 tag2 e2 r2 vm1 Hvm1.
    apply: add_iinfoP.
    apply: rbindP => r1' /check_eP -/(_ _ _ Hvm1) [Hr1'] /(_ _ _ He) [v2 [He2 Hu2]] Hcx.
    have /(_ _ Hr1') [vm2 [Hwv Hvm2]]:= check_lvalP Hcx _ Hu2 Hw.
    by exists vm2;split=>//;constructor;rewrite He2.
  Qed.

  Lemma check_esP e1 e2 r re s vm: 
    check_es e1 e2 r = ok re ->
    eq_alloc r s.(evm) vm ->
    eq_alloc re s.(evm) vm /\
    forall v1,  sem_pexprs s e1 = ok v1 ->
    exists v2, sem_pexprs (Estate s.(emem) vm) e2 = ok v2 /\ 
               List.Forall2 value_uincl v1 v2.
  Proof.
    case: s => sm svm. 
    rewrite /check_es; elim: e1 e2 r => [ | e1 es1 Hrec] [ | e2 es2] r //=.
    + by move=> [] <- ?;split=>// -[] //= ?;exists [::].
    move=> H Hea;apply: rbindP H => r' /check_eP /(_ Hea) [] Hea' He.
    move=> /Hrec /(_ Hea') [] Hre Hes;split=> // v1.
    rewrite /sem_pexprs;apply: rbindP => ve1 /He [ve2 /=[-> Hve]].
    apply:rbindP => ev2 /Hes [ves2 []];rewrite /sem_pexprs => -> Hves [] <- /=.
    by exists (ve2 :: ves2);split => //;constructor.
  Qed.

  Local Lemma Hopn s1 s2 o xs es : 
    Let x := Let x := sem_pexprs s1 es in sem_sopn o x
    in write_lvals s1 xs x = Ok error s2 -> Pi_r s1 (Copn xs o es) s2.
  Proof.
    apply: rbindP => v.
    apply: rbindP => ves He Ho Hw ii r1 [] //= xs2 o2 es2 r2 vm1 Hvm1.
    case:ifPn => //= /eqP <-.
    apply: add_iinfoP.
    apply: rbindP => r1' /check_esP -/(_ _ _ Hvm1) [Hr1'] /(_ _ He) [v2 [He2 Hu2]].
    have [v' [Ho' Hv] Hcxs]:= vuincl_sem_opn Hu2 Ho.
    have /(_ _ Hr1') [vm2 [Hwv Hvm2]]:= check_lvalsP Hcxs _ Hv Hw.
    by exists vm2;split=>//;constructor;rewrite He2 /= Ho'.
  Qed.

  Local Lemma Hif_true s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem p1 s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    case: s1 => sm1 svm1.
    apply: rbindP => ve Hve Hto _ Hc1 ii r1 [] //= e' c1' c2' r2 vm1 Hvm1.
    apply: rbindP => r1';apply: add_iinfoP => /check_eP -/(_ _ _ Hvm1) [] Hr1'.
    move=> /(_ _ _ Hve) [ve' [Hve' /value_uincl_bool -/(_ _ Hto)]] [??];subst ve ve'.
    apply: rbindP => r3 Hr3;apply: rbindP => r4 Hr4 [] <-.
    have [vm2 [Hvm2 Hsem]]:= Hc1 ii _ _ _ _ Hr1' Hr3;exists vm2;split.
    + by eapply eq_alloc_incl;eauto;apply M.merge_incl_l.
    by apply Eif_true => //;rewrite Hve'.
  Qed.

  Local Lemma Hif_false s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error false ->
    sem p1 s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    case: s1 => sm1 svm1.
    apply: rbindP => ve Hve Hto _ Hc1 ii r1 [] //= e' c1' c2' r2 vm1 Hvm1.
    apply: rbindP => r1';apply: add_iinfoP => /check_eP -/(_ _ _ Hvm1) [] Hr1'.
    move=> /(_ _ _ Hve) [ve' [Hve' /value_uincl_bool -/(_ _ Hto)]] [??];subst ve ve'.
    apply: rbindP => r3 Hr3;apply: rbindP => r4 Hr4 [] <-.
    have [vm2 [Hvm2 Hsem]]:= Hc1 ii _ _ _ _ Hr1' Hr4;exists vm2;split.
    + by eapply eq_alloc_incl;eauto;apply M.merge_incl_r.
    by apply Eif_false => //;rewrite Hve'.
  Qed.

  Local Lemma loopP ii check_c n r1 r2:
    loop ii check_c n r1 = ok r2 -> 
      exists r2', 
      [/\ check_c r2 = ok r2', M.incl r2 r1 & M.incl r2 r2'].
  Proof.
    elim: n r1 r2 => //= n Hrec r1 r2.
    apply: rbindP => r2' Hc;case:ifPn => [? [] <- | _ /Hrec].
    + exists r2';split=>//;apply M.incl_refl.
    move=> [r2'' [H1 H2 H3]];exists r2'';split=>//.
    apply: (M.incl_trans H2); apply M.merge_incl_l.
  Qed.
    
  Local Lemma Hwhile_true s1 s2 s3 e c:
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem p1 s1 c s2 -> Pc s1 c s2 ->
    sem_i p1 s2 (Cwhile e c) s3 -> Pi_r s2 (Cwhile e c) s3 -> 
    Pi_r s1 (Cwhile e c) s3.
  Proof.
    case: s1 => sm1 svm1.
    apply: rbindP => ve Hve Hto _ Hc _ Hrec ii r1 [] //= e2 c2 r2 vm1 Hvm1.
    move=> Hloop;have [r2' []]:= loopP Hloop;apply: rbindP => r3;apply: add_iinfoP.
    move=> He Hc0; move: (Hc0) => /Hc{Hc}Hc Hincl.
    have := eq_alloc_incl Hincl Hvm1.
    move=> /(check_eP He) [] /Hc [vm2 [Hvm2 Hc2]] /(_ _ _ Hve) [ve' ] [Hve' Uve] Hr2.
    have : check_i ii (Cwhile e c) (Cwhile e2 c2) r2 = ok r2.
    + by rewrite /= Loop.nbP /= He /= Hc0 /= Hr2.
    have /Hrec H := eq_alloc_incl Hr2 Hvm2.
    move=> /H [vm3] [] ? Hw;exists vm3;split => //.
    apply: Ewhile_true;eauto;rewrite Hve' /=.
    by have [_ ->]:= value_uincl_bool Uve Hto.
  Qed.

  Local Lemma Hwhile_false s e c:
    Let x := sem_pexpr s e in to_bool x = Ok error false ->
    Pi_r s (Cwhile e c) s.
  Proof.
    case s=> m vm.
    apply: rbindP => ve Hve Hto ii r1 [] //= e2 c2 r2 vm1 Hvm1.
    move=> Hloop;have [r2' []]:= loopP Hloop;apply: rbindP => r3;apply: add_iinfoP.
    move=> He _ Hincl;move /eq_alloc_incl : (Hincl) => /(_ _ _ Hvm1) -/(check_eP He) [] Hr3.
    move=> /(_ _ _ Hve) [ve'] [] Hve' Uve;exists vm1;split.
    + by apply: eq_alloc_incl Hvm1.
    apply: Ewhile_false;eauto;rewrite Hve' /=.
    by have [_ ->]:= value_uincl_bool Uve Hto.
  Qed.
 
  Local Lemma Hfor s1 s2 (i:var_i) d lo hi c vlo vhi :
    Let x := sem_pexpr s1 lo in to_int x = Ok error vlo ->
    Let x := sem_pexpr s1 hi in to_int x = Ok error vhi ->
    sem_for p1 i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.
  Proof.
    case: s1 => sm1 svm1.
    move=> Hlo Hhi Hc Hfor ii r1 [] //= i2 [[d2 lo2] hi2] c2 r2 vm1 Hvm1.
    case: eqP => //= ?;subst d2.
    apply: rbindP => r1'; apply: add_iinfoP.
    apply: rbindP => r1'' /check_eP -/(_ _ _ Hvm1) [Hr1'' Heqlo].
    apply: rbindP Hlo => vlo' /Heqlo{Heqlo} [vlo''] [Hlo2] Hvlo'.
    move=> /(value_uincl_int Hvlo') [] ??;subst vlo' vlo''.
    move=>  /check_eP -/(_ _ _ Hr1'') [Hr1' Heqhi].
    apply: rbindP Hhi => vhi' /Heqhi{Heqhi} [vhi''] [Hhi2] Hvhi'.
    move=> /(value_uincl_int Hvhi') [] ??;subst vhi' vhi''.
    move=> /loopP [r2'] [];apply: rbindP => r2'';apply:add_iinfoP.
    move=> Hcv Hcc Hr2r1 Hr2r2.
    have := Hfor _ _ _ _ _ _ _ (eq_alloc_incl Hr2r1 Hr1') Hcv Hcc Hr2r2.
    move=> [vm2 [Hvm2 Hsem2]];exists vm2;split=> //.
    econstructor;rewrite ?Hlo2 ?Hhi2 /=;eauto.
  Qed.
    
  Local Lemma Hfor_nil s i c: Pfor i [::] s c s.
  Proof. 
    by move=> i2 ii r1 r1' c2 r2 vm1 Ha ???;exists vm1;split=> //;constructor.
  Qed.

  Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w:Z) (ws:seq Z) c :
    write_var i w s1 = Ok error s1' ->
    sem p1 s1' c s2 ->
    Pc s1' c s2 ->
    sem_for p1 i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
  Proof.
    move=> Hwi _ Hc _ Hfor i2 ii r1 r1' c2 r2 vm2 Heq Hr1' Hcc Hincl. 
    have [vm3 [Hwi2 Hvm3]] := check_lvalP Hr1' Heq (value_uincl_refl _) Hwi.
    have [vm4 [Hvm4 Hsc]] := Hc _ _ _ _ _ Hvm3 Hcc.
    have [vm5 [Hvm5 Hsf]] := Hfor _ _ _ _ _ _ _ (eq_alloc_incl Hincl Hvm4) Hr1' Hcc Hincl.
    by exists vm5;split=>//;econstructor;eauto.
  Qed.

  Local Lemma Hcall s1 m2 s2 ii xs fn args vargs vs:
    sem_pexprs s1 args = Ok error vargs ->
    sem_call p1 (emem s1) fn vargs m2 vs ->
    Pfun (emem s1) fn vargs m2 vs ->
    write_lvals {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
    Pi_r s1 (Ccall ii xs fn args) s2.
  Proof.
    move=> Hes Hsc Hfun Hw ii' r1 [] //= ii2 xs2 fn2 args2 r2 vm1 Hr1.
    case: eqP => //= ?;subst fn2;apply: add_iinfoP.
    apply: rbindP => r1' Hca Hcxs.
    have [Hr1' /(_ _ Hes) [vargs2 [Hargs2 Hvargs]]] := check_esP Hca Hr1.
    have Hs2 := Hfun _ Hvargs.
    have Hvs : List.Forall2 value_uincl vs vs.
    + by apply: List_Forall2_refl value_uincl_refl.
    have /(_ _ Hr1') [vm2 [Hw2 Hr2]]:= check_lvalsP Hcxs _ Hvs Hw.
    exists vm2;split=>//;econstructor;eauto.
  Qed.

  Section REFL.

    Hypothesis eq_prog : p1 = p2.

    Local Lemma Hproc_eq m1 m2 fn f vargs s1 vm2 vres: 
      get_fundef p1 fn = Some f ->
      write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
      sem p1 s1 (f_body f) {| emem := m2; evm := vm2 |} -> 
      Pc s1 (f_body f) {| emem := m2; evm := vm2 |} ->
      mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
      List.Forall is_full_array vres -> 
      Pfun m1 fn vargs m2 vres.
    Proof.
      move=> Hget Hw Hsem _ Hres Hfull vargs2 Hvargs2;rewrite -eq_prog.
      have: sem_call p1 m1 fn vargs m2 vres by econstructor;eauto.
      by apply: sem_call_uincl.
    Qed.

    Lemma alloc_funP_eq_aux fn f f' m1 vargs vres s1 s2: 
      check_fundef (fn, f) (fn, f') tt = ok tt ->
      write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
      sem p1 s1 (f_body f) s2 ->
      mapM (fun x : var_i => get_var (evm s2) x) (f_res f) = ok vres ->
      List.Forall is_full_array vres ->
      exists s1' vm2,
       [ /\ write_vars (f_params f') vargs {| emem := m1; evm := vmap0 |} = ok s1', 
        sem p2 s1' (f_body f') (Estate (emem s2) vm2) &
        mapM (fun x : var_i => get_var vm2 x) (f_res f') = ok vres].
    Proof.
      rewrite /check_fundef eq_refl;apply: add_finfoP.
      apply:rbindP => r1;apply:add_iinfoP => Hcparams.
      apply:rbindP => r2 Hcc;apply: rbindP => r3;apply: add_iinfoP => Hcres _.
      rewrite write_vars_lvals=> /(check_lvalsP Hcparams). 
      move=> /(_ vargs _ eq_alloc_empty) [ | vm3 /= [Hw2 Hvm3]].
      + by apply: List_Forall2_refl.
      move=> /(sem_Ind Hskip Hcons HmkI Hassgn Hopn Hif_true Hif_false 
                Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc_eq) Hc.
      have [vm4 /= [Hvm4 Hsc2] Hres Hfull]:= Hc _ _ _ _ _ Hvm3 Hcc.
      do 2 eexists;split;eauto;first by rewrite write_vars_lvals.
      have := check_esP Hcres Hvm4.
      move=> [Hr3];rewrite sem_pexprs_get_var => /(_ _ Hres) [vres2 /= []].
      by rewrite sem_pexprs_get_var => ? /(is_full_array_uincls Hfull) ->.
    Qed.

  End REFL.
   
  Local Lemma Hproc m1 m2 fn f vargs s1 vm2 vres: 
    get_fundef p1 fn = Some f ->
    write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
    sem p1 s1 (f_body f) {| emem := m2; evm := vm2 |} -> 
    Pc s1 (f_body f) {| emem := m2; evm := vm2 |} ->
    mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
    List.Forall is_full_array vres -> 
    Pfun m1 fn vargs m2 vres.
  Proof.
    move=> Hget Hw _ Hc Hres Hfull.
    have [fd2 [Hget2 /=]]:= all_checked Hget.
    rewrite eq_refl; apply:add_finfoP;apply:rbindP => r1;apply:add_iinfoP => Hcparams.
    apply:rbindP => r2 Hcc;apply: rbindP => r3;apply: add_iinfoP => Hcres _.
    move=> vargs2 Hvargs2.
    move: Hw;rewrite write_vars_lvals=> /(check_lvalsP Hcparams). 
    move=> /(_ _ _ eq_alloc_empty Hvargs2) [vm3 /= [Hw2 Hvm3]].
    have [vm4 /= [Hvm4 Hsc2]]:= Hc _ _ _ _ _ Hvm3 Hcc.
    econstructor;eauto;first by rewrite write_vars_lvals.
    have /(_ {| emem := emem s1; evm := vm2 |} vm4 Hvm4) := check_esP Hcres.
    move=> [Hr3];rewrite sem_pexprs_get_var => /(_ _ Hres) [vres2 /= []].
    by rewrite sem_pexprs_get_var => ? /(is_full_array_uincls Hfull) ->.
  Qed.

  Lemma alloc_callP f mem mem' va vr: 
    sem_call p1 mem f va mem' vr -> 
    sem_call p2 mem f va mem' vr.
  Proof.
    move=>
      /(@sem_call_Ind p1 Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
            Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
    by move=> H;apply H;apply List_Forall2_refl;apply value_uincl_refl.
  Qed.

End PROOF.

Lemma alloc_funP_eq p fn f f' m1 vargs vres s1 s2: 
  check_fundef (fn, f) (fn, f') tt = ok tt ->
  write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
  sem p s1 (f_body f) s2 ->
  mapM (fun x : var_i => get_var (evm s2) x) (f_res f) = ok vres ->
  List.Forall is_full_array vres ->
  exists s1' vm2,
   [ /\ write_vars (f_params f') vargs {| emem := m1; evm := vmap0 |} = ok s1', 
    sem p s1' (f_body f') (Estate (emem s2) vm2) &
    mapM (fun x : var_i => get_var vm2 x) (f_res f') = ok vres].
Proof. by apply alloc_funP_eq_aux. Qed.

End MakeCheckAlloc.

Module MakeMalloc(M:gen_map.MAP).

  Definition valid (mvar: M.t Ident.ident) (mid: Ms.t M.K.t) :=
    forall x id, M.get mvar x = Some id <-> Ms.get mid id = Some x.
 
  Lemma valid_uniqx mvar mid : valid mvar mid ->
     forall x x' id , M.get mvar x = Some id -> M.get mvar x' = Some id ->
                      x = x'.
  Proof. by move=> H x x' id /H Hx /H;rewrite Hx=> -[]. Qed.

  Lemma valid_uniqid mvar mid : valid mvar mid ->
     forall id id' x, Ms.get mid id = Some x -> Ms.get mid id' = Some x ->
                      id = id'.
  Proof. by move=> H id id' x /H Hx /H;rewrite Hx=> -[]. Qed.

  Record t_ := mkT { mvar : M.t Ident.ident; mid : Ms.t M.K.t; mvalid: valid mvar mid }.
  Definition t := t_.

  Definition get (m:t) (x:M.K.t) := M.get (mvar m) x.

  Lemma mvalid_uniqx m x x' id: get m x = Some id -> get m x' = Some id -> x = x'.
  Proof. rewrite /get;apply valid_uniqx with (mid m);apply mvalid. Qed.

  Definition rm_id (m:t) id := 
    match Ms.get (mid m) id with
    | Some x => M.remove (mvar m) x
    | None   => mvar m
    end.

  Definition rm_x (m:t) x := 
    match M.get (mvar m) x with
    | Some id => Ms.remove (mid m) id
    | None    => mid m
    end.

  Lemma rm_idP m id x : M.get (rm_id m id) x <> Some id.
  Proof.
    rewrite /rm_id. case Heq: ((mid m).[id])%ms => [x'|];last first.
    + by move=> /mvalid;rewrite Heq.   
    by rewrite M.removeP; case: (x' =P x) => // Hne /mvalid;rewrite Heq=> -[] ?;elim Hne.
  Qed. 

  Lemma rm_xP m x id : Ms.get (rm_x m x) id <> Some x.
  Proof.
    rewrite /rm_x. case Heq: (M.get (mvar m) x) => [id'|];last first.
    + by move=> /mvalid;rewrite Heq.   
    by rewrite Ms.removeP; case: (id'=Pid) => // Hne /mvalid;rewrite Heq=> -[] ?;elim Hne.
  Qed. 

  Lemma valid_set m x id : valid (M.set (rm_id m id) x id) (Ms.set (rm_x m x) id x).
  Proof.
    move=> y idy; case (x =P y) => [->|/eqP Hne]. 
    + rewrite M.setP_eq.
      case (id =P idy) => [<-| Hnei];first by rewrite Ms.setP_eq.
      split => [[]/Hnei | ] //. 
      by rewrite Ms.setP_neq => [/rm_xP//| ]; apply /eqP.
    rewrite M.setP_neq //.
    case (id =P idy) => [<-| /eqP Hnei].
    + by rewrite Ms.setP_eq;split=> [/rm_idP//|[] H];move: Hne;rewrite H eq_refl.
    rewrite Ms.setP_neq // /rm_id /rm_x.
    case Heq: ((mid m).[id])%ms => [z|];case Heq':(M.get (mvar m) x) => [i|];
    rewrite ?M.removeP ?Ms.removeP;last by apply mvalid.
    + case:(_ =P _) => H;case:(_ =P _)=> H'; subst => //;last by apply mvalid.
      + split=>// /(valid_uniqid (mvalid m) Heq) H. 
        by move: Hnei;rewrite H eq_refl.
      split=> // /(valid_uniqx (mvalid m) Heq') H'. 
      by move: Hne;rewrite H' eq_refl.
    + case:(_ =P _) => H;last by apply mvalid.
      subst;split=> // /(valid_uniqid (mvalid m) Heq) H. 
      by move: Hnei;rewrite H eq_refl.
    case:(_ =P _) => H;last by apply mvalid.
    subst;split=> // /(valid_uniqx (mvalid m) Heq') H. 
    by move: Hne;rewrite H eq_refl.
  Qed.

  Definition set m x id := mkT (valid_set m x id).

  Lemma valid_empty : valid (@M.empty _) (@Ms.empty _).
  Proof. by move=> x id;rewrite M.get0 Ms.get0. Qed.

  Definition empty := mkT valid_empty.

  Definition merge m1 m2 := 
    M.fold 
     (fun x idx m => 
        match get m2 x with    
        | Some idx' => if idx == idx' then set m x idx else m
        | None      => m
        end) (mvar m1) empty.

  Lemma get0 x : get empty x = None.
  Proof. by rewrite /get M.get0. Qed.

  Lemma setP_eq m x id : get (set m x id) x = Some id.
  Proof. by rewrite /get /set /=;rewrite M.setP_eq. Qed.

  Lemma setP_neq m x y id id' : 
    x != y -> get (set m x id) y = Some id' ->
    get m y = Some id' /\ id <> id'.
  Proof.
    move=> Hne;rewrite /get /set /= M.setP_neq // /rm_id.
    case Heq: ((mid m).[id])%ms => [x'|] //=. 
    + rewrite M.removeP;case:ifP => // /eqP Hne' H;split=>// ?;subst.
      by move/mvalid :H;rewrite Heq => -[].
    move=> H;split=>// ?;subst.
    by move/mvalid:H;rewrite Heq.
  Qed.

  Lemma mergeP m1 m2 x id : 
    get (merge m1 m2) x = Some id -> get m1 x = Some id /\ get m2 x = Some id.
  Proof.
    rewrite /merge M.foldP;set f := (f in foldl f).
    pose P := fun m => 
      get m x = Some id -> get m1 x = Some id /\ get m2 x = Some id.
    have H : forall (l:list (M.K.t * Ident.ident)) m, 
      (forall p, p \in l -> get m1 p.1 = Some p.2) ->
      P m -> P (foldl f m l).
    + elim=> [|p l Hrec] //= m Hl Hm;apply Hrec.
      + by move=> ? H;apply Hl;rewrite in_cons H orbC.
      rewrite /f /P;case Heq2: (get m2 p.1) => [id'|];last by apply Hm.
      case: (_=P_) => Heq;last by apply Hm.
      subst;case: (p.1 =P x) => [| /eqP] Heq.
      + by subst;rewrite setP_eq=> [] <-;split=>//;apply /Hl /mem_head.
      by move=> /setP_neq [] // ??;apply Hm.
    apply H;first by move=> p /M.elementsP.
    by rewrite /P get0. 
  Qed.

  Definition incl m1 m2 :=
    M.fold (fun x id b => b && (get m2 x == Some id))
              (mvar m1) true.
  
  Lemma inclP m1 m2 : 
    reflect (forall x id, get m1 x = Some id -> get m2 x = Some id) (incl m1 m2).
  Proof.
    rewrite /incl M.foldP;set f := (f in foldl f).
    set l := (M.elements _); set b := true.
    have : forall p, p \in l -> get m1 p.1 = Some p.2.
    + by move=> p /M.elementsP.
    have : uniq [seq x.1 | x <- l]. apply M.elementsU.
    have : 
      reflect (forall x id, (x,id) \notin l -> get m1 x = Some id -> get m2 x = Some id) b.
    + by constructor=> x id /M.elementsP. 
    elim:l b=> /= [|p ps Hrec] b Hb => [Hu | /andP[Hnin Hu]] Hin.
    + by apply (equivP Hb);split=> H ?? => [|_];apply H.
    apply Hrec=> //;first last.
    + by move=> ? Hp0;apply Hin;rewrite in_cons Hp0 orbC.
    rewrite /f;case: Hb=> {Hrec} /= Hb.
    + case: (_ =P _) => Heq;constructor.
      + move=> x id Hnx;case : ((x,id) =P p)=> [|/eqP/negbTE]Hp;first by subst.
        by apply Hb;rewrite in_cons Hp.
      move=> H;apply/Heq/H;last by apply/Hin/mem_head.
      by move: Hnin;apply: contra;apply: map_f.
    constructor=> H;apply Hb=> x id.
    rewrite in_cons negb_or=> /andP [] _;apply H.     
  Qed.    

  Lemma incl_refl r : incl r r.
  Proof. by apply/inclP. Qed.

  Lemma incl_trans r2 r1 r3  : incl r1 r2 -> incl r2 r3 -> incl r1 r3.
  Proof. by move=> /inclP H1 /inclP H2;apply/inclP=> x id /H1 /H2. Qed.

  Lemma merge_incl_l r1 r2 : incl (merge r1 r2) r1.
  Proof. by apply/inclP=> x id /mergeP []. Qed.

  Lemma merge_incl_r r1 r2 : incl (merge r1 r2) r2.
  Proof. by apply/inclP=> x id /mergeP []. Qed.

End MakeMalloc.

Module CBAreg.

  Module M.

  Module Mv := MakeMalloc Mvar.

  Definition mset_valid (mvar: Mvar.t Ident.ident) (mset:Sv.t) := 
    (forall x id, Mvar.get mvar x = Some id -> Sv.In x mset).
 
  Record t_ := mkT { 
    mv : Mv.t;
    mset : Sv.t;
    svalid: mset_valid (Mv.mvar mv) mset;
  }.

  Definition t := t_.

  Definition get (m:t) (x:var) := Mv.get (mv m) x.

  Lemma mset_valid_set m x id : mset_valid (Mv.mvar (Mv.set (mv m) x id)) (Sv.add x (mset m)).
  Proof.
    move=> y idy;rewrite Mvar.setP;case: eqP=> [-> ?|?];first by SvD.fsetdec.
    rewrite /Mv.rm_id;case ((Mv.mid (mv m)).[id])%ms => [x'|].
    rewrite Mvar.removeP;case: ifP => //= _ /svalid;SvD.fsetdec.
    by move=> /svalid;SvD.fsetdec.
  Qed.

  Definition set m x id := mkT (@mset_valid_set m x id).

  Lemma mset_valid_empty s : mset_valid (Mv.mvar Mv.empty) s.
  Proof. by  move=> x id;rewrite Mvar.get0. Qed.
    
  Definition empty_s s := mkT (mset_valid_empty s).

  Definition empty := empty_s Sv.empty.

  Lemma mset_valid_merge m1 m2 : 
    mset_valid (Mv.mvar (Mv.merge (mv m1) (mv m2))) (Sv.union (mset m1) (mset m2)).
  Proof. by move=> x id /Mv.mergeP [] /svalid ? /svalid ?;SvD.fsetdec. Qed.

  Definition merge m1 m2 := mkT (@mset_valid_merge m1 m2).

  Lemma get0 x : get empty x = None.
  Proof. by apply Mv.get0. Qed.

  Lemma setP_eq m x id : get (set m x id) x = Some id.
  Proof. by apply Mv.setP_eq. Qed.

  Lemma setP_neq m x y id id' : 
    x != y -> get (set m x id) y = Some id' ->
    get m y = Some id' /\ id <> id'.
  Proof. apply Mv.setP_neq. Qed.

  Lemma setP_mset m x id : mset (set m x id) = Sv.add x (mset m).
  Proof. by []. Qed.

  Lemma mergeP m1 m2 x id : 
    get (merge m1 m2) x = Some id -> get m1 x = Some id /\ get m2 x = Some id.
  Proof. apply Mv.mergeP. Qed.

  Lemma mergeP_mset m1 m2 : mset (merge m1 m2) = Sv.union (mset m1) (mset m2).
  Proof. by []. Qed.

  Definition incl m1 m2 :=
    Mv.incl (mv m1) (mv m2) && Sv.subset (mset m2) (mset m1).
  
  Lemma inclP m1 m2 : 
    reflect ((forall x id, get m1 x = Some id -> get m2 x = Some id) /\
             Sv.Subset (mset m2) (mset m1))
            (incl m1 m2).
  Proof.
    rewrite /incl; apply (equivP andP).
    match goal with |- (is_true ?A /\ _) <-> (?B /\ _) => have : reflect B A end.
    + apply Mv.inclP.
    by move=> /rwP ->;rewrite SvD.F.subset_iff.
  Qed.    

  Lemma incl_refl r : incl r r.
  Proof. by apply/inclP;split. Qed.

  Lemma incl_trans r2 r1 r3 : incl r1 r2 -> incl r2 r3 -> incl r1 r3.
  Proof. 
    move=> /inclP [H1 H3] /inclP [H2 H4];apply/inclP;split;last by SvD.fsetdec.
    by move=> x id /H1 /H2. 
  Qed.

  Lemma merge_incl_l r1 r2 : incl (merge r1 r2) r1.
  Proof. 
    apply/inclP;split;first by move=> x id /mergeP []. 
    rewrite (mergeP_mset r1 r2);SvD.fsetdec.
  Qed.

  Lemma merge_incl_r r1 r2 : incl (merge r1 r2) r2.
  Proof. 
    apply/inclP;split;first by move=> x id /mergeP []. 
    rewrite (mergeP_mset r1 r2);SvD.fsetdec.
  Qed.

  End M.

  Definition check_v xi1 xi2 (m:M.t) : cexec M.t :=
    let x1 := xi1.(v_var) in
    let x2 := xi2.(v_var) in    
    if vtype x1 == vtype x2 then
      match M.get m x1 with
      | None     => 
        if Sv.mem x1 (M.mset m) then cerror (Cerr_varalloc xi1 xi2 "variable already set") 
        else cok (M.set m x1 (vname x2))
      | Some id' => 
        if vname x2 == id' then cok m 
        else cerror (Cerr_varalloc xi1 xi2 "variable mismatch")
      end
    else cerror (Cerr_varalloc xi1 xi2 "type mismatch").

  Fixpoint check_e (e1 e2:pexpr) (m:M.t) : cexec M.t:= 
    match e1, e2 with 
    | Pconst n1, Pconst n2 => 
      if n1 == n2 then cok m else cerror (Cerr_neqexpr e1 e2 salloc) 
    | Pbool  b1, Pbool  b2 => 
      if b1 == b2 then cok m else cerror (Cerr_neqexpr e1 e2 salloc)
    | Pcast  e1, Pcast  e2 => check_e e1 e2 m 
    | Pvar   x1, Pvar   x2 => check_v x1 x2 m
    | Pget x1 e1, Pget x2 e2 => check_v x1 x2 m >>= check_e e1 e2
    | Pload x1 e1, Pload x2 e2 => check_v x1 x2 m >>= check_e e1 e2
    | Pnot   e1, Pnot   e2 => check_e e1 e2 m
    | Papp2 o1 e11 e12, Papp2 o2 e21 e22 =>
      if o1 == o2 then check_e e11 e21 m >>= check_e e12 e22
      else cerror (Cerr_neqop2 o1 o2 salloc)
    | _, _ => cerror (Cerr_neqexpr e1 e2 salloc)
    end.

  Definition check_var (xi1 xi2:var_i) m : cexec M.t :=
    let x1 := xi1.(v_var) in
    let x2 := xi2.(v_var) in
    if vtype x1 == vtype x2 then cok (M.set m x1 (vname x2))
    else cerror (Cerr_varalloc xi1 xi2 "type mismatch").

  Definition check_lval (x1 x2:lval) m : cexec M.t :=
    match x1, x2 with
    | Lnone  _   , Lnone _     => cok m 
    | Lvar x1    , Lvar x2     => check_var x1 x2 m
    | Lmem x1 e1 , Lmem x2 e2  => check_v x1 x2 m >>= check_e e1 e2
    | Laset x1 e1, Laset x2 e2 => check_v x1 x2 m >>= check_e e1 e2 >>= check_var x1 x2
    | _          , _           => cerror (Cerr_neqrval x1 x2 salloc)
    end.
     
  Definition eq_alloc (r:M.t) (vm1 vm2:vmap) := 
    [/\ vm_uincl vmap0 vm2,
        (forall x, ~Sv.In x (M.mset r) -> vm1.[x] = undef_addr x.(vtype)) &
        (forall x id,  M.get r x = Some id -> eval_uincl vm1.[x] vm2.[Var (vtype x) id])].
  
  Lemma eq_alloc_empty: eq_alloc M.empty vmap0 vmap0.
  Proof. done. Qed.

  Lemma eq_alloc_incl r1 r2 vm vm':
    M.incl r2 r1 -> 
    eq_alloc r1 vm vm' -> 
    eq_alloc r2 vm vm'.
  Proof. 
    move=> /M.inclP [Hi Hsub] [Huincl epa eqa];split=>//.
    + by move=> x Hx;apply epa;SvD.fsetdec.
    move=> x id /Hi;apply eqa. 
  Qed.

  Lemma check_vP x1 x2 r re vm1 vm2 : 
    check_v x1 x2 r = ok re ->
    eq_alloc r vm1 vm2 ->
    eq_alloc re vm1 vm2 /\
    (forall v1 : value,
       get_var vm1 x1 = ok v1 ->
       exists v2 : value, get_var vm2 x2 = ok v2 /\ value_uincl v1 v2).
  Proof.
    rewrite /check_v;case:eqP => //= Ht.
    case Hget : M.get => [id | ].
    + case: eqP => //= ? [<-];subst id => Hea;split=>//.
      case: Hea => _ _ /(_ _ _ Hget) Hev v1 {Hget} Hget.    
      case: x1 x2 Ht Hget Hev=> [[xt1 xn1] ii1] [[xt2 xn2] ii2] /= <-.
      rewrite /get_var;apply: rbindP => /= z -> [<-].
      case: (vm2.[_])%vmap => //= z' Hz;exists (to_val z');split => //=.
      by rewrite -to_val_uincl.
    case: ifPn => //= /Sv_memP Hnot [] <- [Hvm0 Hset Huincl];split;first split=>//.
    + by move=> x;rewrite M.setP_mset => ?;apply Hset;SvD.fsetdec.
    + move=> x id;case : ((v_var x1) =P x) => [<- | /eqP Hne].
      + rewrite M.setP_eq => -[<-].
        by rewrite (Hset _ Hnot) /=;apply: (Hvm0 {| vtype := vtype x1; vname := vname x2 |}).
      by move=> /(M.setP_neq Hne) [??];apply Huincl.
    move=> v1;rewrite /get_var.
    rewrite (Hset _ Hnot) /=.
    case: x2 Ht => [[xt2 xn2] ?] /= <-.
    case: (vtype x1) => //= p [<-].
    have := Hvm0 {| vtype := sarr p; vname := xn2 |};rewrite /vmap0 /=.
    by case: (vm2.[_])%vmap => //= a Ha; exists (Varr a).
  Qed.

  Lemma check_eP e1 e2 r re vm1 vm2 :
    check_e e1 e2 r = ok re ->
    eq_alloc r vm1 vm2 ->
    eq_alloc re vm1 vm2 /\
    forall m v1,  sem_pexpr (Estate m vm1) e1 = ok v1 ->
    exists v2, sem_pexpr (Estate m vm2) e2 = ok v2 /\ value_uincl v1 v2.
  Proof.
    elim : e1 e2 r re vm1 =>
      [z1 | b1 | e1 He1 | x1 | x1 e1 He1 | x1 e1 He1 | e1 He1 | o1 e11 He11 e12 He12 ]
      [z2 | b2 | e2 | x2 | x2 e2 | x2 e2 | e2 | o2 e21 e22 ] //= r re s.
    + by case: ifPn => // /eqP <- [->] ?;split=> // ?? [] <-; exists z1.
    + by case: ifPn => // /eqP <- [->] ?;split=> // ?? [] <-; exists b1.
    + move=> /He1 H /H [? {He1}He1];split=>// m v1.
      apply: rbindP => z;apply:rbindP => v1' /He1 [v2 [-> /=]] Uv Hto [] <-.
      have [_ -> /=]:= value_uincl_int Uv Hto.
      by exists (Vword (I64.repr z)).
    + by move=> /check_vP Hv /Hv [Hea H].
    + apply: rbindP => r' Hcv Hce Hea. 
      have [Hea' Hget]:= check_vP Hcv Hea.
      have [Hre Hse1]:= He1 _ _ _ _ Hce Hea';split=>// m v1.
      apply: on_arr_varP => n t Heqt /Hget [v2 []].
      rewrite /on_arr_var;case: v2 => //= n' t' -> [] ? Ht /=;subst n'.
      apply: rbindP => w;apply: rbindP => ve /Hse1 [v2 [-> U2 Hto]].
      have [_ -> /=]:= value_uincl_int U2 Hto.
      by apply: rbindP => w' /Ht -> [] <-;exists (Vword w').
    + apply: rbindP => r' Hcv Hce Hea. 
      have [Hea' Hget]:= check_vP Hcv Hea.
      have [Hre Hse1]:= He1 _ _ _ _ Hce Hea';split=>// m v1.
      apply: rbindP => w1;apply: rbindP => ve1 /Hget [ve1' [->]]. 
      move=> /value_uincl_word H/H{H}[??];subst.
      apply: rbindP => w2;apply: rbindP => ve /Hse1 [v2 [-> /value_uincl_word H/H [_ ->]]] /=.
      by exists v1.
    + move=> H /(He1 _ _ _ _ H) [Hea Hse1];split=>//.
      move=> m v1;apply:rbindP => b;apply: rbindP => ve /Hse1 [v2 [->] /= U2 Hto [] <-].
      by have [_ -> /=]:= value_uincl_bool U2 Hto; exists (Vbool (~~b)).
    case: eqP => // <-;apply:rbindP => r' Hs1 Hs2 Hea.
    have [Hea' Hse1]:= He11 _ _ _ _ Hs1 Hea.  
    have [? Hse2]:= He12 _ _ _ _ Hs2 Hea';split=>// m v.
    apply: rbindP => v1 /Hse1 [v1' [-> U1]].
    apply: rbindP => v2 /Hse2 [v2' [-> U2]].
    by apply vuincl_sem_sop2.
  Qed.

  Lemma check_varP r1 r1' vm1 vm2 vm1' x1 x2 v1 v2 :
    eq_alloc r1 vm1 vm2 ->
    check_var x1 x2 r1 = ok r1' ->
    set_var vm1 x1 v1 = ok vm1' ->
    value_uincl v1 v2 ->
    exists vm2' : vmap,
      set_var vm2 x2 v2 = ok vm2' /\ eq_alloc r1' vm1' vm2'.
  Proof.
    rewrite /check_var;case: eqP => //= Ht Hea [<-].
    apply: rbindP => v1' Hv1' [<-] Hu.
    have [v2' [Hv2' Hu']]:= of_val_uincl Hu Hv1'.
    case: x2 Ht => -[xt2 xn2] _ /= <-.
    exists (vm2.[{| vtype := vtype x1; vname := xn2 |} <- ok v2']);split.
    + by rewrite /set_var /= Hv2'.
    case: Hea => Hvm0 Hin Hget; set x2 := {|vtype := _ |};split.
    + move=> z;case (x2 =P z) => [<- | /eqP Hne].
      + rewrite Fv.setP_eq /vmap0 Fv.get0 /x2 /= => {Hu' Hv2'}.
        case: (vtype x1) v2' => //= p v2' i v H.
        by have := Array.getP_empty H.
      by rewrite Fv.setP_neq.
    + move=> z;rewrite M.setP_mset => Hnin.
      by rewrite Fv.setP_neq;[apply Hin|apply /eqP];SvD.fsetdec.
    move=> x id;case: ((v_var x1) =P x) => [<- | /eqP Hne].
    + by rewrite M.setP_eq => -[<-];rewrite !Fv.setP_eq.
    move=> /(M.setP_neq Hne) [] Hx1 Hid;rewrite !Fv.setP_neq //;first by apply Hget.
    by apply /eqP => -[] _ /Hid.
  Qed.

  Lemma check_lvalP r1 r1' x1 x2 s1 s1' vm1 v1 v2 :
    check_lval x1 x2 r1 = ok r1' ->
    eq_alloc r1 s1.(evm) vm1 ->
    value_uincl v1 v2 ->
    write_lval x1 v1 s1 = ok s1' ->
    exists vm1', 
      write_lval x2 v2 (Estate s1.(emem) vm1) = ok (Estate s1'.(emem) vm1') /\
      eq_alloc r1' s1'.(evm) vm1'.
  Proof.
    case: x1 x2 => /= [ii1 | x1 | x1 p1 | x1 p1] [ii2 | x2 | x2 p2 | x2 p2] //=.
    + by move=> [<-] ?? [<-];exists vm1.  
    + rewrite /write_var=> Hc Hvm1 Hv;apply rbindP => vm1' Hset [<-] /=.
      by have [vm2 [-> Hr1']/=]:= check_varP Hvm1 Hc Hset Hv; exists vm2.
    + apply: rbindP => r2 Hcv Hce Hvm1 Hv.
      apply: rbindP => wx;apply:rbindP => vx.
      have [Hr2 H/H{H} [vx' [-> Hvx /=]]]:= check_vP Hcv Hvm1.
      move=> /(value_uincl_word Hvx) [_ ->] /=.
      apply: rbindP => we;apply:rbindP => ve.
      case: s1 Hvm1 Hr2 => sm1 svm1 /= Hvm1 Hr2.
      have [Hr1' H/H{H} [ve' [-> Hve]]]:= check_eP Hce Hr2.
      move=> /(value_uincl_word Hve) [_ ->] /=.
      apply: rbindP => w /(value_uincl_word Hv) [_ ->] /=.
      by apply: rbindP => ? -> -[<-];exists vm1.
     apply: rbindP => r2;apply:rbindP=> r3 Hcv Hce Hcva Hvm1 Hv.
     apply: on_arr_varP => n t Htx;rewrite /on_arr_var /=.
     have [Hr3 H/H{H} [vx2 [->]]]:= check_vP Hcv Hvm1.
     case: vx2 => //= n0 t2 [? Ht];subst n0.
     apply: rbindP => we;apply:rbindP => ve.
     case: s1 Hvm1 Hr3 => sm1 svm1 /= Hvm1 Hr3.
     have [Hr1' H/H{H} [ve' [-> Hve]]]:= check_eP Hce Hr3.
     move=> /(value_uincl_int Hve) [_ ->] /=.
     apply: rbindP => w /(value_uincl_word Hv) [_ ->] /=.
     apply: rbindP => t1' Ht1'.
     have [t2' [-> Ht2']]:= Array_set_uincl Ht Ht1'. 
     apply: rbindP => vm2 Hvm2 [<-] /=.
     have Ut' : value_uincl (Varr t1') (Varr t2') by done.
     by have [vm2' [-> ?] /=]:= check_varP Hr1' Hcva Hvm2 Ut';exists vm2'.
   Qed.

End CBAreg.

Module CheckAllocReg :=  MakeCheckAlloc CBAreg.