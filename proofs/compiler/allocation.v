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
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import psem.
Require Import compiler_util ZArith.
Import Utf8.

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

  Parameter check_e : pexpr -> pexpr -> M.t -> cexec (M.t * leak_e_tr).

  Parameter check_lval : option (stype * pexpr) -> lval -> lval -> M.t -> cexec (M.t * leak_e_tr).

  Parameter eq_alloc : M.t -> vmap -> vmap -> Prop.

  Parameter eq_alloc_empty : eq_alloc M.empty vmap0 vmap0.

  Parameter eq_alloc_incl : forall r1 r2 vm vm',
    M.incl r2 r1 ->
    eq_alloc r1 vm vm' ->
    eq_alloc r2 vm vm'.

  Parameter check_eP : forall gd e1 e2 r re lte vm1 vm2,
    check_e e1 e2 r = ok (re, lte) ->
    eq_alloc r vm1 vm2 ->
    eq_alloc re vm1 vm2 /\
    forall m v1 l1,  sem_pexpr gd (Estate m vm1) e1 = ok (v1, l1) ->
                     exists v2, sem_pexpr gd (Estate m vm2) e2 = ok (v2, leak_E lte l1) /\ value_uincl v1 v2.

  Parameter check_lvalP : forall gd r1 r1' ltr1' x1 x2 e2 s1 s1' l1' vm1 v1 v2,
    check_lval e2 x1 x2 r1 = ok (r1', ltr1') ->
    eq_alloc r1 s1.(evm) vm1 ->
    value_uincl v1 v2 ->
    oapp (fun te2 =>
            Let vl := sem_pexpr gd (Estate s1.(emem) vm1) te2.2 in
            truncate_val te2.1 vl.1 = ok v2) true e2 ->
        (*sem_pexpr gd (Estate s1.(emem) vm1) te2.2 >>= truncate_val te2.1 = ok v2) true e2 ->*)
    write_lval gd x1 v1 s1 = ok (s1', l1') ->
    exists vm1',
      write_lval gd x2 v2 (Estate s1.(emem) vm1) = ok (Estate s1'.(emem) vm1', leak_E ltr1' l1') /\
      eq_alloc r1' s1'.(evm) vm1'.

End CheckB.

Definition salloc : string := "allocation".

Module MakeCheckAlloc (C:CheckB).

Import C.

Section LOOP.

  Variable ii:instr_info.
  Variable check_c : M.t -> ciexec (M.t * leak_c_tr).

  Fixpoint loop (n:nat) (m:M.t) : ciexec (M.t * leak_c_tr) :=
    match n with
    | O => cierror ii (Cerr_Loop "allocation")
    | S n =>
      Let m' := check_c m in
      if M.incl m m'.1 then ok (m, m'.2)
      else loop n (M.merge m m'.1)
    end.

  Variable A : Type.
  Variable check_c2 : M.t -> ciexec (M.t * M.t * A).
  
  Fixpoint loop2 (n:nat) (m:M.t) :=
    match n with
    | O => cierror ii (Cerr_Loop "allocation")
    | S n =>
      Let rc := check_c2 m in
      let: (m', m'', ltm') := rc in 
      if M.incl m m'' then ok (m', ltm')
      else loop2 n (M.merge m m'')
    end.

End LOOP.

Definition check_e_error := Cerr_fold2 "allocation:check_e".

Definition cmd2_error := Cerr_fold2 "allocation:check_cmd".

Definition check_es es1 es2 r := fold2 check_e_error (fun e1 e2 r1 => Let rs := check_e e1 e2 r1.1 in
                                                        ok (rs.1, rcons r1.2 rs.2)) es1 es2 (r, [::]).


(*Definition check_es es1 es2 r := check_e es1 es2 r.*)

Definition check_lvals ls1 ls2 r :=
  fold2 (Cerr_fold2 "allocation:check_lvals") (fun l1 l2 r1 => Let rs := check_lval None l1 l2 r1.1 in ok(rs.1, rcons r1.2 rs.2)) ls1 ls2 (r, [::]).

(*Definition check_lvals :=
  fold2 (Cerr_fold2 "allocation:check_lvals") (check_lval None).*)

Definition check_var x1 x2 r := check_lval None (Lvar x1) (Lvar x2) r.

Definition check_vars xs1 xs2 r := check_lvals (map Lvar xs1) (map Lvar xs2) r.

Check loop2.

Fixpoint check_i iinfo i1 i2 r : ciexec (M.t * leak_i_tr) :=
  match i1, i2 with
  | Cassgn x1 _ ty1 e1, Cassgn x2 _ ty2 e2 =>
    if ty1 == ty2 then
      Let res := add_iinfo iinfo (check_e e1 e2 r) in
      Let rls := add_iinfo iinfo (check_lval (Some (ty2, e2)) x1 x2 res.1) in 
      ciok (rls.1, LT_ile (LT_seq [:: res.2 ; rls.2]))                  
    else cierror iinfo (Cerr_neqty ty1 ty2 salloc)
  | Copn xs1 _ o1 es1, Copn xs2 _ o2 es2 =>
    if o1 == o2 then
      Let res := add_iinfo iinfo (check_es es1 es2 r) in
      Let rls := add_iinfo iinfo (check_lvals xs1 xs2 res.1) in
      ciok (rls.1, LT_ile (LT_seq [:: LT_seq res.2 ; LT_seq rls.2]))
      (*add_iinfo iinfo (check_es es1 es2 r >>= check_lvals xs1 xs2)*)
    else cierror iinfo (Cerr_neqop o1 o2 salloc)
  | Ccall _ x1 f1 arg1, Ccall _ x2 f2 arg2 =>
    if f1 == f2 then
      Let res := add_iinfo iinfo (check_es arg1 arg2 r) in
      Let rls := add_iinfo iinfo (check_lvals x1 x2 res.1) in 
      ciok (rls.1, (LT_icall (LT_seq res.2) (LT_seq rls.2)))
    else cierror iinfo (Cerr_neqfun f1 f2 salloc)
  | Cif e1 c11 c12, Cif e2 c21 c22 =>
    Let res := add_iinfo iinfo (check_e e1 e2 r) in
    Let r1 := fold2 (iinfo, cmd2_error) (fun e1 e2 r1 => Let rs := check_I e1 e2 r1.1 in
                                               ok (rs.1, rcons r1.2 rs.2)) c11 c21 (res.1, [::]) in
    Let r2 := fold2 (iinfo, cmd2_error) (fun e1 e2 r1 => Let rs := check_I e1 e2 r1.1 in
                                         ok (rs.1, rcons r1.2 rs.2)) c12 c22 (res.1, [::]) in 
    ok (M.merge r1.1 r2.1, LT_icond res.2 r1.2 r2.2)
  | Cfor x1 (d1,lo1,hi1) c1, Cfor x2 (d2,lo2,hi2) c2 =>
    if d1 == d2 then
      Let rlo := add_iinfo iinfo (check_e lo1 lo2 r) in
      Let rhi := add_iinfo iinfo (check_e hi1 hi2 rlo.1) in 
      Let rv := add_iinfo iinfo (check_var x1 x2 r) in 
      let check_c r := fold2 (iinfo, cmd2_error) (fun e1 e2 r1 => Let rs := check_I e1 e2 r1.1 in
                                               ok (rs.1, rcons r1.2 rs.2)) c1 c2 (rv.1, [::]) in
      Let res := loop iinfo check_c Loop.nb rhi.1 in
      ok (r, LT_ifor (LT_seq [:: rlo.2; rhi.2]) res.2)
    else cierror iinfo (Cerr_neqdir salloc)
  | Cwhile a1 c1 e1 c1', Cwhile a2 c2 e2 c2' =>
    let check_c r :=
      Let rc := fold2 (iinfo, cmd2_error) (fun e1 e2 r1 => Let rs := check_I e1 e2 r1.1 in
                                               ok (rs.1, rcons r1.2 rs.2)) c1 c2 (r, [::]) in
      Let re := add_iinfo iinfo (check_e e1 e2 r) in
      Let rc' := fold2 (iinfo, cmd2_error) (fun e1 e2 r1 => Let rs := check_I e1 e2 r1.1 in
                                               ok (rs.1, rcons r1.2 rs.2)) c1' c2' (re.1, [::]) in 
      ok (re.1, rc'.1, (rc.2, re.2, rc'.2)) in
    Let r := loop2 iinfo check_c Loop.nb r in
    let: (r, (ltc, lte, ltc')) := r in
    ok (r, LT_iwhile ltc lte ltc')

  | _, _ => cierror iinfo (Cerr_neqinstr i1 i2 salloc)
  end

with check_I i1 i2 r :=
  match i1, i2 with
  | MkI _ i1, MkI ii i2 => check_i ii i1 i2 r
  end.

(*Fixpoint check_i iinfo i1 i2 r : ciexec M.t :=
  match i1, i2 with
  | Cassgn x1 _ ty1 e1, Cassgn x2 _ ty2 e2 =>
    if ty1 == ty2 then
      add_iinfo iinfo (check_e e1 e2 r >>= check_lval (Some (ty2,e2)) x1 x2)
    else cierror iinfo (Cerr_neqty ty1 ty2 salloc)
  | Copn xs1 _ o1 es1, Copn xs2 _ o2 es2 =>
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
  | Cwhile a1 c1 e1 c1', Cwhile a2 c2 e2 c2' =>
    let check_c r :=
      Let r := fold2 (iinfo,cmd2_error) check_I c1 c2 r in
      Let re := add_iinfo iinfo (check_e e1 e2 r) in
      Let r' := fold2 (iinfo,cmd2_error) check_I c1' c2' re in
      ok (re, r') in
    Let r := loop2 iinfo check_c Loop.nb r in
    ok r

  | _, _ => cierror iinfo (Cerr_neqinstr i1 i2 salloc)
  end

with check_I i1 i2 r :=
  match i1, i2 with
  | MkI _ i1, MkI ii i2 => check_i ii i1 i2 r
  end.*)

Definition check_cmd iinfo := fold2 (iinfo, cmd2_error) (fun e1 e2 r1 => Let rs := check_I e1 e2 r1.1 in
                                                               ok (rs.1, rcons r1.2 rs.2)).

(** NEED TO FIX **)
Definition check_fundef (f1 f2: funname * fundef) (_:Datatypes.unit) :=
  let (f1,fd1) := f1 in
  let (f2,fd2) := f2 in
  if (f1 == f2) && (fd1.(f_tyin) == fd2.(f_tyin)) && (fd1.(f_tyout) == fd2.(f_tyout)) then
    add_finfo f1 f2 (
    Let rvs := add_iinfo fd1.(f_iinfo) (check_vars fd1.(f_params) fd2.(f_params) M.empty) in
    Let rcs := check_cmd fd1.(f_iinfo) fd1.(f_body) fd2.(f_body) (rvs.1, [:: LT_ile (LT_seq rvs.2)]) in
    let es1 := map Pvar fd1.(f_res) in
    let es2 := map Pvar fd2.(f_res) in
    Let res := add_iinfo fd1.(f_iinfo) (check_es es1 es2 rcs.1) in
    ok (tt, (fd1, (rcs.2 ++ [:: LT_ile (LT_seq res.2)]))))
    (*Let rcs := check_cmd fd1.(f_iinfo) fd1.(f_body) fd2.(f_body) rvs.1 in
    let es1 := map Pvar fd1.(f_res) in
    let es2 := map Pvar fd2.(f_res) in
    Let res := add_iinfo fd1.(f_iinfo) (check_es es1 es2 rcs.1) in
    ok tt)*)
  else cferror (Ferr_neqfun f1 f2).

Definition check_prog_aux prog1 prog2 :=
  Let rs := fold2 Ferr_neqprog (fun f1 f2 r1 => Let rs := check_fundef f1 f2 r1.1 in ok (tt, (rcons r1.2 rs.2)))
                  (p_funcs prog1) (p_funcs prog2) (tt, [::]) in
  let rslt := unzip2 rs.2 in
  let funnames := map fst (p_funcs prog1) in
  let rsfnlt := zip funnames rslt in
  ok (rs.1, rsfnlt).

(*Definition check_prog_aux prog1 prog2 :=  fold2 Ferr_neqprog check_fundef (p_funcs prog1) (p_funcs prog2) tt.*)

Definition check_prog prog1 prog2 :=
  if prog1.(p_globs) == prog2.(p_globs) then check_prog_aux prog1 prog2
  else cferror Ferr_glob_neq.

                         
Lemma check_lvalsP gd xs1 xs2 vs1 vs2 r1 r2 lts s1 s2 l2 vm1 :
  check_lvals xs1 xs2 r1 = ok (r2, lts) ->
  eq_alloc r1 s1.(evm) vm1 ->
  List.Forall2 value_uincl vs1 vs2 ->
  write_lvals gd s1 xs1 vs1 = ok (s2, l2) ->
  exists vm2,
    write_lvals gd (Estate s1.(emem) vm1) xs2 vs2 =
    ok (Estate s2.(emem) vm2, map2 leak_E lts l2) /\
    eq_alloc r2 s2.(evm) vm2.
Proof.
  rewrite /write_lvals /=.
  elim: xs1 xs2 vs1 vs2 r1 r2 lts s1 s2 l2 vm1 => [ | x1 xs1 Hrec] [ | x2 xs2] //=
    vs1 vs2 r1 r2 lts s1 s2 l2 vm1.
  + move=> Hcvs Hvm [] //= [] <- <- /=. exists vm1.
    rewrite /check_lvals in Hcvs. rewrite /= in Hcvs. by case: Hcvs=> <- <- /=.
  + rewrite /check_lvals. move=> /= Hcvs Hvm [] v /=. inversion v.
    t_xrbindP. move=> v' vs' vs'' Hv Hvs' [s ls] [s' l'] Hw /= [] Hs Hl Hws.
    move: Hcvs. t_xrbindP. move=> [t' lts'] [t'' lt''] Hcv [] Ht Hlts Hcvs.
     have [ //| vm3 [->/= Hvm3]] := check_lvalP (e2:= None) Hcv Hvm Hv _ Hw.
    (*move: check_lvalP. move=> Hcv'.
    move: (Hcv' gd r1 t'' lt'' x1 x2 None s1 s' l' vm1 v v' Hcv Hvm Hv).*)
     move: (Hrec).
 Admitted.


 (* + move=> s0 vm0 Hcvs Hvm [] //= [] <- -> /=.
    exists vm0. rewrite /check_lvals in Hcvs. rewrite /= in Hcvs.
    case: Hcvs=> <- <- /=. split.
  + by move=> [<-] Hvm1 [] //= [<-];exists vm1.
  apply: rbindP => r3 Hx Hcxs Hvm1 [] //= {vs1 vs2}.
  move=> v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s3 Hw Hws.
  have [ //| vm3 [->/= Hvm3]] := check_lvalP (e2:= None) Hx Hvm1 Hv _ Hw.
  apply: Hrec Hcxs Hvm3 Hvs Hws.
Qed.*)

Section PROOF.


  Variable p1 p2:prog.
  Variable Fs: seq (funname * seq leak_i_tr).
  Notation gd := (p_globs p1).
  Hypothesis Hcheck: check_prog_aux p1 p2 = ok (tt, Fs).
  Hypothesis eq_globs : p_globs p1 = p_globs p2.

  Lemma all_checked : forall fn fd1,
    get_fundef (p_funcs p1) fn = Some fd1 ->
    exists fd2, exists ltc,  get_fundef (p_funcs p2) fn = Some fd2 /\ check_fundef (fn,fd1) (fn,fd2) tt = ok (tt, ltc).
  Proof.
    Admitted.
    (*move: Hcheck; rewrite /check_prog_aux;clear Hcheck eq_globs.
    move: (p_funcs p1) (p_funcs p2);clear p1 p2.
    elim => [ | [fn1' fd1'] p1 Hrec] [ | [fn2 fd2] p2] //.
    apply: rbindP => -[] Hc /Hrec {Hrec} Hrec.
    have ? : fn1' = fn2.
    + by move: Hc;rewrite /check_fundef; case:ifP => // /andP[]/andP[]/eqP.
    subst=> fn fd1;rewrite !get_fundef_cons.
    case:ifPn => [/eqP -> [] <-| _ /Hrec //].
    by exists fd2.
  Qed.*)

 (* Let Pi_r s1 (i1:instr_r) li s2:=
    forall ii r1 i2 r2 lti vm1, eq_alloc r1 (evm s1) vm1 ->
    check_i ii i1 i2 r1 = ok (r2, lti) ->
    exists vm2, eq_alloc r2 (evm s2) vm2 /\
                sem_i p2 (Estate (emem s1) vm1) i2 (leak_I (leak_Fun Fs) li lti) (Estate (emem s2) vm2).*)

  Let Pi_r s1 (i1:instr_r) li s2:=
    forall ii r1 i2 r2 lti vm1, eq_alloc r1 (evm s1) vm1 ->
    check_i ii i1 i2 r1 = ok (r2, lti) ->
    exists vm2, eq_alloc r2 (evm s2) vm2 /\
      sem p2 (Estate (emem s1) vm1) [:: (MkI ii i2)] (leak_I (leak_Fun Fs) li lti) (Estate (emem s2) vm2).

  (*Let Pi s1 (i1:instr) s2:=
    forall r1 i2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_I i1 i2 r1 = ok (r2) ->
    exists vm2, eq_alloc r2 (evm s2) vm2 /\
      sem_I p2 (Estate (emem s1) vm1) i2 (Estate (emem s2) vm2).*)

  Let Pi s1 (i1:instr) li s2:=
    forall r1 i2 r2 lti vm1, eq_alloc r1 (evm s1) vm1 ->
    check_I i1 i2 r1 = ok (r2, lti) ->
    exists vm2, eq_alloc r2 (evm s2) vm2 /\
      sem p2 (Estate (emem s1) vm1) [:: i2] (leak_I (leak_Fun Fs) li lti) (Estate (emem s2) vm2).

  Let Pc s1 (c1:cmd) lc s2:=
    forall ii r1 c2 r2 ltc vm1, eq_alloc r1.1 (evm s1) vm1 ->
    check_cmd ii c1 c2 r1 = ok (r2, ltc) ->
    exists vm2, eq_alloc r2 (evm s2) vm2 /\
      sem p2 (Estate (emem s1) vm1) c2 (leak_Is (leak_I (leak_Fun Fs)) ltc lc) (Estate (emem s2) vm2).

  Let Pfor (i1:var_i) vs s1 c1 lf s2 :=
    forall i2 ii r1 r1' ltv c2 r2 ltf vm1, eq_alloc r1 (evm s1) vm1 ->
    check_var i1 i2 r1 = ok (r1', ltv) ->
    check_cmd ii c1 c2 (r1', [:: LT_ile ltv]) = ok (r2, ltf) -> M.incl r1 r2 ->
    exists vm2, eq_alloc r1 (evm s2) vm2 /\
                sem_for p2 i2 vs (Estate (emem s1) vm1) c2 (leak_Iss (leak_I (leak_Fun Fs)) ltf lf)
                        (Estate (emem s2) vm2).

  Let Pfun m fn vargs1 lf m' vres :=
    forall vargs2, List.Forall2 value_uincl vargs1 vargs2 ->
    exists vres',
       sem_call p2 m fn vargs2 (lf.1, (leak_Is (leak_I (leak_Fun Fs)) (leak_Fun Fs lf.1) lf.2)) m' vres' /\
       List.Forall2 value_uincl vres vres'.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    move=> s ii r1 [ | ??] //= r2 ltc vm1 Heq [] Hr.
    rewrite Hr in Heq. rewrite /= in Heq.
    exists vm1. split=> //; constructor.
  Qed.

  Local Lemma Hcons : sem_Ind_cons p1 Pc Pi.
  Proof.
    rewrite /sem_Ind_cons. rewrite /Pi. rewrite /Pc.
    move=> s1 s2 s3 i c li lc Hsi Hi Hsc Hc ii [r1 lr1] [ | i2 c2] //= r2 ltc vm1 Hvm1.
    t_xrbindP. move=> [r3' ltc'] [r2' lti'] Hci <- Hcc.
    move: (Hi r1 i2 r2' lti' vm1 Hvm1 Hci). move=> {Hi} [] vm2 [] Hvm2 Hsc'.
    move: (Hc ii ((r2', lti').1,
                  rcons lr1 (r2', lti').2) c2 r2 ltc vm2 Hvm2 Hcc). move=> {Hc} [] vm3 [] Hvm3 Hsc''.
    exists vm3. split=>//. rewrite /leak_Is. admit.
  Admitted.

  Local Lemma HmkI : sem_Ind_mkI p1 Pi_r Pi.
  Proof.
    move=> ii i s1 s2 li Hsi Hi r1 [i2i i2] r2 lti vm1 /Hi Hvm /= /Hvm [vm2 [Hvm2 Hsc]].
    by exists vm2;split=>//;constructor.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn p1 Pi_r.
  Proof.
    move => s1 s2 x tag ty e v v' le lw.
    case: s1 => sm1 svm1 He Htr Hw ii r1 [] //= x2 tag2 ty2 e2 r2 lti vm1 Hvm1.
    case: eqP => // <- {ty2}. t_xrbindP. move=> [re lte]. apply: add_iinfoP.
    move=> /check_eP Hce [rv ltv]. apply: add_iinfoP. move=>Hcv [] <- <-. 
    move: (Hce gd svm1 vm1 Hvm1). move=> [] Hvm2 He'. move: (He' sm1 v le He).
    move=> [] v'' [] {He'} He' Hv. move: truncate_value_uincl.
    move=> Ht. move: (Ht ty v v'' v' Hv Htr). move=> [] v''' Htr' {Ht} Hv'.
    move: check_lvalP. move=> Hcv'.
    move: (Hcv' gd re rv ltv x x2 (Some (ty, e2)) {|emem := sm1; evm := svm1|}
                s2 lw vm1 v' v''' Hcv Hvm2 Hv').
    move=> /= {Hcv'}. rewrite He' /=. move=> H. move: (H Htr' Hw). move=> {H} [] vm2 [] Hcv' Hvm3.
    exists vm2. split=> // /=; econstructor. apply EmkI. apply Eassgn with v'' v'''. replace (p_globs p2) with gd.
    auto. auto. replace (p_globs p2) with gd. apply Hcv'. constructor.
  Qed.

  Lemma check_esP e1 e2 r re lte s vm:
    check_es e1 e2 r = ok (re, lte) ->
    eq_alloc r s.(evm) vm ->
    eq_alloc re s.(evm) vm /\
    forall vs,  sem_pexprs gd s e1 = ok vs ->
    exists vs', sem_pexprs (p_globs p2) (Estate s.(emem) vm) e2 = ok vs' /\
               List.Forall2 value_uincl (unzip1 vs) (unzip1 vs') /\
               LSub (unzip2 vs') = LSub (map2 leak_E lte (unzip2 vs)).
  Proof.
    rewrite -eq_globs;case: s => sm svm.
    rewrite /check_es; elim: e1 e2 r [::] lte => [ | e1 es1 Hrec] [ | e2 es2] r lte1 lte2 //=.
    + move=> [] <- <- Hvm. split=> // -[] //= ?; exists [::]. split. auto. split=> //.
      rewrite /=. constructor. rewrite /=. case: lte1. constructor. constructor.
    t_xrbindP. move=> [rh lth] [re' lte'] /(check_eP gd) /= He [] <- <- Hce Hvm.
    move: (He svm vm Hvm). move=> {He} [] Hvm2 He. split.
    move: (Hrec es2 re' (rcons lte1 lte') lte2 Hce Hvm2). move=> /= {Hrec} [] Hvm3 Hes. auto.
    t_xrbindP. move=> vs' [yv yl] He' vs'' Hes <- /=. move: (He sm yv yl He').
    move=> {He} [] yv' [] -> Hv /=. move: (Hrec es2 re' (rcons lte1 lte') lte2 Hce Hvm2).
    move=> /= {Hrec} [] Hvm3 Hes'. move: (Hes' vs'' Hes). move=> [] vs''' [] -> [] Hvs Hl /=.
    exists ((yv', leak_E lte' yl) :: vs'''). split=> //. split. rewrite /=.
    constructor; auto. rewrite /=. case: Hl => -> /=. admit.
  Admitted.

  Local Lemma Hopn : sem_Ind_opn p1 Pi_r.
  Proof.
    move => s1 s2 t o xs es lo. rewrite /sem_sopn.
    t_xrbindP. move=> ves Hes vo Hex [vw vl] Hws <- <- /=.
    rewrite /Pi_r. move=> ii r1 [] //= xs1 t' o1 es1 r2 lti vm1 Hvm1.
    case: ifPn => //= /eqP <-. t_xrbindP. move=> [yv yl]. apply: add_iinfoP.
    move=> Hces [rv ltv]. apply: add_iinfoP. move=> Hcvs [] <- <-.
    move: check_esP. move=> Hces'. move: (Hces' es es1 r1 yv yl s1 vm1 Hces Hvm1).
    move=> {Hces'} [] Hvm2 Hes'. move: (Hes' ves Hes). move=> {Hes} [] ves' [] Hes [] Hvs Hls.
    move: check_lvalsP. move=> Hcvs'.
    move: vuincl_exec_opn. move=> Hex'. move: (Hex' o (unzip1 ves) (unzip1 ves') vo Hvs Hex).
    move=> [] vo' [] {Hex'} Hex' Hvo.
    move: (Hcvs' gd xs xs1 vo vo' yv rv ltv s1 vw vl vm1 Hcvs Hvm2 Hvo Hws).
    move=> {Hcvs'} [] vm2 [] Hws' Hvm3. exists vm2; split=> //. econstructor.
    constructor. constructor. rewrite /sem_sopn /=. rewrite Hes /=. rewrite Hex' /=.
    replace (p_globs p2) with gd. rewrite Hws' /=. rewrite Hls /=. auto.
    constructor.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p1 Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 le lc.
    case: s1 => sm1 svm1 Hve Hc Hc1 ii r1 [] //= e' c1' c2' r2 lti vm1 /= Hvm1.
    t_xrbindP. move=> [re lte]. apply: add_iinfoP. move=> /check_eP  -/(_ gd _ _ Hvm1) [] Hr1'.
    move=> /(_ _ _ _ Hve) [ve' [Hve' /value_uincl_bool1 ?]];subst ve'.
    move=> [r3 lt3] Hr3;move => [r4 lt4] Hr4 [] <- <-. rewrite /Pc in Hc1. rewrite /= in Hc1.
    have [vm2 [Hvm2 Hsem]]:= Hc1 ii (re, [::]) _ r3 lt3 _ Hr1' Hr3;exists vm2;split.
    + rewrite /=. apply eq_alloc_incl with r3. apply M.merge_incl_l. auto.
    econstructor. constructor. apply Eif_true. replace (p_globs p2) with gd.
    auto. apply Hsem. constructor.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p1 Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 le lc.
    case: s1 => sm1 svm1 Hve Hc Hc1 ii r1 [] //= e' c1' c2' r2 lti vm1 /= Hvm1.
    t_xrbindP. move=> [re lte]. apply: add_iinfoP. move=> /check_eP  -/(_ gd _ _ Hvm1) [] Hr1'.
    move=> /(_ _ _ _ Hve) [ve' [Hve' /value_uincl_bool1 ?]];subst ve'.
    move=> [r3 lt3] Hr3;move => [r4 lt4] Hr4 [] <- <-. rewrite /Pc in Hc1. rewrite /= in Hc1.
    have [vm2 [Hvm2 Hsem]]:= Hc1 ii (re, [::]) _ r4 lt4 _ Hr1' Hr4;exists vm2;split.
    + rewrite /=. apply eq_alloc_incl with r4. apply M.merge_incl_r. auto.
    econstructor. constructor. apply Eif_false. replace (p_globs p2) with gd.
    auto. apply Hsem. constructor.
  Qed.
  
    apply: rbindP => r1';apply: add_iinfoP => /check_eP -/(_ gd _ _ Hvm1) [] Hr1'.
    move=> /(_ _ _ Hve) [ve' [Hve' /value_uincl_bool1 ?]];subst ve'.
    apply: rbindP => r3 Hr3;apply: rbindP => r4 Hr4 [] <-.
    have [vm2 [Hvm2 Hsem]]:= Hc1 ii _ _ _ _ Hr1' Hr4;exists vm2;split.
    + by eapply eq_alloc_incl;eauto;apply M.merge_incl_r.
    by apply Eif_false => //;rewrite -eq_globs Hve'.
  Qed.

  Local Lemma loop2P ii check_c n r1 r2:
    loop2 ii check_c n r1 = ok r2 ->
      exists r2' r3,
      [/\ check_c r2' = ok (r2, r3), M.incl r2' r1 & M.incl r2' r3].
  Proof.
    elim: n r1 r2 => //= n Hrec r1 r2.
    apply: rbindP => -[r2_1 r2_2] Hc;case:ifPn => [? [] <- | _ /Hrec].
    + exists r1, r2_2;split=>//;apply M.incl_refl.
    move=> [r2' [r3 [H1 H2 H3]]];exists r2', r3;split=>//.
    apply: (M.incl_trans H2); apply M.merge_incl_l.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p1 Pc Pi_r.
  Proof.
    move => s1 s2 s3 s4 a c e c'.
    case: s2 => sm2 svm2 _ Hc Hse _ Hc' _ Hw ii r1 [] //= a2 c2 e2 c2' r2 vm1 Hvm1.
    apply: rbindP => r /loop2P [r2' [r3 [H Hir1 Hir3]]] [?];subst r.
    have Hvmr2' := eq_alloc_incl Hir1 Hvm1.
    apply: rbindP H=> r0 Cc2; move /Hc: (Hvmr2') (Cc2) => H /H {H} [vm2 [Hvm2 /= Hc2]].
    apply: rbindP => re Hadd; apply: add_iinfoP (Hadd)=> Hre.
    have /= [Hrevm2 /(_ _ _ Hse) [vb' [Hse2]]]:= check_eP gd Hre Hvm2.
    move=> /value_uincl_bool1?;subst vb'.
    apply: rbindP => r' Cc2' [??];subst r2 r3.
    move /Hc': (Hrevm2) (Cc2')=> H /H {H} [vm3 [Hvm3 /= Hc2']].
    have /(Hw ii) {Hw} Hw:= eq_alloc_incl Hir3 Hvm3.
    have : check_i ii (Cwhile a c e c') (Cwhile a2 c2 e2 c2') r2' = ok re.
    + by rewrite /= Loop.nbP /= Cc2 /= Hadd /= Cc2' /= Hir3 /=.
    move=> /Hw [vm4 [Hvm4 Hsw]];exists vm4;split => //.
    by apply: Ewhile_true Hsw;eauto;rewrite -eq_globs Hse2.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p1 Pc Pi_r.
  Proof.
    move => s1 s2 a c e c'.
    case: s2 => sm2 svm2 _ Hc Hse ii r1 [] //= a2 c2 e2 c2' r2 vm1 Hvm1.
    apply: rbindP => r /loop2P [r2' [r3 [H Hir1 Hir3]]] [?];subst r.
    have Hvmr2' := eq_alloc_incl Hir1 Hvm1.
    apply: rbindP H=> r0 Cc2; move /Hc: (Hvmr2') (Cc2) => H /H {H} [vm2 [Hvm2 /= Hc2]].
    apply: rbindP => re Hadd; apply: add_iinfoP (Hadd)=> Hre.
    have /= [Hrevm2 /(_ _ _ Hse) [vb' [Hse2]]]:= check_eP gd Hre Hvm2.
    move=> /value_uincl_bool1 ?;subst vb'.
    apply: rbindP => r' Cc2' [??];subst r2 r3.
    exists vm2;split => //.
    by apply: Ewhile_false;rewrite // -eq_globs Hse2.
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

  Local Lemma Hfor : sem_Ind_for p1 Pi_r Pfor.
  Proof.
    move => s1 s2 i d lo hi c vlo vhi.
    case: s1 => sm1 svm1.
    move=> Hlo Hhi Hc Hfor ii r1 [] //= i2 [[d2 lo2] hi2] c2 r2 vm1 Hvm1.
    case: eqP => //= ?;subst d2.
    apply: rbindP => r1'; apply: add_iinfoP.
    apply: rbindP => r1'' /check_eP -/(_ gd _ _ Hvm1) [Hr1'' Heqlo].
    have [vlo'' [Hlo2 /value_uincl_int1 Hvlo']] := Heqlo _ _ Hlo;subst vlo''.
    move=>  /check_eP -/(_ gd _ _ Hr1'') [Hr1' Heqhi].
    have [vhi'' [Hhi2 /value_uincl_int1 Hhi']] := Heqhi _ _ Hhi;subst vhi''.
    move=> /loopP [r2'] [];apply: rbindP => r2'';apply:add_iinfoP.
    move=> Hcv Hcc Hr2r1 Hr2r2.
    have := Hfor _ _ _ _ _ _ _ (eq_alloc_incl Hr2r1 Hr1') Hcv Hcc Hr2r2.
    move=> [vm2 [Hvm2 Hsem2]];exists vm2;split=> //.
    econstructor; rewrite -?eq_globs ?Hlo2 ?Hhi2 /= ;eauto.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    by move=> s i c i2 ii r1 r1' c2 r2 vm1 Ha ???;exists vm1;split=> //;constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p1 Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hwi _ Hc _ Hfor i2 ii r1 r1' c2 r2 vm2 Heq Hr1' Hcc Hincl.
    have [//|vm3 [Hwi2 Hvm3]] := check_lvalP (gd := gd) Hr1' Heq (value_uincl_refl _) _ Hwi.
    have [vm4 [Hvm4 Hsc]] := Hc _ _ _ _ _ Hvm3 Hcc.
    have [vm5 [Hvm5 Hsf]] := Hfor _ _ _ _ _ _ _ (eq_alloc_incl Hincl Hvm4) Hr1' Hcc Hincl.
    by exists vm5;split=>//;econstructor;eauto.
  Qed.

  Local Lemma Hcall : sem_Ind_call p1 Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 ii xs fn args vargs vs Hes Hsc Hfun Hw ii' r1 [] //= ii2 xs2 fn2 args2 r2 vm1 Hr1.
    case: eqP => //= ?;subst fn2;apply: add_iinfoP.
    apply: rbindP => r1' Hca Hcxs.
    have [Hr1' /(_ _ Hes) [vargs2 [Hargs2 Hvargs]]] := check_esP Hca Hr1.
    have [v' [Hs2 Hvs]]:= Hfun _ Hvargs.
    have /(_ _ Hr1') [vm2 [Hw2 Hr2]]:= check_lvalsP Hcxs _ Hvs Hw.
    exists vm2;split=>//. by econstructor;eauto;rewrite -?eq_globs.
  Qed.

  Section REFL.

    Hypothesis eq_prog : p1 = p2.

    Local Lemma Hproc_eq m1 m2 fn f vargs vargs' s1 vm2 vres vres':
      get_fundef (p_funcs p1) fn = Some f ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
      sem p1 s1 (f_body f) {| emem := m2; evm := vm2 |} ->
      Pc s1 (f_body f) {| emem := m2; evm := vm2 |} ->
      mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      Pfun m1 fn vargs' m2 vres'.
    Proof.
      move=> Hget Hca Hw Hsem _ Hres Hcr vargs2 Hvargs2;rewrite -eq_prog.
      have: sem_call p1 m1 fn vargs' m2 vres' by econstructor;eauto.
      by apply: sem_call_uincl.
    Qed.

    Lemma alloc_funP_eq_aux fn f f' m1 vargs vargs' vres s1 s2 vres':
      check_fundef (fn, f) (fn, f') tt = ok tt ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
      sem p1 s1 (f_body f) s2 ->
      mapM (fun x : var_i => get_var (evm s2) x) (f_res f) = ok vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      exists s1' vm2 vres1 vres1',
       [ /\ mapM2 ErrType truncate_val f'.(f_tyin) vargs' = ok vargs,
        write_vars (f_params f') vargs {| emem := m1; evm := vmap0 |} = ok s1',
        sem p2 s1' (f_body f') (Estate (emem s2) vm2),
        mapM (fun x : var_i => get_var vm2 x) (f_res f') = ok vres1 &
        List.Forall2 value_uincl vres' vres1' /\
        mapM2 ErrType truncate_val f'.(f_tyout) vres1 = ok vres1'].
    Proof.
      rewrite /check_fundef eq_refl => /=.
      case: ifP => // /andP[]/eqP htyin /eqP htyout;apply: add_finfoP.
      apply:rbindP => r1;apply:add_iinfoP => Hcparams.
      apply:rbindP => r2 Hcc;apply: rbindP => r3;apply: add_iinfoP => Hcres _ Hca.
      rewrite (write_vars_lvals gd)=> /(check_lvalsP Hcparams).
      move=> /(_ vargs _ eq_alloc_empty) [ | vm3 /= [Hw2 Hvm3]].
      + by apply: List_Forall2_refl.
      move=> /(sem_Ind Hskip Hcons HmkI Hassgn Hopn Hif_true Hif_false
                Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc_eq) Hc.
      have [vm4 /= [Hvm4 Hsc2] Hres Hcr]:= Hc _ _ _ _ _ Hvm3 Hcc.
      have := check_esP Hcres Hvm4.
      move=> [Hr3];rewrite sem_pexprs_get_var => /(_ _ Hres) [vres1' /= []].
      rewrite sem_pexprs_get_var => hmap huincl.
      have [vres2' ??]:= mapM2_truncate_val Hcr huincl.
      do 4 eexists;split;eauto.
      + by rewrite -htyin.
      + by rewrite (write_vars_lvals gd).
      by rewrite -htyout;eauto.
    Qed.

  End REFL.

  Local Lemma Hproc : sem_Ind_proc p1 Pc Pfun.
  Proof.
    move=> m1 m2 fn f vargs vargs' s1 vm2 vres vres' Hget Hca Hw _ Hc Hres Hcr.
    have [fd2 [Hget2 /=]]:= all_checked Hget.
    rewrite eq_refl /=;case: ifP => // /andP[]/eqP htyin /eqP htyout.
    apply:add_finfoP;apply:rbindP => r1;apply:add_iinfoP => Hcparams.
    apply:rbindP => r2 Hcc;apply: rbindP => r3;apply: add_iinfoP => Hcres _.
    move=> vargs2 Hvargs2.
    have [vs2 htr hall2]:= mapM2_truncate_val Hca Hvargs2.
    move: Hw;rewrite (write_vars_lvals gd)=> /(check_lvalsP Hcparams).
    move=> /(_ _ _ eq_alloc_empty hall2) [vm3 /= [Hw2 Hvm3]].
    have [vm4 /= [Hvm4 Hsc2]]:= Hc _ _ _ _ _ Hvm3 Hcc.
    have /(_ {| emem := emem s1; evm := vm2 |} vm4 Hvm4) := check_esP Hcres.
    move=> [Hr3];rewrite sem_pexprs_get_var => /(_ _ Hres) [vres1' /= []].
    rewrite sem_pexprs_get_var => H1 H2.
    have [vs3 ??]:= mapM2_truncate_val Hcr H2.
    econstructor;split;eauto.
    econstructor;eauto.
    + by rewrite -htyin; eauto.
    + by rewrite (write_vars_lvals gd).
    by rewrite -htyout.
  Qed.

  Lemma alloc_callP_aux f mem mem' va vr:
    sem_call p1 mem f va mem' vr ->
    exists vr', sem_call p2 mem f va mem' vr' /\ List.Forall2 value_uincl vr vr'.
  Proof.
    move=>
      /(@sem_call_Ind p1 Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
            Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
    move=> H;apply H.
    apply List_Forall2_refl;apply value_uincl_refl.
  Qed.

End PROOF.

Lemma alloc_callP p1 p2 (H: check_prog p1 p2 = ok tt) f mem mem' va vr:
    sem_call p1 mem f va mem' vr ->
    exists vr', sem_call p2 mem f va mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof.
  move: H;rewrite /check_prog;case: eqP => // heq hc.
  by apply alloc_callP_aux.
Qed.

Lemma alloc_funP_eq p fn f f' m1 vargs vargs' vres vres' s1 s2:
  check_fundef (fn, f) (fn, f') tt = ok tt ->
  mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
  write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
  sem p s1 (f_body f) s2 ->
  mapM (fun x : var_i => get_var (evm s2) x) (f_res f) = ok vres ->
  mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
  exists s1' vm2 vres1 vres1',
   [ /\  mapM2 ErrType truncate_val f'.(f_tyin) vargs' = ok vargs,
    write_vars (f_params f') vargs {| emem := m1; evm := vmap0 |} = ok s1',
    sem p s1' (f_body f') (Estate (emem s2) vm2),
    mapM (fun x : var_i => get_var vm2 x) (f_res f') = ok vres1 &
    List.Forall2 value_uincl vres' vres1' /\
    mapM2 ErrType truncate_val f'.(f_tyout) vres1 = ok vres1'
    ].
Proof. by apply alloc_funP_eq_aux. Qed.

End MakeCheckAlloc.*)

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

  Lemma valid_rm m id : valid (rm_id m id) (Ms.remove (mid m) id).
  Proof.
    move=> x id';rewrite Ms.removeP;case:eqP => [<- | ].
    + rewrite /rm_id; case Heq: ((_).[id])%ms => [xid|].
      + rewrite M.removeP;case:ifPn => //= /eqP ne;split => //.
        by rewrite (mvalid m x id) Heq => -[?];subst x.
      by split=>//;rewrite (mvalid m x id) Heq.
    move=> Hne; rewrite /rm_id; case Heq: ((_).[id])%ms => [xid|].
    + rewrite M.removeP;case:ifPn => //= /eqP Hx.
      + subst xid; split => //.
        by move: Heq; rewrite -(mvalid m x id) -(mvalid m x id') => -> [] /Hne.
      by apply mvalid.
    by apply mvalid.
  Qed.

  Definition remove m id := mkT (valid_rm m id).

  Lemma removeP m id x' :
    get (remove m id) x' =
      match get m x' with
      | Some id' => if id == id' then None else Some id'
      | None     => None
      end.
  Proof.
    rewrite /remove /get /=.
    rewrite /rm_id;case Heq: ((mid m).[id])%ms => [x | ].
    + rewrite M.removeP;case:ifPn => /eqP Hx.
      + subst x;case Heqx: M.get => [id' | ]=> //.
        by move:Heq;rewrite -mvalid Heqx => -[->];rewrite eq_refl.
      case Heqx: M.get => [id' | ]=> //.
      case:ifPn=> // /eqP ?;subst id'.
      by move: Heqx;rewrite mvalid Heq => -[]/Hx.
    case Heqx: M.get => [id' | ]=> //.
    case:ifPn=> // /eqP ?;subst id'.
    by move: Heqx;rewrite mvalid Heq.
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

  Definition bool_dec (b:bool) : {b} + {~~b} :=
    if b as b0 return ({b0} + {~~ b0}) then left (erefl true)
    else right (erefl true).

  Definition vsubtype x y := subtype (vtype x) (vtype y).

  Definition vsubtypeP x y := bool_dec (vsubtype x y).

  Definition mset_valid (mvar: Mvar.t var) (mset:Sv.t) :=
    forall x id, Mvar.get mvar x = Some id -> Sv.In x mset /\ vsubtype x id.

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
    + by move=> [?];subst; split=> //;SvD.fsetdec.
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
    if vsubtypeP x id is left h then add m x id h
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
     if vsubtype x id && (x == y) then Some id else get m y.
  Proof.
    rewrite /addc;case: vsubtypeP => [ heq | /negbTE -> //].
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
      have : vsubtype p.1 p.2.
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
    have :
      (forall p, p \in Mvar.elements (merge_aux m1 m2) -> vsubtype p.1 p.2).
    + move=> p /Mvar.elementsP -/merge_auxP ?.
      have : get m1 p.1 = Some p.2 \/ get m2 p.1 = Some p.2 by intuition.
      by move=> [] /svalid [].
    elim : Mvar.elements (empty_s _) => //= -[x idx] l Hl m Hp Hm.
    apply Hl;first by move=> p hin;apply Hp;rewrite in_cons hin orbT.
    move:Hm;rewrite /f /P /addc /=.
    case: vsubtypeP => [? | ].
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

  Definition check_v xi1 xi2 (m:M.t) : cexec (M.t) :=
    let x1 := xi1.(v_var) in
    let x2 := xi2.(v_var) in
    if M.vsubtypeP x1 x2 is left h then
      match M.get m x1 with
      | None     =>
        if Sv.mem x1 (M.mset m)
        then cerror (Cerr_varalloc xi1 xi2 "variable already set") 
        else cok (M.set m x1 x2 h)
      | Some x2' =>
        if x2 == x2' then cok m
        else cerror (Cerr_varalloc xi1 xi2 "variable mismatch")
      end
    else cerror (Cerr_varalloc xi1 xi2 "type mismatch").

  Fixpoint check_e_eval (e1 e2:pexpr) (m:M.t) : cexec M.t :=
    let err _ := cerror (Cerr_neqexpr e1 e2 salloc) in
    match e1, e2 with
    | Pconst n1, Pconst n2 =>
      if n1 == n2 then cok m else err tt
    | Pbool  b1, Pbool  b2 =>
      if b1 == b2 then cok m else err tt
    | Parr_init n1, Parr_init n2 =>
      if n1 == n2 then cok m else err tt
    | Pvar   x1, Pvar   x2 => check_v x1 x2 m
    | Pglobal g1, Pglobal g2 =>
      if g1 == g2 then cok m else err tt
    | Pget w1 x1 e1, Pget w2 x2 e2 =>
      if w1 == w2 then check_v x1 x2 m >>= check_e_eval e1 e2 else err tt
    | Pload w1 x1 e1, Pload w2 x2 e2 =>
      if w1 == w2 then check_v x1 x2 m >>= check_e_eval e1 e2 else err tt
    | Papp1 o1 e1, Papp1 o2 e2 =>
      if o1 == o2 then check_e_eval e1 e2 m
      else cerror (Cerr_neqop1 o1 o2 salloc)
     | Papp2 o1 e11 e12, Papp2 o2 e21 e22 =>
      if o1 == o2 then check_e_eval e11 e21 m >>= check_e_eval e12 e22
      else cerror (Cerr_neqop2 o1 o2 salloc)
    | PappN o1 es1, PappN o2 es2 =>
      if o1 == o2
      then fold2 (Cerr_fold2 "allocation: check_e (appN)") check_e_eval es1 es2 m
      else cerror (Cerr_neqopN o1 o2 salloc)
    | Pif t e e1 e2, Pif t' e' e1' e2' =>
      if t == t' then
        check_e_eval e e' m >>= check_e_eval e1 e1' >>= check_e_eval e2 e2'
      else err tt
    | _, _ => err tt
    end.

  
  Definition check_e (e1 e2 : pexpr) (m : M.t) : cexec (M.t * leak_e_tr) :=
    Let rs := check_e_eval e1 e2 m in
    cok (rs, LT_id).

  Definition check_var (x1 x2:var) m (h:M.vsubtype x1 x2): cexec (M.t) :=
    cok (M.set m x1 x2 h).

  Definition check_varc (xi1 xi2:var_i) m : cexec (M.t) :=
    let x1 := xi1.(v_var) in
    let x2 := xi2.(v_var) in
    if M.vsubtypeP x1 x2 is left h then check_var m h
    else cerror (Cerr_varalloc xi1 xi2 "type mismatch").

  Definition is_Pvar (e:option (stype * pexpr)) :=
    match e with
    | Some (ty, Pvar x) => Some (ty,x)
    | _ => None
    end.

  Lemma is_PvarP e ty x : is_Pvar e = Some (ty,x) -> e = Some (ty, Pvar x).
  Proof. by case: e => //= -[? []] //= v [<- <-]. Qed.

  Definition check_lval_eval (e2:option (stype * pexpr)) (x1 x2:lval) m : cexec M.t :=
    let err _ := cerror (Cerr_neqlval x1 x2 salloc) in
    match x1, x2 with
    | Lnone  _ t1, Lnone _ t2  =>
      if subtype t1 t2 then cok m else err tt
    | Lnone  _ t1, Lvar x      =>
      if subtype t1 x.(v_var).(vtype) then
        cok (M.remove m x.(v_var))
      else err tt
    | Lvar x1    , Lvar x2     =>
      match is_Pvar e2 with
      | Some (ty, x2') =>
        if M.vsubtypeP x1 x2 is left h then
          if (vtype x1 == ty) && (vtype x1 == vtype x2) && (x2.(v_var) == x2') then cok (M.add m x1 x2 h)
          else check_var m h
        else cerror (Cerr_varalloc x1 x2 "type mismatch")
      | _               => check_varc x1 x2 m
      end
    | Lmem w1 x1 e1, Lmem w2 x2 e2  =>
      if w1 == w2 then check_v x1 x2 m >>= check_e_eval e1 e2 else err tt
    | Laset w1 x1 e1, Laset w2 x2 e2 =>
      if w1 == w2 then check_v x1 x2 m >>= check_e_eval e1 e2 >>= check_varc x1 x2
      else err tt
    | _          , _           => err tt
    end.

  Definition check_lval  (e2:option (stype * pexpr)) (x1 x2:lval) m : cexec (M.t * leak_e_tr) :=
    Let rs := check_lval_eval e2 x1 x2 m in
    cok (rs, LT_id).

  Definition eq_alloc (r:M.t) (vm1 vm2:vmap) :=
    [/\ vm_uincl vmap0 vm2,
        (forall x, ~Sv.In x (M.mset r) -> vm1.[x] = pundef_addr x.(vtype)) &
        (forall x x', M.get r x = Some x' ->
                      eval_uincl vm1.[x] vm2.[x'])].

  Lemma eq_alloc_empty: eq_alloc M.empty vmap0 vmap0.
  Proof. by split;rewrite /vm_uincl=> *;rewrite /vmap0 !Fv.get0. Qed.

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
    apply: eval_uincl_trans; apply subtype_eval_uincl_pundef.
    by have []:= M.svalid hget.
  Qed.

  Lemma check_vP x1 x2 r re vm1 vm2 :
    check_v x1 x2 r = ok re ->
    eq_alloc r vm1 vm2 ->
    eq_alloc re vm1 vm2 /\
    (forall v1 : value,
       get_var vm1 x1 = ok v1 ->
       exists v2 : value, get_var vm2 x2 = ok v2 /\ value_uincl v1 v2).
  Proof.
    rewrite /check_v;case: M.vsubtypeP => // hsub.
    have husub : subtype (vundef_type (vtype x1)) (vtype x2).
    +  by apply (subtype_trans (subtype_vundef_type (vtype x1))).
    case Hget : M.get => [id | ].
    + case: eqP => //= ? [<-];subst id => Hea;split=>//.
      case: Hea => _ _ /(_ _ _ Hget) Hev v1 {Hget} Hget.
      case: x1 x2 hsub husub Hget Hev=> [[xt1 xn1] ii1] [[xt2 xn2] ii2] /= hsub husub.
      rewrite /get_var;apply: on_vuP => //= t -> <- /=.
      by case: (vm2.[_])%vmap => //= z' Hz';exists (pto_val z').
    case: ifPn => //= /Sv_memP Hnot [] <- [ Hvm0 Hset Huincl];split;first split=>//.
    + by move=> x;rewrite M.setP_mset => ?;apply Hset;SvD.fsetdec.
    + move=> x id;rewrite M.setP;case:eqP => [<- [<-]| Hne].
      + rewrite (Hset _ Hnot) /=.
        apply: (eval_uincl_trans (v2:= (pundef_addr (vtype x2)))).
        + by apply subtype_eval_uincl_pundef.
        by have := Hvm0 x2; rewrite Fv.get0.
      by case:ifP => // _;apply Huincl.
    move=> v1;rewrite /get_var (Hset _ Hnot) //=.
    case: x2 hsub husub (Hvm0 x2) => [[xt2 xn2] ?] /= hsub husub;rewrite Fv.get0 /= => heval.
    apply on_vuP => [ v heq| //] ?;subst v1.
    have : eval_uincl (pundef_addr (vtype x1)) vm2.[{| vtype := xt2; vname := xn2 |}].
    + by apply: eval_uincl_trans heval; apply subtype_eval_uincl_pundef.
    by rewrite heq; case: (vm2.[_]) => //= a ?; eexists;split;first by reflexivity.
  Qed.

  Section CHECK_EP.
    Context (gd: glob_decls) (vm2: vmap).

    Let P e1 : Prop :=
      ∀ e2 r re lte vm1, check_e e1 e2 r = ok (re, lte) →
      eq_alloc r vm1 vm2 →
      eq_alloc re vm1 vm2 ∧
      ∀ m v1 l1, sem_pexpr gd {| emem := m ; evm := vm1 |} e1 = ok (v1, l1) →
      ∃ v2, sem_pexpr gd {| emem := m ; evm := vm2 |} e2 = ok (v2, leak_E lte l1)  ∧ value_uincl v1 v2.

    Let Q es1 : Prop :=
      ∀ es2 r re lte vm1 err,
      fold2 err (fun e1 e2 r1 => Let rs := check_e e1 e2 r1.1 in
                            ok (rs.1, rcons r1.2 rs.2)) es1 es2 (r, [::]) = ok (re, lte) ->
      (*fold2 err check_e es1 es2 r = ok re →*)
      eq_alloc r vm1 vm2 →
      eq_alloc re vm1 vm2 ∧
      ∀ m vs1, sem_pexprs gd {| emem := m ; evm := vm1 |} es1 = ok vs1 →
               ∃ vs2, sem_pexprs gd {| emem := m ; evm := vm2 |} es2 = ok vs2 
                      /\ List.Forall2 value_uincl (unzip1 vs1) (unzip1 vs2)
                      /\ LSub (unzip2 vs1) = leak_E (LT_seq lte) (LSub (unzip2 vs2)).                

    Lemma check_e_esP : (∀ e, P e) ∧ (∀ es, Q es).
    Proof.
      apply: pexprs_ind_pair; split; subst P Q => //=.
      - move=> [] r re lte vm1 err Ht Hvm. case: Ht=> <- <- /=.
        split. auto. move=> m' vs1 [] <- /=. exists [::].
        split. auto. split. rewrite /=. auto. auto.
        move=> //=.
      - move=> e1 he1 es1 hes1 [] // e2 es2 r re lte vm1 err.
        t_xrbindP. move=> [r' lte'] [r'' lte''] ok_r' <- /= ok_re h.
        move: (he1 e2 r r'' lte'' vm1 ok_r' h). move=> {he1} [] h'' he1.
        move: (hes1 es2 r re lte vm1 err). admit.
      - move=> z [] // z2 r re lte vm1 //.
        case: ifPn. move=> /eqP <- [] <- <- Hvm. split. auto. move=> vm2' v1 l1 [] <- <- /=.
        exists z. by split. move=> /eqP H //=.
      - move=> b1 [] // b2 r re lte vm1.
        case: ifPn. move=> /eqP <- [] <- <- Hvm. split. auto. move=> vm2' v1 l1 [] <- <- /=.
        exists b1. by split. move=> /eqP H //=.
      - move=> n1 [] // n2 r re lte vm1.
        case: ifPn. move=> /eqP <- [] <- <- Hvm. split. auto. move=> vm2' v1 l1 [] <- <- /=.
        exists (Varr (WArray.empty n1)). by split. move=> /eqP H //=.
      - move=> x1 [] // x2 r re lte vm1.
        t_xrbindP. move=> m' /check_vP Hv [] <- <- Hvm.
        move: (Hv vm1 vm2 Hvm). move=> [] Hvm' Hv'. split. auto.
        move=> vm2' v1 l1. t_xrbindP. move=> v1' Hg <- <- /=.
        move: (Hv' v1' Hg). move=> [] v2 [] -> Hv'' /=. exists v2.
        by split.
      - move=> g1 [] // g2 r re lte vm1.
        case: ifPn. move=> /eqP <- [] <- <- Hvm. split. auto. move=> vm2' v1 l1.
        t_xrbindP. move=> v2 Hg <- <- /=. rewrite Hg /=. exists v2. by split.
        move=> /eqP H //=.
      - move=> sz1 x1 e1 He1 [] // sz2 x2 e2 r re lte vm1.
        case: eqP => // <-. t_xrbindP. move=> m Hcv [m' lte'] Hec [] <- <- /= Hvm.
        move: check_vP. move=> Hcv'. move: (Hcv' x1 x2 r m vm1 vm2 Hcv Hvm).
        move=> [] Hvm' {Hcv'} Hcv'. move: (He1 e2 m m' lte' vm1 Hec Hvm').
        move=> [] Hvm'' He' {He1}. split. auto. move=> vm1' v1 l1.
        apply: on_arr_varP=> n t Heqt /Hcv' [v2 []].
        rewrite /on_arr_var; case: v2 => //= n' t' -> Ht.
        t_xrbindP. move=> [yv yl] He1 z Hv sz2' /WArray.uincl_get Ha <- <- /=.
        move: (He' vm1' yv yl He1). move=> [] yv' [] -> /= Hyv.
        move: value_uincl_int. move=> Hvv. move: (Hvv yv yv' z Hyv Hv).
        move=> {Hvv} [] Hyv1 Hyv2. rewrite -Hyv1 in Hyv2. rewrite -Hyv2 in Hv.
        rewrite Hv /=. move: (Ha n' t' Ht). move=> {Ha} -> /=. exists (Vword sz2').
        by split.
      - move=> sz1 x1 e1 He1 [] // sz2 x2 e2 r re lte vm1.
        case: eqP => // ->. t_xrbindP. move=> m Hcv [m' lt'] Hce [] <- <- Hvm.
        move: check_vP. move=>Hcv'. move: (Hcv' x1 x2 r m vm1 vm2 Hcv Hvm).
        move=> [] Hvm' Hg. move: (He1 e2 m m' lt' vm1 Hce Hvm'). move=> [] Hvm'' Hec.
        split. auto. move=> vm1' v1 l1. t_xrbindP.
        move=> yv v Hg'  /value_uincl_word Hp [yv' yl'] He yv''
               /value_uincl_word Hp' w Hr <- <- /=.
        move: (Hec vm1' yv' yl' He). move=> [] v2 [] He2 Hv.
        move: (Hg v Hg'). move=> {Hg} [] v3 [] -> Hv' /=.
        move: (Hp v3 Hv'). move=> -> /=. rewrite He2 /=.
        move: (Hp' v2 Hv). move=> -> /=. rewrite Hr /=. exists (Vword w).
        by split.
      - move=> op1 e1 He1 [] // op2 e2 r re lte vm1.
        case: eqP => // <-. move=> Hce Hvm1.
        move: (He1 e2 r re lte vm1 Hce Hvm1). move=> [] Hvm' He.
        split. auto. t_xrbindP. move=> vm1' v l [yv yl] he vo Ho <- <- /=.
        move: (He vm1' yv yl he). move=> {He} [] yv2 [] -> Hyv /=.
        move: vuincl_sem_sop1. move=> Ho'. move: (Ho' op1 yv yv2 vo Hyv Ho).
        move=> -> /=. exists vo. by split.
      - move=> op1 e11 He11 e12 He12 [] // op2 e21 e22 r re lte vm1.
        case: eqP => // <-. t_xrbindP. move=> [m lt] He1 [m' lt'] He2 [] <- <- Hvm1.
        move: (He11 e21 r m lt vm1 He1 Hvm1). move=> [] Hvm1' He1'.
        move: (He12 e22 m m' lt' vm1 He2 Hvm1'). move=> [] Hvm1'' He2'.
        split. auto. t_xrbindP. move=> vm1' v l [v1' l1'] he1 [v2' l2'] he2 /=.
        move: (He1' vm1' v1' l1' he1). move=> [] v2 [] -> Hv vo Ho' <- <- /=.
        move: (He2' vm1' v2' l2' he2). move=> [] v3 [] -> Hov /=.
        move: vuincl_sem_sop2. move=> Ho''. move: (Ho'' op1 v1' v2 v2' v3 vo Hv Hov Ho').
        move=> {Ho''} -> /=. exists vo. by split.
      - move=> op1 es1 Hes1 [] // op2 es2 r re lte vm1.
        case: eqP => // <- {op2}. t_xrbindP. move=> [m lt] ok_re [] <- <- Hvm.
        move: (Hes1 es2 r m lt vm1 (Cerr_fold2 "allocation: check_e (appN)") ok_re Hvm).
        move=> [] Hvm' /= Hes. split. auto. t_xrbindP. move=> vm1' v l vs Hes' ov Ho <- <- /=.
        rewrite /sem_pexprs in Hes. move: (Hes vm1' vs Hes').
        move=> {Hes} [] vs' [] -> [] Hv Hl /=. move: vuincl_sem_opN.
        move=> Hovn. move: (Hovn op1 (unzip1 vs) ov (unzip1 vs') Ho Hv).
        move=> [] ov' -> Hv' /=. exists ov'. case: Hl=> Hl1. admit.
       move=> t e He e11 He11 e12 He12 [] // t' e2 e21 e22 r re lte vm1.
       case: eqP => // <-.
       t_xrbindP. move=> [m lt] Hce [m' lt'] Hce1 [m'' lt''] Hce2 [] <- <- Hvm.
       move: (He e2 r m lt vm1 Hce Hvm). move=> {He} [] Hvm' He'.
       move: (He11 e21 m m' lt' vm1 Hce1 Hvm'). move=> {He11} [] Hvm1' He1'.
       move: (He12 e22 m' m'' lt'' vm1 Hce2 Hvm1'). move=> {He12} [] Hvm2' He2'.
       split. auto. t_xrbindP.
       move=> vm1' v l [yv yl] he b /value_uincl_bool hb [yv' yl'] he1' [yv'' yl''] he2' tv
                   /truncate_value_uincl ht tv' /truncate_value_uincl ht' <- <- /=.
       move: (He' vm1' yv yl he). move=> [] v1' [] -> Hv1 /= {He'}.
       move: (hb v1' Hv1). move=> [] _ -> /=. move: (He1' vm1' yv' yl' he1').
       move=> [] v2' [] -> Hv2 /= {He1'}. move: (He2' vm1' yv'' yl'' he2').
       move=> [] v3' [] -> Hv3 /= {He2'}. move: (ht v2' Hv2). move=> [] vt -> Hvt /=.
       move: (ht' v3' Hv3). move=> [] vt' -> Hvt' /=. case: (b). exists vt. by split.
       exists vt'.  by split.
   Admitted.

  End CHECK_EP.

  Definition check_eP gd e1 e2 r re vm1 vm2 :=
    (check_e_esP gd vm2).1 e1 e2 r re vm1.

  Lemma vm_uincl0_set vm x (v : exec (psem_t (vtype x))) :
    vm_uincl vmap0 vm ->
    ((exists v', v = ok v') \/ v = undef_error) ->
    vm_uincl vmap0 vm.[x <- apply_undef v].
  Proof.
    move=> Hvm0 H z; case (x =P z) => [<- | /eqP Hne].
    + rewrite Fv.setP_eq /vmap0 Fv.get0 /=.
      by case: H => [[v']|] ?;subst v => //=;apply eval_uincl_undef.
    by rewrite Fv.setP_neq.
  Qed.

  Lemma eq_alloc_set x1 (v1 :exec (psem_t (vtype x1))) r x2 (v2 :exec (psem_t (vtype x2)))
            vm1 vm2 (h:M.vsubtype x1 x2) :
    eq_alloc r vm1 vm2 ->
    eval_uincl v1 v2 ->
    ((exists v', v1 = ok v') \/ (v1 = undef_error /\ vtype x1 = sbool)) ->
    eq_alloc (M.set r x1 x2 h) vm1.[x1 <- apply_undef v1]
                               vm2.[x2 <- apply_undef v2].
  Proof.
    move=> [Hvm0 Hin Hget] Hu H1.
    have H2: (exists v', v2 = ok v') \/ (v2 = undef_error /\ vtype x2 = sbool).
    + elim H1 => [[v1' ?] | [? hx1]]; subst v1.
      + by move: Hu => /=; case: v2 => //; eauto.
      move: h;rewrite /M.vsubtype hx1 => /eqP ->.
      by case: v2 Hu => /= [ | ? <-]; eauto.
    split.
    + apply vm_uincl0_set => //;intuition.
    + move=> z;rewrite M.setP_mset => Hnin.
      by rewrite Fv.setP_neq;[apply Hin|apply /eqP];SvD.fsetdec.
    move=> x id;rewrite M.setP;case:eqP => [<-[<-] | /eqP Hne].
    + rewrite !Fv.setP_eq.
      case: H1 Hu => [ [v1' ?]| [? heq1]];subst v1;
      case: H2 => [ [v2' ?]| [? heq2]];subst v2 => //=; last by rewrite heq1 heq2.
      by move: h v2'; rewrite /M.vsubtype heq1 => /eqP <-.
    case: ifPn => //= /Sv_memP Hid Hgetx.
    rewrite !Fv.setP_neq //;first by apply Hget.
    move: Hgetx;rewrite M.Mv.mvalid => Hgetx.
    by apply/eqP => ?; subst id; apply: Hid.
  Qed.

  Lemma eq_alloc_add x1 (v1:exec (psem_t (vtype x1))) r x2  vm1 vm2 (h:M.vsubtype x1 x2) :
    eq_alloc r vm1 vm2 ->
    let v2 := vm2.[x2] in
    eval_uincl v1 v2 ->
    ((exists v', v1 = ok v') \/ (v1 = undef_error /\ vtype x1 = sbool)) ->
    eq_alloc (M.add r x1 x2 h) vm1.[x1 <- apply_undef v1]
                               vm2.[x2 <- apply_undef v2].
  Proof.
    move=> [Hvm0 Hin Hget] v2 /= Hu H1.
    have H2: (exists v', v2 = ok v') \/ (v2 = undef_error /\ vtype x2 = sbool).
    + elim H1 => [[v1' ?] | [? hx1]]; subst v1.
      + by move: Hu => /=; case: v2 => //; eauto.
      move: h;rewrite /M.vsubtype hx1 => /eqP ->.
      by case: v2 Hu => /= [ | ? <-]; eauto.
    split.
    + by apply vm_uincl0_set => //;intuition.
    + move=> z;rewrite M.addP_mset => Hnin.
      by rewrite Fv.setP_neq;[apply Hin|apply /eqP];SvD.fsetdec.
    move=> x id;rewrite M.addP;case:eqP => [<-[<-] | /eqP Hne].
    + rewrite !Fv.setP_eq.
      case: H1 Hu => [ [v1' ?]| [? heq1]];subst v1;
      case: H2 => [ [v2' ->]| [-> heq2]] => //=;last by rewrite heq1 heq2.
      by move: h v2'; rewrite /M.vsubtype heq1 => /eqP <-.
    move=> hx;rewrite Fv.setP_neq //.
    case: (x2 =P id) => [? | /eqP hne];last by rewrite Fv.setP_neq //;apply Hget.
    subst;rewrite Fv.setP_eq;have := Hget _ _ hx.
    move: H2;rewrite /v2 => -[ [v' ->]| [-> ?]] /=; case : vm1.[x] => //= -[] // _.
    by case: (vtype id).
  Qed.

  Lemma check_varP r1 r1' vm1 vm2 vm1' x1 x2 v1 v2 (h:M.vsubtype x1 x2):
    eq_alloc r1 vm1 vm2 ->
    @check_var x1 x2 r1 h = ok r1' ->
    set_var vm1 x1 v1 = ok vm1' ->
    value_uincl v1 v2 ->
    exists vm2' : vmap,
      set_var vm2 x2 v2 = ok vm2' /\ eq_alloc r1' vm1' vm2'.
  Proof.
    rewrite /check_var => Hea -[<-].
    apply: set_varP; rewrite /set_var.
    + move=> vx1 hvx1 <- hu.
      have [vx1' [hv2x1 hvx1']]:= pof_val_uincl hu hvx1.
      have [vx2 -> hsub /=] := subtype_pof_val_ok h hv2x1.
      eexists;split;first reflexivity.
      have hincl: eval_uincl (ok vx1) (ok vx2).
      + by apply: (eval_uincl_trans (v2:= ok vx1')).
      by apply (eq_alloc_set h Hea hincl); eauto.
    move=> v1' Hv1' <- Hu.
    case: x1 v1' h Hv1' (h) => t1 x1 /= /eqP ?;subst t1.
    case: x2 => t2 x2 h;rewrite /M.vsubtype => /to_bool_undef ? /=;subst v1.
    move=> h0; have /eqP ? := h0; subst t2; move: Hu => /eqP.
    move=> /type_of_val_bool [? | [b ?]]; subst v2 => /=;
      eexists; (split; first reflexivity).
    + have hincl : @eval_uincl sbool sbool undef_error undef_error by done.
      apply (eq_alloc_set h Hea hincl);eauto.
    have hincl : @eval_uincl sbool sbool undef_error (ok b) by done.
    apply (eq_alloc_set h Hea hincl);eauto.
  Qed.

  Lemma check_varcP r1 r1' vm1 vm2 vm1' x1 x2 v1 v2 :
    eq_alloc r1 vm1 vm2 ->
    check_varc x1 x2 r1 = ok r1' ->
    set_var vm1 x1 v1 = ok vm1' ->
    value_uincl v1 v2 ->
    exists vm2' : vmap,
      set_var vm2 x2 v2 = ok vm2' /\ eq_alloc r1' vm1' vm2'.
  Proof.
    by rewrite /check_varc; case: M.vsubtypeP => // h; apply check_varP.
  Qed.

  Lemma eq_alloc_rm r x s vm z :
    eval_uincl (pundef_addr (vtype x)) z ->
    eq_alloc r (evm s) vm ->
    eq_alloc (M.remove r x) (evm s) vm.[x <- z].
  Proof.
    move=> Hz [Hmap0 Hinit Halloc];split.
    + move=> y;case:(x =P y) => [<-|/eqP ne].
      + by rewrite Fv.setP_eq /vmap0 Fv.get0.
      by rewrite Fv.setP_neq.
    + by move=> y /=;apply: Hinit.
    move=> x0 id; rewrite M.removeP.
    case: M.get (Halloc x0) => [id' | ] //.
    move=> /(_ _ (refl_equal _));case:ifPn => //= Hne He [?];subst id'.
    rewrite Fv.setP_neq //;by apply: contra Hne => /eqP ->.
  Qed.

  Lemma check_lvalP gd r1 r1' lt' x1 x2 e2 s1 s1' le1' vm1 v1 v2 :
    check_lval e2 x1 x2 r1 = ok (r1', lt') ->
    eq_alloc r1 s1.(evm) vm1 ->
    value_uincl v1 v2 ->
    oapp (fun te2 =>
            Let vl := sem_pexpr gd (Estate s1.(emem) vm1) te2.2 in
            truncate_val te2.1 vl.1 = ok v2) true e2 ->
    (*oapp (fun te2 =>
        sem_pexpr gd (Estate s1.(emem) vm1) te2.2 >>= truncate_val te2.1 = ok v2) true e2 ->*)
    write_lval gd x1 v1 s1 = ok (s1', le1') ->
    exists vm1',
      write_lval gd x2 v2 (Estate s1.(emem) vm1) = ok (Estate s1'.(emem) vm1', leak_E lt' le1') /\
      eq_alloc r1' s1'.(evm) vm1'.
  Proof.
    case: x1 x2 => /= [ii1 t1 | x1 | sz1 x1 p1 | sz1 x1 p1]
                      [ii2 t2 | x2 | sz2 x2 p2 | sz2 x2 p2] //=.
    + case: ifP => //= hs [] <- <- Hvm Hv H. t_xrbindP.
      move=> s' Hw <- <-. move: write_noneP. move=> Hw'.
      move: (Hw' s1 s' t1 v1 Hw). move=> [] <- [] [] u hpof.
      rewrite /write_none. have [v1' ]:= subtype_pof_val_ok hs hpof.
      move=> /(pof_val_uincl Hv) [v2' [-> ]] /=; eauto. move=> hv' Hv''.
      exists vm1. split. auto. move: (Hw' s1 s' t1 v1 Hw). move=> [] -> Hc.
      auto. subst t1;move/eqP: hs => ?;subst t2.
      move: (Hw' s1 s' sbool v1 Hw). move=> [] -> [] [] u' hpof.
      have [->|[b] ->] /=:= pof_val_undef Hv u. eauto. exists vm1. by split.
      have [->|[b] ->] /=:= pof_val_undef Hv u. eauto. exists vm1. by split.
    + case:ifP => //= hs [] <- <- Heqa Hu Happ. t_xrbindP. move=> s H <- <-.
      have [-> ]:= write_noneP H.
      rewrite /write_var /set_var => -[ [u]| ].
      + move=> /(subtype_pof_val_ok hs) [v3].
        move=> /(pof_val_uincl Hu) [z' [-> ?]] /= ?.
        eexists; split; eauto; apply eq_alloc_rm => //.
        by apply eval_uincl_undef.
      move=> [hpof ?];subst t1; case : x2 hs => -[tx2 x2] ii2 /= /eqP ?;subst tx2.
      have [->|[b] ->] /= := pof_val_undef Hu hpof; eexists;(split; first by eauto);
      apply eq_alloc_rm => //.   
    + rewrite /write_var=> Hc Hvm1 Hv Happ. t_xrbindP. 
      move=> s vm1' Hset [<-] /= <- <-. 
      move: Hc;case: is_Pvar (@is_PvarP e2).
      + move=> [ty x] /(_ _ _ (refl_equal _)) ?;subst e2.
        case: M.vsubtypeP => // ht; case:ifPn.
        move=> /andP[]/andP[]/eqP ? /eqP heqt /eqP;subst ty.
        move: x1 x2 x heqt ht Hset Happ=> [[xt1 xn1] ii1] [[xt2 xn2] ii2] [x ii] /=.
        set x1 := {| vname := xn1 |}; set x2 := {| vname := xn2 |}.
        move=> hteq ht hset. t_xrbindP.
        move=> [v2'' l2'] v2' Happ [] <- <- htr Hx2 [] H1 H2;subst => /=.
        apply: set_varP hset => /=;rewrite /set_var.
        + move=> v1' Hv1 ?;subst.
          apply: on_vuP Happ => //.
          move=> v2_ hv2_ ?;subst.
          have ?:= truncate_pto_val htr;subst v2.
          rewrite pof_val_pto_val /=;eexists;split;first reflexivity.
          have /= := @eq_alloc_add x1 (ok v1') r1 x2 (evm s1) vm1 ht Hvm1.
          rewrite hv2_ /= /pval_uincl => H;apply H;last by eauto.
          by apply (value_uincl_pof_val Hv1 Hv).
        move=> /= hniw hv1 ?;subst; rewrite hniw /=.
        apply: on_vuP Happ => //.
        move=> v2_ heq ?;subst;have ?:= truncate_pto_val htr;subst v2.
        rewrite pof_val_pto_val /=;eexists;split;first reflexivity.
        have /= := @eq_alloc_add x1 (pundef_addr xt2) r1 x2 (evm s1) vm1 ht Hvm1.
        rewrite heq /= apply_undef_pundef_addr=> H;apply H.
        + by apply eval_uincl_undef.
        by move /eqP: hniw => ->;right. admit.
       t_xrbindP. move=> h m hc;have [vm2' [-> /= hb]]:= check_varcP Hvm1 hc Hset Hv;eauto.
       move=> [] <- <- /=. by exists vm2'.
    + case: eqP => // -> /=. t_xrbindP.
      move=> r2 Hcv [r2' lt2'] Hce [] <- <- /= Hvm1 Hv Happ.
      move=> vx v Hg /value_uincl_word Hvx [yv yl] /= He vx'
             /value_uincl_word Hvx' ve /value_uincl_word Hve m Hw <- <-.
      move: check_vP. move=> Hcv'. move: (Hcv' x1 x2 r1 r2 (evm s1) vm1 Hcv Hvm1).
      move=> [] Hvm' Hg' {Hcv'}. move: (Hg' v Hg). move=> {Hg'} [] v' [] -> Hvv' /=.
      move: (Hvx v' Hvv'). move=> -> /=. move: check_eP.
      move=> Hce'. move: (Hce' gd p1 p2 r2 r2' lt2' vm1 (evm s1) Hce Hvm').
      move=> [] Hvm'' He' {Hce'}.
      replace s1 with {| emem := s1.(emem); evm := s1.(evm) |} in He.
      move: (He' s1.(emem) yv yl He). move=> {He'} [] yv' [] -> Hyv /=.
      move: (Hvx' yv' Hyv). move=> -> /=. move: (Hve v2 Hv). move=> -> /=.
      rewrite Hw /=. exists vm1. by split. admit.
    case: eqP => // -> /=. t_xrbindP.
    move=> r2 Hcv [r2' lt2'] Hce r2'' Hvc [] <- <- /= Hvm1 Hv Happ.
    apply: on_arr_varP => n t Htx;rewrite /on_arr_var /=. t_xrbindP.
    move=> Hg [yv yl] He i /value_uincl_int Hi w /value_uincl_word Hw a Ha s Hs <- <- /=.
    move: check_vP. move=> Hcv'. move: (Hcv' x1 x2 r1 r2 (evm s1) vm1 Hcv Hvm1).
    move=> [] Hvm' Hg' {Hcv'}. move: (Hg' (Varr t) Hg). move=> {Hg'} [] v' [] -> /=.
    case: (v') => //=. move=> len t1' Hwa'.
    move: check_eP. move=> Hce'. move: (Hce' gd p1 p2 r2 r2' lt2' vm1 (evm s1) Hce Hvm').
    move=> [] Hvm'' He' {Hce'}. replace s1 with {| emem := s1.(emem); evm := s1.(evm) |} in He.
    move: (He' s1.(emem) yv yl He). move=> {He'} [] yv' [] -> Hyv /=.
    move: (Hi yv' Hyv). move=> [] /= Hyv1 -> /=. move: (Hw v2 Hv). move=> -> /=.
    have [t2' [-> Ht2' /=]]:= WArray.uincl_set Hwa' Ha.
    have Hu: value_uincl (Varr a) (Varr t2') := Ht2'.
    move: check_varcP. move=> H.
    move: (H r2' r2'' (evm s1) vm1 s x1 x2 (Varr a) (Varr t2') Hvm'' Hvc Hs Hu).
    move=> [] vm1' [] -> Hvm2 /=.  exists vm1'. by split. admit.
  Admitted.

End CBAreg.

Module CheckAllocReg :=  MakeCheckAlloc CBAreg.
