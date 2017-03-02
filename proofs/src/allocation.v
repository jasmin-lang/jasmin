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



(*Fixpoint val_uincl2 (t1 t2:stype) : st2ty t1 -> st2ty t2 -> Prop := 
  match t1 return (st2ty t1 -> st2ty t2 -> Prop) with
  | sword => 
    match t2 return (st2ty sword -> st2ty t2 -> Prop) with
    | sword => fun w1 w2 => w1 = w2
    | _     => fun _ _ => False
    end
  | sbool =>
    match t2 return (st2ty sbool -> st2ty t2 -> Prop) with
    | sbool => fun b1 b2 => b1 = b2
    | _     => fun _ _ => False
    end
  | t11 ** t12 =>
    match t2 return (st2ty (t11 ** t12) -> st2ty t2 -> Prop) with
    | t21 ** t22 =>  
      fun v1 v2 => @val_uincl2 t11 t21 v1.1 v2.1 /\ @val_uincl2 t12 t22 v1.2 v2.2
    | _ => fun _ _ => False
    end
  | sarr n1 =>
    match t2 return (st2ty (sarr n1) -> st2ty t2 -> Prop) with
    | sarr n2 => 
      fun (t1:Array.array n1 word) (t2:Array.array n2 word) => 
        n1 = n2 /\
        forall i v : word, Array.get t1 i = ok v -> Array.get t2 i = ok v
    | _     => fun _ _ => False
    end
  end.

Lemma val_uincl2P t (v1 v2:st2ty t): val_uincl v1 v2 <-> val_uincl2 v1 v2.
Proof.
  elim: t v1 v2 => //= [t1 Ht1 t2 Ht2 | p] v1 v2;first by rewrite Ht1 Ht2.
  split=> [|[]];auto.
Qed.
*)

(*
Definition eval_rval (s:estate) (x:rval) : result _ (seq value) :=
  match x with
  | Rnone _   => ok [::]
  | Rvar _    => ok [::]
  | Rmem x e  => 
    let vx := get_var (evm s) x in 
    Let ve := sem_pexpr s e in
    ok [:: vx; ve]
  | Raset x e =>
    let vx := get_var (evm s) x in 
    Let ve := sem_pexpr s e in
    ok [:: vx; ve]
  end.

Definition eval_rvals s xs := 
  Let vs := mapM (eval_rval s) xs in ok (flatten vs).
*)

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
  
  Parameter check_rval : rval  -> rval  -> M.t -> cexec M.t.

  Parameter check_rvals : rvals  -> rvals  -> M.t -> cexec M.t.

  Parameter eq_alloc : M.t -> vmap -> vmap -> Prop.

  Parameter eq_alloc_empty: forall vm, all_empty_arr vm -> eq_alloc M.empty vm vm.

  Parameter eq_alloc_incl: forall r1 r2 vm vm',
    M.incl r2 r1 -> 
    eq_alloc r1 vm vm' -> 
    eq_alloc r2 vm vm'.

  Parameter check_eP: forall e1 e2 r re s vm, 
    check_e e1 e2 r = ok re ->
    eq_alloc r s.(evm) vm ->
    eq_alloc re s.(evm) vm /\
    forall v1,  sem_pexpr s e1 = ok v1 ->
    exists v2, sem_pexpr (Estate s.(emem) vm) e2 = ok v2 /\ value_uincl v1 v2.

  Parameter check_rvalP: forall x1 x2 v1 v2 r1 r2 s1 s2 vm1, 
    check_rval x1 x2 r1 = ok r2 ->
    eq_alloc r1 s1.(evm) vm1 ->
    write_rval x1 v1 s1 = ok s2 ->
    value_uincl v1 v2 ->
    exists vm2, 
      write_rval x2 v2 (Estate s1.(emem) vm1) = ok (Estate s2.(emem) vm2) /\
      eq_alloc r2 s2.(evm) vm2.

  Parameter check_rvalsP: forall xs1 xs2 vs1 vs2 r1 r2 s1 s2 vm1, 
    check_rvals xs1 xs2 r1 = ok r2 ->
    eq_alloc r1 s1.(evm) vm1 ->
    write_rvals s1 xs1 vs1 = ok s2 ->
    List.Forall2 value_uincl vs1 vs2 ->
    exists vm2, 
      write_rvals (Estate s1.(emem) vm1) xs2 vs2 = ok (Estate s2.(emem) vm2) /\
      eq_alloc r2 s2.(evm) vm2.

(* 

    eq_alloc r2 s.(evm) vm /\
    forall vs1, eval_rval s x1 = ok vs1 ->
    exists vs2, 
      eval_rval (Estate s.(emem) vm) x2 = ok vs2 /\ 
      List.Forall2 value_uincl vs1 vs2.
 
  Parameter check_rval_rP: forall x1 x2 v1 v2 vs1 vs2 r1 r2 s0 s0' s1 s2 vm1, 
    check_rval_r x1 x2 r1 = ok r2 ->
    eq_alloc r1 s1.(evm) vm1 ->
    eval_rval s0 x1 = ok vs1 -> eval_rval s0' x2 = ok vs2 -> 
    List.Forall2 value_uincl vs1 vs2 ->
    value_uincl v1 v2 ->
    write_rval_aux s0 x1 v1 s1 = ok s2 ->
    exists vm2, 
      write_rval_aux s0' x2 v2 (Estate s1.(emem) vm1) = ok (Estate s2.(emem) vm2) /\
      eq_alloc r2 s2.(evm) vm2.
*)
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

(*Definition check_rval x1 x2 r := 
  check_rval_e x1 x2 r >>= check_rval_r x1 x2.

Definition check_rv_error := Cerr_fold2 "allocation:check_rvals".

Definition check_rvals_e := fold2 check_rv_error check_rval_e.

Definition check_rvals_r := fold2 check_rv_error check_rval_r.

Definition check_rvals xs1 xs2 r :=
  check_rvals_e xs1 xs2 r >>= check_rvals_r xs1 xs2. *)

Definition check_var x1 x2 r := check_rval (Rvar x1) (Rvar x2) r.

Definition check_vars xs1 xs2 r := check_rvals (map Rvar xs1) (map Rvar xs2) r.

Fixpoint check_i iinfo i1 i2 r := 
  match i1, i2 with
  | Cassgn x1 _ e1, Cassgn x2 _ e2 => 
    add_iinfo iinfo (check_e e1 e2 r >>= check_rval x1 x2)
  | Copn xs1 o1 es1, Copn xs2 o2 es2 =>
    if o1 == o2 then
      add_iinfo iinfo (check_es es1 es2 r >>= check_rvals xs1 xs2)
    else cierror iinfo (Cerr_neqop o1 o2 salloc)
  | Ccall _ x1 f1 arg1, Ccall _ x2 f2 arg2 => 
    if f1 == f2 then 
      add_iinfo iinfo (check_es arg1 arg2 r >>= check_rvals x1 x2)
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

(* TODO: MOVE THIS *)

Lemma get_fundef_cons fnd p fn: 
  get_fundef (fnd :: p) fn = if fn == fnd.1 then Some fnd.2 else get_fundef p fn.
Proof.
  rewrite /get_fundef;case:ifP => /=; by case: ifPn => //= ?;rewrite ltnS => ->.
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
    forall i2 ii r1 c2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_cmd ii c1 c2 r1 = ok r2 -> M.incl r1 r2 ->
    exists vm2, eq_alloc r2 (evm s2) vm2 /\ 
      sem_for p2 i2 vs (Estate (emem s1) vm1) c2 (Estate (emem s2) vm2).

  Let Pfun (mem1:Memory.mem) fd1 vargs1 (mem1':Memory.mem) vres :=
    forall fn fd2, check_fundef (fn, fd1) (fn, fd2) tt = ok tt ->
    forall mem2 mem2' vargs2, List.Forall2 value_uincl vargs1 vargs2 ->
       sem_call p2 mem2 fd2 vargs2 mem2' vres.

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
(*
  Lemma write_rval_eval s0 x v s1 s2 :
    write_rval_aux s0 x v s1 = ok s2 ->
    exists vs,  eval_rval s0 x = ok vs.
  Proof.
    case: x => [ii| x | x e | x e] /=.
    + by move=> _;exists [::].
    + by move=> _;exists [::].
    + by apply: rbindP => wx ?;apply: rbindP => we;apply: rbindP => ve /= -> /= _ _;eauto.
    apply: on_arr_varP => n t ?;apply rbindP => i;apply: rbindP => ve -> /= _ _;eauto.
  Qed.

  Lemma check_rvalP x1 x2 v1 v2 r1 r2 s1 s2 vm1 :
    check_rval x1 x2 r1 = ok r2 ->
    eq_alloc r1 s1.(evm) vm1 ->
    value_uincl v1 v2 ->
    write_rval x1 v1 s1 = ok s2 ->
    exists vm2, 
      write_rval x2 v2 (Estate s1.(emem) vm1) = ok (Estate s2.(emem) vm2) /\
      eq_alloc r2 s2.(evm) vm2.
  Proof.
    apply: rbindP => r1' /check_rval_eP Hce Hcr /Hce [] Hvm1 Hvs1 Hv.
    rewrite /write_rval=> Hwr;have [vs1 Hevs1]:= write_rval_eval Hwr.
    have [vs2 [Hevs2 Hvs]] := Hvs1 _ Hevs1.
    apply (check_rval_rP Hcr Hvm1 Hevs1 Hevs2 Hvs Hv Hwr).
  Qed.

  Lemma eval_rvals_cons s x1 xs1 vs1 : 
    eval_rvals s (x1 :: xs1) = ok vs1 ->
    exists vs2 vs3,
    [/\ eval_rval s x1 = ok vs2,
        eval_rvals s xs1 = ok vs3 & vs1 = vs2 ++ vs3].
  Proof.
    rewrite /eval_rvals;apply rbindP=> vs /=.
    apply: rbindP => y H1; apply: rbindP => ys H2 [] <- [] <-.
    by exists y, (flatten ys);rewrite H2.
  Qed.
*)
(*
(*TODO MOVE *)
Lemma List_Forall2_cat A B (P:A -> B -> Prop) l1 l2 l1' l2' : 
  List.Forall2 P l1 l2 -> List.Forall2 P l1' l2' -> List.Forall2 P (l1 ++ l1') (l2 ++ l2').
Proof.
  by elim => // x1 x2 {l1 l2} l1 l2 ? ? Hrec /Hrec ? /=;constructor.
Qed.

  Lemma check_rvals_eP: forall xs1 xs2 r1 r2 s vm, 
    check_rvals_e xs1 xs2 r1 = ok r2 ->
    eq_alloc r1 s.(evm) vm ->
    eq_alloc r2 s.(evm) vm /\
    forall vs1, eval_rvals s xs1 = ok vs1 ->
    exists vs2, 
      eval_rvals (Estate s.(emem) vm) xs2 = ok vs2 /\ 
      List.Forall2 value_uincl vs1 vs2.
  Proof.
    elim => [ | x1 xs1 Hrec] [ | x2 xs2] //= r1 r2 s vm.
    + by move=> [] <- ?;split=>//= vs1 [<-];exists [::];split.
    apply: rbindP => r1' /check_rval_eP He /Hrec Hes /He [] /Hes [] H1 H2 H3.
    split=> // vs1 /eval_rvals_cons [y [ys]] [] /H3 [vs2 [Hvs2 Fvs2]].
    move=> /H2 [vs3 [Hvs3 Fvs3]] ->;exists (vs2++vs3);split.
    + by rewrite /eval_rvals /= Hvs2 /=;apply: rbindP Hvs3 => ? -> [] <-.
    by apply List_Forall2_cat.
  Qed.

  Lemma check_rvals_rP: forall xs1 xs2 v1 v2 vs1 vs2 r1 r2 s0 s0' s1 s2 vm1, 
    check_rvals_r xs1 xs2 r1 = ok r2 ->
    eq_alloc r1 s1.(evm) vm1 ->
    eval_rvals s0 xs1 = ok vs1 -> eval_rvals s0' xs2 = ok vs2 -> 
    List.Forall2 value_uincl vs1 vs2 ->
    List.Forall2 value_uincl v1 v2 ->
    (fold2 ErrType (write_rval_aux s0) xs1) v1 s1 = ok s2 ->
    exists vm2, 
      (fold2 ErrType (write_rval_aux s0') xs2) v2 (Estate s1.(emem) vm1) = 
         ok (Estate s2.(emem) vm2) /\
      eq_alloc r2 s2.(evm) vm2.
  Proof.
    elim => [ | x1 xs1 Hrec] [ | x2 xs2] //= v1 v2 vs1 vs2 r1 r2 s0 s0' s1 s2 vm1.
    + by move=> [] <- ???? [ [<-] | //]; exists vm1.
    apply:rbindP => r1' /check_rval_rP He /Hrec Hes /He{He}He.  
    move=> /eval_rvals_cons [y1 [ys1]] [] Hy1 Hys1 ?;subst.
    move=> /eval_rvals_cons [y2 [ys2]] [] Hy2 Hys2 ?;subst.
Search _ List.Forall2.
 /He{He}He /He{He}He .
      
  Lemma check_rvalsP xs1 xs2 v1 v2 r1 r2 s1 s2 vm1 :
    check_rvals xs1 xs2 r1 = ok r2 ->
    eq_alloc r1 s1.(evm) vm1 ->
    List.Forall2 value_uincl v1 v2 ->
    write_rvals s1 xs1 v1 = ok s2 ->
    exists vm2, 
      write_rvals (Estate s1.(emem) vm1) xs2 v2 = ok (Estate s2.(emem) vm2) /\
      eq_alloc r2 s2.(evm) vm2.
  Proof.
    apply: rbindP => r1';rewrite /write_rvals.

   fold2 check_rv_error check_rval_e xs1 xs2 r1 = ok r1' ->

   fold2 check_rv_error check_rval_r xs1 xs2 r1'' = ok r2 ->
   eq_alloc r1 (evm s1) vm1 ->
   List.Forall2 value_uincl v1 v2 ->
   fold2 ErrType (write_rval_aux s1) xs1 v1 s1 = ok s2 ->
   exists vm2 : vmap,
     fold2 ErrType (write_rval_aux {| emem := emem s1; evm := vm1 |}) xs2 v2
       {| emem := emem s1; evm := vm1 |} =
     ok {| emem := emem s2; evm := vm2 |} /\ eq_alloc r2 (evm s2) vm2

Print write_rvals.
    apply: rbindP => r1' /check_rval_eP Hce Hcr /Hce [] Hvm1 Hvs1 Hv.
    rewrite /write_rval=> Hwr;have [vs1 Hevs1]:= write_rval_eval Hwr.
    have [vs2 [Hevs2 Hvs]] := Hvs1 _ Hevs1.
    apply (check_rval_rP Hcr Hvm1 Hevs1 Hevs2 Hvs Hv Hwr).
  Qed.


 Parameter check_rval_rP: forall x1 x2 v1 v2 vs1 vs2 r1 r2 s0 s1 s2 vm1, 
    check_rval_r x1 x2 r1 = ok r2 ->
    eq_alloc r1 s1.(evm) vm1 ->
    eval_rval s0 x1 = ok vs1 -> eval_rval s0 x2 = ok vs2 -> 
    List.Forall2 value_uincl vs1 vs2 ->
    value_uincl v1 v2 ->
    write_rval_aux s0 x1 v1 s1 = ok s2 ->
    exists vm2, 
      write_rval_aux s0 x2 v2 (Estate s1.(emem) vm1) = ok (Estate s2.(emem) vm2) /\
      eq_alloc r2 s2.(evm) vm2.
 
    move=> /Hvs1 [vs2].


 write_rval x1 v1 s1 = ok s2
*)
(* TODO MOVE *)
Lemma add_iinfoP A (a:A) (e:cexec A) ii (P:Prop):  
  (e = ok a -> P) -> 
  add_iinfo ii e = ok a -> P.
Proof. by case: e=> //= a' H [] Heq;apply H;rewrite Heq. Qed.

  Local Lemma Hassgn s1 s2 x tag e :
    Let v := sem_pexpr s1 e in write_rval x v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn x tag e) s2.
  Proof.
    apply: rbindP => v He Hw ii r1 [] //= x2 tag2 e2 r2 vm1 Hvm1.
    apply: add_iinfoP.
    apply: rbindP => r1' /check_eP -/(_ _ _ Hvm1) [Hr1'] /(_ _ He) [v2 [He2 Hu2]].
    move=> /check_rvalP -/(_ _ _ _ _ _ Hr1' Hw Hu2) [vm2] [Hwv Hvm2].
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
    in write_rvals s1 xs x = Ok error s2 -> Pi_r s1 (Copn xs o es) s2.
  Proof.
    apply: rbindP => v.
    apply: rbindP => ves He Ho Hw ii r1 [] //= xs2 o2 es2 r2 vm1 Hvm1.
    case:ifPn => //= /eqP <-.
    apply: add_iinfoP.
    apply: rbindP => r1' /check_esP -/(_ _ _ Hvm1) [Hr1'] /(_ _ He) [v2 [He2 Hu2]].
    have [v' [Ho' Hv] ]:= vuincl_sem_opn Hu2 Ho.
    move=> /check_rvalsP -/(_ _ _ _ _ _ Hr1' Hw Hv) [vm2] [Hwv Hvm2].
    by exists vm2;split=>//;constructor;rewrite He2 /= Ho'.
  Qed.

  Local Lemma Hif_true s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem p1 s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    apply: rbindP => ve Hve Hto _ Hc1 ii r1 [] //= e' c1' c2' r2 vm1 Hvm1.
    apply: rbindP => r1';apply: add_iinfoP => /check_eP -/(_ _ _ Hvm1) [] Hr1'.
    move=> /(_ _ Hve) [ve' [Hve' /value_uincl_bool -/(_ _ Hto)]] [??];subst.
    apply: rbindP => r3 Hr3;apply: rbindP => r4 Hr4 [] <-.
    have [vm2 [Hvm2 Hsem]]:= Hc1 ii _ _ _ _ Hr1' Hr3;exists vm2;split.
    + by eapply eq_alloc_incl;eauto;apply M.merge_incl_l.
    by apply Eif_true => //;rewrite Hve'.
  Qed.

  Local Lemma Hif_false s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error false ->
    sem p1 s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    apply: rbindP => ve Hve Hto _ Hc1 ii r1 [] //= e' c1' c2' r2 vm1 Hvm1.
    apply: rbindP => r1';apply: add_iinfoP => /check_eP -/(_ _ _ Hvm1) [] Hr1'.
    move=> /(_ _ Hve) [ve' [Hve' /value_uincl_bool -/(_ _ Hto)]] [??];subst.
    apply: rbindP => r3 Hr3;apply: rbindP => r4 Hr4 [] <-.
    have [vm2 [Hvm2 Hsem]]:= Hc1 ii _ _ _ _ Hr1' Hr4;exists vm2;split.
    + by eapply eq_alloc_incl;eauto;apply M.merge_incl_r.
    by apply Eif_false => //;rewrite Hve'.
  Qed.

  Lemma loopP ii check_c n r1 r2:
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
    
(* TODO Move this *)
Axiom Loop_nbP : Loop.nb = (Loop.nb .-1).+1.

  Local Lemma Hwhile_true s1 s2 s3 e c:
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem p1 s1 c s2 -> Pc s1 c s2 ->
    sem_i p1 s2 (Cwhile e c) s3 -> Pi_r s2 (Cwhile e c) s3 -> 
    Pi_r s1 (Cwhile e c) s3.
  Proof.
    apply: rbindP => ve Hve Hto _ Hc _ Hrec ii r1 [] //= e2 c2 r2 vm1 Hvm1.
    move=> Hloop;have [r2' []]:= loopP Hloop;apply: rbindP => r3;apply: add_iinfoP.
    move=> He Hc0; move: (Hc0) => /Hc{Hc}Hc Hincl.
    have := eq_alloc_incl Hincl Hvm1.
    move=> /(check_eP He) [] /Hc [vm2 [Hvm2 Hc2]] /(_ _ Hve) [ve' ] [Hve' Uve] Hr2.
    have : check_i ii (Cwhile e c) (Cwhile e2 c2) r2 = ok r2.
    + by rewrite /= Loop_nbP /= He /= Hc0 /= Hr2.
    have /Hrec H := eq_alloc_incl Hr2 Hvm2.
    move=> /H [vm3] [] ? Hw;exists vm3;split => //.
    apply: Ewhile_true;eauto;rewrite Hve' /=.
    by have [_ ->]:= value_uincl_bool Uve Hto.
  Qed.

  Local Lemma Hwhile_false s e c:
    Let x := sem_pexpr s e in to_bool x = Ok error false ->
    Pi_r s (Cwhile e c) s.
  Proof.
    apply: rbindP => ve Hve Hto ii r1 [] //= e2 c2 r2 vm1 Hvm1.
    move=> Hloop;have [r2' []]:= loopP Hloop;apply: rbindP => r3;apply: add_iinfoP.
    move=> He _ Hincl;move /eq_alloc_incl : (Hincl) => /(_ _ _ Hvm1) -/(check_eP He) [] Hr3.
    move=> /(_ _ Hve) [ve'] [] Hve' Uve;exists vm1;split.
    + by apply: eq_alloc_incl Hvm1.
    apply: Ewhile_false;eauto;rewrite Hve' /=.
    by have [_ ->]:= value_uincl_bool Uve Hto.
  Qed.
 
(*
  Local Lemma Hfor s1 s2 (i:var_i) d lo hi c vlo vhi :
    Let x := sem_pexpr s1 lo in to_int x = Ok error vlo ->
    Let x := sem_pexpr s1 hi in to_int x = Ok error vhi ->
    sem_for p1 i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.
  Proof.
    move=> Hlo Hhi Hc Hfor ii r1 []//= i2. [d2 [lo2 hi2 vm1 Hvm1.
 Hm /=.
    set ww := write_i _;set m' := remove_cpm _ _.
    have Hm'1 : valid_cpm (evm s1) m' by apply: valid_cpm_rm Hm.
    have Heqm: Mvar_eq m' (remove_cpm m' (Sv.union (Sv.singleton i) (write_c c))).
    + by have := remove_cpm2 m ww; rewrite /m' /ww write_i_for => ->.
    have := Hfor _ Heqm Hm'1.      
    case Heq1: const_prop => [m'' c'] /= Hsem;split.
    + by apply: valid_cpm_rm Hm;apply (@write_iP p);econstructor;eauto.
    apply sem_seq1;constructor;econstructor.
    + by apply: rbindP Hlo => v /(const_prop_eP Hm) -> /=;eauto.
    + by apply: rbindP Hhi => v /(const_prop_eP Hm) -> /=;eauto.
    done.
  Qed.

  Local Lemma Hfor_nil s i c: Pfor i [::] s c s.
  Proof. by move=> m Hm;constructor. Qed.

  Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w:Z) (ws:seq Z) c :
    write_var i w s1 = Ok error s1' ->
    sem p s1' c s2 ->
    Pc s1' c s2 ->
    sem_for p i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
  Proof.
    move => Hw Hsemc Hc Hsemf Hf m Heqm Hm.
    have Hm' : valid_cpm (evm s1') m.
    + have Hmi : Mvar_eq m (Mvar.remove m i).
      + move=> z;rewrite Mvar.removeP;case:ifPn => [/eqP <- | Hneq //]. 
        rewrite Heqm;move: (remove_cpm_spec m (Sv.union (Sv.singleton i) (write_c c)) i).
        by case: Mvar.get => // a [];SvD.fsetdec.
      have -> := valid_cpm_m (refl_equal (evm s1')) Hmi.
      by apply: remove1_cpmP Hw Hm.
    have [_ Hc']:= Hc _ Hm'.        
    have /(Hf _ Heqm) : valid_cpm (evm s2) m.
    + have -> := valid_cpm_m (refl_equal (evm s2)) Heqm.
      apply: valid_cpm_rm Hm'=> z Hz;apply: (writeP Hsemc);SvD.fsetdec. 
    by apply: EForOne Hc'.
  Qed.

  Local Lemma Hcall s1 m2 s2 ii xs fn fd args vargs vs:
        get_fundef p fn = Some fd ->
        sem_pexprs s1 args = Ok error vargs ->
        sem_call p (emem s1) fd vargs m2 vs ->
        Pfun (emem s1) fd vargs m2 vs ->
        write_rvals {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
        Pi_r s1 (Ccall ii xs fn args) s2.
  Proof.
    move=> Hfn Hargs Hcall Hfun Hvs m ii' Hm /=;split.
    + by apply: valid_cpm_rm Hm;apply (@write_iP p);econstructor;eauto.
    apply sem_seq1;constructor;econstructor;eauto.
    + by rewrite (@get_map_prog const_prop_fun) Hfn.
    + by apply const_prop_esP.
    by apply const_prop_rvsP.
  Qed.

  Local Lemma Hproc m1 m2 (fd : fundef) vargs vres : 
    (forall vm0 : vmap,
       all_empty_arr vm0 ->
       exists (s1 : estate) (vm2 : vmap),
           [/\ write_vars (f_params fd) vargs {| emem := m1; evm := vm0 |} =
               Ok error s1,
               sem p s1 (f_body fd) {| emem := m2; evm := vm2 |},
               Pc s1 (f_body fd) {| emem := m2; evm := vm2 |}
             & map (fun (x:var_i) => get_var vm2 x) fd.(f_res) = vres]) ->
    List.Forall is_full_array vres -> Pfun m1 fd vargs m2 vres.
  Proof.
    case: fd=> fi fparams fc fres. 
    move=> Hrec Hfull;constructor => // vm0 /Hrec [] s1 [] vm2 [] /= Hargs Hsem Hc Hres.
    exists s1, vm2;split => //= {Hrec}.
    + by case : const_prop.
    + have : valid_cpm (evm s1) empty_cpm by move=> x n;rewrite Mvar.get0.
      by move=> /Hc [];case: const_prop.
    by case : const_prop.  
  Qed.

  Lemma const_prop_callP fd mem mem' va vr: 
    sem_call p mem fd va mem' vr -> 
    sem_call p' mem (const_prop_fun fd) va mem' vr.
  Proof.
    apply (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

  Let Pi (i1:instr_r) := 
    forall r1 i2 r2, check_i i1 i2 r1 = Ok unit r2 ->
    forall m1 m2 vm1 vm2, sem_i (Estate m1 vm1) i1 (Estate m2 vm2) ->
    forall vm1', eq_alloc r1 vm1 vm1' ->
    exists vm2', eq_alloc r2 vm2 vm2' /\ 
     sem_i (Estate m1 vm1') i2 (Estate m2 vm2').

  Let PI (i1:instr) :=
    forall r1 i2 r2, check_I i1 i2 r1 = Ok unit r2 ->
    forall m1 m2 vm1 vm2, sem_I (Estate m1 vm1) i1 (Estate m2 vm2) ->
    forall vm1', eq_alloc r1 vm1 vm1' ->
    exists vm2', eq_alloc r2 vm2 vm2' /\ 
     sem_I (Estate m1 vm1') i2 (Estate m2 vm2').
    
  Let Pc (c1:cmd) := 
    forall r1 c2 r2, fold2 tt check_I c1 c2 r1 = Ok unit r2 ->
    forall m1 m2 vm1 vm2, sem (Estate m1 vm1) c1 (Estate m2 vm2) ->
    forall vm1', eq_alloc r1 vm1 vm1' ->
    exists vm2', eq_alloc r2 vm2 vm2' /\ 
     sem (Estate m1 vm1') c2 (Estate m2 vm2').

  Let Pf ta tr (fd1:fundef ta tr) := 
    forall fd2, check_fd fd1 fd2 ->
    forall mem mem' va va' vr, val_uincl va va' ->
    sem_call mem fd1 va mem' vr ->
    sem_call mem fd2 va' mem' vr.
  
  Let HI : forall info i, Pi i -> PI (MkI info i).
  Proof.
   move=> info1 i1 Hi r1 [info2 i2] r2.

  Let Hskip : Pc [::].
  Proof.
    move=> r1 [] //= r2 [] <- m1 m2 vm1 vm2 H;inversion H;clear H;subst.
    move=> vm1' Hvm1;exists vm1';split=>//=;constructor.
  Qed.

  Let Hseq  : forall i c,  PI i -> Pc c -> Pc (i::c).
  Proof.
    move=> i1 c1 Hi Hc r1 [//|i2 c2] r2 /=.
    case Hci : check_i => [ri|] //= Hcc m1 m3 vm1 vm3 H;inversion H;clear H;subst.
    move=> vm1' Hvm1;case: s2 H3 H5 => m2 vm2 H3 H5. 
    have [vm2' [Hvm2 Hi2]]:= Hi _ _ _ Hci _ _ _ _ H3 _ Hvm1.
    have [vm3' [Hvm3 Hc2]]:= Hc _ _ _ Hcc _ _ _ _ H5 _ Hvm2.
    by exists vm3';split=> //;apply (Eseq Hi2 Hc2).
  Qed.
 
  Lemma eq_write t (rv1 rv2:rval t) v1 v2 r1 r2 s1 s1' vm1:
    check_rval rv1 rv2 r1 = Ok unit r2 ->
    eq_alloc r1 s1.(evm) vm1 ->
    val_uincl v1 v2 ->
    write_rval s1 rv1 v1 = ok s1' ->
    exists vm2, write_rval (Estate s1.(emem) vm1) rv2 v2 = ok (Estate s1'.(emem) vm2) /\
                eq_alloc r2 s1'.(evm) vm2.
  Proof. by move=> Hc Hrn /val_uincl2P Hu; apply (eq_write_aux Hc). Qed. 

 
  Lemma eq_alloc_merge r1 r2 vm vm': 
    eq_alloc r1 vm vm' \/ eq_alloc r2 vm vm' ->
    eq_alloc (M.merge r1 r2) vm vm'.
  Proof. 
    by move=> [];apply eq_alloc_incl;[apply M.merge_incl_l | apply M.merge_incl_r].
  Qed.

  Let Hbcmd : forall t (x:rval t) e, Pi (Cassgn x e).
  Proof. 
    move=> t1 x1 e1 r1 [] //= t2 x2 e2 r2.
    case Heq: check_e => [re|]//= Heqr m1 m2 vm1 vm2 Hi;sinversion Hi.
    sinversion H2;sinversion H3=> vm1'.
    case Heq1: sem_pexpr H4 => [v1|]//= Heqw Heqa.
    have ?:= check_e_eqt Heq;subst.
    have /(_ {| emem := m1; evm := vm1 |} _ Heqa):= check_eP Heq.
    move=>[Heqa' /(_ _ Heq1)] [v1' /=] [Hv1' Hu1'].
    have /= [vm3 [Hw3 Heqw3]]:= eq_write Heqr Heqa' Hu1' Heqw.
    by exists vm3;split=>//;constructor;rewrite Hv1'.
  Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Proof.
    move=> e1 c11 c12 Hc1 Hc2 r [] //= e2 c21 c22 r'.
    case He: check_e => [re|] //=.
    case Heq1 : (fold2 tt check_i c11) => [r1|] //=.
    case Heq2 : (fold2 tt check_i c12) => [r2|] //= [] <-.
    move=> m1 m2 vm1 vm2 H vm1' Hr; sinversion H.
    have /(_ {| emem := m1; evm := vm1 |} _ Hr) := check_eP He.
    move=> [Hre Hv].
    case:cond H5 H6 => /Hv [? []/= Hse ? Hsc];subst.
    + have [vm2' [Hr1 Hsc']]:=  Hc1 _ _ _ Heq1 _ _ _ _ Hsc _ Hre.
      exists vm2';split;last by econstructor;eauto.
      by apply: eq_alloc_incl Hr1;apply M.merge_incl_l.
    have [vm2' [Hr2 Hsc']]:= Hc2 _ _ _ Heq2 _ _ _ _ Hsc _ Hre.
    exists vm2';split;last by econstructor;eauto.
    by apply: eq_alloc_incl Hr2;apply M.merge_incl_r.
  Qed.

  Lemma loopP check n r1 r1': 
    loop check n r1 = Ok unit r1' ->
    exists r2, [/\ check r1' = Ok unit r2 , M.incl r1' r1 & M.incl r1' r2].
  Proof.
    elim : n r1 => //= n Hrec r1.    
    case Heq: check => [r2|]//=.
    case: ifP => Hincl.
    + move => [] ?;subst r1';exists r2;split=>//;apply M.incl_refl.
    move=> /Hrec [r3 [H1 H2 H3]];exists r3;split=>//.
    apply/(M.incl_trans H2)/M.merge_incl_l.
  Qed.

  Opaque nb_loop.
 
  Let Hfor  : forall i rn c, Pc c -> Pi (Cfor i rn c).
  Proof.
    move=> i1 [[dir1 hi1] low1] c1 Hc r1 []//= i2 [[dir2 hi2] low2] c2 r2'.
    case:ifP=> //= /eqb_dirP <- {dir2}.
    case Hlo: check_e => [rlo|] //=.
    case Hhi: check_e => [rhi|] //=.
    move=> /loopP [r1'] [].
    case Hcr : check_rval=> [ri|]//= Hcc Hincl Hincl' m1 m2 vm1 vm2 H;sinversion H.
    have Hfor: forall vm1', eq_alloc r2' vm1 vm1' ->
          exists vm2', eq_alloc r2' vm2 vm2' /\
          sem_for i2 [seq n2w i | i <- wrange dir1 vlow vhi]
             {| emem := m1; evm := vm1' |} c2 {| emem := m2; evm := vm2' |}.
    + elim: [seq n2w i | i <- _] m1 vm1 H9 {H8 H7}=> [ | w ws Hws] m1 vm1 H10;sinversion H10.
      + by move=> vm2' Hvm2;exists vm2';split=>//;constructor.
      move=> vm1' Hvm1;case: s2 H3 H7=> m3 vm3 /= H3 H7.
      have /=:= eq_write Hcr (Hvm1: eq_alloc r2' (evm {| emem := m1; evm := vm1 |}) vm1')
                             (erefl w) H1.
      move=> [vm1''] [Hw] Hvm1'';case:s1' Hw Hvm1'' H1 H3 => m1' vm2' Hw Hvm1'' H1 H3.
      have [vm3' [Hvm3' Hc2]]:= Hc _ _ _ Hcc _ _ _ _ H3 _ Hvm1''.
      have []:= Hws _ _ H7 vm3';first by apply: eq_alloc_incl Hvm3'.
      by move=> vm4 [Hvm4 Hsf];exists vm4;split=>//;apply: EForOne Hc2 Hsf.
    move=> vm1' Hvm1.
    have [Hrlo /(_ _ H8)/=[vlo2 [Hvlo /= ?]] ]:=
      check_eP Hlo (Hvm1: eq_alloc r1 (evm {| emem := m1; evm := vm1 |}) vm1').
    have [Hrhi /(_ _ H7)/=[vhi2 [Hvhi /= ?]] ]:= check_eP Hhi Hrlo.
    have []:= Hfor vm1'; first by apply: eq_alloc_incl Hrhi.
    by move=> vm2' [Hvm2 Hsf];exists vm2';subst;split=>//; apply: EFor Hsf.
  Qed.

  Let Hwhile  : forall e c, Pc c -> Pi (Cwhile e c).
  Proof.
    move=> e1 c1 Hc r1 []//= e2 c2 r2 /loopP [r2' []].
    case Hce: check_e => [re|] //= Hcc Hincl Hincl'.
    move=> m1 m2 vm1 vm2 H;sinversion H.
    have Hwhile: forall vm1', eq_alloc r2 vm1 vm1' ->
          exists vm2', eq_alloc r2 vm2 vm2' /\
          sem_while {| emem := m1; evm := vm1' |} e2 c2
                    {| emem := m2; evm := vm2' |}.
    + move: H4 Hcc Hce Hc.
      set st1 := {| emem := m1; evm := vm1 |}; set st2 := {| emem := m2; evm := vm2 |}.
      rewrite [m1]/(emem st1) [m2]/(emem st2) [vm1]/(evm st1) [vm2]/(evm st2) //.
      move: st1 st2=> st1 st2 {m1 vm1 m2 vm2}.
      elim=> {e1 c1} [ st e1 c1 He1 | [m1 vm1] [m2 vm2] [m3 vm3] e1 c1 He1 Hc1 Hw Hrec]
         Hcc Hce Hc vm1' Hvm1.
      + exists vm1';split=>//;constructor=> /=.
        by have [? /(_ _ He1) [? /= [-> <-]]]:= check_eP Hce Hvm1.
      have [Hre /(_ _ He1) [vt /= [Hse2 ?]]]:= 
        check_eP Hce (Hvm1: eq_alloc r2 (evm {| emem := m1; evm := vm1 |}) vm1');subst vt.
      have [vm2' [Hvm2 Hsc]] := (Hc _ _ _ Hcc _ _ _ _ Hc1 _ Hre). 
      have []:= Hrec Hcc Hce Hc vm2';first by apply:(eq_alloc_incl _ Hvm2).
      by move=> vm3' /= [Hvm3 Hsw];exists vm3';split=>//;apply: EWhileOne Hsw.
    move=> vm1' Hvm1;have []:= Hwhile vm1';first by apply: eq_alloc_incl Hvm1.
    by move=> vm2' [Hvm2 Hsw];exists vm2';split=> //;constructor.
  Qed.

  Let Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Proof.
    move=> ta tr x1 fd1 a1 Hf r1 [] //= ?? x2 fd2 a2 r2.
    case:ifP=> //= Hcf.
    case Hca: check_e=> [re|] //= Hcx m1 m2 vm1 vm2 H;sinversion H.
    unfold rarg in * => {rarg}.
    sinversion H5;sinversion H6;sinversion H7;sinversion H0;sinversion H2.
    have ? := check_e_eqt Hca; have ?:= check_rval_eqt Hcx;subst.
    case Hsa: sem_pexpr H1 => [va|] //= _.
    move=> vm1' Hvm1.
    have := check_eP Hca (Hvm1: eq_alloc r1 (evm {| emem := m1; evm := vm1 |}) vm1').
    move=> [Hre /(_ _ Hsa) [va' [/=Hsa' Hu]]]. rewrite Hsa /= in H8.
    have := Hf _ Hcf _ _ _ _ _ Hu H8. 
    have [vm2' /= [??]?]:= 
     eq_write Hcx (Hre:eq_alloc re (evm {| emem := m0; evm := vm1 |}) vm1')
               (val_uincl_refl res) H9. 
    by exists vm2';split=>//;econstructor;eauto;rewrite Hsa'.
  Qed.

  Let Hfunc : forall ta tr (x:rval ta) c (re:pexpr tr), Pc c -> Pf (FunDef x c re).
  Proof.
    move=> ta tr x1 c1 re1 Hc fd2. 
    have ->/= : fd2 = FunDef (fd_arg fd2) (fd_body fd2) (fd_res fd2) by case fd2.
    case Hcx: check_rval => [r1|]//=.   
    case Hcc: fold2 => [r2|]//=.
    case Hcr: check_e => [rr|]//= _ mem mem' va va' vr Hu H;sinversion H.
    sinversion H0;constructor=> // vm0 Hemp.
    case: (H6 vm0 Hemp)=> -[m1 vm1] /= [] vm1' [Hw Hsem Hvr] {H6}.
    have /(_ _ (eq_alloc_empty _)) [] //=:= eq_write Hcx _ Hu Hw.
    move=> vm2 [Hw2 Heqa].
    have [vm2' [Heqa' Hsem']]:= Hc _ _ _ Hcc _ _ _ _ Hsem _ Heqa.
    eexists;eexists;split;eauto.
    have [] /=:= check_eP Hcr (Heqa':eq_alloc r2 (evm {| emem := mem'; evm := vm1' |}) vm2').
    by move=> Heqa1 /(_ _ Hvr) [vr' /=[] ?  /(is_full_array_uincl H8) ->].
  Qed.
 
  Lemma check_fdP ta tr (f1 f2 : fundef ta tr) mem mem' va vr: 
    check_fd f1 f2 -> 
    sem_call mem f1 va mem' vr -> sem_call mem f2 va mem' vr.
  Proof.
    have H := (@func_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc _ _ f1 f2).
    by move=> ?;apply H.
  Qed.

End PROOF.
*)
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

  Lemma setP_eq m x id: get (set m x id) x = Some id.
  Proof. by rewrite /get /set /=;rewrite M.setP_eq. Qed.

  Lemma setP_neq m x y id id': 
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

  Lemma mergeP m1 m2 x id: 
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

  Lemma setP_eq m x id: get (set m x id) x = Some id.
  Proof. by apply Mv.setP_eq. Qed.

  Lemma setP_neq m x y id id': 
    x != y -> get (set m x id) y = Some id' ->
    get m y = Some id' /\ id <> id'.
  Proof. apply Mv.setP_neq. Qed.

  Lemma setP_mset m x id: mset (set m x id) = Sv.add x (mset m).
  Proof. by []. Qed.

  Lemma mergeP m1 m2 x id: 
    get (merge m1 m2) x = Some id -> get m1 x = Some id /\ get m2 x = Some id.
  Proof. apply Mv.mergeP. Qed.

  Lemma mergeP_mset m1 m2: mset (merge m1 m2) = Sv.union (mset m1) (mset m2).
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

  Lemma incl_trans r2 r1 r3  : incl r1 r2 -> incl r2 r3 -> incl r1 r3.
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
        match vtype x1 with
        | sarr _ => 
          if Sv.mem x1 (M.mset m) then cerror (Cerr_varalloc xi1 xi2 "array already set") 
          else cok (M.set m x1 (vname x2))
        | _ => cerror (Cerr_varalloc xi1 xi2 "variable not set") 
        end
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

  Definition check_rval_e (x1 x2:rval) m : cexec M.t :=
    match x1, x2 with
    | Rnone _, Rnone _ => cok m
    | Rvar _ , Rvar  _ => cok m
    | Rmem x1 e1, Rmem x2 e2 => check_v x1 x2 m >>= check_e e1 e2
    | Raset x1 e1, Raset x2 e2 => check_v x1 x2 m >>= check_e e1 e2
    | _      , _       => cerror (Cerr_neqrval x1 x2 salloc)
    end.

  Definition check_var_aux (xi1 xi2:var_i) m : cexec M.t :=
    let x1 := xi1.(v_var) in
    let x2 := xi2.(v_var) in
    if vtype x1 == vtype x2 then cok (M.set m x1 (vname x2))
    else cerror (Cerr_varalloc xi1 xi2 "type mismatch").

  Fixpoint check_rval_aux (x1 x2:rval) m : cexec M.t :=
    match x1, x2 with
    | Rnone  _, Rnone _  => cok m 
    | Rvar xi1, Rvar xi2 => check_var_aux xi1 xi2 m
    | Rmem x1 _ , Rmem x2 _  => check_var_aux x1 x2 m
    | Raset xi1 _, Raset xi2 _ => check_var_aux xi1 xi2 m
    | _       , _        => cerror (Cerr_neqrval x1 x2 salloc)
    end.

  Definition check_rvals_e := fold2 (Cerr_fold2 "allocation:check_rvals_e") check_rval_e.

  Definition check_rvals_aux := fold2 (Cerr_fold2 "allocation:check_rvals_aux") check_rval_aux.

  Definition check_rval (x1 x2:rval) m := 
    check_rval_e x1 x2 m >>= (check_rval_aux x1 x2).

  Definition check_rvals (xs1 xs2:rvals) m := 
    check_rvals_e xs1 xs2 m >>= (check_rvals_aux xs1 xs2).

(*    
  Definition eq_alloc (r:M.t) (vm1 vm2:vmap) := 
    (forall x, ~Sv.In x (M.mset r) -> is_empty_array vm1.[x]) /\
    (forall x id,  M.get r x = Some id ->
       val_uincl vm1.[x] vm2.[Var (vtype x) id]).
  
  Lemma eq_alloc_empty vm: 
    all_empty_arr vm ->
    eq_alloc M.empty vm vm.
  Proof. 
    move=> Hall;split;first by move=> ?.
    by move=> ??;rewrite M.get0. 
  Qed.
  
  Lemma eq_alloc_incl r1 r2 vm vm':
    M.incl r2 r1 -> 
    eq_alloc r1 vm vm' -> 
    eq_alloc r2 vm vm'.
  Proof. 
    move=> /M.inclP [Hi Hsub] [epa eqa];split.
    + by move=> x Hx;apply epa;SvD.fsetdec.
    move=> x id /Hi;apply eqa. 
  Qed.
  
  Lemma check_rval_eqt t1 t2 (r1 r2:M.t) (rv1:rval t1) (rv2:rval t2):
    check_rval rv1 rv2 r1 = Ok unit r2 -> t1 = t2.
  Proof.
    rewrite /check_rval;case: check_rval_mem => //= {r1} r1.
    elim: rv1 t2 rv2 r1 r2 => [x1 | e1| ?? x11 Hx1 x12 Hx2] t2 [x2 | e2| ?? x21 x22] //= r1 r2.
    + by case:ifP => [/eqP|].
    case Heq: check_rval_aux => [r' /=|//] /Hx1 ->.
    by rewrite (Hx2 _ _ _ _ Heq).
  Qed.
      
  Lemma check_e_eqt r r' t1 (e1:pexpr t1) t2 (e2:pexpr t2):
    check_e e1 e2 r = Ok unit r' -> t1 = t2.
  Proof.
    elim: e1 r r' t2 e2 =>
        [ x1 | e1 He1 | n1 | b1 | ?? o1 e1 He1
        | ??? o1 e11 He1 e12 He2 | ???? o1 e11 He1 e12 He2 e13 He3] r r' t2
        [ x2 | e2 | n2 | b2 | ?? o2 e2
        | ??? o2 e21  e22 | ???? o2 e21 e22 e23] //=.
    + by rewrite /check_v;case:ifP => [/eqP|].
    + by case Ho: eqb_sop1 => //= /He1 Heqt;case: (eqb_sop1P Heqt Ho).
    + case Ho: eqb_sop2=> //=;case H1: check_e => [r1|]//=.
      by move=> /He1 in H1 => /He2 H2;case:(eqb_sop2P H1 H2 Ho).
    case Ho: eqb_sop3=> //=;case H1: check_e => [r1|]//=;case H2: check_e => [r2|]//=.
    by move=> /He1 in H1;move=> /He2 in H2 =>/He3 H3;case:(eqb_sop3P H1 H2 H3 Ho).
  Qed.

  Lemma check_eP_aux t1 (e1:pexpr t1) t2 (e2: pexpr t2) r re s vm:
    check_e e1 e2 r = Ok unit re ->
    eq_alloc r s.(evm) vm ->
    eq_alloc re s.(evm) vm /\
    forall v1,  sem_pexpr s e1 = ok v1 ->
    exists v2, sem_pexpr (Estate s.(emem) vm) e2 = ok v2 /\ val_uincl2 v1 v2.
  Proof.
   elim:e1 t2 e2 r re =>
     [ [xt1 x1] | e1 He1 | n1 | b1 | ?? o1 e1 He1
      | ??? o1 e11 He1 e12 He2 | ???? o1 e11 He1 e12 He2 e13 He3] t2
      [ [xt2 x2] | e2 | n2 | b2 | ?? o2 e2
      | ??? o2 e21  e22 | ???? o2 e21 e22 e23] //= r re.
   + rewrite /check_v;case:ifPn => //= /eqP ?;subst.
     case Heq: M.get => [x2'|] //=.
     + case: ifP => //= /eqP ? [] ? [epa eqa];subst;split=>// ? [] <-.
       exists vm.[{| vtype := xt2; vname := x2' |}];split=>//.
       by have /= /val_uincl2P := eqa _ _ Heq.
     case: xt2 Heq=>//= p Heq.
     case:ifP=> //= /Sv_memP Hin [] <- [epa eqa];split;[split|].
     + move=> x;rewrite M.setP_mset => ?;apply epa;SvD.fsetdec.
     + move=> x id;case: ({| vtype := sarr p; vname := x1 |} =P x)=> [<- | /eqP Hne].
       + by rewrite M.setP_eq=> -[] <- /= i v;rewrite (epa _ Hin)=> H;case (Array.getP_empty H).
       by move=> /(M.setP_neq Hne) [] ??;apply eqa.
     move=> ? [] <-;exists vm.[{| vtype := sarr p; vname := x2 |}];split=>//;split=>//.
     by move=> i v;rewrite (epa _ Hin)=> H;case:(Array.getP_empty H).
   + move=> Hc He;have [Heq Hv1]:= He1 _ _ _ _ Hc He;split=>// v1.
     case Heqp:sem_pexpr => [p|]//=. 
     move=> /Hv1 in Heqp;case Heqp => ? /=[] -> <- /= ->;eauto.
   + by case:eqP => //= <- [] <- Hok;split=>// v1 [] <-;eexists;eauto.
   + by case:eqP => //= <- [] <- Hok;split=>// v1 [] <-;eexists;eauto.
   + case:ifP => //= Ho He;have ?:= check_e_eqt He;subst.
     move: He=>/He1 He /He{He1 He} [Hok Hv1];split=>//.
     move=> v1;case Heq1:(sem_pexpr _ e1) => [v1'|]//=.
     case: (eqb_sop1P (erefl _) Ho) => ?;subst=> <-.
     case: (Hv1 _ Heq1)=> v2' [He2 /val_uincl2P Hu2]. 
     by move=> /(sem_sop1_uincl Hu2) [v2 [Hs Hu]];exists v2;rewrite He2 -val_uincl2P.
   + case:ifP => //= Ho.
     case Heq1: check_e => [v1|] //=.
     case Heq2: check_e => [v2|] //= [] <-.
     have ?:= check_e_eqt Heq1;have ?:= check_e_eqt Heq2;subst.
     move: Heq1=>/He1{He1} He1 /He1{He1} [Hok1 Hv1].
     move: Heq2 Hok1=>/He2{He2} He2 /He2{He2} [Hok2 Hv2];split=>//.
     move=> v;case Heq1:(sem_pexpr _ e11) => [v1'|]//=.
     case Heq2:(sem_pexpr _ e12) => [v2'|]//=.
     case: (eqb_sop2P (erefl _) (erefl _) Ho) => ?;subst=> <-.
     case: (Hv1 _ Heq1)=> v1'' [He21 /val_uincl2P Hu21]. 
     case: (Hv2 _ Heq2)=> v2'' [He22 /val_uincl2P Hu22].
     move=> /(sem_sop2_uincl Hu21 Hu22) [vv [Hs Hu]].
     by exists vv;rewrite He21 He22 -val_uincl2P.
   case:ifP => //= Ho.
   case Heq1: check_e => [v1|] //=.
   case Heq2: check_e => [v2|] //=.
   case Heq3: check_e => [v3|] //= [] <-.
   have ?:= check_e_eqt Heq1;have ?:= check_e_eqt Heq2;have ?:= check_e_eqt Heq3;subst.
   move: Heq1=>/He1{He1} He1 /He1{He1} [Hok1 Hv1].
   move: Heq2 Hok1=>/He2{He2} He2 /He2{He2} [Hok2 Hv2].
   move: Heq3 Hok2=>/He3{He3} He3 /He3{He3} [Hok3 Hv3];split=>//.
   move=> v;case Heq1:(sem_pexpr _ e11) => [v1'|]//=.
   case Heq2:(sem_pexpr _ e12) => [v2'|]//=.
   case Heq3:(sem_pexpr _ e13) => [v3'|]//=.
   case: (eqb_sop3P (erefl _) (erefl _) (erefl _) Ho) => ?;subst=> <-.
   case: (Hv1 _ Heq1)=> v1'' [He21 /val_uincl2P Hu21]. 
   case: (Hv2 _ Heq2)=> v2'' [He22 /val_uincl2P Hu22].
   case: (Hv3 _ Heq3)=> v3'' [He23 /val_uincl2P Hu23].
   move=> /(sem_sop3_uincl Hu21 Hu22 Hu23) [vv [Hs Hu]].
   by exists vv;rewrite He21 He22 He23 -val_uincl2P.
  Qed.

  Lemma check_eP t (e1:pexpr t) (e2: pexpr t)  r re s vm: 
    check_e e1 e2 r = Ok unit re ->
    eq_alloc r s.(evm) vm ->
    eq_alloc re s.(evm) vm /\
    forall v1,  sem_pexpr s e1 = ok v1 ->
    exists v2, sem_pexpr (Estate s.(emem) vm) e2 = ok v2 /\ val_uincl v1 v2.
  Proof.
    move=> He Hok;have [Hok' Hv]:= check_eP_aux He Hok.
    by split=>// v1 /Hv [v2 [? /val_uincl2P ?]]; exists v2.
  Qed.

  Fixpoint eq_vval_mem t1 (v1:vval t1) t2 (v2: vval t2) : Prop := 
    match v1, v2 with
    | Vmem p1, Vmem p2 => p1 = p2
    | Vpair _ _ v11 v12, Vpair _ _ v21 v22 => 
      eq_vval_mem v11 v21 /\ eq_vval_mem v12 v22
    | Vvar _, Vvar _ => True
    | _, _ => False
    end.

  Lemma check_rval_memP t1 (x1:rval t1) t2 (x2: rval t2) r re s vm: 
    check_rval_mem x1 x2 r = Ok unit re ->
    eq_alloc r s.(evm) vm ->
    eq_alloc re s.(evm) vm /\
    forall v1, rval2vval s x1 = ok v1 ->
    exists v2, rval2vval (Estate s.(emem) vm) x2 = ok v2 /\ eq_vval_mem v1 v2.
  Proof.
    elim: x1 t2 x2 r re s vm  =>
      [[t1' x1] | e1 | ?? x11 Hx1 x12 Hx2] ?
      [[ t2' x2] | e2 | ?? x21 x22] //= r re s vm. 
    + by move=> [] <- Heqa;split=>// ? [] <-;eexists;split;eauto.
    + move=> /check_eP H /H{H} [Heqa Hv1];split=>// v1.
      case Heq: sem_pexpr => [p1|]//= [] <-.
      have [p2 [-> /= ->]]:= Hv1 _ Heq;eexists;split;eauto=> //=.
    case Hc2: check_rval_mem => [re2|] //= Hc1 Heqa.
    have [Heqa2 Hv2]:= Hx2 _ _ _ _ _ _ Hc2 Heqa.
    have [Heqa1 Hv1]:= Hx1 _ _ _ _ _ _ Hc1 Heqa2;split=>// v1.
    case Heq1: (rval2vval _ x11) => [v11|]//=.
    case Heq2: (rval2vval _ x12) => [v12|]//= [] <-.
    have [v2' [-> H2]]:= Hv2 _ Heq2; have [v1' [-> H1]] /=:= Hv1 _ Heq1.
    by eexists;split;eauto.
  Qed.

  Lemma eq_write_aux t1 (rv1:rval t1) t2 (rv2:rval t2) v1 v2 r1 r2 s1 s1' vm1:
     check_rval rv1 rv2 r1 = Ok unit r2 ->
     eq_alloc r1 s1.(evm) vm1 ->
     val_uincl2 v1 v2 ->
     write_rval s1 rv1 v1 = ok s1' ->
     exists vm2, write_rval (Estate s1.(emem) vm1) rv2 v2 = ok (Estate s1'.(emem) vm2) /\
                 eq_alloc r2 s1'.(evm) vm2.
  Proof.
    rewrite /check_rval;case Hc: check_rval_mem => [r1'|] //= Hca Heqa Hu.
    rewrite /write_rval; case Heqrv: rval2vval => [vr|] //= Hw.
    have [Heqa' /(_ _ Heqrv) [vr' [Heq Hvr]]]:= check_rval_memP Hc Heqa.
    rewrite Heq.
    move=> {Hc Heqa r1};move: {1}{| emem := emem s1; evm := vm1 |} Heq => s0 Hs0.
    move: {1}s1 Heqrv => s0' Heqrv.
    elim: rv1 t2 rv2 vr vr' r1' r2 v1 v2 s1 s1' vm1 Hca Heqrv Hs0 Hw Hu Heqa' Hvr =>
      [[t1' x1] | e1 | ?? x11 Hx1 x12 Hx2] ?
      [[ t2' x2] | e2 | ?? x21 x22] //= vr vr' r1' r2 v1 v2 s1 s1' vm1.
    + case: ifP => //= /eqP ?;subst t2'=> -[] <- [] <- [] <- /= [] <- /= ? [epa eqa] _.
      eexists;split;eauto;split.
      + move=> x;rewrite M.setP_mset => Hin.
        rewrite Fv.setP_neq;first by apply epa;SvD.fsetdec.
        by rewrite eq_sym;apply /eqP;SvD.fsetdec.
      move=> x id;case: ({| vtype := t1'; vname := x1 |} =P x) => [<-/=| /eqP Hne].
      + by rewrite M.setP_eq=> -[] <-;rewrite !Fv.setP_eq val_uincl2P.
      move=> Hget;have [Hx Hne2] := M.setP_neq Hne Hget.
      rewrite !Fv.setP_neq //;first by apply eqa.
      by apply /eqP => -[] ??;apply Hne2.    
    + move=> [] <-.
      case: sem_pexpr => [p1|] //= [] <-.
      case: sem_pexpr => [p2|] //= [] <-.
      case:s1 => [m1 vm1'] /= Hw <- Heqa <- /=.
      case: write_mem Hw => [m'|] //= [] <-.
      eexists;split;eauto=> /=.
    case Hc2 : check_rval_aux=> [r2'|] //= Hc1.    
    case Hv1 : (rval2vval _ x11) => [vr1|]//=.
    case Hv2 : (rval2vval _ x12) => [vr2|]//= [] <-.
    case Hs01 : (rval2vval _ x21) => [vr1'|]//=.
    case Hs02 : (rval2vval _ x22) => [vr2'|]//= [] <-.
    case Hw2: write_vval => [s2|] //= Hw1 [Hu1 Hu2] Heqa [Hvr1 Hvr2].
    have [vm3 /= [Hvm3 Heqa']]:= Hx2 _ _ _ _ _ _ _ _ _ _ _ Hc2 Hv2 Hs02 Hw2 Hu2 Heqa Hvr2. 
    have [vm4 /= [Hvm4 Heqa'' ]] := Hx1 _ _ _ _ _ _ _ _ _ _ _ Hc1 Hv1 Hs01 Hw1 Hu1 Heqa' Hvr1.
    rewrite Hvm3 /=;eexists;eauto.
  Qed.
*)
End CBAreg.

Module CheckAllocReg :=  MakeCheckAlloc CBAreg.