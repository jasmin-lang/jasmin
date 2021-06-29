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
Require Import expr compiler_util ZArith psem compiler_util.
Require Export leakage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.


Definition ct_c (ct_i: instr -> Sv.t -> ciexec Sv.t)
                       c s :  ciexec Sv.t :=
  foldr (fun i r => Let so := r in ct_i i so) (ciok s) c.

(*
Section LOOP.

  Variable dead_code_c : Sv.t -> ciexec (Sv.t * cmd * leak_c_tr).
  Variable dead_code_c2 : Sv.t -> ciexec (Sv.t * (Sv.t * (cmd*cmd) * (leak_c_tr * leak_c_tr))).
  Variable ii : instr_info.

  Fixpoint loop (n:nat) (rx:Sv.t) (wx:Sv.t) (s:Sv.t) : ciexec (Sv.t * cmd * leak_c_tr) :=
    match n with
    | O => cierror ii (Cerr_Loop "dead_code")
    | S n =>
      Let sc := dead_code_c s in
      let: (s',c', F') := sc in
      let s' := Sv.union rx (Sv.diff s' wx) in
      if Sv.subset s' s then ciok (s,c', F')
      else loop n rx wx (Sv.union s s')
    end.

  Fixpoint wloop (n:nat) (s:Sv.t) : ciexec (Sv.t * (cmd * cmd) * (leak_c_tr * leak_c_tr)) :=
    match n with
    | O =>  cierror ii (Cerr_Loop "dead_code")
    | S n =>
      Let sc := dead_code_c2 s in
      let: (s',sic) := sc in
      if Sv.subset s' s then ciok sic
      else wloop n (Sv.union s s')
    end.

End LOOP.
*)

Definition write_mem (r:lval) : bool :=
  if r is Lmem _ _ _ then true else false.

Module Dep.

(* Sv.t set of needed variable, bool = true when depend on memory *)
Definition t := (Sv.t * bool)%type.   

Definition empty : t := (Sv.empty, false).

Definition union (s1 s2:t) := 
  (Sv.union s1.1 s2.1, s1.2 || s2.2).

Definition add (x:var) (s:t) := 
  (Sv.add x s.1, s.2).

Definition addm (s:t) := (s.1, true).

End Dep.

Fixpoint readm (e: pexpr) := 
  match e with
  | Pconst _ 
  | Pbool _ 
  | Parr_init _ 
  | Pvar _ 
  | Pglobal _ => false 
   
  | Pget _ _ e1 => readm e1

  | Pload _ x e1 => true 

  | Papp1 _ e1     => readm e1 
  | Papp2 _ e1 e2  => (readm e1) || (readm e2) 
  | PappN _ es     => has readm es 
  | Pif _ e1 e2 e3 => [|| readm e1, readm e2 | readm e3]
  end.

Definition readms (es: pexprs) := has readm es.

(* forall e, 
     ~readm e -> 
     forall s1 s2, evm s1 = evm s2 -> eval_expr s1 e1 = eval_expr s2 e2 *)

Fixpoint ct_e (e: pexpr) := 
  match e with
  | Pconst _ 
  | Pbool _ 
  | Parr_init _ 
  | Pvar _ 
  | Pglobal _ => Dep.empty 
   
  | Pget _ _ e1  => (read_e e1, readm e1)

  | Pload _ x e1 => (Sv.add x (read_e e1), readm e1)

  | Papp1 _ e1     => ct_e e1 
  | Papp2 _ e1 e2  => Dep.union (ct_e e1) (ct_e e2) 
  | PappN _ es     => foldl (fun s e => Dep.union s (ct_e e)) Dep.empty es 
  | Pif _ e1 e2 e3 => Dep.union (ct_e e1) (Dep.union (ct_e e2) (ct_e e3))
  end.

Definition ct_es (es: pexprs) := 
  foldl (fun s e => Dep.union s (ct_e e)) Dep.empty es.

(* 
    ct_expr e = (s, usem) ->
    forall s1 s2, 
       evm s1 =[s] evm s2 ->
       (usem -> emem s1 = emem s2) ->
       eval_expr s1 e = ok(v1, l1) -> 
       eval_expr s2 e = ok(v2, l2) ->
       l1 = l2
*)


Definition ct_lval (lv : lval) :=
  match lv with 
  | Lnone _ _ => Dep.empty
  | Lvar x => Dep.empty (* produces empty leakage *)
  | Lmem _ x e => (Sv.add x (read_e e), readm e) (* x represents pointer and e is offset *)
  | Laset _ x e => (read_e e, readm e)
  end.

Definition error {A: Type} (i:instr_info) := @cierror i (Cerr_Loop "constant-time error") A.

Definition readm_lval (ii:instr_info) (lv:lval) : ciexec Sv.t :=
  let r := ct_lval lv in 
  if r.2 then error ii else ok r.1.

Definition read_em (ii:instr_info) (e:pexpr) := 
  let se := read_e e in
  let usem := readm e in
  if usem then error ii 
  else ok se.

Definition read_ems (ii: instr_info) (es:pexprs) :=
  let se := read_es es in
  let usem := readms es in
  if usem then error ii 
  else ok se.

Definition readm_cte (ii:instr_info) (e:pexpr) :=
   let (se,usem) := ct_e e in
   if usem then error ii
   else ok se.

Definition readm_ctes (ii:instr_info) (es:pexprs) :=
   let (se,usem) := ct_es es in
   if usem then error ii
   else ok se.

(* [l1::l2::l3] => ((empty U ct_lval l1) U ct_lval l2) U ct_lval l3 *)
Definition ct_lvals (lvs: lvals) := 
  foldl (fun s e => Dep.union s (ct_lval e)) Dep.empty lvs.

Definition readm_lvals (ii: instr_info) (lvs: lvals) : ciexec Sv.t :=
  let rs := ct_lvals lvs in 
  if rs.2 then error ii else ok rs.1.
               
Fixpoint ct_i (i:instr) (s:Sv.t) {struct i} : ciexec Sv.t :=
  let (ii,ir) := i in
  match ir with
  (* {I} x := e {O} *)
  | Cassgn x tag ty e =>
    let sx := vrv x in
    Let sx' := readm_lval ii x in 
    if disjoint s sx then
      Let se := readm_cte ii e in 
      ok (Sv.union sx' (Sv.union se s))
    else
      Let se := read_em ii e in 
      ok (Sv.union sx' (Sv.union (Sv.diff s sx) se))      

  (* {I} xs := o(es) {O} *)
  | Copn xs tag o es => 
    let sx := vrvs xs in
    Let sx' := readm_lvals ii xs in 
      if disjoint s sx then 
        Let se := readm_ctes ii es in 
        ok (Sv.union sx' (Sv.union se s))
      else 
        Let se := read_ems ii es in 
        ok (Sv.union sx' (Sv.union (Sv.diff s sx) se)) 

  | Cif b c1 c2 =>
    Let s1 := ct_c ct_i c1 s in
    Let s2 := ct_c ct_i c2 s in
    Let sb := read_em ii b in
    ok (Sv.union (Sv.union s1 s2) sb)

  | Cwhile a c e c' =>
    Let se := read_em ii e in 
    Let sc := ct_c ct_i c se in 
    Let sc' := ct_c ct_i c' sc in
    
    error ii



    (*let dobody s_o :=
    let s_o' := read_e_rec s_o e in
    Let sci := dead_code_c dead_code_i c s_o' in
    let: (s_i, c, Fc) := sci in
    Let sci' := dead_code_c dead_code_i c' s_i in
    let: (s_i', c', Fc') := sci' in
    ok (s_i', (s_i, (c,c'), (Fc,Fc'))) in
    Let sc := wloop dobody ii Loop.nb s in
    let: (s, (c,c'), (Fc,Fc')) := sc in
    ciok (s, [:: MkI ii (Cwhile a c e c') ], LT_iwhile Fc LT_id Fc')*)

| _ => error ii
end.

 

Section Correctness_Proof.

Variables p : prog.

  (* ct_i inst o = i
     m1 =i m2 ->
     exists m2', m1' =o m2' /\ sem p m1' [:: inst] [:: li] m2' *)  
     
  Let Pi_r (s:estate) (i:instr_r) (li:leak_i) (s':estate) :=
    forall ii s2,
      match ct_i (MkI ii i) s2 with
      | Ok s1 =>
        wf_vm s.(evm) ->
        forall vm1', s.(evm) =[s1] vm1' ->
          exists vm2', s'.(evm) =[s2] vm2' /\
          sem p (Estate s.(emem) vm1') [::(MkI ii i)] [::li] (Estate s'.(emem) vm2') 
      | _ => True
      end.


  Let Pi (s:estate) (i:instr) (li:leak_i) (s':estate) :=
    forall s2,
      match ct_i i s2 with
      | Ok s1 =>
        wf_vm s.(evm) ->
        forall vm1', s.(evm) =[s1] vm1' ->
          exists vm2', s'.(evm) =[s2] vm2' /\
          sem p (Estate s.(emem) vm1') [:: i] [::li] (Estate s'.(emem) vm2') 
      | _ => True
      end.

  Let Pc (s:estate) (c:cmd) (lc:leak_c) (s':estate) :=
    forall s2,
      match ct_c ct_i c s2 with
      | Ok s1 =>
        wf_vm s.(evm) ->
        forall vm1', s.(evm) =[s1] vm1' ->
          exists vm2', s'.(evm) =[s2] vm2' /\
          sem p (Estate s.(emem) vm1') c lc (Estate s'.(emem) vm2') 
      | _ => True
      end.


Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    case=> mem vm s2 Hwf vm' Hvm.
    exists vm'; split=> //.
    constructor.
  Qed.

Local Lemma Hcons : sem_Ind_cons p Pc Pi.
  Proof.
    move=> s1 s2 s3 i c li lc H Hi H' Hc sv3 /=.
    have := Hc sv3.
    case: (ct_c ct_i c sv3) => [sv2|//] Hc' /=.
    have := Hi sv2.
    case: (ct_i i sv2)=> [sv1|] //= Hi' Hwf vm1' /(Hi' Hwf).
    have Hwf2 := wf_sem_I H Hwf.
    move=> [vm2' [Heq2 Hsi']];case: (Hc' Hwf2 _ Heq2) => [vm3' [Heq3 Hsc']].
    exists vm3';split=> //.
    by apply: sem_app Hsi' Hsc'.
  Qed.

Local Lemma HmkI : sem_Ind_mkI p Pi_r Pi.
  Proof. move=> ii i s1 s2 li Hi Hp. exact: Hp. Qed.


Local Lemma Hif_true : sem_Ind_if_true p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc Hval Hp Hc ii sv0 /=.
    case Heq: (ct_c ct_i c1 sv0)=> [sv1 /=|//].
    case: (ct_c ct_i c2 sv0)=> [sv2 /=|//]. 
    rewrite /read_em /=. case: (readm e)=> //= Hwf vm1' Hvm.
    move: (Hc sv0).
    rewrite Heq.
    move=> /(_ Hwf vm1') [|vm2' [Hvm2' Hvm2'1]].
    apply: eq_onI Hvm; SvD.fsetdec.
    exists vm2'; split=> //.
    econstructor; constructor.
    constructor=> //.
    symmetry in Hvm. admit.
  Admitted.

Local Lemma Hif_false : sem_Ind_if_false p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc Hval Hp Hc ii sv0 /=.
    case Heq: (ct_c ct_i c2 sv0)=> [sv1 /=|//].
    case: (ct_c ct_i c1 sv0)=> [sv2 /=|//].
    rewrite /read_em /=. case: (readm e)=> //= Hwf vm1' Hvm.
    move: (Hc sv0).
    rewrite Heq.
    move=> /(_ Hwf vm1') [|vm2' [Hvm2' Hvm2'1]].
    apply: eq_onI Hvm; SvD.fsetdec.
    exists vm2'; split=> //.
    econstructor; constructor.
    constructor=> //.
    symmetry in Hvm. admit.
  Admitted.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 x tag ty e v v' le lw.
    move: s1 s2 => [m1 vm1] [m2 vm2] Hv htr Hw ii s2 /=.
    rewrite /readm_lval /=. case: (ct_lval x).2=> //=.
    rewrite /readm_cte /=. case: ifP=> //=.
    (* x is not in s2 *)
    + move=> Hdisj. case: (ct_e e)=> //=. move=> sv1 b. case: ifP=> //=.
      move=> Hb Hwf vm1' Hvm.
      eexists; split=> //=.
      econstructor. econstructor. apply Eassgn with v v'.
      rewrite /ct_lval in Hvm. case: x Hw Hvm Hdisj=> //=.
      (* var *)
      + move=> x xty. t_xrbindP. move=> s2' /= Hw Hs Hl /= Hvm Hdisj.
        subst. 
  Admitted.


End Correctness_Proof.

Section Checker_Proof.

Variables p : prog.

  (* ct_i inst o = i
     m1 =i m2 ->
     sem p m1 [:: inst] [:: li] m1' ->
     exists m2' li', sem p m2 [:: inst] [:: li'] m2' ->
     m1' =o m2' /\ li = li'.*) 
     
  Let Pi_r (s:estate) (i:instr_r) (li:leak_i) (s':estate) :=
    forall ii s2,
      match ct_i (MkI ii i) s2 with
      | Ok s1 =>
        wf_vm s.(evm) ->
        forall vm1', s.(evm) =[s1] vm1' ->
        sem p (Estate s.(emem) s.(evm)) [::(MkI ii i)] [::li] (Estate s'.(emem) vm1') -> 
        exists vm2' li', sem p (Estate s.(emem) vm1') [::(MkI ii i)] [::li'] (Estate s'.(emem) vm2') /\
                     s'.(evm) =[s2] vm2' /\ [:: li] = [:: li']
     | _ => True
     end.

  Let Pi (s:estate) (i:instr) (li:leak_i) (s':estate) :=
    forall s2,
      match ct_i i s2 with
      | Ok s1 =>
        wf_vm s.(evm) ->
        forall vm1', s.(evm) =[s1] vm1' ->
        sem p (Estate s.(emem) s.(evm)) [:: i] [::li] (Estate s'.(emem) vm1') -> 
        exists vm2' li', sem p (Estate s.(emem) vm1') [:: i] [::li'] (Estate s'.(emem) vm2') /\
                     s'.(evm) =[s2] vm2' /\ [:: li] = [:: li']
     | _ => True
     end.

  Let Pc (s:estate) (c:cmd) (lc:leak_c) (s':estate) :=
    forall s2,
      match ct_c ct_i c s2 with
      | Ok s1 =>
        wf_vm s.(evm) ->
        forall vm1', s.(evm) =[s1] vm1' ->
        sem p (Estate s.(emem) s.(evm)) c lc (Estate s'.(emem) vm1') -> 
        exists vm2' lc', sem p (Estate s.(emem) vm1') c lc' (Estate s'.(emem) vm2') /\
                     s'.(evm) =[s2] vm2' /\ lc = lc'
     | _ => True
     end.


End Checker_Proof.








