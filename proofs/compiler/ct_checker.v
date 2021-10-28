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

(* checker for command *)
Definition ct_c (ct_i: instr -> Sv.t -> ciexec Sv.t)
                       c s :  ciexec Sv.t :=
  foldr (fun i r => Let so := r in ct_i i so) (ciok s) c.

(* checks if we are writing in the memory : returns true if we are writing in memory *)
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

(* checks for expression if it involves memory *)
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

(* ct checker for expressions, returns also the boolean (memory depend) *)
(* I think we should add x in case of var and Pget *)
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

(* ct checker for left val *)
Definition ct_lval (lv : lval) :=
  match lv with 
  | Lnone _ _ => Dep.empty
  | Lvar x => Dep.empty (* produces empty leakage *)
  | Lmem _ x e => (Sv.add x (read_e e), readm e) (* x represents pointer and e is offset *)
  | Laset _ x e => (read_e e, readm e)
  end.

Definition error {A: Type} (i:instr_info) := @cierror i (Cerr_Loop "constant-time error") A.

(* if depends on memory return error *)
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


(* ct checker for instructions *)
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

Section Read_em_e_es_eq_on.

Context (p:prog).

Let P e : Prop :=
    forall Se ii s1 s1', 
    read_em ii e = ok Se ->
    evm (s1) =[Se] evm (s1') ->
    sem_pexpr (p_globs p) s1 e = sem_pexpr (p_globs p) s1' e.

Let Q es : Prop :=
    forall Se ii s1 s1', 
    read_ems ii es = ok Se ->
    evm (s1) =[Se] evm (s1') ->
    sem_pexprs (p_globs p) s1 es = sem_pexprs (p_globs p) s1' es.

Lemma or_foo a b: a || b = false ->
a = false /\ b = false.
Proof.
move=> hor. split=> //=.
case: a hor=> //=. case: b hor=> //=.
case: a=> //=.
Qed.

Lemma or_foo' a b c: [|| a, b | c] = false ->
a = false /\ b = false /\ c = false.
Proof.
move=> hor. split=> //=.
case: a hor=> //=. case: b hor=> //=.
case: a=> //=. case: a=> //=.
Qed.

Lemma read_em_e_es_eq_on: (forall e, P e) * (forall es, Q es). 
Proof.
apply: pexprs_ind_pair ; split; subst P Q => //=.
(* Pexprs *)
+ move=> e he es hes Se ii s1 s1' /=.
  rewrite /read_ems /=. rewrite /read_em in he.
  case: ifP=> //= hr [] <-. rewrite /read_es /=.
  have [hr1 hr2] := or_foo hr. rewrite /read_ems /= hr2 /= in hes.
  rewrite hr1 /= in he. rewrite read_esE /= read_eE. move=> hvm.
  have hvm1 : evm s1 =[read_e e] evm s1'. 
  + by apply: eq_onI hvm; SvD.fsetdec.
  have heq : ok (read_e e) = ok (read_e e). + by auto.
  have -> := (he (read_e e) ii s1 s1' (heq _) hvm1).
  have hvm2 : evm s1 =[read_es es] evm s1'. 
  + by apply: eq_onI hvm; SvD.fsetdec.
  have heq' : ok (read_es es) = ok (read_es es). + by auto.
  by have -> := (hes (read_es es) ii s1 s1' (heq' _) hvm2).
(* Var *)
+ move=> x Se ii s1 s1' /=. rewrite /read_em /=.
  move=> [] <- /= /get_var_eq_on -> //=. rewrite /read_e /=.
  by apply SvP.MP.Dec.F.add_1.
(* Pget *)
+ move=> sz x e hrec Se ii s1 s1'. rewrite /read_em /=. case: ifP=> //= hr [] <- /=.
  rewrite /read_e /= read_eE /=. move=> hvm.
  rewrite /read_em /= hr /= in hrec.
  have hvm' : evm s1 =[read_e e] evm s1'.
  + by apply: eq_onI hvm; SvD.fsetdec.
  have heq : ok (read_e e) = ok (read_e e). + by auto.
  have -> /= := hrec (read_e e) ii s1 s1' (heq _) hvm'. 
  rewrite (@on_arr_var_eq_on _ _ _ _ _ _ hvm) /=  ?read_eE //.
  by SvD.fsetdec.
(* Pop1 *)
+ move=> op e hrec Se ii s1 s1' /=. rewrite /read_em /=. case: ifP=> //= hr [] <- /=.
  rewrite /read_e /= read_eE /=. move=> hvm.
  rewrite /read_em /= hr /= in hrec.
  have hvm' : evm s1 =[read_e e] evm s1'.
  + by apply: eq_onI hvm; SvD.fsetdec.
  have heq : ok (read_e e) = ok (read_e e). + by auto.
  by have -> /= := hrec (read_e e) ii s1 s1' (heq _) hvm'. 
(* Pop2 *)
+ move=> op e1 he1 e2 he2 Se ii s1 s1'. rewrite /read_em /=.
  case:ifP=> //= hr [] <-. rewrite /read_e /=. rewrite ?read_eE /=.
  move=> hvm. rewrite /read_em /= in he1 he2.
  have hvm1 : evm s1 =[read_e e1] evm s1'.
  + by apply: eq_onI hvm; SvD.fsetdec.
  have hvm2 : evm s1 =[read_e e2] evm s1'.
  + by apply: eq_onI hvm; SvD.fsetdec.
  have [hr1 hr2] := or_foo hr. rewrite hr1 /= in he1.
  rewrite hr2 /= in he2. have heq : ok (read_e e1) = ok (read_e e1). + by auto.
  have heq' : ok (read_e e2) = ok (read_e e2). + by auto.
  have -> := (he1 (read_e e1) ii s1 s1' (heq _) hvm1).
  by have -> := (he2 (read_e e2) ii s1 s1' (heq' _) hvm2).
(* PopN *)
+ move=> opN es hrec Se ii s1 s1'. rewrite /read_em /=.
  case: ifP=> //=. rewrite /read_ems /= in hrec.
  move=> hr [] <-. rewrite /read_e /=. move=> hvm.
  rewrite /readms hr /= /read_es /= in hrec.
  have hvm1 : evm s1 =[read_es_rec Sv.empty es] evm s1'.
  + by apply: eq_onI hvm; SvD.fsetdec.
  have heq : ok (read_es_rec Sv.empty es) = ok (read_es_rec Sv.empty es). + by auto.
  have hes := (hrec (read_es_rec Sv.empty es) ii s1 s1' (heq _) hvm1).
  rewrite /sem_pexprs in hes. by rewrite hes /=.
(* Pif *)
move=> ty e he e1 he1 e2 he2 Se ii s1 s1'. rewrite /read_em /=.
case:ifP=> //= hr [] <-. rewrite /read_e /= ?read_eE /=.
move=> hvm. have hvm1 : evm s1 =[read_e e] evm s1'.
+ by apply: eq_onI hvm; SvD.fsetdec.
have hvm2 : evm s1 =[read_e e1] evm s1'.
+ by apply: eq_onI hvm; SvD.fsetdec.
have hvm3 : evm s1 =[read_e e2] evm s1'.
+ by apply: eq_onI hvm; SvD.fsetdec.
have heq1 : ok (read_e e) = ok (read_e e). + by auto.
have heq2 : ok (read_e e1) = ok (read_e e1). + by auto.
have heq3 : ok (read_e e2) = ok (read_e e2). + by auto.
rewrite /read_em /= in he he1 he2. 
have [hr1 [hr2 hr3]] := or_foo' hr. rewrite hr1 in he.
rewrite hr2 in he1. rewrite hr3 in he2.
have -> := (he (read_e e) ii s1 s1' (heq1 _) hvm1).
have -> := (he1 (read_e e1) ii s1 s1' (heq2 _) hvm2).
by have -> := (he2 (read_e e2) ii s1 s1' (heq3 _) hvm3).
Qed.


Let P_ct e : Prop :=
    forall S ii s1 s1' v le v' le', readm_cte ii e = ok S ->
    evm (s1) =[S] evm (s1') ->
    sem_pexpr (p_globs p) s1 e =  ok (v, le) ->
    sem_pexpr (p_globs p) s1' e = ok (v', le') ->
    le = le'.

Let Q_ct es : Prop :=
    forall S ii s1 s1' vs vs', readm_ctes ii es = ok S ->
    evm (s1) =[S] evm (s1') ->
    sem_pexprs (p_globs p) s1 es =  ok vs ->
    sem_pexprs (p_globs p) s1' es = ok vs' ->
    (unzip2 vs) = (unzip2 vs').

Lemma readm_ct_e_es_eq_on : (forall e, P_ct e) * (forall es, Q_ct es). 
Proof.
apply: pexprs_ind_pair; split; subst P_ct Q_ct => //=.
(* pexprs:empty *)
+ admit.
(* pexprs:nonempty *)
+ admit.
(* const *)
+ move=> z S ii s1 s1' v le v' le' /= _ _. by move=> [] _ <- [] _ <-.
(* bool *)
+ move=> b S ii s1 s1' v le v' le' /= _ _. by move=> [] _ <- [] _ <-.
(* array_init *)
+ move=> n S ii s1 s1' v le v' le' /= _ _. by move=> [] _ <- [] _ <-.
(* var *)
+ move=> x S ii s1 s1' v le v' le' /=. rewrite /readm_cte /=.
  move=> [] <- /=. admit.
(* Pglobal *)
+ move=> g S ii s1 s1' v le v' le' /=. rewrite /readm_cte /=.
  move=> [] <- _ /=. t_xrbindP. by move=> vg -> _ <- vg' [] _ _.
(* Pget *)
+ move=> sz x e hrec S ii s1 s1' v le v' le'. rewrite /readm_cte /=.
  case:ifP=> //= hr [] <- hvm. rewrite /readm_cte /= in hrec.
  move: hrec. case: (ct_e e) => //= S' b hrec. case: b hrec=> //= hrec. move=> H.
  admit. admit.
(* Pload *)
+ move=> sz x e hrec S ii s1 s1' v le v' le' /=. rewrite /readm_cte /=.
  case: ifP=> //= hr [] <- hvm.
  have hin : Sv.In x (Sv.add x (read_e e)).
  + by SvD.fsetdec.
  rewrite /readm_cte in hrec. move: (hrec (read_e e) ii s1 s1') => {hrec} /= hrec.
  case: (ct_e e) hrec=> //= S' b hrec. case: b hrec=> //= hrec.
  + admit.
  have heq : ok (read_e e) = ok (read_e e). by auto.
  t_xrbindP=> vp vg hg hp -[v1 l1] he vp' /= hp' w /= hread hv <- vg' vp'' 
  hg' hp'' -[v2 l2] he' vp''' hp''' w' hread' hv' <- /=.
  have := (hrec v1 l1 v2 l2). admit.
(* Papp1 *)
+ move=> op e hrec S ii s1 s1' v1 l1 v2 l2. rewrite /readm_cte /=.
  rewrite /readm_cte in hrec. move: hrec.
  case: (ct_e e)=> //= S' b. case: b=> //= hrec.
  move=> hr hvm. t_xrbindP=> -[v1' l1'] he /= vo hop hv <- -[v2' l2'] he' vo' ho' hv' /= <-. 
  by have <- := (hrec S ii s1 s1' v1' l1' v2' l2' hr hvm he he').
(* Papp2 *)
+ move=> op e1 hrec1 e2 hrec2 S ii s1 s1' v1 l1 v2 l2 /=. move: hrec1 hrec2. 
  rewrite /readm_cte /=. case: (ct_e e1)=> //= S' b. case: b=> //=.
  case: (ct_e e2)=> //= S'' b'. case: b'=> //=.
  move=> hrec1 hrec2 [] <- hvm. 
  t_xrbindP=> -[v1' l1'] he -[v2' l2'] he' vo ho hv <- -[v1'' l1''] he'' -[v2'' l2''] he''' vo' ho' hv' /= <-.
  have heq : ok S' = ok S'. + by auto.
  have heq' : ok S'' = ok S''. + by auto.
  have hvm1 : evm s1 =[S'] evm s1'. + by apply: eq_onI hvm; SvD.fsetdec.
  have hvm2 : evm s1 =[S''] evm s1'. + by apply: eq_onI hvm; SvD.fsetdec.
  have <- := (hrec1 S' ii s1 s1' v1' l1' v1'' l1'' (heq _) hvm1 he he'').
  by have <- := (hrec2 S'' ii s1 s1' v2' l2' v2'' l2'' (heq' _) hvm2 he' he''').
(* PopN *)
+ move=> op es hrec S ii s1 s1' v le v' le'. move: hrec. rewrite /readm_cte /readm_ctes /=.
  admit.
(* Pif *)
move=> ty e hrec1 e1 hrec2 e2 hrec3 S ii s1 s1' ve le ve' le'. rewrite /readm_cte /=.
case: ifP=> //= hr [] <- hvm. move: hrec1 hrec2 hrec3. rewrite /readm_cte /=. move: hvm.
have [hr1 [hr2 hr3]]:= or_foo' hr. case: (ct_e e) hr1=> //= Se b -> //=.
case: (ct_e e1) hr2=> //= Se1 b1 -> //=. case: (ct_e e2) hr3=> //= Se2 b2 -> //=.
move=> hvm hrec1 hrec2 hrec3. 
have hvm1 : evm s1 =[Se] evm s1'. + by apply: eq_onI hvm; SvD.fsetdec.
have hvm2 : evm s1 =[Se1] evm s1'. + by apply: eq_onI hvm; SvD.fsetdec.
have hvm3 : evm s1 =[Se2] evm s1'. + by apply: eq_onI hvm; SvD.fsetdec.
have heq1 : ok Se = ok Se. + by auto.
have heq2 : ok Se1 = ok Se1. + by auto.
have heq3 : ok Se2 = ok Se2. + by auto.
t_xrbindP=> -[v1 l1] he1 be /= hb1 -[v2 l2] he2 -[v3 l3] he3 vt /= ht vt' /= ht' hve <-.
move=> -[v1' l1'] he1' be' /= hb1' -[v2' l2'] he2' -[v3' l3'] he3' vt'' ht'' /= vt''' /= ht''' /= hf <- /=.
have -> := hrec1 Se ii s1 s1' v1 l1 v1' l1' (heq1 _) hvm1 he1 he1'.







Admitted.

End Read_em_e_es_eq_on.

Definition read_em_e_eq_on p e Se ii s1 s1':=
  (read_em_e_es_eq_on p).1 e Se ii s1 s1'.

Definition readm_ct_e_eq_on p e Se ii s1 s1':=
  (readm_ct_e_es_eq_on p).1 e Se ii s1 s1'.

Section Read_lval_e_es_eq_on.

Lemma readm_ct_lval_eq_on x p ii v v' Sx s1 s1' s2 s2' le le': 
  readm_lval ii x = ok Sx ->
  evm (s1) =[Sx] evm (s1') ->
  write_lval (p_globs p) x v s1 =  ok (s2, le) ->
  write_lval (p_globs p) x v' s1' = ok (s2', le') ->
  le = le'.
Proof.
case:x => [vi ty | x | sz x e | sz' x e ] /=.
(* Lnone *)
+ rewrite /readm_lval /=. move=> [] <- /= hvm. t_xrbindP=> y /write_noneP [] -> H hs <- s2''.
  by rewrite /write_none=> H' hs'.
(* Lvar *)
+ rewrite /readm_lval /=. move=> [] <- hvm. by t_xrbindP=> y hw hs <- s2'' hw' _.
(* Lmem *)
+ rewrite /readm_lval /=. case: ifP=> //=. move=> hr [] <- hvm /=.
  have hg := get_var_eq_on _ hvm. have -> /= := (hg x). 
  have := read_em_e_eq_on. rewrite /read_em /=. move=> her.
Admitted.

Lemma readm_ct_lavls_eq_on p ii xs vs vs' Sx s1 s1' s2 s2' le le':
  readm_lvals ii xs = ok Sx ->
  evm (s1) =[Sx] evm (s1') ->
  write_lvals (p_globs p) s1 xs vs =  ok (s2, le) ->
  write_lvals (p_globs p) s1' xs vs' = ok (s2', le') ->
  le = le'.
Proof.
Admitted.


Lemma read_lval_eq_on p x v s1 s1' s2 s2' le le':
  write_lval (p_globs p) x v s1 = ok (s2, le) ->
  write_lval (p_globs p) x v s1' = ok (s2', le') ->
  evm s2 =[vrv x] evm s2'.
Proof.
case:x => [vi ty | x | sz x e | sz' x e ] /=.
Admitted.


Lemma read_lvals_eq_on p xs vs s1 s1' s2 s2' le le':
  write_lvals (p_globs p) s1 xs vs = ok (s2, le) ->
  write_lvals (p_globs p) s1' xs vs = ok (s2', le') ->
  evm s2 =[vrvs xs] evm s2'.
Proof.
Admitted.

End Read_lval_e_es_eq_on.


  
(*R1 : 
read_em ii e = ok Se
evm s1 =[Se]  evm s1' ->
sem_pexpr (p_globs p) s1 e = sem_pexpr (p_globs p) s1' e.
(*
sem_pexpr (p_globs p) s1 e = ok (v, le) ->
sem_pexpr (p_globs p) s1' e = ok (v', le') ->
v = v' /\ le = le'

*)

R2
readm_cte ii e = ok S ->
evm s =[Se]  evm s' ->
sem_pexpr (p_globs p) s  e = ok (v,  l) -> 
sem_pexpr (p_globs p) s' e = ok (v', l') -> 
l = l'


W1 : 
readm_lval ii x = ok S ->
evm s1 =[S]  evm s1' ->
write_lval gd x v  s1 = ok (s2, l) ->
write_lval gd x v' s1' = ok (s2', l') ->
l = l'.

W2 :
write_lval gd x v  s1 = ok (s2, l) ->
write_lval gd x v s1' = ok (s2', l') ->
evm s1 =[vrv x] evm s1'.*)

Section Checker_Proof.

Variables p : prog.

  (* ct_i inst o = i
     m1 =i m2 ->
     sem p m1 [:: inst] [:: li] m1' ->
     sem p m2 [:: inst] [:: li'] m2' ->
     m1' =o m2' /\ li = li'.*) 

   Let Pi_r (s1:estate) (i:instr_r) (l1:leak_i) (s1':estate) :=
    forall ii I O s2 s2' l2, ct_i (MkI ii i) O = ok I ->
                          s1.(evm) =[I] s2.(evm) ->
                          sem_I p s2 (MkI ii i) l2 s2' ->
                          s1'.(evm) =[O] s2'.(evm) /\ l1 = l2.


   Let Pi (s1:estate) (i:instr) (l1:leak_i) (s1':estate) :=
    forall I O s2 s2' l2, ct_i i O = ok I ->
                          s1.(evm) =[I] s2.(evm) ->
                          sem_I p s2 i l2 s2' ->
                          s1'.(evm) =[O] s2'.(evm) /\ l1 = l2.

   Let Pc (s1:estate) (c:cmd) (l1:leak_c) (s1':estate) :=
    forall I O s2 s2' l2, ct_c ct_i c O = ok I ->
                          s1.(evm) =[I] s2.(evm) ->
                          sem p s2 c l2 s2' ->
                          s1'.(evm) =[O] s2'.(evm) /\ l1 = l2.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    case=> mem vm I O s2 s2' lc /= [] <- /= Hvm Hsem.
    by have [-> ->]:= semE Hsem.
  Qed.

  Local Lemma Hcons : sem_Ind_cons p Pc Pi.
  Proof.
    move=> s1 s2 s3 i c li lc H Hi H' Hc I O s1' s2' lc' /=.
    t_xrbindP=> //= O' /= Hch Hih Hvm Hsem.
    have [s3' [li'] [lc''] [Hi' Hc' ->]]:= semE Hsem.
    have [Hvm' ->] := Hi I O' s1' s3' li' Hih Hvm Hi'.
    have [Hvm'' ->] := Hc O' O s3' s2' lc'' Hch Hvm' Hc'.
    by split=> //=.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p Pi_r Pi.
  Proof. 
    move=> ii i s1 s2 li Hi Hp I O s1' s2' li' Hih Hvm Hi'.
    have [Hvm' ->] := Hp ii I O s1' s2' li' Hih Hvm Hi'. 
    by split=> //=.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 x tag ty e v v' le lw. 
    move: s1 s2 => [m1 vm1] [m2 vm2] He htr Hw ii I O s2 s2' li' /=.
    t_xrbindP=> S Hr. case: ifP=> //= Hdisj.
    + t_xrbindP=> S' Hct <- Hvm Hsem.
      have /= Hi := sem_IE Hsem. 
      have [v1 [v2 [le' [lw' [He' Ht Hw' ->]]]]]:= sem_iE' Hi.
      have Hvm' : evm  {| emem := m1; evm := vm1 |} =[S']  evm s2.
      + by apply: eq_onI Hvm; SvD.fsetdec.
      have -> := readm_ct_e_eq_on Hct Hvm' He He'.
      have Hvm'' : evm  {| emem := m1; evm := vm1 |} =[S]  evm s2.
      + by apply: eq_onI Hvm; SvD.fsetdec.
      have -> := readm_ct_lval_eq_on Hr Hvm'' Hw Hw'.
      split=> //. have /= Hvm''' := disjoint_eq_on Hdisj Hw'.
      have /= Hvm1 := disjoint_eq_on Hdisj Hw.
      have /= Hvm2 : evm  {| emem := m1; evm := vm1 |} =[O] evm s2.
      + by apply: eq_onI Hvm; SvD.fsetdec. 
      have Hvm3 := eq_onT Hvm2 Hvm'''. 
      have -> : vm2 =[O] evm s2. 
      + apply: eq_onT Hvm2. by apply: eq_onS. 
      by apply Hvm'''.
    t_xrbindP=> Se Hr' <- Hvm Hsem.
    have /= Hi := sem_IE Hsem. 
    have [v1 [v2 [le' [lw' [He' Ht Hw' ->]]]]]:= sem_iE' Hi.
    have Hvm' : evm  {| emem := m1; evm := vm1 |} =[Se]  evm s2.
    + by apply: eq_onI Hvm; SvD.fsetdec.
    have := read_em_e_eq_on p Hr' Hvm'. rewrite He /= He' /=.
    move=> [] heq <-. have Hvm'' : evm  {| emem := m1; evm := vm1 |} =[S]  evm s2.
    + by apply: eq_onI Hvm; SvD.fsetdec.
    have -> := readm_ct_lval_eq_on Hr Hvm'' Hw Hw'. split=> //.
    rewrite -heq in Ht. rewrite Ht in htr. case: htr=> heq'.
    rewrite heq' in Hw'. have /= Hvm1 := read_lval_eq_on Hw Hw'.
    have Hvm2 : vm1 =[(Sv.diff O (vrv x))] evm s2.
    + by apply: eq_onI Hvm; SvD.fsetdec.
    move=> z hin. apply Hvm1.
    admit.
  Admitted.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
   move=> s1 s2 t o xs es lo. rewrite /sem_sopn /=.
   t_xrbindP=> vs Hes vx Hex -[s1' lw] Hws /= <- <- /=.
   move=> ii I O s2' s2'' li /=. 
   t_xrbindP=> S Hr. case: ifP=> //= Hdisj.
   + t_xrbindP=> S' Hct <- Hvm Hsem.
     have /= Hi := sem_IE Hsem. 
     have [lo' [Hopn ->]]:= sem_iE' Hi. rewrite /sem_sopn /= in Hopn.
     move: Hopn. t_xrbindP=> vs' Hes' vx' Hex' -[s3 lw'] Hws' /= <- <-.
     have Hvm' : evm s1 =[S']  evm s2'.
     + by apply: eq_onI Hvm; SvD.fsetdec.
     have Hvm'' : evm s1 =[S]  evm s2'.
     + by apply: eq_onI Hvm; SvD.fsetdec.
     have -> := (readm_ct_e_es_eq_on p).2 es S' ii s1 s2' vs vs' Hct Hvm' Hes Hes'.
     have -> := readm_ct_lavls_eq_on Hr Hvm'' Hws Hws'. split=> //.
     have /= Hvm''' := disjoint_eq_ons Hdisj Hws.
      have /= Hvm1 := disjoint_eq_ons Hdisj Hws'.
      have /= Hvm2 : evm s1 =[O] evm s2'.
      + by apply: eq_onI Hvm; SvD.fsetdec. 
      have Hvm3 := eq_onT Hvm2 Hvm1. 
      have -> : evm s1' =[O] evm s1. 
      + by apply: eq_onS. 
      by apply Hvm3.
   t_xrbindP=> Se Hr' <- Hvm Hsem.
   have /= Hi := sem_IE Hsem. 
   have [lo' [Hopn ->]]:= sem_iE' Hi. rewrite /sem_sopn /= in Hopn.
   move: Hopn. t_xrbindP=> vs' Hes' vx' Hex' -[s3 lw'] Hws' /= <- <-.
   have Hvm' : evm s1 =[Se]  evm s2'.
   + by apply: eq_onI Hvm; SvD.fsetdec. 
   have Hes'' := (read_em_e_es_eq_on p).2 es Se ii s1 s2' Hr' Hvm'.
   rewrite Hes Hes' in Hes''. case: Hes''=> Heq. rewrite Heq.
   have Hvm'' : evm s1 =[S]  evm s2'.
   + by apply: eq_onI Hvm; SvD.fsetdec. 
   have -> := readm_ct_lavls_eq_on Hr Hvm'' Hws Hws'. split=> //.
   rewrite Heq in Hex. rewrite Hex' in Hex. case: Hex=> Heq'.
   rewrite Heq' in Hws'. have Hvm1 := read_lvals_eq_on Hws Hws'.
   have Hvm2 : evm s1 =[(Sv.diff O (vrvs xs))] evm s2'.
   + by apply: eq_onI Hvm; SvD.fsetdec.

  Admitted.

   
  Local Lemma Hif_true : sem_Ind_if_true p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc Hval Hp Hc ii I O s1' s2' li' /=.
    t_xrbindP=> I' Hch I'' Hch' Se Heh <- Hvm Hsem.
    have /= Hi := sem_IE Hsem. 
    have [b' [le'] [lc'] [He'] Hi' ->]:= sem_iE' Hi.
    have Hvm' : evm s1 =[Se]  evm s1'.
    + by apply: eq_onI Hvm; SvD.fsetdec.
    have He'' := read_em_e_eq_on p Heh Hvm'. rewrite He'' in Hval.
    rewrite He' in Hval.
    case: b' Hi' He' Hval=> //= Hi' He' Hval. 
    have Hvm'' : evm s1 =[I']  evm s1'.
    + by apply: eq_onI Hvm; SvD.fsetdec.
    have [Hvm''' <-] := Hc I' O s1' s2' lc' Hch Hvm'' Hi'. split=> //=.  
    by case: Hval=> <-. 
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc Hval Hp Hc ii I O s1' s2' li' /=.
    t_xrbindP=> I' Hch I'' Hch' Se Heh <- Hvm Hsem.
    have /= Hi := sem_IE Hsem. 
    have [b' [le'] [lc'] [He'] Hi' ->]:= sem_iE' Hi.
    have Hvm' : evm s1 =[Se]  evm s1'.
    + by apply: eq_onI Hvm; SvD.fsetdec.
    have He'' := read_em_e_eq_on p Heh Hvm'. rewrite He'' in Hval.
    rewrite He' in Hval.
    case: b' Hi' He' Hval=> //= Hi' He' Hval. 
    have Hvm'' : evm s1 =[I'']  evm s1'.
    + by apply: eq_onI Hvm; SvD.fsetdec.
    have [Hvm''' <-] := Hc I'' O s1' s2' lc' Hch' Hvm'' Hi'. split=> //=.  
    by case: Hval=> <-. 
  Qed.
   

End Checker_Proof.








