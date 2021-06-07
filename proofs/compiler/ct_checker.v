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
From mathcomp Require Import all_ssreflect.
Require Import expr compiler_util ZArith.
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

Definition read_ctem (ii:instr_info) (e:pexpr) :=
   let (se,usem) := ct_e e in
   if usem then error ii
   else ok se.

Fixpoint ct_i (i:instr) (s:Sv.t) {struct i} : ciexec Sv.t :=
  let (ii,ir) := i in
  match ir with
  | Cassgn x tag ty e =>
    let sx := vrv x in
    Let sx' := readm_lval ii x in 
    if Sv.exists_ (fun x => Sv.mem x s) sx then
      Let se := read_em ii e in 
      ok (Sv.union sx' (Sv.union (Sv.diff s sx) se))
    else 
      Let se := read_ctem ii e in 
      ok (Sv.union sx' (Sv.union se s))

  | Cif b c1 c2 =>
    Let s1 := ct_c ct_i c1 s in
    Let s2 := ct_c ct_i c2 s in
    Let sb := read_em ii b in
    ok (Sv.union (Sv.union s1 s2) sb)

| _ => error ii
end.


      
    (* x = e *)
    (* s1 = 
        if x \in read_e then 
          s \{x} U read_e 
        else s
       ct_expr e -> Sv.t 
        


    let w := write_i ir in
    if tag != AT_keep then
      if disjoint s w && negb (write_mem x) then ciok (s, [::], LT_iremove)
      else if check_nop x ty e then ciok (s, [::], LT_iremove)
      else ciok (read_rv_rec (read_e_rec (Sv.diff s w) e) x, [:: i ], LT_ikeep)
    else   ciok (read_rv_rec (read_e_rec (Sv.diff s w) e) x, [:: i ], LT_ikeep)

  | Copn xs tag o es =>
    let w := vrvs xs in
    if tag != AT_keep then
      if disjoint s w && negb (has write_mem xs) then ciok (s, [::], LT_iremove)
      else if check_nop_opn xs o es then ciok (s, [::], LT_iremove)
      else ciok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i], LT_ikeep)
    else ciok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i], LT_ikeep)

  | Cif b c1 c2 =>
    Let sc1 := dead_code_c dead_code_i c1 s in
    Let sc2 := dead_code_c dead_code_i c2 s in
    let: (s1,c1,F1) := sc1 in
    let: (s2,c2,F2) := sc2 in
    ciok (read_e_rec (Sv.union s1 s2) b, [:: MkI ii (Cif b c1 c2)], LT_icond (LT_id) F1 F2)

  | Cfor x (dir, e1, e2) c =>
    Let sc := loop (dead_code_c dead_code_i c) ii Loop.nb
                   (read_rv (Lvar x)) (vrv (Lvar x)) s in
    let: (s, c, F) := sc in
    ciok (read_e_rec (read_e_rec s e2) e1,[:: MkI ii (Cfor x (dir,e1,e2) c) ], LT_ifor LT_id F)

  | Cwhile a c e c' =>
    let dobody s_o :=
    let s_o' := read_e_rec s_o e in
    Let sci := dead_code_c dead_code_i c s_o' in
    let: (s_i, c, Fc) := sci in
    Let sci' := dead_code_c dead_code_i c' s_i in
    let: (s_i', c', Fc') := sci' in
    ok (s_i', (s_i, (c,c'), (Fc,Fc'))) in
    Let sc := wloop dobody ii Loop.nb s in
    let: (s, (c,c'), (Fc,Fc')) := sc in
    ciok (s, [:: MkI ii (Cwhile a c e c') ], LT_iwhile Fc LT_id Fc')

  | Ccall _ xs f es =>
    ciok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i], LT_icall f LT_id LT_id)
  end.

Definition dead_code_fd (fd: fundef) :=
  let 'MkFun ii tyi params c tyo res := fd in
  let s := read_es (map Pvar res) in
  Let c := dead_code_c dead_code_i c s in
  let: (s,c,F) := c in
  ciok (MkFun ii tyi params c tyo res, F).

Definition dead_code_prog (p: prog) : cfexec (prog * leak_f_tr) :=
  Let funcs := map_cfprog_leak dead_code_fd (p_funcs p) in
  ok ({| p_globs := p_globs p; p_funcs := funcs.1 |}, funcs.2).





