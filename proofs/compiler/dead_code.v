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

Inductive leak_trans_i : Type :=
  | LTremove : leak_trans_i
  | LTkeep   : leak_trans_i
  | LTsub1   : seq leak_trans_i -> leak_trans_i 
  | LTsub2   : seq leak_trans_i -> seq leak_trans_i -> leak_trans_i.

Notation leak_trans_c := (seq leak_trans_i).

Definition dead_code_c (dead_code_i: instr -> Sv.t -> ciexec (Sv.t * cmd * leak_trans_i))
                       c s :  ciexec (Sv.t * cmd * leak_trans_c):=
  foldr (fun i r =>
    Let r := r in
    let: (s1, c1, Fc) := r in 
    Let ri := dead_code_i i s1 in
    let: (si, ci, Fi) := ri in
    ciok (si, ci ++ c1, Fi :: Fc)) (ciok (s,[::], [::])) c.


Section LOOP.

  Variable dead_code_c : Sv.t -> ciexec (Sv.t * cmd * leak_trans_c).
  Variable dead_code_c2 : Sv.t -> ciexec (Sv.t * (Sv.t * (cmd*cmd) * (leak_trans_c * leak_trans_c))).
  Variable ii : instr_info.

  Fixpoint loop (n:nat) (rx:Sv.t) (wx:Sv.t) (s:Sv.t) : ciexec (Sv.t * cmd * leak_trans_c) :=
    match n with
    | O => cierror ii (Cerr_Loop "dead_code")
    | S n =>
      Let sc := dead_code_c s in
      let: (s',c', F') := sc in
      let s' := Sv.union rx (Sv.diff s' wx) in
      if Sv.subset s' s then ciok (s,c', F')
      else loop n rx wx (Sv.union s s')
    end.

  Fixpoint wloop (n:nat) (s:Sv.t) : ciexec (Sv.t * (cmd * cmd) * (leak_trans_c * leak_trans_c)) :=
    match n with
    | O =>  cierror ii (Cerr_Loop "dead_code")
    | S n =>
      Let sc := dead_code_c2 s in
      let: (s',sic) := sc in
      if Sv.subset s' s then ciok sic
      else wloop n (Sv.union s s')
    end.

End LOOP.

Definition write_mem (r:lval) : bool :=
  if r is Lmem _ _ _ then true else false.

Definition check_nop (rv:lval) ty (e:pexpr) :=
  match rv, e with
  | Lvar x1, Pvar x2 => (x1.(v_var) == x2.(v_var)) && (ty == vtype x1.(v_var))
  | _, _ => false
  end.

Definition check_nop_opn (xs:lvals) (o: sopn) (es:pexprs) :=
  match xs, o, es with
  | [:: x], Ox86 (MOV sz), [:: e] => check_nop x (sword sz) e
  | _, _, _ => false
  end.

Fixpoint dead_code_i (i:instr) (s:Sv.t) {struct i} : ciexec (Sv.t * cmd * leak_trans_i) :=
  let (ii,ir) := i in
  match ir with
  | Cassgn x tag ty e =>
    let w := write_i ir in
    if tag != AT_keep then
      if disjoint s w && negb (write_mem x) then ciok (s, [::], LTremove)
      else if check_nop x ty e then ciok (s, [::], LTremove)
      else ciok (read_rv_rec (read_e_rec (Sv.diff s w) e) x, [:: i ], LTkeep)
    else   ciok (read_rv_rec (read_e_rec (Sv.diff s w) e) x, [:: i ], LTkeep)

  | Copn xs tag o es =>
    let w := vrvs xs in
    if tag != AT_keep then
      if disjoint s w && negb (has write_mem xs) then ciok (s, [::], LTremove)
      else if check_nop_opn xs o es then ciok (s, [::], LTremove)
      else ciok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i], LTkeep)
    else ciok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i], LTkeep)

  | Cif b c1 c2 =>
    Let sc1 := dead_code_c dead_code_i c1 s in
    Let sc2 := dead_code_c dead_code_i c2 s in
    let: (s1,c1,F1) := sc1 in
    let: (s2,c2,F2) := sc2 in
    ciok (read_e_rec (Sv.union s1 s2) b, [:: MkI ii (Cif b c1 c2)], LTsub2 F1 F2)

  | Cfor x (dir, e1, e2) c =>
    Let sc := loop (dead_code_c dead_code_i c) ii Loop.nb
                   (read_rv (Lvar x)) (vrv (Lvar x)) s in
    let: (s, c, F) := sc in
    ciok (read_e_rec (read_e_rec s e2) e1,[:: MkI ii (Cfor x (dir,e1,e2) c) ], LTsub1 F)

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
    ciok (s, [:: MkI ii (Cwhile a c e c') ], LTsub2 Fc Fc')

  | Ccall _ xs f es =>
    ciok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i], LTkeep)
  end.

Definition dead_code_fd (fd: fundef) :=
  let 'MkFun ii tyi params c tyo res := fd in
  let s := read_es (map Pvar res) in
  Let c := dead_code_c dead_code_i c s in
  let: (s,c,F) := c in
  ciok (MkFun ii tyi params c tyo res, F).

Definition leak_trans_fs := seq (funname * leak_trans_c).

Definition dead_code_prog (p: prog) : cfexec (prog * leak_trans_fs) :=
  Let funcs := map_cfprog dead_code_fd (p_funcs p) in        
  let Fs := map (fun nfl => (nfl.1, nfl.2.2)) funcs in
  let funcs := map (fun p => (p.1, p.2.1)) funcs in
  ok ({| p_globs := p_globs p; p_funcs := funcs |}, Fs).

Section LEAK_TRANS.

Variable (Ffs: seq (funname * leak_trans_c)).

Section LEAK_TRANS_LOOP.

  Variable (lrm_i : leak_i -> leak_trans_i -> leak_c).

  Definition lrm_c (lt:leak_trans_c) (lc:leak_c) : leak_c := 
    flatten (map2 lrm_i lc lt).

  Fixpoint lrm_w (lt1 lt2: leak_trans_c) (li: leak_i) : leak_i := 
    match li with
    | Lwhile_false lc1 le => 
      Lwhile_false (lrm_c lt1 lc1) le
    | Lwhile_true lc1 le lc2 li => 
      Lwhile_true (lrm_c lt1 lc1) le (lrm_c lt2 lc2) (lrm_w lt1 lt2 li)
    | _ => (* absurd *)
      li
    end.

  Definition lrm_for (lt:leak_trans_c) (lfor:leak_for) :=
    map (lrm_c lt) lfor.

  Definition lrm_fun (lf: leak_fun) := 
    let fn := lf.1 in
    let lt := odflt [::] (get_fundef Ffs fn) in
    (fn, lrm_c lt lf.2).

End LEAK_TRANS_LOOP.

Fixpoint lrm_i (li: leak_i) (lt: leak_trans_i) {struct li} : leak_c :=
  match lt, li with
  | LTremove, _ => [::]

  | LTkeep, Lcall la lf le => [:: Lcall la (lrm_fun lrm_i lf) le] 

  | LTkeep, _   => [:: li]

  | LTsub1 lt, Lfor le lfor => 
    [:: Lfor le (lrm_for lrm_i lt lfor)]  

  | LTsub2 lt1 lt2, Lcond le b lc =>
    [:: Lcond le b (lrm_c lrm_i (if b then lt1 else lt2) lc) ] 

  | LTsub2 lt1 lt2, (Lwhile_true _ _ _ _ | Lwhile_false _ _) =>
    [:: lrm_w lrm_i lt1 lt2 li] 
 
  | _, _ => (* absurd *) [:: li ]
  end.

End LEAK_TRANS.

(* Ouf ! *)


