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

Definition leakage_i_trans := leakage_i -> leakage_c.

Definition leakage_c_trans := leakage_c -> leakage_c.

Definition leakage_f_trans := leakage_fun -> leakage_fun.

Definition leakage_empty : leakage_i_trans := fun _ => Lempty.

Definition leakage_c_empty : leakage_c_trans := fun _ => Lempty.

Definition leakage_seq1 : leakage_i_trans := fun li => Lcons li Lempty.

Definition leakage_if (F1 F2: leakage_c_trans) (li : leakage_i) : leakage_c := 
  match li with
  | Lcond le b lc => 
    leakage_seq1 (Lcond le b (if b then F1 lc else F2 lc))
  | _ => Lempty
  end.

Fixpoint leak_for (Fc : leakage_c_trans) (lf : leakage_for) : leakage_for :=
  match lf with 
  | Lfor_empty => Lfor_empty
  | Lfor_one lc lf => (Lfor_one (Fc lc) (leak_for Fc lf))
end.

Fixpoint leakage_for (Fc : leakage_c_trans) (li : leakage_i) : leakage_c :=
  match li with 
  | Lfor le lf => leakage_seq1 (Lfor le (leak_for Fc lf))
  | _ => Lempty
  end.

Fixpoint leak_while (Fc : leakage_c_trans) (Fc' : leakage_c_trans) (li : leakage_i) : leakage_i :=
  match li with
  | Lwhile_true lc le lc' lw => (Lwhile_true (Fc lc) le (Fc' lc) (leak_while Fc Fc' lw))
  | Lwhile_false lc le => (Lwhile_false (Fc lc) le)
  | _ => li
  end.

Fixpoint leakage_while (Fc : leakage_c_trans) (Fc' : leakage_c_trans) (li : leakage_i) : leakage_c :=
  match li with
  | Lwhile_true lc le lc' lw => leakage_seq1 (Lwhile_true (Fc lc) le (Fc' lc) (leak_while Fc Fc' lw))
  | Lwhile_false lc le => leakage_seq1 (Lwhile_false (Fc lc) le)
  | _ => Lempty
  end.

Definition leak_fun (Fc : leakage_c_trans) (lf : leakage_fun) : leakage_fun :=
  match lf with 
  | Lfun lc => Lfun (Fc lc)
  end.


Definition leakage_fun_f (Fc : leakage_c_trans) (li : leakage_i) : leakage_c := 
  match li with 
  | Lcall le lf le' => leakage_seq1 (Lcall le (leak_fun Fc lf) le')
  | _ => Lempty
  end.


Fixpoint leakage_i_c (Fc : leakage_c_trans) (Fi : leakage_i_trans) (lc : leakage_c) : leakage_c := 
  match lc with 
  | Lempty => Lempty
  | Lcons li lc' => (Fi li) ++l (leakage_i_c Fc Fi lc')
  end.

Definition dead_code_c (dead_code_i: instr -> Sv.t -> ciexec (Sv.t * cmd * leakage_i_trans))
                       c s :  ciexec (Sv.t * cmd * leakage_c_trans):=
  foldr (fun i r =>
    Let r := r in
    let: (s1, c1, Fc) := r in 
    Let ri := dead_code_i i s1 in
    let: (si, ci, Fi) := ri in
    ciok (si, ci ++ c1, fun lc => leakage_i_c Fc Fi lc)) (ciok (s,[::],leakage_c_empty)) c.


Section LOOP.

  Variable dead_code_c : Sv.t -> ciexec (Sv.t * cmd * leakage_c_trans).
  Variable dead_code_c2 : Sv.t -> ciexec (Sv.t * (Sv.t * (cmd*cmd) * (leakage_c_trans * leakage_c_trans))).
  Variable ii : instr_info.

  Fixpoint loop (n:nat) (rx:Sv.t) (wx:Sv.t) (s:Sv.t) : ciexec (Sv.t * cmd * leakage_c_trans) :=
    match n with
    | O => cierror ii (Cerr_Loop "dead_code")
    | S n =>
      Let sc := dead_code_c s in
      let: (s',c', F') := sc in
      let s' := Sv.union rx (Sv.diff s' wx) in
      if Sv.subset s' s then ciok (s,c', F')
      else loop n rx wx (Sv.union s s')
    end.

  Fixpoint wloop (n:nat) (s:Sv.t) : ciexec (Sv.t * (cmd * cmd) * (leakage_c_trans * leakage_c_trans)) :=
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

Section Section.

Definition Ff := seq (funname * leakage_c_trans).

Fixpoint find_f_l (f : Ff) (fn : funname) : leakage_c_trans :=
  match f with 
  | x :: xl => if x.1 == fn then x.2 else find_f_l xl fn
  | [::] => leakage_c_empty
  end.

Variable ff : Ff.

Fixpoint dead_code_i (i:instr) (s:Sv.t) {struct i} : ciexec (Sv.t * cmd * leakage_i_trans) :=
  let (ii,ir) := i in
  match ir with
  | Cassgn x tag ty e =>
    let w := write_i ir in
    if tag != AT_keep then
      if disjoint s w && negb (write_mem x) then ciok (s, [::], leakage_empty)
      else if check_nop x ty e then ciok (s, [::], leakage_empty)
      else ciok (read_rv_rec (read_e_rec (Sv.diff s w) e) x, [:: i ], leakage_seq1)
    else   ciok (read_rv_rec (read_e_rec (Sv.diff s w) e) x, [:: i ], leakage_seq1)

  | Copn xs tag o es =>
    let w := vrvs xs in
    if tag != AT_keep then
      if disjoint s w && negb (has write_mem xs) then ciok (s, [::], leakage_empty)
      else if check_nop_opn xs o es then ciok (s, [::], leakage_empty)
      else ciok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i], leakage_seq1)
    else ciok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i], leakage_seq1)

  | Cif b c1 c2 =>
    Let sc1 := dead_code_c dead_code_i c1 s in
    Let sc2 := dead_code_c dead_code_i c2 s in
    let: (s1,c1,F1) := sc1 in
    let: (s2,c2,F2) := sc2 in
    ciok (read_e_rec (Sv.union s1 s2) b, [:: MkI ii (Cif b c1 c2)], leakage_if F1 F2)

  | Cfor x (dir, e1, e2) c =>
    Let sc := loop (dead_code_c dead_code_i c) ii Loop.nb
                   (read_rv (Lvar x)) (vrv (Lvar x)) s in
    let: (s, c, F) := sc in
    ciok (read_e_rec (read_e_rec s e2) e1,[:: MkI ii (Cfor x (dir,e1,e2) c) ], leakage_for F)

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
    ciok (s, [:: MkI ii (Cwhile a c e c') ], leakage_while Fc Fc')

  | Ccall _ xs f es =>
    ciok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i], leakage_fun_f (find_f_l ff f))
  end.

Definition dead_code_fd (fd: fundef) :=
  let 'MkFun ii tyi params c tyo res := fd in
  let s := read_es (map Pvar res) in
  Let c' := dead_code_c dead_code_i c s in
  let: (sc, c, F) := c' in 
  ciok (MkFun ii tyi params c tyo res, leak_fun F).

Definition dead_code_fd' (fdl : fun_decl) : funname * fundef * leakage_f_trans := 
  let fd := fdl.2 in 
  let 'MkFun ii tyi params c tyo res := fd in
  let s := read_es (map Pvar res) in
  Let c' := dead_code_c dead_code_i c s in
  let: (sc, c, F) := c' in 
  (fdl.1, MkFun ii tyi params c tyo res, leak_fun F).

Print dead_code_fd.

Check dead_code_fd.

(* We also need to return (funname * (fundef * (leakage_f_trans))) in dead_code_fd *)

(*Definition dead_code_fd (fd: fundef) : fundef * leakage_f_trans :=
  let 'MkFun ii tyi params c tyo res := fd in
  let s := read_es (map Pvar res) in
  Let c' := dead_code_c dead_code_i c s in
  let: (sc, c, F) := c' in 
  ciok (MkFun ii tyi params c tyo res, leak_fun F).*)

End Section.



Definition dead_code_prog (p: prog) : cfexec prog :=
  Let funcs := map_cfprog dead_code_fd (p_funcs p) in
            : list (funname * (fundef * leak_f_trans))
  Let leaks := map (fun (fn, (fd,Ff)) => (fn, Ff)) funcs in
  Let funcs := map (fun (fn, (fd,Ff)) => (fn, fd)) funcs in
  
Definition leak_f
  ok {| p_globs := p_globs p; p_funcs := funcs |}.


[f1 ; f2 ]

f2 { f1 } 