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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Definition leak_i_trans := leakage_i -> leakage_c.
Definition leak_c_trans := leakage_c -> leakage_c.
Definition leak_f_trans := leakage_fun -> leakage_fun.


Definition dead_code_c (dead_code_i: instr -> Sv.t -> ciexec (Sv.t * cmd * leak_c_trans))
                       c s :  ciexec (Sv.t * cmd):=
  foldr (fun i r =>
    Let r := r in
    Let ri := dead_code_i i r.1 in
    ciok (ri.1, ri.2 ++ r.2)) (ciok (s,[::])) c.

Section LOOP.

  Variable dead_code_c : Sv.t -> ciexec (Sv.t * cmd * leak_c_trans)).
  Variable dead_code_c2 : Sv.t -> ciexec (Sv.t * (Sv.t * (cmd*cmd) * (leak_c_trans * leak_c_trans))).
  Variable ii : instr_info.

  Fixpoint loop (n:nat) (rx:Sv.t) (wx:Sv.t) (s:Sv.t) : ciexec (Sv.t * cmd * leak_c_trans) :=
    match n with
    | O => cierror ii (Cerr_Loop "dead_code")
    | S n =>
      Let sc := dead_code_c s in
      let: (s',c') := sc in
      let s' := Sv.union rx (Sv.diff s' wx) in
      if Sv.subset s' s then ciok (s,c')
      else loop n rx wx (Sv.union s s')
    end.

  Fixpoint wloop (n:nat) (s:Sv.t) : ciexec (Sv.t * (cmd * cmd) * (leak_c_trans * leak_c_trans)) :=
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

Definition leak_empty : leak_i_trans :=
  fun Ffun (_:leakage_i) => Lempty.

Definition leak_seq1 : leak_i_trans := 
   fun Ffun li => Lcons li Lempty.

Definition leak_if (F1 F2: leak_c_trans) : leakage_c := 
  fun Ffun (li:leakage_i) => 
  match li with
  | Lcond le b lc => 
    leak_seq1 (Lcond le b (if b then F1 Ffun lc else F2 Ffun lc))
  | _ => Lempty
  end.

Fixpoint leak_while Fc Fc' (li:leakage_i) := 
  match li with
  | Lwhile_true lc le lc' lw => 
    leak_seq1 (Lwhile_true (Fc lc) le (Fc' lc') (leak_while Fc Fc' lw))
  | Lwhile_false lc le =>
    leak_seq1 (Lwhile_false (Fc lc) le)
  | _ => Lempty
  end.

Section Section.

Variable (Ff: seq (funname * leaf_f_trans)).

Fixpoint dead_code_i (i:instr) (s:Sv.t) {struct i} : ciexec (Sv.t * cmd * leak_i_trans ) :=
  let (ii,ir) := i in
  match ir with
  | Cassgn x tag ty e =>
    let w := write_i ir in
    if tag != AT_keep then
      if disjoint s w && negb (write_mem x) then ciok (s, [::], leak_empty)
      else if check_nop x ty e then ciok (s, [::])
      else ciok (read_rv_rec (read_e_rec (Sv.diff s w) e) x, [:: i ], leak_seq1)
    else   ciok (read_rv_rec (read_e_rec (Sv.diff s w) e) x, [:: i ], leak_seq1)

  | Copn xs tag o es =>
    let w := vrvs xs in
    if tag != AT_keep then
      if disjoint s w && negb (has write_mem xs) then ciok (s, [::], leak_empty)
      else if check_nop_opn xs o es then ciok (s, [::])
      else ciok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i])
    else ciok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i])

  | Cif b c1 c2 =>
    Let sc1 := dead_code_c dead_code_i c1 s in
    Let sc2 := dead_code_c dead_code_i c2 s in
    let: (s1,c1,F1) := sc1 in
    let: (s2,c2,F2) := sc2 in
    ciok (read_e_rec (Sv.union s1 s2) b, [:: MkI ii (Cif b c1 c2)], leak_if F1 F2)

  | Cfor x (dir, e1, e2) c =>
    Let sc := loop (dead_code_c dead_code_i c) ii Loop.nb
                   (read_rv (Lvar x)) (vrv (Lvar x)) s in
    let: (s, c) := sc in
    ciok (read_e_rec (read_e_rec s e2) e1,[:: MkI ii (Cfor x (dir,e1,e2) c) ])

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
    ciok (s, [:: MkI ii (Cwhile a c e c') ], leak_while Fc Fc')

  | Ccall _ xs f es =>
    let Ff := Ffun f in
    ciok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i], (fun Ffun =>  )

    end
  end.

Definition dead_code_fd (fd: fundef) : fundef * leak_f_trans :=
  let 'MkFun ii tyi params c tyo res := fd in
  let s := read_es (map Pvar res) in
  Let c := dead_code_c dead_code_i c s in
  ciok (MkFun ii tyi params c.2 tyo res, ....).

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