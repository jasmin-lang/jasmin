(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect.
Require Import expr compiler_util ZArith.
Require Export leakage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.


Definition dead_code_c (dead_code_i: instr -> Sv.t -> ciexec (Sv.t * cmd * leak_i_tr))
                       c s :  ciexec (Sv.t * cmd * leak_c_tr):=
  foldr (fun i r =>
    Let r := r in
    let: (s1, c1, Fc) := r in 
    Let ri := dead_code_i i s1 in
    let: (si, ci, Fi) := ri in
    ciok (si, ci ++ c1, Fi :: Fc)) (ciok (s,[::], [::])) c.


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

Definition write_mem (r:lval) : bool :=
  if r is Lmem _ _ _ then true else false.

Definition check_nop (rv:lval) ty (e:pexpr) :=
  match rv, e with
  | Lvar x1, Pvar x2 => (x1.(v_var) == x2.(v_var)) && (ty == vtype x1.(v_var))
  | _, _ => false
  end.

(* TODO: this should be factorized out to be independant of x86 *)
Definition check_nop_opn (xs:lvals) (o: sopn) (es:pexprs) :=
  match xs, o, es with
  | [:: x], Ox86 (MOV sz), [:: e] => check_nop x (sword sz) e
  | [:: x], Ox86 (VMOVDQU sz), [:: e] => check_nop x (sword sz) e
  | _, _, _ => false
  end.

Fixpoint dead_code_i (i:instr) (s:Sv.t) {struct i} : ciexec (Sv.t * cmd * leak_i_tr) :=
  let (ii,ir) := i in
  match ir with
  | Cassgn x tag ty e =>
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





