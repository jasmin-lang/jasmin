Require Import expr.

Section NORMALIZE_COND.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
.

Fixpoint normalize_cond_e (e : pexpr) : pexpr :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ _ | Pvar _ => e
  | Pget al aa ws x e => Pget al aa ws x (normalize_cond_e e)
  | Psub aa ws len x e => Psub aa ws len x (normalize_cond_e e)
  | Pload al ws e => Pload al ws (normalize_cond_e e)
  | Papp1 o e => Papp1 o (normalize_cond_e e)
  | Papp2 o e1 e2 =>
      let e1 := normalize_cond_e e1 in
      let e2 := normalize_cond_e e2 in
      match o with
      | Ogt k => Papp2 (Olt k) e2 e1
      | Oge k => Papp2 (Ole k) e2 e1
      | _ => Papp2 o e1 e2
      end
  | PappN o es => PappN o (map normalize_cond_e es)
  | Pif ty b e1 e2 =>
      Pif ty (normalize_cond_e b) (normalize_cond_e e1) (normalize_cond_e e2)
  end.

Definition normalize_cond_es := map normalize_cond_e.

Fixpoint normalize_cond_eassert (a : eassert) : eassert :=
  match a with
  | Pexpr e => Pexpr (normalize_cond_e e)
  | PappN_safety o es => PappN_safety o [seq normalize_cond_e e | e <- es]
  | Pis_var_init x => Pis_var_init x
  | Pis_mem_init e1 e2 =>
    Pis_mem_init (normalize_cond_e e1) (normalize_cond_e e2)
  | Pand a1 a2 =>
    Pand (normalize_cond_eassert a1) (normalize_cond_eassert a2)
  end.

Definition normalize_cond_assertion (a : assertion) : assertion :=
  let '(lbl, e) := a in (lbl, normalize_cond_eassert e).

Definition normalize_cond_lval (x : lval) : lval :=
  match x with
  | Lnone _ _ | Lvar _ => x
  | Lmem al ws vi e => Lmem al ws vi (normalize_cond_e e)
  | Laset al aa ws x e => Laset al aa ws x (normalize_cond_e e)
  | Lasub aa ws len x e => Lasub aa ws len x (normalize_cond_e e)
  end.

Definition normalize_cond_lvals := map normalize_cond_lval.

Let normalize_cond_ii_aux nc (i : instr) : instr :=
  let 'MkI ii ir := i in MkI ii (nc ii ir).

Let normalize_cond_c_aux nc (c : cmd) : cmd := map (normalize_cond_ii_aux nc) c.

Fixpoint normalize_cond_i (ii : instr_info) (i : instr_r) : instr_r :=
  let rec := normalize_cond_c_aux normalize_cond_i in
  match i with
  | Cassgn x tg ty e =>
      Cassgn (normalize_cond_lval x) tg ty (normalize_cond_e e)
  | Copn xs t o es =>
      Copn (normalize_cond_lvals xs) t o (normalize_cond_es es)
  | Csyscall xs o es =>
      Csyscall (normalize_cond_lvals xs) o (normalize_cond_es es)
  | Cassert a => Cassert (normalize_cond_assertion a)
  | Cif e c1 c2 => Cif (normalize_cond_e e) (rec c1) (rec c2)
  | Cfor x (dir, lo, hi) c =>
      Cfor x (dir, normalize_cond_e lo, normalize_cond_e hi) (rec c)
  | Cwhile al c1 e info c2 =>
      Cwhile al (rec c1) (normalize_cond_e e) info (rec c2)
  | Ccall xs f es =>
      Ccall (normalize_cond_lvals xs) f (normalize_cond_es es)
  end.

Definition normalize_cond_ii := normalize_cond_ii_aux normalize_cond_i.
Definition normalize_cond_c := normalize_cond_c_aux normalize_cond_i.

Definition normalize_cond_fd (fd : _fundef unit) : _fundef unit :=
  {|
    f_info := f_info fd;
    f_contract := f_contract fd;
    f_tyin := f_tyin fd;
    f_params := f_params fd;
    f_body := normalize_cond_c fd.(f_body);
    f_tyout := f_tyout fd;
    f_res := f_res fd;
    f_extra := f_extra fd;
  |}.

Definition normalize_cond_fun_decl
  (fd : funname * _fundef unit) : funname * _fundef unit :=
  let '(fn, fd) := fd in (fn, normalize_cond_fd fd).

Definition normalize_cond_prog (p : _uprog) : _uprog :=
  {|
    p_funcs := map normalize_cond_fun_decl (p_funcs p);
    p_globs := p_globs p;
    p_extra := p_extra p;
  |}.

End NORMALIZE_COND.
