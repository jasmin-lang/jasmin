From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util expr allocation remove_assert.

Section LEGALIZE_NAMES.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
  (rename : funname -> var -> Ident.ident)
.

#[local] Existing Instance progUnit.

Definition legalize_names_LC : LoopCounter :=
  {|
    loop_counter := 100;
    loop_counterP := erefl;
  |}.

Definition sigma_var (fn : funname) (x : var) : var :=
  {|
    vtype := x.(vtype);
    vname := rename fn x;
  |}.

Definition sigma_var_i (fn : funname) (x : var_i) : var_i :=
  {|
    v_var := sigma_var fn x.(v_var);
    v_info := x.(v_info);
  |}.

Definition sigma_gvar (fn : funname) (x : gvar) : gvar :=
  match x.(gs) with
  | Slocal =>
    {|
      gv := sigma_var_i fn x.(gv);
      gs := Slocal;
    |}
  | Sglob => x
  end.

Fixpoint sigma_e (fn : funname) (e : pexpr) : pexpr :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ _ => e
  | Pvar x => Pvar (sigma_gvar fn x)
  | Pget al aa ws x e => Pget al aa ws (sigma_gvar fn x) (sigma_e fn e)
  | Psub aa ws len x e => Psub aa ws len (sigma_gvar fn x) (sigma_e fn e)
  | Pload al ws e => Pload al ws (sigma_e fn e)
  | Papp1 o e => Papp1 o (sigma_e fn e)
  | Papp2 o e1 e2 => Papp2 o (sigma_e fn e1) (sigma_e fn e2)
  | PappN o es => PappN o (map (sigma_e fn) es)
  | Pif ty b e1 e2 => Pif ty (sigma_e fn b) (sigma_e fn e1) (sigma_e fn e2)
  end.

Definition sigma_es (fn : funname) := map (sigma_e fn).

Fixpoint sigma_eassert (fn : funname) (a : eassert) : eassert :=
  match a with
  | Pexpr e => Pexpr (sigma_e fn e)
  | PappN_safety o es => PappN_safety o (map (sigma_e fn) es)
  | Pis_var_init x => Pis_var_init (sigma_var_i fn x)
  | Pis_mem_init e1 e2 => Pis_mem_init (sigma_e fn e1) (sigma_e fn e2)
  | Pand a1 a2 => Pand (sigma_eassert fn a1) (sigma_eassert fn a2)
  end.

Definition sigma_assertion (fn : funname) (a : assertion) : assertion :=
  let '(lbl, e) := a in (lbl, sigma_eassert fn e).

Definition sigma_assertions (fn : funname) := map (sigma_assertion fn).

Definition sigma_lval (fn : funname) (x : lval) : lval :=
  match x with
  | Lnone _ _ => x
  | Lvar x => Lvar (sigma_var_i fn x)
  | Lmem al ws vi e => Lmem al ws vi (sigma_e fn e)
  | Laset al aa ws x e => Laset al aa ws (sigma_var_i fn x) (sigma_e fn e)
  | Lasub aa ws len x e => Lasub aa ws len (sigma_var_i fn x) (sigma_e fn e)
  end.

Definition sigma_lvals (fn : funname) := map (sigma_lval fn).

Let sigma_ii_aux rc (i : instr) : instr :=
  let 'MkI ii ir := i in MkI ii (rc ir).

Let sigma_c_aux rc (c : cmd) : cmd := map (sigma_ii_aux rc) c.

Fixpoint sigma_ir (fn : funname) (ir : instr_r) : instr_r :=
  let rec := sigma_c_aux (sigma_ir fn) in
  match ir with
  | Cassgn x tg ty e => Cassgn (sigma_lval fn x) tg ty (sigma_e fn e)
  | Copn xs t o es => Copn (sigma_lvals fn xs) t o (sigma_es fn es)
  | Csyscall xs o es => Csyscall (sigma_lvals fn xs) o (sigma_es fn es)
  | Cassert a => Cassert (sigma_assertion fn a)
  | Cif e c1 c2 => Cif (sigma_e fn e) (rec c1) (rec c2)
  | Cfor x (dir, lo, hi) c =>
      Cfor (sigma_var_i fn x) (dir, sigma_e fn lo, sigma_e fn hi) (rec c)
  | Cwhile al c1 e info c2 =>
      Cwhile al (rec c1) (sigma_e fn e) info (rec c2)
  | Ccall xs f es => Ccall (sigma_lvals fn xs) f (sigma_es fn es)
  end.

Definition sigma_i (fn : funname) := sigma_ii_aux (sigma_ir fn).
Definition sigma_c (fn : funname) := sigma_c_aux (sigma_ir fn).

Definition sigma_contract (fn : funname) (c : fun_contract) : fun_contract :=
  {|
    f_iparams := map (sigma_var_i fn) c.(f_iparams);
    f_ires := map (sigma_var_i fn) c.(f_ires);
    f_pre := sigma_assertions fn c.(f_pre);
    f_post := sigma_assertions fn c.(f_post);
  |}.

Definition sigma_fd (fn : funname) (fd : _fundef unit) : _fundef unit :=
  {|
    f_info := fd.(f_info);
    f_contract := option_map (sigma_contract fn) fd.(f_contract);
    f_tyin := fd.(f_tyin);
    f_params := map (sigma_var_i fn) fd.(f_params);
    f_body := sigma_c fn fd.(f_body);
    f_tyout := fd.(f_tyout);
    f_res := map (sigma_var_i fn) fd.(f_res);
    f_extra := fd.(f_extra);
  |}.

Definition sigma_fun_decl
  (fd : funname * _fundef unit) : funname * _fundef unit :=
  let '(fn, fd) := fd in (fn, sigma_fd fn fd).

Definition legalize_names_p (p : _uprog) : _uprog :=
  {|
    p_funcs := map sigma_fun_decl p.(p_funcs);
    p_globs := p.(p_globs);
    p_extra := p.(p_extra);
  |}.

Definition legalize_names_dead_vars
  (fd : _ufun_decl) (ii : instr_info) : Sv.t := Sv.empty.

Definition legalize_names_prog (p : _uprog) : cexec _uprog :=
  let p0 := remove_assert_prog p in
  let p' := legalize_names_p p0 in
  Let _ :=
    check_uprog (wsw := nosubword) (LC := legalize_names_LC)
      legalize_names_dead_vars
      p0.(p_extra) p0.(p_funcs) p'.(p_extra) p'.(p_funcs)
  in
  ok p'.

End LEGALIZE_NAMES.
