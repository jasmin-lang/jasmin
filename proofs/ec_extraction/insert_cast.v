From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Require Import expr compiler_util word safety.

Module Import E.

  Definition pass : string := "insert_cast".

  Definition ierror msg := {|
    pel_msg      := PPEstring msg;
    pel_fn       := None;
    pel_fi       := None;
    pel_ii       := None;
    pel_vi       := None;
    pel_pass     := Some pass;
    pel_internal := true
  |}.

End E.

Section INSERT.

Context `{asmop:asmOp} {pd: PointerData} {msfsz : MSFsize}.

Definition add_cast (e : pexpr) (ty : atype) : pexpr :=
  let ety := type_of_expr e in
  if convertible ety ty then e
  else match ty, ety with
  | aword ws, aword ews =>
      if (ws <= ews)%CMP then Papp1 (Ozeroext ws ews) e
      else e
  | _, _ => e
  end.

Fixpoint insert_cast_e (e : pexpr) : pexpr :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ _ | Pvar _ | Pis_var_init _ => e
  | Pget al aa ws x e => Pget al aa ws x (insert_cast_e e)
  | Psub al ws len x e => Psub al ws len x (insert_cast_e e)
  | Pload al ws e => Pload al ws (insert_cast_e e)
  | Papp1 o e =>
      Papp1 o (add_cast (insert_cast_e e) (type_of_op1 o).1)
  | Papp2 o e1 e2 =>
      let: (ty1, ty2, _) := type_of_op2 o in
      Papp2 o (add_cast (insert_cast_e e1) ty1) (add_cast (insert_cast_e e2) ty2)
  | PappN o es =>
      let tys := (type_of_opN o).1 in
      let es := map insert_cast_e es in
      if size tys == size es then PappN o (map2 add_cast es tys)
      else e
  | Pif ty e1 e2 e3 =>
    Pif ty (insert_cast_e e1) (add_cast (insert_cast_e e2) ty) (add_cast (insert_cast_e e3) ty)
  | Pbig _ _ _ _ _ _  => e (* This will be removed *)
  | Pis_mem_init e1 e2 => Pis_mem_init (insert_cast_e e1) (insert_cast_e e2)
  end.

Definition insert_cast_lv (lv : lval) :=
  match lv with
  | Lnone _ _ | Lvar _ => lv
  | Lmem al ws vi e => Lmem al ws vi (insert_cast_e e)
  | Laset al aa ws x e => Laset al aa ws x (insert_cast_e e)
  | Lasub aa ws len x e => Lasub aa ws len x e
  end.

Definition insert_cast_lvs := map insert_cast_lv.

Definition insert_cast_assertion (a : assertion) := (a.1, insert_cast_e a.2).
Definition insert_cast_assertions := map insert_cast_assertion.

Section PROG.

Context (p : _uprog).

Fixpoint insert_cast_i (i : instr) :=
  let (ii, ir) := i in
  let ir :=
    match ir with
    | Cassgn x tag ty e => Cassgn (insert_cast_lv x) tag ty (add_cast (insert_cast_e e) ty)
    | Copn xs tag o es =>
      let tys := sopn_tin o in
      let es := map insert_cast_e es in
      if size tys == size es then Copn (insert_cast_lvs xs) tag o (map2 add_cast es tys)
      else ir
    | Csyscall xs o es =>
      let tys := scs_tin (syscall_sig_u o) in
      let es := map insert_cast_e es in
      if size tys == size es then Csyscall (insert_cast_lvs xs) o (map2 add_cast es tys)
      else ir
    | Cassert a => Cassert (insert_cast_assertion a)
    | Cif e c1 c2 => Cif (insert_cast_e e) (map insert_cast_i c1) (map insert_cast_i c2)
    | Cfor x (d, e1, e2) c => Cfor x (d, insert_cast_e e1, insert_cast_e e2) (map insert_cast_i c)
    | Cwhile al c1 e ii c2 =>
        Cwhile al (map insert_cast_i c1) (insert_cast_e e) ii (map insert_cast_i c2)
    | Ccall xs f es =>
      match get_fundef (p_funcs p) f with
      | None => ir
      | Some fd =>
        let tys := f_tyin fd in
        let es := map insert_cast_e es in
        if size tys == size es then Ccall (insert_cast_lvs xs) f (map2 add_cast es tys)
        else ir
      end
    end in
  MkI ii ir.

Definition insert_cast_fc (fc : fun_contract) :=
  let (p, r, pre, post) := fc in
  MkContra p r (insert_cast_assertions pre) (insert_cast_assertions post).

Definition insert_cast_fd (fd : ufundef) :=
  let (fi, fc, fti, fp, fb, fto, fr, fe) := fd in
  MkFun fi (omap insert_cast_fc fc) fti fp (map insert_cast_i fb) fto fr fe.

Definition insert_cast_prog :=
  map_prog insert_cast_fd p.

End PROG.

End INSERT.
