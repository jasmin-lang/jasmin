(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Import expr sem_op_typed compiler_util allocation.
Import Utf8.
Import oseq.
Require Import flag_combination.

Local Open Scope seq_scope.
Local Open Scope Z_scope.


Definition wi2w_wiop1 s (o : wiop1) (e : pexpr) : pexpr :=
  match o with
  | WIwint_of_int sz => Papp1 (Oword_of_int sz) e
  | WIint_of_wint sz => Papp1 (Oint_of_word s sz) e
  | WIword_of_wint _ => e
  | WIwint_of_word _ => e
  | WIwint_ext sz1 sz2 =>
    let o := if s is Unsigned then Ozeroext sz1 sz2 else Osignext sz1 sz2 in
    Papp1 o e
  | WIneg sz => Papp1 (Oneg (Op_w sz)) e
  end.

Definition wi2w_op1 (o : sop1) (e : pexpr) : pexpr :=
  if o is Owi1 s o then wi2w_wiop1 s o e else Papp1 o e.

Definition wi2w_wiop2 s sz (o : wiop2) : sop2 :=
  match o with
  | WIadd => Oadd (Op_w sz)
  | WImul => Omul (Op_w sz)
  | WIsub => Osub (Op_w sz)
  | WIeq  => Oeq  (Op_w sz)
  | WIneq => Oneq (Op_w sz)
  | WIlt  => Olt  (Cmp_w s sz)
  | WIle  => Ole  (Cmp_w s sz)
  | WIgt  => Ogt  (Cmp_w s sz)
  | WIge  => Oge  (Cmp_w s sz)
  | WIdiv => Odiv s (Op_w sz)
  | WImod => Omod s (Op_w sz)
  | WIshl => Olsl (Op_w sz)
  | WIshr => if s is Signed then Oasr (Op_w sz) else Olsr sz
  end.

Definition wi2w_op2 (o : sop2) : sop2 :=
  if o is Owi2 s sz o then wi2w_wiop2 s sz o else o.

Fixpoint wi2w_e (e: pexpr) : pexpr :=
  match e with
  | Pconst _
  | Pbool _
  | Parr_init _
  | Pvar _
      => e
  | Pget al aa ws x e => Pget al aa ws x (wi2w_e e)
  | Psub al ws len x e => Psub al ws len x (wi2w_e e)
  | Pload al ws x e => Pload al ws x (wi2w_e e)
  | Papp1 o e => wi2w_op1 o (wi2w_e e)
  | Papp2 o e1 e2 => Papp2 (wi2w_op2 o) (wi2w_e e1) (wi2w_e e2)
  | PappN o es => PappN o (map wi2w_e es)
  | Pif ty e1 e2 e3 => Pif ty (wi2w_e e1) (wi2w_e e2) (wi2w_e e3)
  end.

Definition wi2w_lv (x : lval) : lval :=
  match x with
  | Lnone vi t => Lnone vi t
  | Lvar x => Lvar x
  | Lmem al ws x e => Lmem al ws x (wi2w_e e)
  | Laset al aa ws x e => Laset al aa ws x (wi2w_e e)
  | Lasub aa ws len x e => Lasub aa ws len x (wi2w_e e)
  end.

Section WITH_PARAMS.

Context `{asmop:asmOp}.

Fixpoint wi2w_ir (ir:instr_r) : instr_r :=
  match ir with
  | Cassgn x tag ty e =>
    Cassgn (wi2w_lv x) tag ty (wi2w_e e)

  | Copn xs t o es =>
    Copn (map wi2w_lv xs) t o (map wi2w_e es)

  | Csyscall xs o es =>
    Csyscall (map wi2w_lv xs) o (map wi2w_e es)

  | Cif b c1 c2 =>
    Cif (wi2w_e b) (map wi2w_i c1) (map wi2w_i c2)

  | Cfor x (dir, e1, e2) c =>
    Cfor x (dir, wi2w_e e1, wi2w_e e2) (map wi2w_i c)

  | Cwhile a c e info c' =>
    Cwhile a (map wi2w_i c) (wi2w_e e) info (map wi2w_i c')

  | Ccall xs f es =>
    Ccall (map wi2w_lv xs) f (map wi2w_e es)

  end

with wi2w_i (i:instr) : instr :=
  let (ii,ir) := i in
  MkI ii (wi2w_ir ir).

Definition wi2w_fun {eft} (f: _fundef eft) :=
  let 'MkFun ii si p c so r ev := f in
  MkFun ii si p (map wi2w_i c) so r ev.

(* This function is internal, variable annotation still contain "sint" "uint" after this pass *)
Definition wi2w_prog_internal {pT:progT} (p: prog) : prog := map_prog wi2w_fun p.

Definition wi2w_prog {wsw: WithSubWord}
   (remove_wint_annot: funname -> fundef -> fundef)
   (dead_vars_fd : fun_decl → instr_info → Sv.t)
   (p : prog) :=
  let p := wi2w_prog_internal p in
  let pv := map_prog_name remove_wint_annot p in
  Let _ := allocation.check_uprog dead_vars_fd p.(p_extra) p.(p_funcs) pv.(p_extra) pv.(p_funcs) in
  ok pv.

End WITH_PARAMS.
