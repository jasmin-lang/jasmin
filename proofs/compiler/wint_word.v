(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Import expr sem_op_typed compiler_util.
Import Utf8.
Import oseq.
Require Import flag_combination.

Local Open Scope seq_scope.
Local Open Scope Z_scope.

Section WITH_PARAMS.

Context `{asmop:asmOp}.

Definition wi2w_opk (k : EO.op_kind) : op_kind :=
  match k with
  | EO.Op_int => Op_int
  | EO.Op_w _ _ sz => Op_w sz
  end.

Definition wi2w_cmpk (k : EO.op_kind) : cmp_kind :=
  match k with
  | EO.Op_int => Cmp_int
  | EO.Op_w _ s sz => Cmp_w s sz
  end.

Definition wi2w_op1 (o : EO.sop1) (e : pexpr) : pexpr :=
  match o with
  | EO.Oword_of_int _ _ sz => Papp1 (Oword_of_int sz) e
  | EO.Oint_of_word _ s sz => Papp1 (Oint_of_word s sz) e
  | EO.Oword_of_wint _ _ => e
  | EO.Owint_of_word _ _ => e
  | EO.Oword_ext _ s sz1 sz2 =>
    let o := if s is Unsigned then Ozeroext sz1 sz2 else Osignext sz1 sz2 in
    Papp1 o e
  | EO.Onot => Papp1 Onot e
  | EO.Olnot sz => Papp1 (Olnot sz) e
  | EO.Oneg k => Papp1 (Oneg (wi2w_opk k)) e
  end.

Definition signedness_div si k :=
  match k with
  | EO.Op_int => si
  | EO.Op_w _ si _ => si
  end.

Definition wi2w_op2 (o : EO.sop2) : sop2 :=
  match o with
  | EO.Obeq => Obeq
  | EO.Oand => Oand
  | EO.Oor  => Oor
  | EO.Oadd k => Oadd (wi2w_opk k)
  | EO.Omul k => Omul (wi2w_opk k)
  | EO.Osub k => Osub (wi2w_opk k)
  | EO.Oeq  k => Oeq  (wi2w_opk k)
  | EO.Oneq k => Oneq (wi2w_opk k)
  | EO.Olt  k => Olt  (wi2w_cmpk k)
  | EO.Ole  k => Ole  (wi2w_cmpk k)
  | EO.Ogt  k => Ogt  (wi2w_cmpk k)
  | EO.Oge  k => Oge  (wi2w_cmpk k)
  | EO.Odiv si k => Odiv (signedness_div si k) (wi2w_opk k)
  | EO.Omod si k => Omod (signedness_div si k) (wi2w_opk k)
  | EO.Oshl k => Olsl (wi2w_opk k)

  | EO.Oshr k =>
    match k with
    | EO.Op_int => Oasr Op_int
    | EO.Op_w _ s sz => if s is Signed then Oasr (Op_w sz) else Olsr sz
    end
  | EO.Oland sz => Oland sz
  | EO.Olor  sz => Olor  sz
  | EO.Olxor sz => Olxor sz
  | EO.Oror  sz => Oror  sz
  | EO.Orol  sz => Orol  sz
  | EO.Ovadd ve sz => Ovadd ve sz
  | EO.Ovsub ve sz => Ovsub ve sz
  | EO.Ovmul ve sz => Ovmul ve sz
  | EO.Ovlsr ve sz => Ovlsr ve sz
  | EO.Ovlsl ve sz => Ovlsl ve sz
  | EO.Ovasr ve sz => Ovasr ve sz
  end.

Fixpoint wi2w_e (e:eexpr) : pexpr :=
  match e with
  | Pconst i => Pconst i
  | Pbool b => Pbool b
  | Parr_init len => Parr_init len
  | Pvar x => Pvar x
  | Pget al aa ws x e => Pget al aa ws x (wi2w_e e)
  | Psub al ws len x e => Psub al ws len x (wi2w_e e)
  | Pload al ws x e => Pload al ws x (wi2w_e e)
  | Papp1 o e => wi2w_op1 o (wi2w_e e)
  | Papp2 o e1 e2 => Papp2 (wi2w_op2 o) (wi2w_e e1) (wi2w_e e2)
  | PappN o es => PappN o (map wi2w_e es)
  | Pif ty e1 e2 e3 => Pif ty (wi2w_e e1) (wi2w_e e2) (wi2w_e e3)
  end.

Definition wi2w_lv (x : elval) : lval :=
  match x with
  | Lnone vi t => Lnone vi t
  | Lvar x => Lvar x
  | Lmem al ws x e => Lmem al ws x (wi2w_e e)
  | Laset al aa ws x e => Laset al aa ws x (wi2w_e e)
  | Lasub aa ws len x e => Lasub aa ws len x (wi2w_e e)
  end.

Fixpoint wi2w_ir (ir:einstr_r) : instr_r :=
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

with wi2w_i (i:einstr) : instr :=
  let (ii,ir) := i in
  MkI ii (wi2w_ir ir).

Definition wi2w_fun (f: efundef) :=
  let 'MkFun ii si p c so r ev := f in
  MkFun ii si p (map wi2w_i c) so r ev.

Definition wi2w_prog (p:eprog) : prog := map_prog wi2w_fun p.

End WITH_PARAMS.
