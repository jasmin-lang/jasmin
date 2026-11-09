From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import expr compiler_util.

Local Open Scope seq_scope.
Local Open Scope Z_scope.

Set Printing Implicit.

(* Make all implicit truncations explicit. *)

Section TOEC_CAST.

Context `{asmop : asmOp} {pd : PointerData} {msfsz : MSFsize}.

Definition toec_cast_c (ec_cast_i : instr -> instr) (c : cmd) : cmd := (map ec_cast_i c).


Definition type_of_expr (e : pexpr) : atype :=
  match e with
  | Pconst _            => aint
  | Pbool _             => abool
  | Parr_init ws len    => aarr ws len
  | Pvar x              => vtype (gv x)
  | Pget _ _ ws _ _     => aword ws
  | Psub _ ws len _ _   => aarr ws len
  | Pload _ ws _        => aword ws
  | Papp1 o _           => (type_of_op1 o).2
  | Papp2 o _ _         => (type_of_op2 o).2
  | PappN o _           => (type_of_opN o).2
  | Pif ty _ _ _        => ty
  end.

Definition cast_top (ety gty : atype) (e : pexpr) : pexpr :=
  if ety == gty then e else
  match ety, gty with
  | aword szo, aword szi => if (szo < szi)%CMP then Papp1 (Ozeroext szo szi) e else e
  | _, _ => e
  end.

Definition cast_e (ty : atype) (e : pexpr) : pexpr :=
  cast_top ty (type_of_expr e) e.

Fixpoint cast_es (tys : seq atype) (es : pexprs) : pexprs :=
  match tys, es with
  | ty :: tys, e :: es => cast_e ty e :: cast_es tys es
  | _, _ => es
  end.

Fixpoint toec_cast_rec (e : pexpr) : pexpr :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ _ | Pvar _ => e
  | Pget al aa ws x ei => Pget al aa ws x (cast_e aint (toec_cast_rec ei))
  | Psub aa ws len x ei => Psub aa ws len x (cast_e aint (toec_cast_rec ei))
  | Pload al ws ei => Pload al ws (cast_e (aword Uptr) (toec_cast_rec ei))
  | Papp1 o e1 => Papp1 o (cast_e (type_of_op1 o).1 (toec_cast_rec e1))
  | Papp2 o e1 e2 =>
      Papp2 o (cast_e (type_of_op2 o).1.1 (toec_cast_rec e1))
              (cast_e (type_of_op2 o).1.2 (toec_cast_rec e2))
  | PappN o es => PappN o (cast_es (type_of_opN o).1 (map toec_cast_rec es))
  | Pif ty b e1 e2 =>
      Pif ty (cast_e abool (toec_cast_rec b))
             (cast_e ty (toec_cast_rec e1))
             (cast_e ty (toec_cast_rec e2))
  end.

Definition toec_cast_te (ty : atype) (e : pexpr) : pexpr :=
  cast_e ty (toec_cast_rec e).

Definition toec_cast_es (tys : seq atype) (es : pexprs) : pexprs :=
  cast_es tys (map toec_cast_rec es).

Definition toec_cast_lv (x : lval) : lval :=
  match x with
  | Lnone _ _ | Lvar _ => x
  | Lmem al ws vi e => Lmem al ws vi (toec_cast_te (aword Uptr) e)
  | Laset al aa ws x e => Laset al aa ws x (toec_cast_te aint e)
  | Lasub aa ws len x e => Lasub aa ws len x (toec_cast_te aint e)
  end.

Section FUNSIG.

Context (fun_tyin : funname -> seq atype).

Fixpoint toec_cast_i (i : instr) : instr :=
  let rec_c := toec_cast_c toec_cast_i in
  let 'MkI ii ir := i in
  MkI ii (
      match ir with
      | Cassgn x tg ty e =>
          Cassgn (toec_cast_lv x) tg ty (toec_cast_te ty e)
      | Copn xs tg o es =>
          Copn (map toec_cast_lv xs) tg o (toec_cast_es (sopn_tin o) es)
      | Csyscall xs o es =>
          Csyscall (map toec_cast_lv xs) o
            (toec_cast_es (scs_tin (syscall_sig_u o)) es)
      | Ccall xs f es =>
          Ccall (map toec_cast_lv xs) f (toec_cast_es (fun_tyin f) es)
      | Cassert _ => ir
      | Cif e c1 c2 => Cif (toec_cast_te abool e) (rec_c c1) (rec_c c2)
      | Cfor x (d, lo, hi) c =>
          Cfor x (d, toec_cast_te aint lo, toec_cast_te aint hi) (rec_c c)
      | Cwhile a c1 e ii c2 =>
          Cwhile a (rec_c c1) (toec_cast_te abool e) ii (rec_c c2)
      end
    ).

Definition toec_cast_fun {eft} (f : _fundef eft) : _fundef eft :=
  with_body f (toec_cast_c toec_cast_i (f_body f)).

End FUNSIG.

Section PROGT.
Context {pT : progT}.

Definition fun_tyin_of (p : prog) (fn : funname) : seq atype :=
  if get_fundef (p_funcs p) fn is Some fd then f_tyin fd else [::].

Definition toec_cast_prog (p : prog) : prog :=
  map_prog (toec_cast_fun (fun_tyin_of p)) p.

End PROGT.
End TOEC_CAST.

