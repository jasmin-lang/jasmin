From mathcomp Require Import ssreflect ssrfun ssrbool eqtype. 
From mathcomp Require Import word_ssrZ.
Require Import ZArith.

Require Import expr sem_op_typed compiler_util lea.

Import Utf8.
Import oseq.

Require Import arch_decl arch_extra riscv riscv_instr_decl riscv_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
Local Open Scope Z_scope.

Section Section.
Context {atoI: arch_toIdent} {pT: progT}.

Section tmp.
Context (tmp: var_i).

Fixpoint lower_addressing_i (i: instr) :=
  let (ii,ir) := i in
  match ir with
  | Copn xs t o [:: Pload al ws x e] => 
    match mk_lea ws e with
    | Some lea =>
      match lea.(lea_base), lea.(lea_offset) with
      | None, Some(off) => 
        if lea.(lea_disp) != 0%Z then [:: i]
        else map (MkI ii) [:: Copn [:: Lvar tmp] AT_none (Oriscv SLLI) [:: Pvar (mk_lvar off); Pconst lea.(lea_scale)]; 
                              Copn [:: Lvar tmp] AT_none (Oriscv ADD) [:: Pvar (mk_lvar x); Pvar (mk_lvar tmp)];
                              Copn xs t o [:: Pload al ws tmp (Pconst 0)]]
      | _, _ =>  [:: i]
      end
    | None => [:: i]
    end
  | Copn xs t o _ => [:: i ]
  | Cassgn _ _ _ _ 
  | Csyscall _ _ _
  | Ccall _ _ _ => [:: i]      
  | Cif b c1 c2 =>
    let c1 := conc_map lower_addressing_i c1 in
    let c2 := conc_map lower_addressing_i c2 in
    [:: MkI ii (Cif b c1 c2)]
  | Cfor x (dir, e1, e2) c =>
    let c := conc_map lower_addressing_i c in
    [:: MkI ii (Cfor x (dir, e1, e2) c) ]
  | Cwhile a c e c' =>
    let c := conc_map lower_addressing_i c in
    let c' := conc_map lower_addressing_i c' in
    [:: MkI ii (Cwhile a c e c')]
  end.

Definition lower_addressing_fun (f: fundef) :=
  let 'MkFun ii si p c so r ev := f in
  let c := conc_map lower_addressing_i c in
  MkFun ii si p c so r ev.

End tmp.

Definition lower_addressing_prog (fresh_reg: string -> stype -> Ident.ident) (p:prog) : prog := 
let tmp := VarI {| vtype := sword Uptr; vname := fresh_reg "__tmp__"%string (sword Uptr) |} dummy_var_info in
map_prog (lower_addressing_fun tmp) p.

End Section.
