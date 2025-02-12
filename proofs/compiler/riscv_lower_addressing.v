From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.

Require Import expr sem_op_typed compiler_util lea.

Import Utf8.
Import oseq.

Require Import
  arch_decl
  arch_extra
  riscv_instr_decl
  riscv_decl
  riscv
  riscv_extra.

Local Open Scope seq_scope.
Local Open Scope Z_scope.

Module E.

Definition pass_name := "lower_addressing"%string.

Definition error msg := {|
    pel_msg := pp_s msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := None;
    pel_pass := Some pass_name;
    pel_internal := true
  |}.

End E.

Section Section.
Context {atoI: arch_toIdent} {pT: progT}.

Section tmp.

Context (tmp: var_i).

(* inspired from scale_of_z in asm_gen *)
Definition shift_of_scale (z: Z) : option Z :=
  match z with
  | 1%Z => Some 0
  | 2%Z => Some 1
  | 4%Z => Some 2
  | _ => None
  end.

(* We introduce these helper functions, else the number of cases in the pattern-
   matching explodes, due to the way Coq handles pattern-matchings. *)
Definition is_one_Lmem xs :=
  if xs is [:: Lmem al ws x e] then Some (al, ws, x, e) else None.

Definition is_one_Pload es :=
  if es is [:: Pload al ws x e] then Some (al, ws, x, e) else None.

(* Lmem and Pload cases are almost identical, so we factorize both cases. *)
Definition compute_addr x e :=
  let%opt lea := mk_lea Uptr (Papp2 (Oadd (Op_w Uptr)) (Pvar (mk_lvar x)) e) in
  let%opt base := lea.(lea_base) in
  let%opt off := lea.(lea_offset) in
  if tmp == base :> var then None
  else
    let%opt shift := shift_of_scale lea.(lea_scale) in
    Some ([::
      Copn [:: Lvar tmp] AT_none (Oriscv SLLI) [:: Pvar (mk_lvar off); wconst (wrepr Uptr shift)];
      Copn [:: Lvar tmp] AT_none (Oriscv ADD) [:: Pvar (mk_lvar base); Pvar (mk_lvar tmp)]],
      wconst (wrepr Uptr lea.(lea_disp))).

Fixpoint lower_addressing_i (i: instr) :=
  let (ii,ir) := i in
  match ir with
  | Copn xs t o es =>
    if is_one_Lmem xs is Some (al, ws, x, e) then
      if compute_addr x e is Some (prelude, disp) then
        map (MkI ii) (prelude ++ [:: Copn [:: Lmem al ws tmp disp] t o es])
      else [:: i]
    else if is_one_Pload es is Some (al, ws, x, e) then
      if compute_addr x e is Some (prelude, disp) then
        map (MkI ii) (prelude ++ [:: Copn xs t o [:: Pload al ws tmp disp]])
      else [:: i]
    else [:: i]
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
  | Cwhile a c e info c' =>
    let c := conc_map lower_addressing_i c in
    let c' := conc_map lower_addressing_i c' in
    [:: MkI ii (Cwhile a c e info c')]
  end.

Definition lower_addressing_c := conc_map lower_addressing_i.

Definition lower_addressing_fd (f: fundef) :=
  let body := f.(f_body) in
  Let _ := assert (~~ Sv.mem tmp (read_c body))
                  (E.error "fresh variable not fresh (body)")
  in
  Let _ := assert (~~ Sv.mem tmp (vars_l f.(f_res)))
                  (E.error "fresh variable not fresh (res)")
  in
  ok (with_body f (lower_addressing_c body)).

End tmp.

Definition lower_addressing_prog
    (fresh_reg: string -> stype -> Ident.ident) (p:prog) : cexec prog :=
  let tmp :=
    VarI
      {| vtype := sword Uptr; vname := fresh_reg "__tmp__"%string (sword Uptr) |}
      dummy_var_info
  in
  Let funcs := map_cfprog (lower_addressing_fd tmp) p.(p_funcs) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End Section.
