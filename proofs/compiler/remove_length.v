(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrbool.
Require Import expr compiler_util.

Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "remove length arguments".

  Definition remove_length_error := pp_internal_error_s pass.

End E.

Section ASM_OP.

Context
  {pd : PointerData}
  {asm_op : Type}
  {asmop:asmOp asm_op}
  {pT : progT}.

Fixpoint no_var_e e :=
  match e with
  | Pconst _ | Pbool _ => true
  | Parr_init _ al => no_var_al al
  | Pvar x => no_var_ty x.(gv).(vtype)
  | Pget _ _ _ x e => no_var_ty x.(gv).(vtype) && no_var_e e
  | Psub _ _ al x e => [&& no_var_al al, no_var_ty x.(gv).(vtype) & no_var_e e]
  | Pload _ _ e => no_var_e e
  | Papp1 _ e => no_var_e e
  | Papp2 _ e1 e2 => no_var_e e1 && no_var_e e2
  | PappN _ es => all no_var_e es
  | Pif ty e1 e2 e3 => [&& no_var_ty ty, no_var_e e1, no_var_e e2 & no_var_e e3]
  end.
Definition no_var_es := all no_var_e.

Definition no_var_lval r :=
  match r with
  | Lnone _ ty => no_var_ty ty
  | Lvar x => no_var_ty x.(vtype)
  | Lmem _ _ _ e => no_var_e e
  | Laset _ _ _ x e => no_var_ty x.(vtype) && no_var_e e
  | Lasub _ _ al x e => [&& no_var_al al, no_var_ty x.(vtype) & no_var_e e]
  end.
Definition no_var_lvals := all no_var_lval.

Fixpoint no_var_i i :=
  let: (MkI ii ir) := i in
  match ir with
  | Cassgn r _ ty e => [&& no_var_lval r, no_var_ty ty & no_var_e e]
  | Copn rs _ _ als es => [&& no_var_lvals rs, all no_var_al als & no_var_es es]
  | Csyscall rs _ es => no_var_lvals rs && no_var_es es
  | Cassert _ => false (* no assert at this point *)
  | Cif b c1 c2 => [&& no_var_e b, all no_var_i c1 & all no_var_i c2]
  | Cfor x (_, lo, hi) c =>
    [&& no_var_ty x.(vtype), no_var_e lo, no_var_e hi & all no_var_i c]
      (* x is of type int per the semantics, so no_var_ty x.(vtype) probably unneeded *)
  | Cwhile _ c1 e _ c2 => [&& all no_var_i c1, no_var_e e & all no_var_i c2]
  | Ccall rs _ _als es => no_var_lvals rs (* && all no_var_al als *) && no_var_es es
  end.

Definition no_var_c := all no_var_i.

Definition no_var_fd (fd : fundef) :=
  [&& all no_var_ty fd.(f_tyin)
    , all (fun (x : var_i) => no_var_ty x.(vtype)) fd.(f_params)
    , all no_var_ty fd.(f_tyout)
    , all (fun (x : var_i) => no_var_ty x.(vtype)) fd.(f_res)
    & no_var_c fd.(f_body)].

Definition with_al eft (fd:_fundef eft) al := {|
  f_info     := fd.(f_info);
  f_contract := fd.(f_contract);
  f_al       := al;
  f_tyin     := fd.(f_tyin);
  f_params   := fd.(f_params);
  f_body     := fd.(f_body);
  f_tyout    := fd.(f_tyout);
  f_res      := fd.(f_res);
  f_extra    := fd.(f_extra);
|}.

Fixpoint remove_length_i (i : instr) :=
  let '(MkI ii ir) := i in
  match ir with
  | Cassgn _ _ _ _
  | Copn _ _ _ _ _
  | Csyscall _ _ _
  | Cassert _
    => i
  | Ccall rs fn als es => MkI ii (Ccall rs fn [::] es)
  | Cif e c1 c2  =>
    let c1 := map remove_length_i c1 in
    let c2 := map remove_length_i c2 in
    MkI ii (Cif e c1 c2)
  | Cfor x (d,lo,hi) c =>
    let c := map remove_length_i c in
    MkI ii (Cfor x (d, lo, hi) c)
  | Cwhile a c1 e info c2 =>
    let c1 := map remove_length_i c1 in
    let c2 := map remove_length_i c2 in
    MkI ii (Cwhile a c1 e info c2)
  end.

Definition remove_length_c := map remove_length_i.

Definition remove_length_fd (fd: fundef) :=
  Let _ := assert (no_var_fd fd) (remove_length_error "length variables remain") in
  let body := remove_length_c fd.(f_body) in
  ok (with_al (with_body fd body) [::]).

Definition remove_length_prog p : cexec prog :=
  Let funcs := map_cfprog remove_length_fd p.(p_funcs) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End ASM_OP.
