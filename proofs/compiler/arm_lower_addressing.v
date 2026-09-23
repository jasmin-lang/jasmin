From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.

Require Import expr compiler_util lea.

Import Utf8.

Require Import
  arch_decl
  arch_extra
  arm_decl
  arm_instr_decl
  arm_extra.

Local Open Scope seq_scope.

Definition lower_addressing_error msg := {|
    pel_msg := pp_s msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := None;
    pel_pass := Some "lower_addressing"%string;
    pel_internal := true
  |}.

(* A load from a global, [x = [rip + n]], is split into the computation of
   the address, [x = rip + n] (a [MOVW]/[MOVT] pair), and the load [x = [x]].
   A conditional load, [x = c ? [rip + n] : y], computes the address into
   [tmp]: the load is evaluated whatever [c] is. *)

Section Section.
Context {atoI : arch_toIdent}.

Section RIP_TMP.

Context (rip : var) (tmp : var_i).

Definition is_load_mn (mn : arm_mnemonic) : bool :=
  mn \in [:: LDR; LDRB; LDRH; LDRSB; LDRSH ].

Definition is_glob_addr (e : pexpr) : bool :=
  if mk_lea Uptr e is Some lea then
    if lea.(lea_base) is Some b then (v_var b == rip) && ~~ isSome lea.(lea_offset)
    else false
  else false.

Definition glob_addr (x : var_i) (e : pexpr) : instr_r :=
  Copn [:: Lvar x ] AT_none (Oasm (ExtOp Oarm_glob_addr)) [:: e ].

Definition lower_glob_load xs t o es : option (seq instr_r) :=
  if o is Oasm (BaseOp (None, ARM_op mn _)) then
    if is_load_mn mn then
      if es is Pload al ws e :: es' then
        if is_glob_addr e then
          if es' is [::] then
            if xs is [:: Lvar x ] then
              if vtype x == aword Uptr then
                Some [:: glob_addr x e; Copn xs t o [:: Pload al ws (Plvar x) ] ]
              else None
            else None
          else Some [:: glob_addr tmp e; Copn xs t o (Pload al ws (Plvar tmp) :: es') ]
        else None
      else None
    else None
  else None.

Fixpoint lower_addressing_i (i: instr) :=
  let (ii,ir) := i in
  match ir with
  | Copn xs t o es =>
    if lower_glob_load xs t o es is Some c then map (MkI ii) c else [:: i ]
  | Cassgn _ _ _ _
  | Csyscall _ _ _
  | Cassert _
  | Ccall _ _ _ => [:: i]
  | Cif b c1 c2 =>
    let c1 := List.flat_map lower_addressing_i c1 in
    let c2 := List.flat_map lower_addressing_i c2 in
    [:: MkI ii (Cif b c1 c2)]
  | Cfor x (dir, e1, e2) c =>
    let c := List.flat_map lower_addressing_i c in
    [:: MkI ii (Cfor x (dir, e1, e2) c) ]
  | Cwhile a c e info c' =>
    let c := List.flat_map lower_addressing_i c in
    let c' := List.flat_map lower_addressing_i c' in
    [:: MkI ii (Cwhile a c e info c')]
  end.

Definition lower_addressing_c := List.flat_map lower_addressing_i.

Definition lower_addressing_fd (f: sfundef) :=
  let body := f.(f_body) in
  Let _ := assert (~~ Sv.mem tmp (read_c body))
                  (lower_addressing_error "fresh variable not fresh (body)")
  in
  Let _ := assert (~~ Sv.mem tmp (vars_l f.(f_res)))
                  (lower_addressing_error "fresh variable not fresh (res)")
  in
  ok (with_body f (lower_addressing_c body)).

End RIP_TMP.

Definition arm_lower_addressing_prog
    (fresh_reg: string -> atype -> Ident.ident) (p: sprog) : cexec sprog :=
  let rip := {| vtype := aword Uptr; vname := p.(p_extra).(sp_rip) |} in
  let tmp :=
    VarI
      {| vtype := aword Uptr; vname := fresh_reg "__tmp__"%string (aword Uptr) |}
      dummy_var_info
  in
  Let funcs := map_cfprog (lower_addressing_fd rip tmp) p.(p_funcs) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End Section.
