From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.

Require Import expr compiler_util lea.

Import Utf8.

Local Open Scope seq_scope.

Definition lower_glob_load_error msg := {|
    pel_msg := pp_s msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := None;
    pel_pass := Some "lower_glob_load"%string;
    pel_internal := true
  |}.

(* A load from a global, [x = [rip + n]], is split into the computation of
   the address, [x = rip + n] (the instruction [glob_addr_op]), and the load
   [x = [x]]. When [x] is not a pointer-sized variable, or when the load has
   other arguments (a conditional load, [x = c ? [rip + n] : y]), the address
   is computed into [tmp]: the load is evaluated whatever [c] is. *)

Section Section.
Context {pd : PointerData} {asm_op : Type} {asmop : asmOp asm_op}.
Context (is_load : asm_op -> bool) (glob_addr_op : asm_op).

Section RIP_TMP.

Context (rip : var) (tmp : var_i).

Definition is_glob_addr (e : pexpr) : bool :=
  if mk_lea Uptr e is Some lea then
    if lea.(lea_base) is Some b then (v_var b == rip) && ~~ isSome lea.(lea_offset)
    else false
  else false.

Definition glob_addr (x : var_i) (e : pexpr) : instr_r :=
  Copn [:: Lvar x ] AT_none (Oasm glob_addr_op) [:: e ].

(* The variable that receives the address. *)
Definition glob_load_dst (xs : lvals) (es' : pexprs) : var_i :=
  if (xs, es') is ([:: Lvar x ], [::]) then
    if vtype x == aword Uptr then x else tmp
  else tmp.

Definition lower_glob_load xs t o es : option (seq instr_r) :=
  if o is Oasm op then
    if is_load op then
      if es is Pload al ws e :: es' then
        if is_glob_addr e then
          let x := glob_load_dst xs es' in
          Some [:: glob_addr x e; Copn xs t o (Pload al ws (Plvar x) :: es') ]
        else None
      else None
    else None
  else None.

Fixpoint lower_glob_load_i (i: instr) :=
  let (ii,ir) := i in
  match ir with
  | Copn xs t o es =>
    if lower_glob_load xs t o es is Some c then map (MkI ii) c else [:: i ]
  | Cassgn _ _ _ _
  | Csyscall _ _ _
  | Cassert _
  | Ccall _ _ _ => [:: i]
  | Cif b c1 c2 =>
    let c1 := List.flat_map lower_glob_load_i c1 in
    let c2 := List.flat_map lower_glob_load_i c2 in
    [:: MkI ii (Cif b c1 c2)]
  | Cfor x (dir, e1, e2) c =>
    let c := List.flat_map lower_glob_load_i c in
    [:: MkI ii (Cfor x (dir, e1, e2) c) ]
  | Cwhile a c e info c' =>
    let c := List.flat_map lower_glob_load_i c in
    let c' := List.flat_map lower_glob_load_i c' in
    [:: MkI ii (Cwhile a c e info c')]
  end.

Definition lower_glob_load_c := List.flat_map lower_glob_load_i.

Definition lower_glob_load_fd (f: sfundef) :=
  let body := f.(f_body) in
  Let _ := assert (~~ Sv.mem tmp (read_c body))
                  (lower_glob_load_error "fresh variable not fresh (body)")
  in
  Let _ := assert (~~ Sv.mem tmp (vars_l f.(f_res)))
                  (lower_glob_load_error "fresh variable not fresh (res)")
  in
  ok (with_body f (lower_glob_load_c body)).

End RIP_TMP.

Definition lower_glob_load_prog
    (fresh_reg: string -> atype -> Ident.ident) (p: sprog) : cexec sprog :=
  let rip := {| vtype := aword Uptr; vname := p.(p_extra).(sp_rip) |} in
  let tmp :=
    VarI
      {| vtype := aword Uptr; vname := fresh_reg "__tmp__"%string (aword Uptr) |}
      dummy_var_info
  in
  Let funcs := map_cfprog (lower_glob_load_fd rip tmp) p.(p_funcs) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End Section.
