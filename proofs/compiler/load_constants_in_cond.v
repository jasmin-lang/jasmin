(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
From Coq Require Import Uint63.
Require Import expr compiler_util.

Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "load constants in conditions".

  Definition load_constants_ref_error := pp_internal_error_s_at pass.

End E.

Section ASM_OP.

Context
  {asm_op : Type}
  {asmop:asmOp asm_op}
  {pT : progT}.

Context (fresh_reg: instr_info -> int -> string -> stype -> Ident.ident).

Definition fresh_word ii n ws :=
  {| v_var :=
      {| vtype := sword ws;
         vname := fresh_reg ii n "__tmp__"%string (sword ws) |};
     v_info := dummy_var_info |}.

Definition process_constant ii n (ws:wsize) e : seq instr_r * pexpr * Sv.t :=
  if is_wconst_of_size ws e is Some z then
    if ~~ (z =? 0)%Z then
      let x := fresh_word ii n ws in
      (* We use AT_rename to have a warning at compile time:
         warning: extra assignment introduced *)
      ([:: Cassgn x AT_rename (sword ws) e], Pvar (mk_lvar x), Sv.singleton x)
    else
      (* On RISC-V, we can replace constant 0 with register x0, so we do not
         need an auxiliary register. *)
      ([::], e, Sv.empty)
  else
    ([::], e, Sv.empty).

Section BODY.

Context (X : Sv.t).

(* Not sure cf_of_condition was written for that, but it is convenient. *)
Definition process_condition ii e : cexec (seq instr_r * pexpr) :=
  if is_Papp2 e is Some (op, e1, e2) then
    match cf_of_condition op with
    | Some (_, ws) =>
      let: (c1, e1, s1) := process_constant ii 0 ws e1 in
      let: (c2, e2, s2) := process_constant ii 1 ws e2 in
      Let _ :=
        assert (disjoint s1 X)
               (load_constants_ref_error ii "bad fresh id (1)")
      in
      Let _ :=
        assert (disjoint s2 X)
               (load_constants_ref_error ii "bad fresh id (2)")
      in
      Let _ :=
        assert (disjoint s1 s2)
               (load_constants_ref_error ii "bad fresh id (disjoint)")
      in
      ok (c1++c2, Papp2 op e1 e2)
    | _ => ok ([::], e)
    end
  else
    ok ([::], e).

Definition load_constants_c (load_constants_i : instr -> cexec cmd) c :=
  Let c := mapM load_constants_i c in
  ok (flatten c).

Fixpoint load_constants_i (i : instr) :=
  let '(MkI ii ir) := i in
  match ir with
  | Cassgn _ _ _ _
  | Copn _ _ _ _
  | Csyscall _ _ _
  | Cassert _ _ _
  | Ccall _ _ _
    => ok [::i]
  | Cif e c1 c2  =>
    Let: (c, e) := process_condition ii e in
    Let c1 := load_constants_c load_constants_i c1 in
    Let c2 := load_constants_c load_constants_i c2 in
    ok (map (MkI ii) (c ++ [:: Cif e c1 c2]))
  | Cfor x (d,lo,hi) c =>
    Let c := load_constants_c load_constants_i c in
    ok [:: MkI ii (Cfor x (d, lo, hi) c)]
  | Cwhile a c1 e info c2 =>
    Let: (c, e) := process_condition info e in
    Let c1 := load_constants_c load_constants_i c1 in
    Let c2 := load_constants_c load_constants_i c2 in
    ok [:: MkI ii (Cwhile a (c1 ++ map (MkI info) c) e info c2)]
  end.

End BODY.

Definition load_constants_fd (fd: fundef) :=
  let body    := fd.(f_body) in
  let write   := write_c body in
  let read    := read_c  body in
  let returns := read_es (map Plvar fd.(f_res)) in
  let X := Sv.union returns (Sv.union write read) in
  Let body := load_constants_c (load_constants_i X) body in
  ok (with_body fd body).

Definition load_constants_prog (doit: bool) p : cexec prog :=
  if doit then
    Let funcs := map_cfprog load_constants_fd p.(p_funcs) in
    ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}
  else ok p.

End ASM_OP.
