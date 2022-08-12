From mathcomp Require Import all_ssreflect.
Require Import expr compiler_util.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
semantics: Ccopy x ws n y

x & y have type array(ws * n)
all y[i] is init (ok u)

*)

Module Import E.
  Definition pass : string := "array copy".

  Definition error := pp_internal_error_s pass.
  Definition error_at := pp_internal_error_s_at pass.

End E.

Section Section.

Context `{asmop:asmOp}.
Context (fresh_counter: Ident.ident).

(*
  x = ArrayInit();
  for i = 0 to n {
    x[i] = y[i];
  }
*)

Definition array_copy ii (x: var_i) xoff xsub (ws: wsize) (n: positive) (y: gvar) yoff :=
  let i_name := fresh_counter in
  let i := {| v_var := {| vtype := sint ; vname := i_name |}; v_info := v_info x |} in
  let ei := Pvar (mk_lvar i) in
  let sz := Z.to_pos (wsize_size ws * n) in
  let instr := [:: MkI ii (Cfor i (UpTo, Pconst 0, Pconst n)
      [:: MkI ii (Cassgn (Laset AAscale ws x (Papp2 (Oadd Op_int) xoff ei))
        AT_none (sword ws) (Pget AAscale ws y (Papp2 (Oadd Op_int) yoff ei)))])
  ] in
  if xsub || eq_gvar (mk_lvar x) y then instr
  else MkI ii (Cassgn (Lvar x) AT_none (sarr sz) (Parr_init sz))::instr.

Definition array_copy_c (array_copy_i : instr -> cexec cmd) (c:cmd) : cexec cmd := 
  Let cs := mapM array_copy_i c in
  ok (flatten cs).

Fixpoint array_copy_i (i:instr) : cexec cmd := 
  let:(MkI ii id) := i in
  match id with
  | Copn xs _ (Ocopy ws n) es =>
    Let xp := if xs is [:: x] then match x with
      | Lvar x =>
        Let _ := assert (vtype x == sarr (Z.to_pos (arr_size ws n)))
          (E.error_at ii "source variable type is incorrect") in
        ok (x, Pconst 0, false)
      | Lasub aa ws' n' x e =>
        Let _ := assert [&& aa == AAscale, ws' == ws & n' == n]
          (E.error_at ii "source subarray parameters are incorrect") in
        ok (x, e, true)
      | _ => Error (E.error_at ii "copy source should be a variable or a subarray")
      end else Error (E.error "assertion failed")
    in
    Let ep := if es is [:: e] then match e with
      | Pvar x =>
        Let _ := assert (vtype (gv x) == sarr (Z.to_pos (arr_size ws n)))
          (E.error_at ii "destination variable type is incorrect") in
        ok (x, Pconst 0)
      | Psub aa ws' n' x e =>
        Let _ := assert [&& aa == AAscale, ws' == ws & n' == n]
          (E.error_at ii "destination subarray parameters are incorrect") in
        ok (x, e)
      | _ => Error (E.error_at ii "copy destination should be a variable or a subarray")
      end else Error (E.error "assertion failed")
    in
    let '(x, xoff, xsub) := xp in
    let '(y, yoff) := ep in
    ok (array_copy ii x xoff xsub ws n y yoff)
  | Cif e c1 c2 =>
    Let c1 := array_copy_c array_copy_i c1 in
    Let c2 := array_copy_c array_copy_i c2 in
    ok [:: MkI ii (Cif e c1 c2)]
  | Cfor i r c =>
    Let c := array_copy_c array_copy_i c in
    ok [:: MkI ii (Cfor i r c)]
  | Cwhile a c1 e c2 =>
    Let c1 := array_copy_c array_copy_i c1 in
    Let c2 := array_copy_c array_copy_i c2 in
    ok [:: MkI ii (Cwhile a c1 e c2)]
  | _ => ok [:: i]
  end.

Context {T} {pT:progT T}.

Definition array_copy_fd (f:fundef) :=
  let 'MkFun fi tyin params c tyout res ev := f in
  Let c := array_copy_c array_copy_i c in
  ok (MkFun fi tyin params c tyout res ev).

Definition array_copy_prog (p:prog) := 
  let V := vars_p (p_funcs p) in 
  Let _ := 
    assert (~~ Sv.mem {| vtype := sint ; vname := fresh_counter |} V)
      (E.error "fresh variables are not fresh ...")
  in
  Let fds := map_cfprog array_copy_fd (p_funcs p) in
  ok {| p_funcs := fds;
        p_globs := p_globs p;
        p_extra := p_extra p|}.

End Section.
