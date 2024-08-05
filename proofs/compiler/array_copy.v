From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Require Import
  compiler_util
  expr
  pseudo_operator.
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

  Definition error := pp_internal_error_s pass "fresh variables are not fresh ...".

End E.

Section Section.

Context `{asmop:asmOp}.
Context
  (fresh_counter: Ident.ident)
  (fresh_temporary: wsize → Ident.ident)
.

(** Replaces each x = #copy(y) with the following:

  x = ArrayInit();
  for i = 0 to n {
    x[i] = y[i];
  }

  The “x = ArrayInit()” part is neither introduced when x and y are the same local variable nor when x is a ptr.

  Each copied value goes through a temporary variable when both x and y are in memory (stack or global).
*)

Definition direct_copy ws x y i :=
  [:: Cassgn (Laset Aligned AAscale ws x i) AT_none (sword ws) (Pget Aligned AAscale ws y i) ].

Definition tmp_var ws :=
  {| vtype := sword ws; vname := fresh_temporary ws |}.

Definition indirect_copy ws x y i :=
  let tmp := {| v_var := tmp_var ws ; v_info := v_info x |} in
  [:: Cassgn (Lvar tmp) AT_none (sword ws) (Pget Aligned AAscale ws y i);
   Cassgn (Laset Aligned AAscale ws x i) AT_none (sword ws) (Pvar (mk_lvar tmp)) ].

Definition needs_temporary x y : bool :=
  is_var_in_memory x && is_var_in_memory y.

Definition array_copy ii (x: var_i) (ws: wsize) (n: positive) (y: gvar) :=
  let i_name := fresh_counter in
  let i := {| v_var := {| vtype := sint ; vname := i_name |}; v_info := v_info x |} in
  let ei := Pvar (mk_lvar i) in
  let sz := Z.to_pos (wsize_size ws * n) in
  let pre :=
    if eq_gvar (mk_lvar x) y
    || is_ptr x
    then Copn [::] AT_none sopn_nop [::]
    else Cassgn (Lvar x) AT_none (sarr sz) (Parr_init sz) in
  [:: MkI ii pre;
      MkI ii
        (Cfor i (UpTo, Pconst 0, Pconst n)
           [seq MkI ii i | i <- (if needs_temporary x y.(gv) then indirect_copy else direct_copy) ws x y ei ])
    ].

Definition array_copy_c (array_copy_i : instr -> cexec cmd) (c:cmd) : cexec cmd :=
  Let cs := mapM array_copy_i c in
  ok (flatten cs).

Definition is_copy o :=
  match o with
  | Opseudo_op (Ocopy ws p) => Some (ws, p)
  | _ => None
  end.

Definition is_Pvar es :=
  match es with
  | [:: Pvar x] => Some x
  | _ => None
  end.

Definition is_Lvar xs :=
  match xs with
  | [:: Lvar x] => Some x
  | _ => None
  end.

Fixpoint array_copy_i (i:instr) : cexec cmd :=
  let:(MkI ii id) := i in
  match id with
  | Cassgn _ _ _ _ => ok [:: i]
  | Copn xs _ o es =>
    match is_copy o with
    | Some (ws, n) =>
      match is_Pvar es with
      | Some y =>
        match is_Lvar xs with
        | Some x =>
          (* FIXME error msg *)
          Let _ := assert (vtype x == sarr (Z.to_pos (arr_size ws n)))
                          (pp_internal_error_s_at E.pass ii "bad type for copy") in
          ok (array_copy ii x ws n y)
        | None =>
          (* FIXME error msg *)
          Error (pp_internal_error_s_at E.pass ii "copy destination is not a var")
        end
      | None =>
        (* FIXME error msg *)
        Error (pp_internal_error_s_at E.pass ii "copy source is not a var")
      end

    | _ => ok [:: i]
    end
  | Csyscall _ _ _ => ok [:: i]
  | Cif e c1 c2    =>
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
  | Ccall _ _ _ => ok [:: i]
  end.

Context {pT: progT}.

Definition array_copy_fd (f:fundef) :=
  let 'MkFun fi tyin params c tyout res ev := f in
  Let c := array_copy_c array_copy_i c in
  ok (MkFun fi tyin params c tyout res ev).

Definition array_copy_prog (p:prog) :=
  let V := vars_p (p_funcs p) in
  let fresh := Sv.add {| vtype := sint ; vname := fresh_counter |} (sv_of_list tmp_var wsizes) in
  Let _ := assert (disjoint fresh V) E.error in
  Let fds := map_cfprog array_copy_fd (p_funcs p) in
  ok {| p_funcs := fds;
        p_globs := p_globs p;
        p_extra := p_extra p|}.

End Section.
