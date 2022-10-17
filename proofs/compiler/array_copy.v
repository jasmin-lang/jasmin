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

  Definition error := pp_internal_error_s pass "fresh variables are not fresh ...". 

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

Definition array_copy ii (x: var_i) (ws: wsize) (n: positive) (y: gvar) :=
  let i_name := fresh_counter in
  let i := {| v_var := {| vtype := concrete (sint) ; vname := i_name |}; v_info := v_info x |} in
  let ei := Pvar (mk_lvar i) in
  let sz := Z.to_pos (wsize_size ws * n) in
  let pre := 
    if eq_gvar (mk_lvar x) y then Copn [::] AT_none Onop [::]
    else Cassgn (Lvar x) AT_none (concrete (sarr sz)) (Parr_init (const_length sz)) in
  [:: MkI ii pre;
      MkI ii 
        (Cfor i (UpTo, Pconst 0, Pconst n) 
           [:: MkI ii (Cassgn (Laset AAscale ws x ei) AT_none (concrete (sword ws)) (Pget AAscale ws y ei))])
    ].

Definition array_copy_c (array_copy_i : instr -> cexec cmd) (c:cmd) : cexec cmd := 
  Let cs := mapM array_copy_i c in 
  ok (flatten cs).

Definition is_copy o := 
  match o with 
  | Ocopy ws p => Some (ws, p) 
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
          Let _ := assert (vtype x == concrete (sarr (Z.to_pos (arr_size ws n))))
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
  | Ccall _ _ _ _ => ok [:: i]
  end.

Context {T} {pT:progT T}.

Definition array_copy_fd (f:fundef) :=
  let 'MkFun fi tyin params c tyout res ev := f in
  Let c := array_copy_c array_copy_i c in
  ok (MkFun fi tyin params c tyout res ev).

Definition array_copy_prog (p:prog) := 
  let V := vars_p (p_funcs p) in 
  Let _ := 
    assert (~~ Sv.mem {| vtype := concrete sint ; vname := fresh_counter |} V) E.error 
  in
  Let fds := map_cfprog array_copy_fd (p_funcs p) in
  ok {| p_funcs := fds;
        p_globs := p_globs p;
        p_extra := p_extra p|}.

End Section.



