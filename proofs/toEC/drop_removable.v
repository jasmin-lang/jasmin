From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
Require Import expr compiler_util dead_code.

Local Open Scope seq_scope.

(* ** The removable variables removed

   The passes of the extraction for safety introduce variables of their own:
   the masks of [explicit_init], the copies of the arguments of the calls,
   the destinations of the results and the variables of the contracts of
   [contracts_to_asserts]. The caller makes [removable] hold for these
   variables, and only for them. Once the assertions are removed
   ([drop_asserts]), nothing but the code that computes them reads them; the
   pass removes them, and with them every trace of these passes, and nothing
   else:
   - the parameters and the results of the functions that are removable
     variables, with the corresponding arguments and destinations at the call
     sites;
   - the assignments and the operators all whose destinations write a
     removable variable;
   - a destination [x], removable, of an operator, a system call or a call
     that is kept becomes [_], of the type of [x];
   - an argument [x] of a call, removable, that an instruction removed since
     the last instruction kept assigns [x := e], at the type of the
     corresponding parameter, becomes [e]. This undoes the copies of the
     arguments of [contracts_to_asserts].

   The pass checks that no removable variable remains in the result, and that
   the destination of a result removed writes a removable variable or
   nothing. Whatever [removable] tells, the values that the removed
   instructions compute are then read by none of the instructions kept, nor
   are those of the results removed; and an argument [e] that replaces [x]
   reads no removable variable, so that it has at the call the value that
   [x] has in the source: the instructions removed in between write only
   removable variables. *)

Module Import E.

  Definition pass : string := "removable variables".

  Definition removable_error :=
    pp_internal_error_s pass "a removable variable is used".

  Definition removable_error_at (ii : instr_info) :=
    pp_internal_error_s_at pass ii
      "the destination of a removable result is not removable".

End E.

Section ASM_OP.

Context `{asmop : asmOp}.

Context (removable : var -> bool).

(* An l-value that writes a removable variable. *)
Definition removable_lv (x : lval) : bool :=
  match x with
  | Lvar x | Laset _ _ _ x _ | Lasub _ _ _ x _ => removable x
  | Lnone _ _ | Lmem _ _ _ _ => false
  end.

(* A destination of an instruction that is kept: a removable variable becomes
   [_]. *)
Definition rm_lv (x : lval) : lval :=
  if x is Lvar y then if removable y then Lnone (v_info y) (vtype y) else x else x.

Context (p : _uprog).

(* The parameters (resp. the results) of [fn] that are kept: those that are
   not removable variables. *)
Definition rmv_params_keep (fn : funname) : option (seq bool) :=
  if get_fundef (p_funcs p) fn is Some fd then
    Some [seq ~~ removable (v_var x) | x <- fd.(f_params)]
  else None.

Definition rmv_res_keep (fn : funname) : option (seq bool) :=
  if get_fundef (p_funcs p) fn is Some fd then
    Some [seq ~~ removable (v_var x) | x <- fd.(f_res)]
  else None.

(* The assignments [x := e] to removable variables removed since the last
   instruction kept: [x] is bound to the type of the assignment and to [e]. *)
Notation copies := (Mvar.t (atype * pexpr)).

(* The copies once [xs] are written: those of the variables written are
   forgotten. *)
Definition forget_lvs (m : copies) (xs : lvals) : copies :=
  foldl (fun m x => Sv.fold (fun y m => Mvar.remove m y) (vrv x) m) m xs.

(* An argument of a call, at the type [ty] of the parameter. *)
Definition subst_arg (m : copies) (ty : atype) (e : pexpr) : pexpr :=
  if e is Pvar x then
    if is_lvar x then
      if Mvar.get m (gv x) is Some (ty', e') then
        if ty == ty' then e' else e
      else e
    else e
  else e.

Definition subst_args (m : copies) (fn : funname) (es : pexprs) : pexprs :=
  if get_fundef (p_funcs p) fn is Some fd then
    if size fd.(f_tyin) == size es then map2 (subst_arg m) fd.(f_tyin) es else es
  else es.

(* The destinations of the results removed write a removable variable, or
   nothing: no value they receive remains in the result. *)
Definition removed_dests (fn : funname) (xs : lvals) : bool :=
  if rmv_res_keep fn is Some k then
    all2 (fun b x => [|| b, removable_lv x | if x is Lnone _ _ then true else false]) k xs
  else true.

Section CMD.

Context (drop_removable_i : copies -> instr -> cexec (copies * cmd)).

Fixpoint drop_removable_c (m : copies) (c : cmd) : cexec (copies * cmd) :=
  match c with
  | [::] => ok (m, [::])
  | i :: c =>
    Let r := drop_removable_i m i in
    Let rc := drop_removable_c r.1 c in
    ok (rc.1, r.2 ++ rc.2)
  end.

End CMD.

Fixpoint drop_removable_i (m : copies) (i : instr) : cexec (copies * cmd) :=
  let 'MkI ii ir := i in
  let kept ir := ok (Mvar.empty _, [:: MkI ii ir]) in
  let body c := Let r := drop_removable_c drop_removable_i (Mvar.empty _) c in ok r.2 in
  match ir with
  | Cassgn x _ ty e =>
    if removable_lv x then
      ok (if x is Lvar y then Mvar.set m y (ty, e) else forget_lvs m [:: x], [::])
    else kept ir
  | Copn xs tg o es =>
    if ~~ nilp xs && all removable_lv xs then ok (forget_lvs m xs, [::])
    else kept (Copn (map rm_lv xs) tg o es)
  | Csyscall xs o es => kept (Csyscall (map rm_lv xs) o es)
  | Cassert _ => kept ir
  | Ccall xs fn es =>
    Let _ := assert (removed_dests fn xs) (removable_error_at ii) in
    let xs := map rm_lv (fn_keep_only rmv_res_keep fn xs) in
    let es := fn_keep_only rmv_params_keep fn (subst_args m fn es) in
    kept (Ccall xs fn es)
  | Cif e c1 c2 =>
    Let c1 := body c1 in
    Let c2 := body c2 in
    kept (Cif e c1 c2)
  | Cfor x r c =>
    Let c := body c in
    kept (Cfor x r c)
  | Cwhile a c1 e ii_w c2 =>
    Let c1 := body c1 in
    Let c2 := body c2 in
    kept (Cwhile a c1 e ii_w c2)
  end.

Definition drop_removable_fd (fn : funname) (fd : ufundef) : cexec ufundef :=
  Let body := drop_removable_c drop_removable_i (Mvar.empty _) fd.(f_body) in
  let fd' :=
    {| f_info := fd.(f_info);
       f_contract := fd.(f_contract);
       f_tyin := fn_keep_only rmv_params_keep fn fd.(f_tyin);
       f_params := fn_keep_only rmv_params_keep fn fd.(f_params);
       f_body := body.2;
       f_tyout := fn_keep_only rmv_res_keep fn fd.(f_tyout);
       f_res := fn_keep_only rmv_res_keep fn fd.(f_res);
       f_extra := fd.(f_extra);
    |} in
  Let _ := assert (~~ Sv.exists_ removable (vars_fd fd')) removable_error in
  ok fd'.

Definition drop_removable_prog : cexec _uprog :=
  Let funcs := map_cfprog_name drop_removable_fd (p_funcs p) in
  ok {| p_funcs := funcs; p_globs := p_globs p; p_extra := p_extra p |}.

End ASM_OP.
