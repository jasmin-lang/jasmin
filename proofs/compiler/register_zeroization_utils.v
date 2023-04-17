From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  linear
  one_varmap
  utils
  var.
Require Import
  compiler_util
  register_zeroization.
Require Import
  arch_decl
  arch_extra.

Section RZ_UTILS.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asme : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {ovmi : one_varmap_info}
  (zeroize_var : (var -> pp_error_loc) -> var -> cexec lopn_args)
  (zeroize_flags : pp_error_loc -> option var -> cexec (seq lopn_args)).

Definition naive_rz_cmd_args
  (rzm : rzmode)
  (xs : seq var)
  (err_flags : pp_error_loc)
  (err_register : var -> pp_error_loc) :
  cexec (seq lopn_args) :=
  let ignore := Sv.union one_varmap.callee_saved (sv_of_list id xs) in
  let f s := filter (fun x => ~~ Sv.mem x ignore) s in
  let regs := if rzm_registers rzm then f (map to_var registers) else [::] in
  let xregs := if rzm_xregisters rzm then f (map to_var xregisters) else [::] in
  Let rzvars := mapM (zeroize_var err_register) (regs ++ xregs) in
  Let rzflags :=
    if rzm_flags rzm then (zeroize_flags err_flags) (ohead regs) else ok [::]
  in
  ok (rzvars ++ rzflags).

End RZ_UTILS.
