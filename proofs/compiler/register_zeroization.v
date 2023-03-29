(* Register zeroization.

  This pass zeroizes all registers (normal, extra registers, and flags).
  The code to do this is architecture specific, as well as the zeroization
  notion.
*)

From mathcomp Require Import
  all_ssreflect
  all_algebra.
Require Import ZArith.

Require Import
  expr
  linear
  linear_util
  one_varmap
  sopn
  utils.
Require Import
  compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module E.

  Definition pass : string := "register zeroization".

  Definition base_error msg :=
    {|
      pel_msg := msg;
      pel_fn := None;
      pel_fi := None;
      pel_ii := None;
      pel_vi := None;
      pel_pass := Some pass;
      pel_internal := true;
    |}.

  Definition cant_zeroize_flags : pp_error_loc :=
    base_error (pp_s "can't zeoize flags").

  Definition cant_zeroize_register (x : var) : pp_error_loc :=
    let: msg := "can't zeroize register"%string in
    base_error (pp_box [:: pp_s msg; pp_s (vname x) ]).

  Definition res_has_bool : pp_error_loc :=
    base_error (pp_s "there's a boolean return variable").

End E.

Record rzmode :=
  {
    rzm_flags : bool;
    rzm_registers : bool;
    rzm_xregisters : bool;
  }.


Section REGISTER_ZEROIZATION_PARAMS.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}.

Record register_zeroization_params :=
  {
    (* The command derived from
         [rz_cmd_args rzm xs err_flags err_register]
       zeroizes registers according to [zrm] except those in [xs], and
       return [err_flags] or [err_register r] if there was an error zeroizing
       flags or a register [r], respectively. *)
    rz_cmd_args :
      rzmode
      -> seq var
      -> pp_error_loc
      -> (var -> pp_error_loc)
      -> cexec (seq lopn_args);
  }.

End REGISTER_ZEROIZATION_PARAMS.

Section WITH_PARAMS.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
  {ovmi : one_varmap_info}
  (rzm_of_fn : funname -> rzmode)
  (rzparams : register_zeroization_params).

Definition rz_cmd (rzm : rzmode) (lfd : lfundef) : cexec lcmd :=
  let vars := map v_var (lfd_res lfd) in
  Let: tt :=
    assert (all (fun x => ~~ is_sbool (vtype x)) vars) E.res_has_bool
  in
  Let args :=
    rz_cmd_args rzparams rzm vars E.cant_zeroize_flags E.cant_zeroize_register
  in
  ok (map (li_of_lopn_args dummy_instr_info) args).

Definition register_zeroization_lfd
  (fn : funname) (lfd : lfundef) : cexec lfundef :=
  if lfd_export lfd
  then
    Let c := rz_cmd (rzm_of_fn fn) lfd in
    ok (with_lfd_body lfd (lfd_body lfd ++ c))
  else
    ok lfd.

Definition register_zeroization_lprog (lp : lprog) : cexec lprog :=
  Let lp_funs := map_lprog_name register_zeroization_lfd (lp_funcs lp) in
  ok
    {|
      lp_rip := lp_rip lp;
      lp_rsp := lp_rsp lp;
      lp_globs := lp_globs lp;
      lp_funcs := lp_funs;
    |}.

End WITH_PARAMS.
