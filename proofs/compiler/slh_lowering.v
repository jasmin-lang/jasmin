(* Lowering of SLH operators.
   This pass transforms source-level SLH operators into architecture-specific
   ones.
   Each architecture provides the mapping
      [shp_lower : seq lval -> slh_op -> seq pexpr -> option copn_args]
   to be used.

   We use a "copy" of the same operators that is architecture-specific (e.g.
   in x86-64 [SLHinit] goes to [Ox86SLHinit], [SLHupdate] goes to
   [Ox86SLHupdate] and so on) but with different input/ouput types to correspond
   to their compilation (which is provided by [assemble_extra]) so that register
   allocation works properly.
   We don't lower to assembly instructions directly so as not to lose track of
   which instructions handle the MSF.
   Here we map [SLHprotect_ptr] to [SLHprotect_ptr_fail], and Stack Allocation
   will replace it with [shp_lower ... SLHprotect_ptr ...] when the pointer
   becomes a register. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import expr.
Require constant_prop flag_combination.
Require Import compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module E.

Definition pass : string := "speculative execution lowering".

Notation internal_error ii s :=
  (pp_internal_error_s_at pass ii s)
  (only parsing).

Definition pp_user_error ii vi (pp : pp_error) := {|
  pel_msg := pp_vbox [:: pp; pp_s "Did you run the speculative constant time checker first?"];
  pel_fn := None;
  pel_fi := None;
  pel_ii := ii;
  pel_vi := vi;
  pel_pass := Some pass;
  pel_internal := false
|}.

Definition cond_not_found (ii : instr_info) oe e : pp_error_loc :=
  let pp_oe :=
    match oe with
    | None => [:: pp_s "no condition are known"]
    | Some e => [:: pp_s "known expression"; pp_e e]
    end in
  pp_user_error (Some ii) None
     (pp_vbox
        [:: pp_hov ([:: pp_s "Not able to prove that"; pp_e e; pp_s "evaluate to true,"]);
            pp_hov pp_oe]).

Definition lvar_variable (ii: instr_info) : pp_error_loc :=
  pp_user_error (Some ii) None
     (pp_s "misspeculation flag should be stored into register").

Definition expr_variable (ii: instr_info) e : pp_error_loc :=
  pp_user_error (Some ii) None
     (pp_vbox [:: pp_s "only register allowed for misspeculation flag:";
                  pp_e e]).

Definition msf_not_found_r (x:var_i) (known : Sv.t) : pp_error_loc :=
   pp_user_error None (Some (v_info x))
     (pp_vbox [:: pp_box [:: pp_s "Variable"; pp_var x; pp_s "is not a misspeculation flag"];
                  pp_box [:: pp_s "Known are"; pp_Sv known]]).

Definition msf_not_found (ii : instr_info) (x:var_i) (known : Sv.t) : pp_error_loc :=
  pp_at_ii ii (msf_not_found_r x known).

Definition invalid_nb_args :=
  pp_internal_error_s pass "invalid number of arguments".

Definition invalid_nb_lvals :=
  pp_internal_error_s pass "invalid number of left values".

Definition cond_uses_mem (ii : instr_info) e : pp_error_loc :=
  pp_user_error (Some ii) None
    (pp_vbox [:: pp_s "Condition has a memory access:";
                 pp_e e]).

Definition lowering_failed (ii : instr_info) : pp_error_loc :=
  pp_user_error (Some ii) None
    (pp_s "The architecture does not provides protection for selective speculative load hardening").

Definition invalid_type_for_msf (ii : instr_info) : pp_error_loc :=
  pp_user_error (Some ii) None (pp_s "Invalid type for msf variable").

Notation internal_error_ s :=
  (pp_internal_error_s pass s).

End E.


(* -------------------------------------------------------------------------- *)
(* Well-formedness analysis. *)
(* Before replacing the sequential version of speculative execution operators
   with the speculative one, we need to ensure that they are used properly in
   the program.
   This analysis ensures that if we are not speculating, sequential and
   speculative execution match.
   We need to keep track of two things:
   1. We know that MSF variables are set to "not speculating".
   2. We know that if we are inside a conditional branch, the guard is true.

   The purpose of this analysis is not to decide whether the program is
   speculative constant time, but rather to decide whether we can lower the
   speculative execution operators.

   We don't need to track nested conditions because the type system rejects
   them. *)

Module Env.

  Section WITH_PARAMS.

  Context {fcparams : flag_combination.FlagCombinationParams}.

  (* We keep track of the condition of the last conditional we entered, and of
     the set of variables that are set as MSFs.

     We keep the simplified version of the condition, using constant
     propagation, in order to deal with double negations.
     The source type system will reject the program anyways if the condition of
     an [update_msf] doesn't correspond with the one in the conditional. *)
  Record t :=
    {
      cond : option pexpr;
      msf_vars : Sv.t;
    }.

  Definition restrict_cond (oc : option pexpr) (xs : Sv.t) : option pexpr :=
    if oc is Some c
    then if ~~ disjoint (read_e c) xs then None else oc
    else oc.

  (* Interface. *)

  Definition empty : t :=
    {|
      cond := None;
      msf_vars := Sv.empty;
    |}.

  Definition initial (ox : option var) : t :=
    {|
      cond := None;
      msf_vars := sv_of_option ox;
    |}.

  Definition update_cond (env : t) (c : pexpr) : t :=
    let c := constant_prop.empty_const_prop_e c in
    {| cond := Some c; msf_vars := msf_vars env; |}.

  Definition meet (env0 env1 : t) : t :=
    let c :=
      match cond env0, cond env1 with
      | Some c0, Some c1 => if eq_expr c0 c1 then Some c0 else None
      | _, _ => None
      end
    in
    {|
      cond := c;
      msf_vars := Sv.inter (msf_vars env0) (msf_vars env1);
    |}.

  (* This order corresponds to how much information the environments carry. *)
  Definition le (env0 env1 : t) : bool :=
    let bcond :=
      match cond env0, cond env1 with
      | None, _ => true
      | Some _, None => false
      | Some c0, Some c1 => eq_expr c0 c1
      end
    in
    bcond && Sv.subset (msf_vars env0) (msf_vars env1).

  Definition is_msf_var (env : t) (x : var) : bool :=
    Sv.mem x (msf_vars env).

  (* If [c] is true then the compiler will have removed the conditional
     branch. *)
  Definition is_cond (env : t) (c : pexpr) : bool :=
    eq_expr c (Pbool true) ||
    let c := constant_prop.empty_const_prop_e c in
    if cond env is Some c' then eq_expr c c' else false.

  Definition after_SLHmove (env : t) (ox : option var) : t :=
    let s := sv_of_option ox in
    {|
      cond := restrict_cond (cond env) s;
      msf_vars := Sv.union s (msf_vars env);
    |}.

  Definition after_assign_var (env : t) (x : var) : t :=
    {|
      cond := restrict_cond (cond env) (Sv.singleton x);
      msf_vars := Sv.remove x (msf_vars env);
    |}.

  Definition after_assign_vars (env : t) (xs : Sv.t) : t :=
    {|
      cond := restrict_cond (cond env) xs;
      msf_vars := Sv.diff (msf_vars env) xs;
    |}.

  End WITH_PARAMS.
End Env.

Section CHECK.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
  {msfsz : MSFsize}
  {fcparams : flag_combination.FlagCombinationParams}
  {pT : progT}.

Section CHECK_SLHO.

  Definition check_e_msf ii env e :=
    match e with
    | Pvar msf =>
      assert (Env.is_msf_var env (v_var (gv msf)) && is_lvar msf) (E.msf_not_found ii (gv msf) (Env.msf_vars env))
    | _ => Error (E.expr_variable ii e)
    end.

  Definition check_lv ii lv :=
    match lv with
    | Lvar x => ok (Some (v_var x))
    | Lnone _ _ => ok None
    | _ => Error (E.lvar_variable ii)
    end.

  Definition check_lv_msf ii lv :=
    Let ox := check_lv ii lv in
    Let _ :=
      assert
        (if ox is Some x then vtype x == sword msf_size else true)
        (E.invalid_type_for_msf ii)
    in
    ok ox.

  Notation get_e es i := (nth (Pconst 0) es i) (only parsing).
  Notation get_lv lvs i := (nth (Lnone dummy_var_info sint) lvs i) (only parsing).

  (* We need to check that when we use an MSF variable it's local and [msf_size]
     bits wide to make the proof go through, but this is ensured by the type
     checker. *)
  Definition check_slho
    (ii : instr_info)
    (lvs : seq lval)
    (slho : slh_op)
    (es : seq pexpr)
    (env : Env.t) :
    cexec Env.t :=
    match slho with
    | SLHinit =>
      Let ox := check_lv_msf ii (get_lv lvs 0) in
      ok (Env.initial ox)

    | SLHupdate =>
      let e := get_e es 0 in
      Let _ := assert (Env.is_cond env e)
                      (E.cond_not_found ii (Env.cond env) e) in
      Let _ := check_e_msf ii env (get_e es 1) in
      Let ox := check_lv_msf ii (get_lv lvs 0) in
      ok (Env.after_SLHmove env ox)

    | SLHmove =>
      Let _ := check_e_msf ii env (get_e es 0) in
      Let ox := check_lv_msf ii (get_lv lvs 0) in
      ok (Env.after_SLHmove env ox)

    | SLHprotect _ =>
      Let _ := check_e_msf ii env (get_e es 1) in
      ok (Env.after_assign_vars env (vrv (get_lv lvs 0)))

    | SLHprotect_ptr _ =>
      Let _ := check_e_msf ii env (get_e es 1) in
      ok (Env.after_assign_vars env (vrv (get_lv lvs 0)))

    | SLHprotect_ptr_fail _ => (* fail should not be used at this point *)
      ok (Env.after_assign_vars env (vrv (get_lv lvs 0)))
    end.

  Variant slh_t :=
    | Slh_None
    | Slh_msf.

  Definition check_f_arg ii env (e:pexpr) (ty:slh_t) :=
    if ty is Slh_msf then check_e_msf ii env e
    else ok tt.

  Definition check_f_args ii env (es:pexprs) (tys:seq slh_t) :=
    mapM2 E.invalid_nb_args (check_f_arg ii env) es tys.

  Definition check_f_lv ii env (lv:lval) (ty:slh_t) :=
    if ty is Slh_msf then
      Let ox := check_lv_msf ii lv in
      ok (Env.after_SLHmove env ox)
    else ok (Env.after_assign_vars env (vrv lv)).

  Fixpoint check_f_lvs ii env (lvs:lvals) (tys: seq slh_t) :=
    match lvs, tys with
    | [::], [::] => ok env
    | lv::lvs, ty::tys => Let env := check_f_lv ii env lv ty in check_f_lvs ii env lvs tys
    | _, _ => Error E.invalid_nb_lvals
    end.

  Fixpoint init_fun_env env (xs:seq var_i) (ttys: seq stype) (tys: seq slh_t) :=
    match xs, ttys, tys with
    | [::], [::], [::] => ok env
    | x::xs, t::ttys, ty::tys =>
        Let env :=
          if ty is Slh_msf then
            Let _ := assert ((vtype (v_var x) == sword msf_size) && (t == sword msf_size))
                            (E.internal_error_ "invalid params (type)") in
            ok (Env.after_SLHmove env (Some (v_var x)))
          else ok (Env.after_assign_var env (v_var x)) in
        init_fun_env env xs ttys tys
    | _, _, _ => Error (E.internal_error_ "invalid params (nb)")
    end.

  Fixpoint check_res env (xs:seq var_i) (ttys: seq stype) (tys: seq slh_t) :=
    match xs, ttys, tys with
    | [::], [::], [::] => ok tt
    | x::xs, t::ttys, ty::tys =>
      Let _ := assert (if ty is Slh_msf then Env.is_msf_var env x else true)
                      (E.msf_not_found_r x (Env.msf_vars env)) in
      Let _ := assert (if ty is Slh_msf then t == sword msf_size else true)
                      (E.internal_error_ "invalid return (type)") in
      check_res env xs ttys tys
    | _, _, _ => Error (E.internal_error_ "invalid return (nb)")
    end.

End CHECK_SLHO.

Section CHECK_FOR.

  (* To check a for loop [for x = _ to _ { c }] we consider the body as an
     environment transformer, and we try to find an environment [env*] such that
     [check_c (after_assign_var env* x) = env'] with [env'] carrying at least as
     much information as [env*] (denoted [env* <= env']).
     This way, we can we weaken the result of [c] from [env'] to [env*].
     This means that we are looking for [env*] a fixed point for the
     transformation induced by [c]. *)

  Context
    (ii : instr_info)
    (x : var)
    (check_c : Env.t -> cexec Env.t).

  (* We use the argument [env] as an initial guess for [env*], and if it is not
     a fixed point we guess the intersection (meet) of [env] and [env'], and
     repeat this process [fuel] times.

     Inside the body of the loop we know that [x] has been set to its new
     value. *)
  Fixpoint check_for (fuel : nat) (env : Env.t) : cexec Env.t :=
    if fuel is S n
    then
      Let env' := check_c (Env.after_assign_var env x) in
      if Env.le env env'
      then ok env
      else check_for n (Env.meet env env')
    else
      Error (ii_loop_iterator E.pass ii).

End CHECK_FOR.

Section CHECK_WHILE.

  (* To check a while loop [while { c0 } (c) { c1 }] we consider the two bodies
     as environment transformers, and we try to find an environment [env*] such
     that [check_c0 env* = ok env0] and [check_c1 env0 = ok env1] with [env1]
     carrying at least as much information as [env*] (denoted [env* <= env1]).
     This way, we can we weaken the result of [c1] from [env1] to [env*].
     This means that we are looking for [env*] a fixed point for the
     transformation induced by [c0; c1].
     We can then take [env0] as a resulting environment for the whole [while],
     since:
     - If [c1] never runs, we get [env0].
     - If [c1] runs at least once, we get the sequence
           env* -c0-> env0 -c1-> env* -c0-> env0 -c1-> ...
     and after [c0] is executed for the last time we get [env0]. *)

  Context
    (ii : instr_info)
    (cond : pexpr)
    (check_c0 check_c1 : Env.t -> cexec Env.t).

  (* Similarly to the for loop case, we use the argument [env] as an initial
     guess for [env*], and if it is not a fixed point we guess the intersection
     (meet) of [env] and [env1], and repeat this process [fuel] times.

     Inside the body of the loop, [c1], we know that the condition is true, and
     after we leave we know that it's false. *)
  Fixpoint check_while (fuel : nat) (env : Env.t) : cexec Env.t :=
    if fuel is S n
    then
      Let env0 := check_c0 env in
      Let env1 := check_c1 (Env.update_cond env0 cond) in
      if Env.le env env1
      then ok (Env.update_cond env0 (enot cond))
      else check_while n (Env.meet env env1)
    else
      Error (ii_loop_iterator E.pass ii).

End CHECK_WHILE.

Notation rec_check_cmd check_i := (fun c env => foldM check_i env c).

Notation chk_mem ii cond :=
  (assert (~~ use_mem cond) (E.cond_uses_mem ii cond))
  (only parsing).

Record sh_params :=
  {
    (* Lower a speculative operator. *)
    shp_lower : seq lval -> slh_op -> seq pexpr -> option copn_args;
  }.

Context
  (shparams : sh_params)
  (fun_info : funname -> seq slh_t * seq slh_t).

(* We need to ensure that conditions don't depend on memory, since this makes it
   impossible to tell whether their value is still true after branching.
   This is not a limitation, since such programs are anyways rejected by the
   type checker because they are not constant time. *)
Fixpoint check_i (i : instr) (env : Env.t) : cexec Env.t :=
  let: check_cmd := rec_check_cmd check_i in
  let: (MkI ii ir) := i in
  match ir with
  | Cassgn lv _ _ _ => ok (Env.after_assign_vars env (vrv lv))

  | Copn lvs _ op es =>
      if op is Oslh slho
      then check_slho ii lvs slho es env
      else ok (Env.after_assign_vars env (vrvs lvs))

  | Csyscall _ _ _ => ok Env.empty

  | Cif cond c0 c1 =>
      Let _ := chk_mem ii cond in
      Let env0 := check_cmd c0 (Env.update_cond env cond) in
      Let env1 := check_cmd c1 (Env.update_cond env (enot cond)) in
      ok (Env.meet env0 env1)

  | Cfor x _ c => check_for ii x (check_cmd c) Loop.nb env

  | Cwhile _ c0 cond c1 =>
      Let _ := chk_mem ii cond in
      check_while ii cond (check_cmd c0) (check_cmd c1) Loop.nb env

  | Ccall xs fn es =>
      let '(in_t, out_t) := fun_info fn in
      Let _ := check_f_args ii env es in_t in
      check_f_lvs ii env xs out_t
  end.

Definition check_cmd (env : Env.t) (c : cmd) : cexec Env.t :=
  rec_check_cmd check_i c env.

Definition check_fd
   (fn:funname) (fd : fundef) : cexec unit :=
  let '(in_t, out_t) := fun_info fn in
  Let env := init_fun_env Env.empty (f_params fd) (f_tyin fd) in_t in
  Let env := check_cmd env (f_body fd) in
  Let _ := check_res env (f_res fd) (f_tyout fd) out_t in
  ok tt.

Definition is_protect_ptr (slho : slh_op) :=
  if slho is SLHprotect_ptr p then Some p
  else None.

Definition lower_slho
  (ii : instr_info)
  (lvs : seq lval)
  (tg : assgn_tag)
  (slho : slh_op)
  (es : seq pexpr) :
  cexec instr_r :=
  if is_protect_ptr slho is Some p then
       ok (Copn lvs tg (Oslh (SLHprotect_ptr_fail p)) es)
  else if shp_lower shparams lvs slho es is Some args then
       ok (instr_of_copn_args tg args)
  else Error (E.lowering_failed ii).

Notation rec_cmd lower_i c := (mapM lower_i c).

Fixpoint lower_i (i : instr) : cexec instr :=
  let lower_cmd c := rec_cmd lower_i c in
  let '(MkI ii ir) := i in
  Let i :=
    match ir with
    | Cassgn _ _ _ _ =>
      ok ir

    | Copn lvs tg op es =>
      if op is Oslh slho
      then lower_slho ii lvs tg slho es
      else ok ir

    | Csyscall _ _ _ =>
        ok ir

    | Cif b c0 c1 =>
      Let c0' := lower_cmd c0 in
      Let c1' := lower_cmd c1 in
      ok (Cif b c0' c1')

    | Cfor x r c =>
      Let c' := lower_cmd c in
      ok (Cfor x r c')

    | Cwhile al c0 b c1 =>
      Let c0' := lower_cmd c0 in
      Let c1' := lower_cmd c1 in
      ok (Cwhile al c0' b c1')

    | Ccall _ _ _ =>
        ok ir
    end
  in
  ok (MkI ii i).

Definition lower_cmd (c : cmd) : cexec cmd := rec_cmd lower_i c.

Definition lower_fd (fn:funname) (fd:fundef) :=
  Let _ := check_fd fn fd in
  let 'MkFun ii si p c so r ev := fd in
  Let c := lower_cmd c in
  ok (MkFun ii si p c so r ev).

Definition is_shl_none ty :=
  if ty is Slh_None then true
  else false.

Definition lower_slh_prog (entries : seq funname) (p : prog) : cexec prog :=
   Let _ := assert (all (fun f => all is_shl_none (fst (fun_info f))) entries)
                   (E.pp_user_error None None (pp_s "export function should not take a misspeculation flag as input")) in
   Let p_funcs := map_cfprog_name lower_fd (p_funcs p) in
   ok  {| p_funcs  := p_funcs;
          p_globs := p_globs p;
          p_extra := p_extra p;
        |}.

End CHECK.
