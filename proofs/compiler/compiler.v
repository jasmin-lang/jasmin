From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith.
Require Import Utf8.

Require Import
  arch_params
  compiler_util
  expr
  flag_combination.
Require Import
  arch_decl
  arch_extra
  asm_gen.
Require Import
  allocation
  array_copy
  array_expansion
  array_init
  constant_prop
  dead_calls
  dead_code
  inline
  linearization
  lowering
  makeReferenceArguments
  propagate_inline
  remove_globals
  stack_alloc
  tunneling
  unrolling.
Require merge_varmaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* FIXME: expr exports wsize, which overrides this. *)
Definition pp_s := compiler_util.pp_s.

Section IS_MOVE_OP.

Context
  `{asmop : asmOp}
  {fcp : FlagCombinationParams}
  (is_move_op : asm_op_t -> bool).

Let postprocess (p: uprog) : cexec uprog :=
  let p := const_prop_prog p in
  dead_code_prog is_move_op p false.

(* FIXME: error really not clear for the user *)
(* TODO: command line option to specify the unrolling depth,
   the error should suggest increasing the number
*)
Fixpoint unroll (n: nat) (p: uprog) : cexec uprog :=
  if n is S n' then
    let: (p', repeat) := unroll_prog p in
    if repeat then
      Let: p'' := postprocess p' in
      unroll n' p''
    else ok p
  else Error (loop_iterator "unrolling").

Definition unroll_loop (p: uprog) :=
  Let p := postprocess p in
  unroll Loop.nb p.

End IS_MOVE_OP.

Section COMPILER.

Variant compiler_step :=
  | Typing                      : compiler_step
  | ParamsExpansion             : compiler_step
  | ArrayCopy                   : compiler_step
  | AddArrInit                  : compiler_step
  | Inlining                    : compiler_step
  | RemoveUnusedFunction        : compiler_step
  | Unrolling                   : compiler_step
  | Splitting                   : compiler_step
  | Renaming                    : compiler_step
  | RemovePhiNodes              : compiler_step
  | DeadCode_Renaming           : compiler_step
  | RemoveArrInit               : compiler_step
  | RegArrayExpansion           : compiler_step
  | RemoveGlobal                : compiler_step
  | MakeRefArguments            : compiler_step
  | LowerInstruction            : compiler_step
  | PropagateInline             : compiler_step
  | StackAllocation             : compiler_step
  | RemoveReturn                : compiler_step
  | RegAllocation               : compiler_step
  | DeadCode_RegAllocation      : compiler_step
  | Linearization               : compiler_step
  | Tunneling                   : compiler_step
  | Assembly                    : compiler_step.

(* This is a list of the compiler passes. It is defined in Coq so that we can
   show that it is exhaustive (cf. [compiler_step_list_complete]).
*)
Definition compiler_step_list := [::
    Typing
  ; ParamsExpansion
  ; ArrayCopy
  ; AddArrInit
  ; Inlining
  ; RemoveUnusedFunction
  ; Unrolling
  ; Splitting
  ; Renaming
  ; RemovePhiNodes
  ; DeadCode_Renaming
  ; RemoveArrInit
  ; RegArrayExpansion
  ; RemoveGlobal
  ; MakeRefArguments
  ; LowerInstruction
  ; PropagateInline 
  ; StackAllocation
  ; RemoveReturn
  ; RegAllocation
  ; DeadCode_RegAllocation
  ; Linearization
  ; Tunneling
  ; Assembly
].

(* To use [Finite.axiom], we must first show that [compiler_step] is [eqType]. *)
Scheme Equality for compiler_step.
Lemma compiler_step_eq_axiom : Equality.axiom compiler_step_beq.
Proof.
  move=> x y; apply:(iffP idP).
  + by apply: internal_compiler_step_dec_bl.
  by apply: internal_compiler_step_dec_lb.
Qed.
Definition compiler_step_eqMixin := Equality.Mixin compiler_step_eq_axiom.
Canonical  compiler_step_eqType  := Eval hnf in EqType compiler_step compiler_step_eqMixin.

Lemma compiler_step_list_complete : Finite.axiom compiler_step_list.
Proof. by case. Qed.

Record stack_alloc_oracles : Type :=
  {
    ao_globals: seq u8; (* static global data: one array holding all data *)
    ao_global_alloc: seq (var * wsize * Z); (* allocation of global variables in the previous array *)
    ao_stack_alloc: funname → stk_alloc_oracle_t;
  }.

Record compiler_params
  {asm_op : Type}
  {asmop : asmOp asm_op}
  (fresh_vars lowering_options : Type) := {
  rename_fd        : instr_info -> funname -> _ufundef -> _ufundef;
  expand_fd        : funname -> _ufundef -> expand_info;
  split_live_ranges_fd : funname -> _ufundef -> _ufundef;
  renaming_fd      : funname -> _ufundef -> _ufundef;
  remove_phi_nodes_fd : funname -> _ufundef -> _ufundef;
  lowering_vars    : fresh_vars;
  inline_var       : var -> bool;
  is_var_in_memory : var_i → bool;
  stack_register_symbol: Ident.ident;
  global_static_data_symbol: Ident.ident;
  stackalloc       : _uprog → stack_alloc_oracles;
  removereturn     : _sprog -> (funname -> option (seq bool));
  regalloc         : seq _sfun_decl -> seq _sfun_decl;
  extra_free_registers : instr_info → option var;
  print_uprog      : compiler_step -> _uprog -> _uprog;
  print_sprog      : compiler_step -> _sprog -> _sprog;
  print_linear     : compiler_step -> lprog -> lprog;
  warning          : instr_info -> warning_msg -> instr_info;
  lowering_opt     : lowering_options;
  is_glob          : var -> bool;
  fresh_id         : glob_decls -> var -> Ident.ident;
  fresh_reg        : string -> stype -> Ident.ident;
  fresh_reg_ptr    : string -> stype -> Ident.ident;
  fresh_counter    : Ident.ident;
  is_reg_ptr       : var -> bool;
  is_ptr           : var -> bool;
  is_reg_array     : var -> bool;
  is_regx          : var -> bool;
}.


Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {syscall_state : Type}.

Context
  {call_conv: calling_convention}
  {fresh_vars lowering_options : Type}
  (aparams : architecture_params fresh_vars lowering_options)
  (cparams : compiler_params fresh_vars lowering_options).

Notation saparams := (ap_sap aparams cparams.(is_regx)).
Notation liparams := (ap_lip aparams).
Notation loparams := (ap_lop aparams).
Notation agparams := (ap_agp aparams).

#[local]
Existing Instance progUnit.

Definition split_live_ranges_prog (p: _uprog) : _uprog :=
  map_prog_name cparams.(split_live_ranges_fd) p.
Definition renaming_prog (p: _uprog) : _uprog :=
  map_prog_name cparams.(renaming_fd) p.
Definition remove_phi_nodes_prog (p: _uprog) : _uprog :=
  map_prog_name cparams.(remove_phi_nodes_fd) p.

Definition var_tmp : var :=
  {| vname := lip_tmp liparams; vtype := sword Uptr; |}.

(* Ensure that export functions are preserved *)
Definition check_removereturn (entries: seq funname) (remove_return: funname → option (seq bool)) :=
  assert (pmap remove_return entries == [::]) (pp_internal_error_s "remove return" "Signature of some export functions are modified").

(** Export functions (entry points) shall not have ptr arguments or return values. *)
Definition allNone {A: Type} (m: seq (option A)) : bool :=
  all (fun a => if a is None then true else false) m.

Definition check_no_ptr entries (ao: funname -> stk_alloc_oracle_t) : cexec unit :=
  allM (λ fn,
       let: sao := ao fn in
       assert (allNone sao.(sao_params)) (pp_at_fn fn (stack_alloc.E.stk_error_no_var "export functions don’t support “ptr” arguments")) >>
       assert (allNone sao.(sao_return)) (pp_at_fn fn (stack_alloc.E.stk_error_no_var "export functions don’t support “ptr” return values")))
    entries.

Definition compiler_first_part (to_keep: seq funname) (p: prog) : cexec uprog :=

  Let p := array_copy_prog cparams.(fresh_counter) p in
  let p := cparams.(print_uprog) ArrayCopy p in

  let p := add_init_prog cparams.(is_ptr) p in
  let p := cparams.(print_uprog) AddArrInit p in

  Let p := inline_prog_err cparams.(inline_var) cparams.(rename_fd) p in
  let p := cparams.(print_uprog) Inlining p in

  Let p := dead_calls_err_seq to_keep p in
  let p := cparams.(print_uprog) RemoveUnusedFunction p in

  Let p := unroll_loop (ap_is_move_op aparams) p in
  let p := cparams.(print_uprog) Unrolling p in

  let pv := split_live_ranges_prog p in
  let pv := cparams.(print_uprog) Splitting pv in
  let pv := renaming_prog pv in
  let pv := cparams.(print_uprog) Renaming pv in
  let pv := remove_phi_nodes_prog pv in
  let pv := cparams.(print_uprog) RemovePhiNodes pv in
  Let _ := check_uprog p.(p_extra) p.(p_funcs) pv.(p_extra) pv.(p_funcs) in
  Let pv := dead_code_prog (ap_is_move_op aparams) pv false in
  let pv := cparams.(print_uprog) DeadCode_Renaming pv in

  let pr := remove_init_prog cparams.(is_reg_array) pv in
  let pr := cparams.(print_uprog) RemoveArrInit pr in

  Let pe := expand_prog cparams.(expand_fd) pr in
  let pe := cparams.(print_uprog) RegArrayExpansion pe in

  Let pg := remove_glob_prog cparams.(is_glob) cparams.(fresh_id) pe in
  let pg := cparams.(print_uprog) RemoveGlobal pg in

  Let pa := makereference_prog cparams.(is_reg_ptr) cparams.(fresh_reg_ptr) pg in
  let pa := cparams.(print_uprog) MakeRefArguments pa in

  Let _ :=
    assert
      (lop_fvars_correct loparams cparams.(lowering_vars) (p_funcs pa))
      (pp_internal_error_s "lowering" "lowering check fails")
  in

  let pl :=
    lower_prog
      (lop_lower_i loparams)
      (lowering_opt cparams)
      (warning cparams)
      (lowering_vars cparams)
      (is_var_in_memory cparams)
      pa
  in
  let pl := cparams.(print_uprog) LowerInstruction pl in

  Let pp := propagate_inline.pi_prog pl in
  let pp := cparams.(print_uprog) PropagateInline pp in

  ok pp.

Definition compiler_third_part (entries: seq funname) (ps: sprog) : cexec sprog :=

  let rminfo := cparams.(removereturn) ps in
  Let _ := check_removereturn entries rminfo in
  Let pr := dead_code_prog_tokeep (ap_is_move_op aparams) false rminfo ps in
  let pr := cparams.(print_sprog) RemoveReturn pr in

  let pa := {| p_funcs := cparams.(regalloc) pr.(p_funcs) ; p_globs := pr.(p_globs) ; p_extra := pr.(p_extra) |} in
  let pa : sprog := cparams.(print_sprog) RegAllocation pa in
  Let _ := check_sprog pr.(p_extra) pr.(p_funcs) pa.(p_extra) pa.(p_funcs) in

  Let pd := dead_code_prog (ap_is_move_op aparams) pa true in
  let pd := cparams.(print_sprog) DeadCode_RegAllocation pd in

  ok pd.

Definition compiler_front_end (entries subroutines : seq funname) (p: prog) : cexec sprog :=

  Let pl := compiler_first_part (entries ++ subroutines) p in

  (* stack + register allocation *)

  let ao := cparams.(stackalloc) pl in
  Let _ := check_no_ptr entries ao.(ao_stack_alloc) in
  Let ps :=
    stack_alloc.alloc_prog
      true
      saparams
      cparams.(fresh_reg)
      (global_static_data_symbol cparams)
      (stack_register_symbol cparams)
      (ao_globals ao)
      (ao_global_alloc ao)
      (ao_stack_alloc ao)
      pl
  in
  let ps : sprog := cparams.(print_sprog) StackAllocation ps in

  Let pd := compiler_third_part entries ps in

  ok pd.

Definition check_export entries (p: sprog) : cexec unit :=
  allM (λ fn,
          if get_fundef (p_funcs p) fn is Some fd then
            assert
              (fd.(f_extra).(sf_return_address) == RAnone)
              (pp_at_fn fn (merge_varmaps.E.gen_error true None (pp_s "export function expects a return address")))
          else Error (pp_at_fn fn (merge_varmaps.E.gen_error true None (pp_s "unknown export function")))
       ) entries.

Definition compiler_back_end entries (pd: sprog) :=
  Let _ := check_export entries pd in
  (* linearisation                     *)
  Let _ := merge_varmaps.check pd cparams.(extra_free_registers) var_tmp in
  Let pl := linear_prog liparams pd cparams.(extra_free_registers) in
  let pl := cparams.(print_linear) Linearization pl in
  (* tunneling                         *)
  Let pl := tunnel_program pl in
  let pl := cparams.(print_linear) Tunneling pl in

  ok pl.

Definition compiler_back_end_to_asm (entries: seq funname) (p: sprog) :=
  Let lp := compiler_back_end entries p in
  assemble_prog agparams lp.

Definition compile_prog_to_asm entries subroutines (p: prog): cexec asm_prog :=
  compiler_front_end entries subroutines p >>= compiler_back_end_to_asm entries.

End COMPILER.
