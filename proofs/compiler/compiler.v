From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype fintype.
From mathcomp Require Import ssralg.
Require Import ZArith Uint63.
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
  lower_spill
  dead_code
  inline
  linearization
  lowering
  makeReferenceArguments
  propagate_inline
  slh_lowering
  remove_globals
  stack_alloc
  stack_zeroization
  tunneling
  unrolling
  wsize.
Require
  merge_varmaps.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* FIXME: expr exports wsize, which overrides this. *)
Definition pp_s := compiler_util.pp_s.

Section IS_MOVE_OP.

Context
  {msfsz : MSFsize}
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
  | LowerSpill                  : compiler_step
  | Inlining                    : compiler_step
  | RemoveUnusedFunction        : compiler_step
  | Unrolling                   : compiler_step
  | Splitting                   : compiler_step
  | Renaming                    : compiler_step
  | RemovePhiNodes              : compiler_step
  | DeadCode_Renaming           : compiler_step
  | RemoveArrInit               : compiler_step
  | MakeRefArguments            : compiler_step
  | RegArrayExpansion           : compiler_step
  | RemoveGlobal                : compiler_step
  | LowerInstruction            : compiler_step
  | PropagateInline             : compiler_step
  | SLHLowering                 : compiler_step
  | StackAllocation             : compiler_step
  | RemoveReturn                : compiler_step
  | RegAllocation               : compiler_step
  | DeadCode_RegAllocation      : compiler_step
  | Linearization               : compiler_step
  | StackZeroization            : compiler_step
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
  ; LowerSpill
  ; Inlining
  ; RemoveUnusedFunction
  ; Unrolling
  ; Splitting
  ; Renaming
  ; RemovePhiNodes
  ; DeadCode_Renaming
  ; RemoveArrInit
  ; MakeRefArguments
  ; RegArrayExpansion
  ; RemoveGlobal
  ; LowerInstruction
  ; PropagateInline
  ; SLHLowering
  ; StackAllocation
  ; RemoveReturn
  ; RegAllocation
  ; DeadCode_RegAllocation
  ; Linearization
  ; StackZeroization
  ; Tunneling
  ; Assembly
].

(* To use [Finite.axiom], we must first show that [compiler_step] is [eqType]. *)
Scheme Equality for compiler_step.
Lemma compiler_step_eq_axiom : Equality.axiom compiler_step_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_compiler_step_dec_bl
       internal_compiler_step_dec_lb).
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
  (lowering_options : Type) := {
  rename_fd        : instr_info -> funname -> _ufundef -> _ufundef;
  expand_fd        : funname -> _ufundef -> expand_info;
  split_live_ranges_fd : funname -> _ufundef -> _ufundef;
  renaming_fd      : funname -> _ufundef -> _ufundef;
  remove_phi_nodes_fd : funname -> _ufundef -> _ufundef;
  stack_register_symbol: Ident.ident;
  global_static_data_symbol: Ident.ident;
  stackalloc       : _uprog → stack_alloc_oracles;
  removereturn     : _sprog -> (funname -> option (seq bool));
  regalloc         : seq _sfun_decl -> seq _sfun_decl;
  print_uprog      : compiler_step -> _uprog -> _uprog;
  print_sprog      : compiler_step -> _sprog -> _sprog;
  print_linear     : compiler_step -> lprog -> lprog;
  refresh_instr_info: funname -> _ufundef -> _ufundef;
  warning          : instr_info -> warning_msg -> instr_info;
  lowering_opt     : lowering_options;
  fresh_id         : glob_decls -> var -> Ident.ident;
  fresh_var_ident  : v_kind -> instr_info -> int -> string -> stype -> Ident.ident;
  slh_info         : _uprog → funname → seq slh_t * seq slh_t;
  stack_zero_info  : funname -> option (stack_zero_strategy * option wsize);
}.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {syscall_state : Type}.

Context
  {call_conv: calling_convention}
  {lowering_options : Type}
  (aparams : architecture_params lowering_options)
  (cparams : compiler_params lowering_options).

Notation saparams := (ap_sap aparams).
Notation liparams := (ap_lip aparams).
Notation loparams := (ap_lop aparams).
Notation shparams := (ap_shp aparams).
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
Definition var_tmp2 : var :=
  {| vname := lip_tmp2 liparams; vtype := sword Uptr; |}.
Definition var_tmps : Sv.t := Sv.add var_tmp2 (Sv.singleton var_tmp).

Definition live_range_splitting (p: uprog) : cexec uprog :=
  let pv := split_live_ranges_prog p in
  let pv := cparams.(print_uprog) Splitting pv in
  let pv := renaming_prog pv in
  let pv := cparams.(print_uprog) Renaming pv in
  let pv := remove_phi_nodes_prog pv in
  let pv := cparams.(print_uprog) RemovePhiNodes pv in
  let pv := map_prog_name (refresh_instr_info cparams) pv in
  Let _ := check_uprog (wsw:= withsubword) p.(p_extra) p.(p_funcs) pv.(p_extra) pv.(p_funcs) in
  Let pv := dead_code_prog (ap_is_move_op aparams) pv false in
  let p := cparams.(print_uprog) DeadCode_Renaming pv in
  ok p.

Definition inlining (to_keep: seq funname) (p: uprog) : cexec uprog :=
  Let p := inline_prog_err (wsw := withsubword) cparams.(rename_fd) p in
  let p := cparams.(print_uprog) Inlining p in

  Let p := dead_calls_err_seq to_keep p in
  let p := cparams.(print_uprog) RemoveUnusedFunction p in
  ok p.

Definition compiler_first_part (to_keep: seq funname) (p: prog) : cexec uprog :=

  Let p :=
    array_copy_prog
      (fresh_var_ident cparams Inline dummy_instr_info 0 "i__copy" sint)
      (λ ws, fresh_var_ident cparams (Reg (Normal, Direct)) dummy_instr_info 0 "tmp" (sword ws))
      p in
  let p := cparams.(print_uprog) ArrayCopy p in

  let p := add_init_prog p in
  let p := cparams.(print_uprog) AddArrInit p in

  Let p :=
    spill_prog
      (fun k ii => fresh_var_ident cparams k ii 0)
      p in
  let p := cparams.(print_uprog) LowerSpill p in

  Let p := inlining to_keep p in

  Let p := unroll_loop (ap_is_move_op aparams) p in
  let p := cparams.(print_uprog) Unrolling p in

  Let p := dead_calls_err_seq to_keep p in
  let p := cparams.(print_uprog) RemoveUnusedFunction p in

  Let pv := live_range_splitting p in

  let pr := remove_init_prog is_reg_array pv in
  let pr := cparams.(print_uprog) RemoveArrInit pr in

  Let pa := makereference_prog (fresh_var_ident cparams (Reg (Normal, Pointer Writable))) pr in
  let pa := cparams.(print_uprog) MakeRefArguments pa in

  Let pe := expand_prog cparams.(expand_fd) to_keep pa in
  let pe := cparams.(print_uprog) RegArrayExpansion pe in

  Let pe := live_range_splitting pe in

  Let pg := remove_glob_prog cparams.(fresh_id) pe in
  let pg := cparams.(print_uprog) RemoveGlobal pg in

  Let _ :=
    assert
      (lop_fvars_correct loparams (fresh_var_ident cparams (Reg (Normal, Direct)) dummy_instr_info 0) (p_funcs pg))
      (pp_internal_error_s "lowering" "lowering check fails")
  in

  let p :=
    lower_prog
      (lop_lower_i loparams)
      (lowering_opt cparams)
      (warning cparams)
      (fresh_var_ident cparams (Reg (Normal, Direct)) dummy_instr_info 0)
      pg
  in
  let p := cparams.(print_uprog) LowerInstruction p in

  Let p := propagate_inline.pi_prog p in
  let p := cparams.(print_uprog) PropagateInline p in

  Let p := lower_slh_prog shparams (cparams.(slh_info) p) to_keep p in
  let p := cparams.(print_uprog) SLHLowering p in

  ok p.

Definition compiler_third_part (returned_params: funname -> option (seq (option nat))) (ps: sprog) : cexec sprog :=

  let rminfo := cparams.(removereturn) ps in
  let rminfo fn :=
    match returned_params fn with
    | Some l =>
      let l' := List.map (fun i => if i is None then true else false) l in
      if all (fun b => b) l' then None else Some l' (* do we want that? *)
    | None => rminfo fn
    end
  in
  Let pr := dead_code_prog_tokeep (ap_is_move_op aparams) false rminfo ps in
  let pr := cparams.(print_sprog) RemoveReturn pr in

  let pa := {| p_funcs := cparams.(regalloc) pr.(p_funcs) ; p_globs := pr.(p_globs) ; p_extra := pr.(p_extra) |} in
  let pa : sprog := cparams.(print_sprog) RegAllocation pa in
  Let _ := check_sprog (wsw:= withsubword) pr.(p_extra) pr.(p_funcs) pa.(p_extra) pa.(p_funcs) in

  Let pd := dead_code_prog (ap_is_move_op aparams) pa true in
  let pd := cparams.(print_sprog) DeadCode_RegAllocation pd in

  ok pd.

(* returns None if not reg ptr, Some false if reg const ptr, Some true if reg mut ptr *)
Definition wptr_status (x : var_i) :=
  match Ident.id_kind x.(vname) with
  | Reg (_, Pointer writable) =>
    Some match writable with | Writable => true | Constant => false end
  | _ => None
  end.

Definition allNone {A: Type} (m: seq (option A)) : bool :=
  all (fun a => if a is None then true else false) m.

(** Export functions (entry points) have restrictions on ptr arguments and returns.
    Namely, the writable ptr arrays should be the first arguments and returned at the same
    positions in the return values.
    This is not a constraint coming from the implementation, it is just meant to give
    a readable correctness theorem. *)
Definition check_wf_ptr entries (p:prog) (ao: funname -> stk_alloc_oracle_t) : cexec unit :=
  Let _ :=
    allM (fun fn =>
      match get_fundef p.(p_funcs) fn with
      | None => ok tt
      | Some fd =>
        assert
          (all2
            (fun (x:var_i) pi => wptr_status x == omap pp_writable pi)
            fd.(f_params) (ao fn).(sao_params))
          (pp_at_fi fd.(f_info) (pp_at_fn fn
            (stack_alloc.E.stk_ierror_no_var "inconsistent wptr_status")))
      end) entries
  in
    allM (fun fn =>
      match get_fundef p.(p_funcs) fn with
      | None => ok tt
      | Some fd =>
        let n := find (fun x => wptr_status x != Some true) fd.(f_params) in
        assert
          ((take n (ao fn).(sao_return) == map Some (iota 0 n)) &&
            allNone (drop n (ao fn).(sao_return)))
          (pp_at_fi fd.(f_info) (pp_at_fn fn
            (stack_alloc.E.stk_error_no_var_gen false
              (pp_nobox [::
                pp_s "the ordering of the arguments or the results is not correct.";
                PPEbreak;
                pp_s "The reg mut ptr must come first in the arguments";
                pp_s " and be returned first, in the same order, in the results."]))))
      end) entries.

Definition compiler_front_end (entries: seq funname) (p: prog) : cexec sprog :=

  Let pl := compiler_first_part entries p in
  (* stack + register allocation *)

  let ao := cparams.(stackalloc) pl in
  Let _ := check_wf_ptr entries p ao.(ao_stack_alloc) in
  Let ps :=
    stack_alloc.alloc_prog
      true
      shparams
      saparams
      (fresh_var_ident cparams (Reg (Normal, Direct)) dummy_instr_info 0)
      (global_static_data_symbol cparams)
      (stack_register_symbol cparams)
      (ao_globals ao)
      (ao_global_alloc ao)
      (ao_stack_alloc ao)
      pl
  in
  let ps : sprog := cparams.(print_sprog) StackAllocation ps in

  let returned_params fn :=
    if fn \in entries then Some (ao_stack_alloc ao fn).(sao_return) else None
  in
  Let pd := compiler_third_part returned_params ps in

  ok pd.

Definition check_export entries (p: sprog) : cexec unit :=
  allM (λ fn,
          if get_fundef (p_funcs p) fn is Some fd then
            assert
              (is_RAnone fd.(f_extra).(sf_return_address))
              (pp_at_fn fn (merge_varmaps.E.gen_error true None (pp_s "export function expects a return address")))
          else Error (pp_at_fn fn (merge_varmaps.E.gen_error true None (pp_s "unknown export function")))
       ) entries.

Definition compiler_back_end entries (pd: sprog) :=
  Let _ := check_export entries pd in
  (* linearisation                     *)
  Let _ := merge_varmaps.check pd var_tmps in
  Let pl := linear_prog liparams pd in
  let pl := cparams.(print_linear) Linearization pl in
  (* stack zeroization                 *)
  let szs_of_fn fn :=
    match cparams.(stack_zero_info) fn with
    | Some (szs, ows) =>
      let ws :=
        match ows with
        | Some ws => ws
        | None =>
          (* the default clear step is the alignment *)
          if get_fundef pl.(lp_funcs) fn is Some lfd then
            lfd.(lfd_align)
          else U8 (* impossible *)
        end
      in
      Some (szs, ws)
    | None => None
    end
  in
  Let pl := stack_zeroization_lprog aparams.(ap_szp) szs_of_fn pl in
  let pl := cparams.(print_linear) StackZeroization pl in
  (* tunneling                         *)
  Let pl := tunnel_program pl in
  let pl := cparams.(print_linear) Tunneling pl in

  ok pl.

Definition compiler_back_end_to_asm (entries: seq funname) (p: sprog) :=
  Let lp := compiler_back_end entries p in
  assemble_prog agparams lp.

Definition compile_prog_to_asm entries (p: prog): cexec asm_prog :=
  compiler_front_end entries p >>= compiler_back_end_to_asm entries.

End COMPILER.
