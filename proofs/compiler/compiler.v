(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import x86_gen expr.
Import ZArith.
Require merge_varmaps.
Require Import compiler_util allocation array_copy array_init inline dead_calls unrolling remove_globals
   constant_prop propagate_inline dead_code array_expansion lowering makeReferenceArguments stack_alloc linearization tunneling.
Require Import x86_decl x86_sem x86_extra.
Require x86_stack_alloc x86_linearization.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Parameters specific to the architecture. *)
Definition mov_ofs := x86_stack_alloc.x86_mov_ofs.
Definition var_tmp := to_var RAX.
Definition lparams := x86_linearization.x86_linearization_params.

Section IS_MOVE_OP.

Context (is_move_op : asm_op_t -> bool).

Definition unroll1 (p:uprog) : cexec uprog:=
  let p := unroll_prog p in
  let p := const_prop_prog p in
  dead_code_prog is_move_op p false.

(* FIXME: error really not clear for the user *)
(* TODO: command line option to specify the unrolling depth,
   the error should suggest increasing the number
*)
Fixpoint unroll (n:nat) (p:uprog) :=
  match n with
  | O   => Error (loop_iterator "unrolling")
  | S n =>
    Let p' := unroll1 p in
    if ((p_funcs p: ufun_decls) == (p_funcs p': ufun_decls)) then ok p
    else unroll n p'
  end.

Definition unroll_loop (p:prog) := unroll Loop.nb p.

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

Record compiler_params := {
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
}.

(* Architecture-dependent functions *)
Record architecture_params := mk_aparams {
  is_move_op       : asm_op_t -> bool
}.

(* System dependant *)
Record system_params := mk_sparams {
  write_syscall : Sv.t; 
  syscall_vsig  : syscall_t -> seq var * seq var;
  callee_saved  : Sv.t;
}.

#[local]
Existing Instance progUnit.

Definition split_live_ranges_prog cp (p: _uprog) : _uprog :=
  map_prog_name cp.(split_live_ranges_fd) p.
Definition renaming_prog cp (p: _uprog) : _uprog :=
  map_prog_name cp.(renaming_fd) p.
Definition remove_phi_nodes_prog cp (p: _uprog) : _uprog :=
  map_prog_name cp.(remove_phi_nodes_fd) p.

Variable cparams : compiler_params.
Variable aparams : architecture_params.
Variable sparams : system_params.

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

  Let p := unroll aparams.(is_move_op) Loop.nb p in
  let p := cparams.(print_uprog) Unrolling p in

  let pv := split_live_ranges_prog cparams p in
  let pv := cparams.(print_uprog) Splitting pv in
  let pv := renaming_prog cparams pv in
  let pv := cparams.(print_uprog) Renaming pv in
  let pv := remove_phi_nodes_prog cparams pv in
  let pv := cparams.(print_uprog) RemovePhiNodes pv in
  Let _ := CheckAllocRegU.check_prog p.(p_extra) p.(p_funcs) pv.(p_extra) pv.(p_funcs) in
  Let pv := dead_code_prog aparams.(is_move_op) pv false in
  let pv := cparams.(print_uprog) DeadCode_Renaming pv in

  let pr := remove_init_prog cparams.(is_reg_array) pv in
  let pr := cparams.(print_uprog) RemoveArrInit pr in

  Let pe := expand_prog cparams.(expand_fd) pr in
  let pe := cparams.(print_uprog) RegArrayExpansion pe in

  Let pg := remove_glob_prog cparams.(is_glob) cparams.(fresh_id) pe in
  let pg := cparams.(print_uprog) RemoveGlobal pg in

  Let pa := makereference_prog cparams.(is_reg_ptr) cparams.(fresh_reg_ptr) pg in
  let pa := cparams.(print_uprog) MakeRefArguments pa in

  Let _ := assert (fvars_correct cparams.(lowering_vars) (p_funcs pa)) 
                  (pp_internal_error_s "lowering" "lowering check fails") in

  let pl := lower_prog cparams.(lowering_opt) cparams.(warning) cparams.(lowering_vars) cparams.(is_var_in_memory) pa in
  let pl := cparams.(print_uprog) LowerInstruction pl in

  Let pp := propagate_inline.pi_prog pl in
  let pp := cparams.(print_uprog) PropagateInline pp in 
  
  ok pp.

Definition compiler_third_part (entries: seq funname) (ps: sprog) : cexec sprog :=

  let rminfo := cparams.(removereturn) ps in
  Let _ := check_removereturn entries rminfo in
  Let pr := dead_code_prog_tokeep aparams.(is_move_op) false rminfo ps in
  let pr := cparams.(print_sprog) RemoveReturn pr in

  let pa := {| p_funcs := cparams.(regalloc) pr.(p_funcs) ; p_globs := pr.(p_globs) ; p_extra := pr.(p_extra) |} in
  let pa : sprog := cparams.(print_sprog) RegAllocation pa in
  Let _ := CheckAllocRegS.check_prog pr.(p_extra) pr.(p_funcs) pa.(p_extra) pa.(p_funcs) in

  Let pd := dead_code_prog aparams.(is_move_op) pa true in
  let pd := cparams.(print_sprog) DeadCode_RegAllocation pd in

  ok pd.

Definition compiler_front_end (entries subroutines : seq funname) (p: prog) : cexec sprog :=

  Let pl := compiler_first_part (entries ++ subroutines) p in

  (* stack + register allocation *)

  let ao := cparams.(stackalloc) pl in
  Let _ := check_no_ptr entries ao.(ao_stack_alloc) in
  Let ps := stack_alloc.alloc_prog
       true
       mov_ofs
       cparams.(fresh_reg)
       cparams.(global_static_data_symbol)
       cparams.(stack_register_symbol)
       ao.(ao_globals) ao.(ao_global_alloc)
       ao.(ao_stack_alloc) pl in
  let ps : sprog := cparams.(print_sprog) StackAllocation ps in

  Let pd := compiler_third_part entries ps in

  ok pd.

Definition check_export entries (p: sprog) : cexec unit :=
  allM (λ fn,
          if get_fundef (p_funcs p) fn is Some fd then
            assert (fd.(f_extra).(sf_return_address) == RAnone)
                   (pp_at_fn fn (merge_varmaps.E.gen_error true None (pp_s "export function expects a return address")))
          else Error (pp_at_fn fn (merge_varmaps.E.gen_error true None (pp_s "unknown export function")))
       ) entries.

Definition compiler_back_end entries (pd: sprog) :=
  Let _ := check_export entries pd in
  (* linearisation                     *)
  Let _ := merge_varmaps.check pd cparams.(extra_free_registers) var_tmp sparams.(callee_saved)
                sparams.(write_syscall) sparams.(syscall_vsig) in
  Let pl := linear_prog pd cparams.(extra_free_registers) lparams in
  let pl := cparams.(print_linear) Linearization pl in
  (* tunneling                         *)
  Let pl := tunnel_program pl in
  let pl := cparams.(print_linear) Tunneling pl in

  ok pl.

Definition compile_prog (entries subroutines : seq funname) (p: prog) :=
  Let pd := compiler_front_end entries subroutines p in
  Let pl := compiler_back_end entries pd in
  ok pl.

Definition check_signature (p: prog) (lp: lprog) (fn: funname) : bool :=
  if get_fundef lp.(lp_funcs) fn is Some fd' then
    if get_fundef (p_funcs p) fn is Some fd then
      signature_of_fundef fd == signature_of_lfundef fd'
    else true
  else true.

Definition compile_prog_to_x86 entries subroutines (p: prog): cexec x86_prog :=
  Let lp := compile_prog entries subroutines p in
(*  Let _ := assert (all (check_signature p lp) entries) Ferr_lowering in *)
  assemble_prog lp.

End COMPILER.

