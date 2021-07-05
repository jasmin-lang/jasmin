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
Require Import compiler_util allocation array_init inline dead_calls unrolling remove_globals
   constant_prop dead_code array_expansion lowering makeReferenceArguments stack_alloc linear tunneling x86_sem.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Instance pT : progT [eqType of unit] := progUnit.

Definition unroll1 (p:uprog) : cfexec uprog:=
  let p := unroll_prog p in
  let p := const_prop_prog p in
  dead_code_prog p.

Fixpoint unroll (n:nat) (p:uprog) :=
  match n with
  | O   => cferror Ferr_loop
  | S n =>
    Let p' := unroll1 p in
    if ((p_funcs p: ufun_decls) == (p_funcs p': ufun_decls)) then cfok p
    else unroll n p'
  end.

Definition unroll_loop (p:prog) := unroll Loop.nb p.

Section COMPILER.

Variant compiler_step :=
  | Typing                      : compiler_step
  | ParamsExpansion             : compiler_step
  | AddArrInit                  : compiler_step
  | Inlining                    : compiler_step
  | RemoveUnusedFunction        : compiler_step
  | Unrolling                   : compiler_step
  | Splitting                   : compiler_step
  | AllocInlineAssgn            : compiler_step
  | DeadCode_AllocInlineAssgn   : compiler_step
  | RegArrayExpansion           : compiler_step
  | RemoveArrInit               : compiler_step
  | RemoveGlobal                : compiler_step
  | LowerInstruction            : compiler_step
  | MakeRefArguments            : compiler_step
  | StackAllocation             : compiler_step
  | RemoveReturn                : compiler_step
  | RegAllocation               : compiler_step
  | DeadCode_RegAllocation      : compiler_step
  | Linearisation               : compiler_step
  | Tunneling                   : compiler_step
  | Assembly                    : compiler_step.

Record stack_alloc_oracles : Type :=
  {
    ao_globals: seq u8; (* static global data: one array holding all data *)
    ao_global_alloc: seq (var * wsize * Z); (* allocation of global variables in the previous array *)
    ao_stack_alloc: funname → stk_alloc_oracle_t;
  }.

Record compiler_params := {
  rename_fd        : instr_info -> funname -> _ufundef -> _ufundef;
  expand_fd        : funname -> _ufundef -> expand_info;
  var_alloc_fd     : funname -> _ufundef -> _ufundef;
  lowering_vars    : fresh_vars;
  inline_var       : var -> bool;
  is_var_in_memory : var_i → bool;
  global_static_data_symbol: Ident.ident;
  stackalloc       : _uprog → stack_alloc_oracles;
  removereturn     : _sprog -> (funname -> option (seq bool));
  regalloc         : seq _sfun_decl -> seq _sfun_decl;
  extra_free_registers : instr_info → option var;
  print_uprog      : compiler_step -> _uprog -> _uprog;
  print_sprog      : compiler_step -> _sprog -> _sprog;
  print_linear     : lprog -> lprog;
  warning          : instr_info -> warning_msg -> instr_info;
  lowering_opt     : lowering_options;
  is_glob          : var -> bool;
  fresh_id         : glob_decls -> var -> Ident.ident;
  is_reg_ptr       : var -> bool;
  is_ptr           : var -> bool;
  is_reg_array     : var -> bool;
}.

Definition var_alloc_prog cp (p: _uprog) : _uprog :=
  map_prog_name cp.(var_alloc_fd) p.

Variable cparams : compiler_params.

(* Ensure that export functions are preserved *)
Definition check_removeturn (entries: seq funname) (remove_return: funname → option (seq bool)) :=
  assert (pmap remove_return entries == [::]) Ferr_topo. (* FIXME: better error message *)

Definition compiler_first_part (to_keep: seq funname) (p: prog) : result fun_error uprog :=

  let p := add_init_prog cparams.(is_ptr) p in
  let p := cparams.(print_uprog) AddArrInit p in

  Let p := inline_prog_err cparams.(inline_var) cparams.(rename_fd) p in
  let p := cparams.(print_uprog) Inlining p in

  Let p := dead_calls_err_seq to_keep p in
  let p := cparams.(print_uprog) RemoveUnusedFunction p in

  Let p := unroll Loop.nb p in
  let p := cparams.(print_uprog) Unrolling p in

  let p := const_prop_prog p in
  let p := cparams.(print_uprog) Unrolling p in

  let pv := var_alloc_prog cparams p in
  let pv := cparams.(print_uprog) AllocInlineAssgn pv in
  Let _ := CheckAllocRegU.check_prog p.(p_extra) p.(p_funcs) pv.(p_extra) pv.(p_funcs) in
  Let pv := dead_code_prog pv in
  let pv := cparams.(print_uprog) DeadCode_AllocInlineAssgn pv in

  let pr := remove_init_prog cparams.(is_reg_array) pv in
  let pr := cparams.(print_uprog) RemoveArrInit pr in

  Let pe := expand_prog cparams.(expand_fd) pr in
  let pe := cparams.(print_uprog) RegArrayExpansion pe in

  Let pg := remove_glob_prog cparams.(is_glob) cparams.(fresh_id) pe in
  let pg := cparams.(print_uprog) RemoveGlobal pg in

  Let pa := makereference_prog cparams.(is_reg_ptr) cparams.(fresh_id) pg in
  let pa := cparams.(print_uprog) MakeRefArguments pa in

  Let _ := assert (fvars_correct cparams.(lowering_vars) (p_funcs pa)) Ferr_lowering in

  let pl := lower_prog cparams.(lowering_opt) cparams.(warning) cparams.(lowering_vars) cparams.(is_var_in_memory) pa in
  let pl := cparams.(print_uprog) LowerInstruction pl in

  ok pl.

Definition compiler_third_part (entries: seq funname) (ps: sprog) : result fun_error sprog :=

  let rminfo := cparams.(removereturn) ps in
  Let _ := check_removeturn entries rminfo in
  Let pr := dead_code_prog_tokeep rminfo ps in
  let pr := cparams.(print_sprog) RemoveReturn pr in

  let pa := {| p_funcs := cparams.(regalloc) pr.(p_funcs) ; p_globs := pr.(p_globs) ; p_extra := pr.(p_extra) |} in
  let pa : sprog := cparams.(print_sprog) RegAllocation pa in
  Let _ := CheckAllocRegS.check_prog pr.(p_extra) pr.(p_funcs) pa.(p_extra) pa.(p_funcs) in

  Let pd := dead_code_prog pa in
  let pd := cparams.(print_sprog) DeadCode_RegAllocation pd in

  ok pd.

Definition compile_prog (entries subroutines : seq funname) (p: prog) :=

  Let pl := compiler_first_part (entries ++ subroutines) p in

  (* stack + register allocation *)

  let ao := cparams.(stackalloc) pl in
  Let ps :=
     stack_alloc.alloc_prog true
       cparams.(global_static_data_symbol) ao.(ao_globals) ao.(ao_global_alloc)
       ao.(ao_stack_alloc) pl in
  let ps : sprog := cparams.(print_sprog) StackAllocation ps in

  Let pd := compiler_third_part entries ps in

  (* linearisation                     *)
  Let _ := merge_varmaps.check pd cparams.(extra_free_registers) in
  Let pl := linear_prog pd cparams.(extra_free_registers) in
  let pl := cparams.(print_linear) pl in
  (* tunneling                         *)
  Let pl := tunnel_program pl in
  let pl := cparams.(print_linear) pl in
  (* asm                               *)
  ok pl.

Definition check_signature (p: prog) (lp: lprog) (fn: funname) : bool :=
  if get_fundef lp.(lp_funcs) fn is Some fd' then
    if get_fundef (p_funcs p) fn is Some fd then
      signature_of_fundef fd == signature_of_lfundef fd'
    else true
  else true.

Definition compile_prog_to_x86 entries subroutines (p: prog): result fun_error xprog :=
  Let lp := compile_prog entries subroutines p in
(*  Let _ := assert (all (check_signature p lp) entries) Ferr_lowering in *)
  assemble_prog lp.

End COMPILER.

