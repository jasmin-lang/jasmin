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

From mathcomp Require Import all_ssreflect.
Require Import x86 expr.
Import ZArith.
Require Import low_memory compiler_util allocation inline dead_calls unrolling
   constant_prop dead_code array_expansion lowering stack_alloc linear.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition unroll1 (p:prog) :=
  let p := unroll_prog p in
  let p := const_prop_prog p in
  dead_code_prog p.

Fixpoint unroll (n:nat) (p:prog) :=
  match n with
  | O   => cferror Ferr_loop
  | S n =>
    Let p' := unroll1 p in
    if p == p' then cfok p
    else unroll n p'
  end.

Definition unroll_loop (p:prog) := unroll Loop.nb p.

Section COMPILER.

Variant compiler_step :=
  | Typing                      : compiler_step
  | ParamsExpansion             : compiler_step
  | Inlining                    : compiler_step
  | RemoveUnusedFunction        : compiler_step
  | Unrolling                   : compiler_step
  | AllocInlineAssgn            : compiler_step
  | DeadCode_AllocInlineAssgn   : compiler_step
  | ShareStackVariable          : compiler_step
  | DeadCode_ShareStackVariable : compiler_step
  | RegArrayExpansion           : compiler_step
  | LowerInstruction            : compiler_step
  | RegAllocation               : compiler_step
  | DeadCode_RegAllocation      : compiler_step
  | StackAllocation             : compiler_step
  | Linearisation               : compiler_step
  | Assembly                    : compiler_step.

Record compiler_params := {
  rename_fd    : funname -> fundef -> fundef;
  expand_fd    : funname -> fundef -> fundef;
  var_alloc_fd : funname -> fundef -> fundef;
  share_stk_fd : funname -> fundef -> fundef;
  lowering_vars : fresh_vars;
  reg_alloc_fd : funname -> fundef -> fundef;
  stk_alloc_fd : funname -> fundef -> seq (var * Z) * sfundef;
  print_prog   : compiler_step -> prog -> prog;
}.

Variable cparams : compiler_params.

Definition expand_prog (p:prog) :=
  List.map (fun f => (f.1, cparams.(expand_fd) f.1 f.2)) p.

Definition var_alloc_prog (p:prog) :=
  List.map (fun f => (f.1, cparams.(var_alloc_fd) f.1 f.2)) p.

Definition share_stack_prog (p:prog) :=
  List.map (fun f => (f.1, cparams.(share_stk_fd) f.1 f.2)) p.

Definition reg_alloc_prog (p:prog) :=
  List.map (fun f => (f.1, cparams.(reg_alloc_fd) f.1 f.2)) p.

Definition stk_alloc_prog (p:prog) : sprog * (seq (seq (var * Z))) :=
  List.split
    (List.map (fun f => let (x, y) := cparams.(stk_alloc_fd) f.1 f.2 in ((f.1, y), x)) p).

Definition compile_prog (entries : seq funname) (p:prog) :=
  Let p := inline_prog_err cparams.(rename_fd) p in
  let p := cparams.(print_prog) Inlining p in

  Let p := dead_calls_err entries p in
  let p := cparams.(print_prog) RemoveUnusedFunction p in

  Let p := unroll Loop.nb p in
  let p := cparams.(print_prog) Unrolling p in

  let pv := var_alloc_prog p in
  let pv := cparams.(print_prog) AllocInlineAssgn pv in
  Let _ := CheckAllocReg.check_prog p pv in
  Let pv := dead_code_prog pv in
  let pv := cparams.(print_prog) DeadCode_AllocInlineAssgn pv in

  let ps := share_stack_prog pv in
  let ps := cparams.(print_prog) ShareStackVariable ps in
  Let _ := CheckAllocReg.check_prog pv ps in
  Let ps := dead_code_prog ps in
  let ps := cparams.(print_prog) DeadCode_ShareStackVariable ps in

  let pe := expand_prog ps in
  let pe := cparams.(print_prog) RegArrayExpansion pe in
  Let _ := CheckExpansion.check_prog ps pe in

  let pl := lower_prog cparams.(lowering_vars) pe in
  let pl := cparams.(print_prog) LowerInstruction pl in

  let pa := reg_alloc_prog pl in
  let pa := cparams.(print_prog) RegAllocation pa in
  Let _ := CheckAllocReg.check_prog pl pa in
  Let pd := dead_code_prog pa in
  let pd := cparams.(print_prog) DeadCode_RegAllocation pd in

  (* stack_allocation                    *)
  let (ps, l) := stk_alloc_prog pd in
  if stack_alloc.check_prog pd ps l then
    (* linearisation                     *)
    Let pl := linear_prog ps in
    (* asm                               *)
    cfok pl
  else cferror Ferr_neqprog.

Definition compile_prog_to_x86 entries (p: prog): result fun_error xprog :=
  Let lp := compile_prog entries p in
  assemble_prog lp.

End COMPILER.
