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
Require Import compiler_util allocation inline unrolling
   constant_prop dead_code array_expansion stack_alloc linear.

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

Record compiler_params := {
  rename_fd    : funname -> fundef -> fundef;
  expand_fd    : funname -> fundef -> fundef;
  var_alloc_fd : funname -> fundef -> fundef;
  reg_alloc_fd : funname -> fundef -> fundef;
  stk_alloc_fd : funname -> fundef -> seq (var * Z) * sfundef;
  print_prog   : string -> prog -> prog;
}.

Variable cparams : compiler_params.

Definition expand_prog (p:prog) := 
  List.map (fun f => (f.1, cparams.(expand_fd) f.1 f.2)) p.

Definition var_alloc_prog (p:prog) := 
  List.map (fun f => (f.1, cparams.(var_alloc_fd) f.1 f.2)) p.

Definition reg_alloc_prog (p:prog) := 
  List.map (fun f => (f.1, cparams.(reg_alloc_fd) f.1 f.2)) p.

Definition stk_alloc_prog (p:prog) : sprog * (seq (seq (var * Z))) :=
  List.split 
    (List.map (fun f => let (x, y) := cparams.(stk_alloc_fd) f.1 f.2 in ((f.1, y), x)) p).

Definition compile_prog (p:prog) := 
  Let p := inline_prog cparams.(rename_fd) p in
  let p := cparams.(print_prog) "inlining" p in      
  (* FIXME: we should remove unused fonctions after inlining *)      
  Let p := unroll Loop.nb p in
  let p := cparams.(print_prog) "unrolling" p in      
  (* FIXME we should perform a step of register allocation to 
     remove assignment of the form x = y introduced by inlining.
     This is particulary true we x and y are Reg array.
     Then we should use dead_code to clean nop assignment.
     If we still have x = y where x and y are Reg array, 
     we should fail or replace it by a sequence of assgnment.
  *)     
  let pv := var_alloc_prog p in
  let pv := cparams.(print_prog) "variable allocation" pv in
  Let _ := CheckAllocReg.check_prog p pv in

  Let pv := dead_code_prog pv in                
  let pv := cparams.(print_prog) "dead_code variable allocation" pv in
 
  let pe := expand_prog pv in
  let pe := cparams.(print_prog) "array expansion" pe in 
  Let _ := CheckExpansion.check_prog pv pe in
  let pa := reg_alloc_prog pe in
  let pa := cparams.(print_prog) "register allocation" pa in 
  Let _ := CheckAllocReg.check_prog pe pa in
  (* dead_code to clean nop assignment *)   
  Let pd := dead_code_prog pa in
  let pd := cparams.(print_prog) "dead_code" pd in 
  (* stack_allocation                  *)
  let (ps, l) := stk_alloc_prog pd in
  if stack_alloc.check_prog pd ps l then
    (* linearisation                     *)
    Let pl := linear_prog ps in
    (* asm                               *)
    cfok pl
  else cferror Ferr_neqprog.

Definition compile_prog_to_x86 (p: prog) : result fun_error xprog :=
  Let lp := compile_prog p in
  assemble_prog lp. 

End COMPILER.
