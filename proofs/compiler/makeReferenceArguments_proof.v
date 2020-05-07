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

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem compiler_util.
Require Export makeReferenceArguments.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Section Section.

  Context (is_reg_ptr : var -> bool) (fresh_id : glob_decls -> var -> Ident.ident).
  Context (p p' : uprog).
  Context (ev : unit).

 (* Hypothesis uniq_funname : uniq [seq x.1 | x <- p_funcs p]. *)

  Hypothesis Hp : makereference_prog is_reg_ptr fresh_id p = ok p'.

  (*Should be shown by assuming other hypotheses or admitted?*)
  Lemma eq_globs : p_globs p = p_globs p'.
  Proof.
   case : p Hp => /= p_funcs p_globs extra.
   rewrite /makereference_prog.
   (*But Let x in ...*)
   t_xrbindP => /=.
   by move => y _ <-.
  Qed.

  Definition get_sig n :=
   if get_fundef p.(p_funcs) n is Some fd then
     (fd.(f_params), fd.(f_res))
   else ([::], [::]).

  Let Pi s1 (i:instr) s2:=
    forall (X:Sv.t) c', update_i is_reg_ptr fresh_id p get_sig X i = ok c' ->
       (* subset (read U write i) X  -> *)
     forall vm1, evm s1 =[X] vm1 ->
     exists vm2, [/\ evm s2 =[X] vm2 &
        sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pi_r s1 (i:instr_r) s2 :=
    forall ii, Pi s1 (MkI ii i) s2.

  Let Pc s1 (c:cmd) s2:=
    forall (X:Sv.t) c', update_c (update_i is_reg_ptr fresh_id p get_sig X) c = ok c' ->
       (* subset (read U write i) X  -> *)
     forall vm1, evm s1 =[X] vm1 ->
     exists vm2, [/\ evm s2 =[X] vm2 &
        sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2)].

  (*I should have something more specific than s1 and s2*)
  (*
  Lemma mkrefargs_c_incl s1 c s2 : Pc s1 c s2.
  Proof.
    move => X c' up vm1 eq.
    
  Qed.
  *)
