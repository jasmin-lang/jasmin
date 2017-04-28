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

(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word utils type var expr memory sem stack_alloc.

Require Import compiler_util.
Require Import ZArith.
Require Import Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Module S.
  Notation vstk nstk := {|v_var := {|vtype := sword; vname := nstk|}; v_info := xH|}.

  Section SEM.

  Variable P:sprog.

  Import Memory.

  Inductive sem : estate -> cmd -> estate -> Prop :=
  | Eskip s : sem s [::] s

  | Eseq s1 s2 s3 i c :
    sem_I s1 i s2 -> sem s2 c s3 -> sem s1 (i::c) s3

  with sem_I : estate -> instr -> estate -> Prop :=
  | EmkI ii i s1 s2: 
    sem_i s1 i s2 ->
    sem_I s1 (MkI ii i) s2

  with sem_i : estate -> instr_r -> estate -> Prop :=
  | Eassgn s1 s2 (x:lval) tag e:
    (Let v := sem_pexpr s1 e in write_lval x v s1) = ok s2 ->
    sem_i s1 (Cassgn x tag e) s2

  | Eopn s1 s2 o xs es:
    sem_pexprs s1 es >>= sem_sopn o >>= (write_lvals s1 xs) = ok s2 ->
    sem_i s1 (Copn xs o es) s2

  | Eif_true s1 s2 e c1 c2 :
    sem_pexpr s1 e >>= to_bool = ok true ->
    sem s1 c1 s2 ->
    sem_i s1 (Cif e c1 c2) s2

  | Eif_false s1 s2 e c1 c2 :
    sem_pexpr s1 e >>= to_bool = ok false ->
    sem s1 c2 s2 ->
    sem_i s1 (Cif e c1 c2) s2

  | Ewhile_true s1 s2 s3 s4 c e c' :
    sem s1 c s2 ->
    sem_pexpr s2 e >>= to_bool = ok true ->
    sem s2 c' s3 ->
    sem_i s3 (Cwhile c e c') s4 ->
    sem_i s1 (Cwhile c e c') s4

  | Ewhile_false s1 s2 c e c' :
    sem s1 c s2 ->
    sem_pexpr s2 e >>= to_bool = ok false ->
    sem_i s1 (Cwhile c e c') s2

  | Ecall s1 m2 s2 ii xs f args vargs vs :
    sem_pexprs s1 args = ok vargs ->
    sem_call s1.(emem) f vargs m2 vs ->
    write_lvals {|emem:= m2; evm := s1.(evm) |} xs vs = ok s2 ->
    sem_i s1 (Ccall ii xs f args) s2

  with sem_call : mem -> funname -> seq value -> mem -> seq value -> Prop :=
  | EcallRun m1 m2 fn sf vargs s1 s2 m2' vm2 vres p:
    get_fundef P fn = Some sf ->
    alloc_stack m1 (sf_stk_sz sf) = ok p ->
    write_var  (vstk (sf_stk_id sf)) p.1 (Estate p.2 vmap0) = ok s1 ->
    write_vars (sf_params sf) vargs s1 = ok s2 ->
    sem s2 (sf_body sf) {| emem := m2'; evm := vm2 |} ->
    mapM (fun (x:var_i) => get_var vm2 x) sf.(sf_res) = ok vres ->
    m2 = free_stack m2' p.1 (sf_stk_sz sf) ->
    List.Forall is_full_array vres ->
    sem_call m1 fn vargs m2 vres.

  End SEM.
End S.

