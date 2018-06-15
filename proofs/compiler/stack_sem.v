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
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word utils type var expr low_memory psem stack_alloc.

Import compiler_util.
Import ZArith.
Import Psatz.
Import Memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Module S.
  Notation vstk nstk := {|v_var := {|vtype := sword U64; vname := nstk|}; v_info := xH|}.

  Section SEM.

  Variable P:sprog.
  Context (gd: glob_decls).

  Inductive sem : estate -> cmd -> estate -> Prop :=
  | Eskip s : sem s [::] s

  | Eseq s1 s2 s3 i c :
    sem_I s1 i s2 -> sem s2 c s3 -> sem s1 (i::c) s3

  with sem_I : estate -> instr -> estate -> Prop :=
  | EmkI ii i s1 s2: 
    sem_i s1 i s2 ->
    sem_I s1 (MkI ii i) s2

  with sem_i : estate -> instr_r -> estate -> Prop :=
  | Eassgn s1 s2 (x:lval) tag ty e v v' :
    sem_pexpr gd s1 e = ok v ->
    truncate_val ty v = ok v' ->
    write_lval gd x v' s1 = ok s2 ->
    sem_i s1 (Cassgn x tag ty e) s2

  | Eopn s1 s2 t o xs es:
    sem_sopn gd o s1 xs es = ok s2 ->
    sem_i s1 (Copn xs t o es) s2

  | Eif_true s1 s2 e c1 c2 :
    sem_pexpr gd s1 e = ok (Vbool true) ->
    sem s1 c1 s2 ->
    sem_i s1 (Cif e c1 c2) s2

  | Eif_false s1 s2 e c1 c2 :
    sem_pexpr gd s1 e = ok (Vbool false) ->
    sem s1 c2 s2 ->
    sem_i s1 (Cif e c1 c2) s2

  | Ewhile_true s1 s2 s3 s4 c e c' :
    sem s1 c s2 ->
    sem_pexpr gd s2 e = ok (Vbool true) ->
    sem s2 c' s3 ->
    sem_i s3 (Cwhile c e c') s4 ->
    sem_i s1 (Cwhile c e c') s4

  | Ewhile_false s1 s2 c e c' :
    sem s1 c s2 ->
    sem_pexpr gd s2 e = ok (Vbool false) ->
    sem_i s1 (Cwhile c e c') s2

  | Ecall s1 m2 s2 ii xs f args vargs vs :
    sem_pexprs gd s1 args = ok vargs ->
    sem_call s1.(emem) f vargs m2 vs ->
    write_lvals gd {|emem:= m2; evm := s1.(evm) |} xs vs = ok s2 ->
    sem_i s1 (Ccall ii xs f args) s2

  with sem_call : mem -> funname -> seq value -> mem -> seq value -> Prop :=
  | EcallRun m1 m2 fn sf vargs vargs' s1 s2 m2' vm2 vres vres' m1':
    get_fundef P fn = Some sf ->
    alloc_stack m1 (sf_stk_sz sf) = ok m1' ->
    write_var  (vstk (sf_stk_id sf)) (Vword (top_stack m1')) (Estate m1' vmap0) = ok s1 ->
    mapM2 ErrType truncate_val sf.(sf_tyin) vargs' = ok vargs ->
    write_vars (sf_params sf) vargs s1 = ok s2 ->
    sem s2 (sf_body sf) {| emem := m2'; evm := vm2 |} ->
    mapM (fun (x:var_i) => get_var vm2 x) sf.(sf_res) = ok vres ->
    mapM2 ErrType truncate_val sf.(sf_tyout) vres = ok vres' ->
    m2 = free_stack m2' (sf_stk_sz sf) ->
    sem_call m1 fn vargs' m2 vres'.

  End SEM.

  Lemma semE p gd s1 c s2 :
    sem p gd s1 c s2 ->
    match c with
    | [::] => s2 = s1
    | i :: c' => exists si, sem_I p gd s1 i si /\ sem p gd si c' s2
    end.
  Proof. case; eauto. Qed.

  Lemma sem_IE p gd s1 i s2 :
    sem_I p gd s1 i s2 ->
    let 'MkI _ r := i in
    sem_i p gd s1 r s2.
  Proof. by case. Qed.

  Lemma sem_iE p gd s1 i s2 :
    sem_i p gd s1 i s2 ->
    match i with
    | Cassgn x _ ty e =>
      exists v v',
      [/\ sem_pexpr gd s1 e = ok v,
       truncate_val ty v = ok v' &
       write_lval gd x v' s1 = ok s2]
    | Copn xs _ op es => sem_sopn gd op s1 xs es = ok s2
    | Cif e c1 c2 =>
      exists b,
      sem_pexpr gd s1 e = ok (Vbool b) /\
      sem p gd s1 (if b then c1 else c2) s2
    | Cfor _ _ _ => False
    | Cwhile c1 e c2 =>
      exists si b,
      sem p gd s1 c1 si /\
      sem_pexpr gd si e = ok (Vbool b) /\
      if b then (exists sj, sem p gd si c2 sj /\ sem_i p gd sj (Cwhile c1 e c2) s2) else si = s2
    | Ccall _ xs fn es =>
      exists vs m2 rs,
      [/\ sem_pexprs gd s1 es = ok vs,
          sem_call p gd (emem s1) fn vs m2 rs &
          write_lvals gd {| emem := m2 ; evm := evm s1 |} xs rs = ok s2 ]
    end.
  Proof.
    case => // {s1 s2 i} s1 s2.
    - by move => x _ ty e v v' ? ? ?; exists v, v'.
    - by move => e c1 c2 ? ?; exists true.
    - by move => e c1 c2 ? ?; exists false.
    - by move => s3 s4 c1 e c2 ? ? ? ?; exists s2, true; eauto.
    - by move => c1 e c2 ? ?; exists s2, false; eauto.
    by move => s _ xs fn es vs rs ? ? ?; exists vs, s2, rs.
  Qed.

End S.
