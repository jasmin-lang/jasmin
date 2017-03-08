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
Require Import ZArith.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr 
               memory dmasm_sem compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap_scope.
Local Open Scope seq_scope.

(* ** unrolling
 * -------------------------------------------------------------------- *)

Definition unroll_cmd (unroll_i: instr -> cmd) (c:cmd) : cmd := 
  List.fold_right (fun i c' => unroll_i i ++ c') [::] c.

Definition assgn ii x e := MkI ii (Cassgn (Rvar x) AT_inline e).

Fixpoint unroll_i (i:instr) : cmd := 
  let (ii, ir) := i in
  match ir with
  | Cassgn _ _ _ => [:: i ]
  | Copn   _ _ _ => [:: i ]
  | Cif b c1 c2  => [:: MkI ii (Cif b (unroll_cmd unroll_i c1) (unroll_cmd unroll_i c2)) ]
  | Cfor i (dir, low, hi) c => 
    let c' := unroll_cmd unroll_i c in
    match is_const low, is_const hi with
    | Some vlo, Some vhi =>
      let l := wrange dir vlo vhi in
      let cs := map (fun n => assgn ii i (Pconst n) :: c') l in
      flatten cs 
    | _, _       => [:: MkI ii (Cfor i (dir, low, hi) c') ]
    end     
  | Cwhile e c   => [:: MkI ii (Cwhile e (unroll_cmd unroll_i c)) ]
  | Ccall _ _ _ _  => [:: i ]
  end.

Definition unroll_fun (f:fundef) :=
  let (ii,p,c,r) := f in
  MkFun ii p (unroll_cmd unroll_i c) r.

Definition unroll_prog (p:prog) := map_prog unroll_fun p.

(* ** proofs
 * -------------------------------------------------------------------- *)

Section PROOF.

  Variable p : prog.

  Definition p' := unroll_prog p.

  Let Pi_r (s:estate) (i:instr_r) (s':estate) :=
    forall ii, sem p' s (unroll_i (MkI ii i)) s'.

  Let Pi (s:estate) (i:instr) (s':estate) :=
    sem p' s (unroll_i i) s'.

  Let Pc (s:estate) (c:cmd) (s':estate) :=
    sem p' s (unroll_cmd unroll_i c) s'.

  Let Pfor (i:var_i) vs s c s' :=
    sem_for p' i vs s (unroll_cmd unroll_i c) s'
    /\ forall ii, sem p' s
      (flatten (map (fun n => assgn ii i (Pconst n) :: (unroll_cmd unroll_i c)) vs)) s'.

  Let Pfun m1 fn vargs m2 vres :=
    sem_call p' m1 fn vargs m2 vres.

  Local Lemma Hskip s : Pc s [::] s.
  Proof. exact: Eskip. Qed.

  Local Lemma Hcons s1 s2 s3 i c :
    sem_I p s1 i s2 ->
    Pi s1 i s2 -> sem p s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
  Proof.
    move=> Hsi Hi Hsc Hc.
    exact: (sem_app Hi Hc).
  Qed.

  Local Lemma HmkI ii i s1 s2 :
    sem_i p s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
  Proof. move=> _ Hi; exact: Hi. Qed.

  Local Lemma Hassgn s1 s2 x tag e :
    Let v := sem_pexpr s1 e in write_rval x v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn x tag e) s2.
  Proof.
    move=> Hw ii.
    by apply: sem_seq1; apply: EmkI; apply: Eassgn.
  Qed.

  Local Lemma Hopn s1 s2 o xs es :
    Let x := Let x := sem_pexprs s1 es in sem_sopn o x
    in write_rvals s1 xs x = Ok error s2 -> Pi_r s1 (Copn xs o es) s2.
  Proof.
    move=> Hw ii.
    by apply: sem_seq1; apply: EmkI; apply: Eopn.
  Qed.

  Local Lemma Hif_true s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem p s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move=> Hb Hsc Hc ii.
    by apply: sem_seq1; apply: EmkI; apply: Eif_true.
  Qed.

  Local Lemma Hif_false s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error false ->
    sem p s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move=> Hb Hsc Hc ii.
    by apply: sem_seq1; apply: EmkI; apply: Eif_false.
  Qed.

  Local Lemma Hwhile_true s1 s2 s3 e c :
    Let x := sem_pexpr s1 e in to_bool x = ok true ->
    sem p s1 c s2 -> Pc s1 c s2 ->
    sem_i p s2 (Cwhile e c) s3 -> Pi_r s2 (Cwhile e c) s3 -> Pi_r s1 (Cwhile e c) s3.
  Proof.
    move=> Hb Hsc Hc Hsi Hi ii.
    apply: sem_seq1; apply: EmkI; apply: Ewhile_true=> //.
    apply: Hc.
    move: Hi=> /(_ ii) Hi.
    sinversion Hi.
    sinversion H2.
    sinversion H4.
    apply: H5.
  Qed.

  Local Lemma Hwhile_false s e c :
    Let x := sem_pexpr s e in to_bool x = ok false ->
    Pi_r s (Cwhile e c) s.
  Proof.
   move=> Hb ii.
   by apply: sem_seq1; apply: EmkI; apply: Ewhile_false.
  Qed.

  Local Lemma Hfor s1 s2 (i:var_i) d lo hi c vlo vhi :
    Let x := sem_pexpr s1 lo in to_int x = Ok error vlo ->
    Let x := sem_pexpr s1 hi in to_int x = Ok error vhi ->
    sem_for p i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.
  Proof.
    move=> Hlo Hhi Hc [Hfor Hfor'] ii.
    rewrite /=.
    case Hlo': (is_const lo)=> [nlo|].
    + case Hhi': (is_const hi)=> [nhi|].
      + have ->: nlo = vlo.
          rewrite /is_const /= in Hlo'.
          by case: lo Hlo Hlo'=> //= z [] -> [] ->.
        have ->: nhi = vhi.
          rewrite /is_const /= in Hhi'.
          by case: hi Hhi Hhi'=> //= z [] -> [] ->.
        exact: Hfor'.
      apply: sem_seq1; apply: EmkI; apply: Efor; [apply: Hlo|apply: Hhi|apply: Hfor].
    apply: sem_seq1; apply: EmkI; apply: Efor; [apply: Hlo|apply: Hhi|apply: Hfor].
  Qed.

  Local Lemma Hfor_nil s i c: Pfor i [::] s c s.
  Proof.
    split=> //=.
    exact: EForDone.
    move=> ii.
    apply: Eskip.
  Qed.

  Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w:Z) (ws:seq Z) c :
    write_var i w s1 = Ok error s1' ->
    sem p s1' c s2 ->
    Pc s1' c s2 ->
    sem_for p i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
  Proof.
    move=> Hw Hsc Hc Hsfor [Hfor Hfor']; split=> [|ii].
    apply: EForOne; [exact: Hw|exact: Hc|exact: Hfor].
    move: Hfor'=> /(_ ii) Hfor'.
    apply: Eseq; [apply: EmkI; apply: Eassgn; exact: Hw|apply: sem_app].
    exact: Hc.
    exact: Hfor'.
  Qed.

  Local Lemma Hcall s1 m2 s2 ii xs fn args vargs vs:
    sem_pexprs s1 args = Ok error vargs ->
    sem_call p (emem s1) fn vargs m2 vs ->
    Pfun (emem s1) fn vargs m2 vs ->
    write_rvals {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
    Pi_r s1 (Ccall ii xs fn args) s2.
  Proof.
    move=> Hexpr Hcall Hfun Hw ii'.
    apply: sem_seq1; apply: EmkI; apply: Ecall; [exact: Hexpr|exact: Hfun|exact: Hw].
  Qed.

  Local Lemma Hproc m1 m2 fn f vargs s1 vm2 vres:
    get_fundef p fn = Some f ->
    write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
    sem p s1 (f_body f) {| emem := m2; evm := vm2 |} ->
    Pc s1 (f_body f) {| emem := m2; evm := vm2 |} ->
    mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
    List.Forall is_full_array vres ->
    Pfun m1 fn vargs m2 vres.
  Proof.
    case: f=> fi fparams fc fres /= Hget Hw _ Hc Hres Hfull.
    have := (@get_map_prog unroll_fun p fn); rewrite Hget /= => Hget'.
    apply: EcallRun=> //.
    exact: Hget'.
    exact: Hw.
    exact: Hc.
    exact: Hres.
  Qed.

  Lemma const_prop_callP f mem mem' va vr:
    sem_call p mem f va mem' vr ->
    sem_call p' mem f va mem' vr.
  Proof.
    apply (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End PROOF.
