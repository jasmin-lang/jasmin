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

(* * Properties of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple finfun.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import gen_map word dmasm_utils dmasm_type dmasm_var dmasm_expr memory
               dmasm_sem dmasm_Ssem.

Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Lemma surj_SEstate s : {| semem := semem s; sevm := sevm s |} = s.
Proof. by case: s. Qed.
  
Definition svmap_eq_except (s : Sv.t) (vm1 vm2 : svmap) :=
  forall x, ~Sv.In x s -> vm1.[x]%vmap = vm2.[x]%vmap.

Notation "vm1 = vm2 [\ s ]" := (svmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Lemma vrvP (r:rval) v s s' : swrite_rval s r v = ok s' -> s.(sevm) = s'.(sevm) [\ vrv r].
Proof.
(*
  elim: r v s=> [x | ?? r1 Hr1 r2 Hr2] v s /= z; rewrite ?vrv_var ?vrv_pair=> ?.
  + rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
  rewrite -Hr1 -?Hr2//; SvD.fsetdec.
Qed.
*)
Admitted.

Section SEM.

Variable P: prog.

Lemma writeP c s1 s2 : 
   ssem P s1 c s2 -> s1.(sevm) = s2.(sevm) [\ write_c c].
Proof.
(*
  apply (@cmd_rect
           (fun i => forall s1 s2,
                       ssem_i s1 i s2 -> s1.(sevm) = s2.(sevm) [\ write_i i])
           (fun c => forall s1 s2, 
                       ssem s1 c s2 -> s1.(sevm) = s2.(sevm) [\ write_c c])
           (fun _ _ _ => True)) => /= {c s1 s2}
    [ |i c1 Hi Hc1|bc|e c1 c2 Hc1 Hc2|x rn c Hc|e c Hc|?? x f a _|//] s1 s2 Hsem;
    inversion Hsem=>{Hsem};subst=> // z.
  + rewrite write_c_cons => Hz;rewrite (Hi _ _ H2) ?(Hc1 _ _ H4) //; SvD.fsetdec. 
  + rewrite write_i_bcmd;case: bc H1 => //= [? r p | r p | ??].
    + by move=> [] <- /=;apply vrvP.
    + by case read_mem => //= w [] <-;apply vrvP.
    by case write_mem => //= ? [] <-.
  + by rewrite write_i_if=> ?;apply Hc1=> //; SvD.fsetdec. 
  + by rewrite write_i_if=> ?;apply Hc2=> //; SvD.fsetdec. 
  + rewrite write_i_for.
    elim: H4 Hc => {w1 w2 e1 e2 dir s1 s2 c} //.
    move=> v w ws c s1 s2 s3 sc _ ih h hc.
    have/ih := hc => -/(_ h) <-; rewrite -(h _ _ sc); last by SvD.fsetdec.
    by rewrite -vrvP //; SvD.fsetdec.
  + rewrite write_i_while.
    elim: H3 Hc => {s1 s2 e c} //.
    move=> s1 s2 s3 e c ? sc ? ih h hc.
    by have/ih := hc => -/(_ h) <-; rewrite -(h _ _ sc); SvD.fsetdec.
  by rewrite write_i_call=> Hin; move: H3 H4=> [] ?;subst=> -[] [] ?;subst;apply vrvP.  
Qed.
*)
Admitted.

(* -------------------------------------------------------------------------- *)
(* Properties on swrite_rval                                                  *)
(* -------------------------------------------------------------------------- *)

(*
Lemma swrite_nin t (rv:rval) (v:svalue) z s:
  ~Sv.In z (vrv rv) ->
  ((swrite_rval s rv v).[z])%vmap = s.[z]%vmap.
Proof.
  elim: rv v s => /= [x | ??? Hr1 ? Hr2] v s;rewrite ?vrv_var ?vrv_pair => Hin.
  + by rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
  rewrite Hr1 ?Hr2 //;SvD.fsetdec.
Qed.

Lemma ssem_swrite_rval s (r:rval sword) w: 
  ssem_rval (swrite_rval s r w) r = w.
Proof. by case H : sword / r w => //= ?;rewrite Fv.setP_eq. Qed.

Lemma swrite_ssem_rval s (r:rval sword): swrite_rval s r (ssem_rval s r) = s.
Proof.
  apply Fv.map_ext=> x1;case H : sword / (r) => [ x2 | ] //=. 
  case: (x2 =P x1) => [ -> | /eqP ? ];first by rewrite Fv.setP_eq. 
  by rewrite Fv.setP_neq.   
Qed.

Lemma ssem_rval2pe t (i:rval t) s: ssem_pexpr s (rval2pe i) = ssem_rval s i.
Proof. by elim: i => //= ??? -> ? ->. Qed.

(* -------------------------------------------------------------------------- *)
(* Properties on donotdep                                                     *)
(* -------------------------------------------------------------------------- *)

Definition donotdep  (s : Sv.t) t (e:pexpr t) := 
  forall s1 s2, s1 = s2 [\ s] -> ssem_pexpr s1 e = ssem_pexpr s2 e.
*)

End SEM.
