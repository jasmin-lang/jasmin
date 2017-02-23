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

(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.

Require Import strings word dmasm_utils.
Require Import dmasm_type dmasm_var dmasm_expr.
Require Import memory dmasm_sem dmasm_Ssem dmasm_Ssem_props.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Axiom fe : forall {T U} (f g : T -> U), (forall x, f x = g x) -> f = g.

(* -------------------------------------------------------------------- *)
Fixpoint st2sst_ty {t : stype} :=
  match t return sem_t t -> ssem_t t with
  | sword     => fun v => v
  | sint      => fun v => v
  | sbool     => fun v => v
  | sarr n    => fun v => 
       (fun i : word => 
          match @Array.get _ n v i return word with
          | Ok w => w
          | _      => n2w 0
          end)
  end.

(* -------------------------------------------------------------------- *)
Definition vmap_to_svmap (v : vmap) : svmap :=
  {| Fv.map := fun x : var => st2sst_ty (v.(Fv.map) x); |}.

(* -------------------------------------------------------------------- *)
Coercion estate_to_sestate (s : estate) :=
  {| semem := s.(emem); sevm := vmap_to_svmap s.(evm); |}.

Definition value_to_svalue (v: value) : svalue :=
  match v with
  | Vbool b => SVbool b
  | Vint i => SVint i
  | Vword w => SVword w
  | Varr n t => SVarr n (@st2sst_ty (sarr n) t)
  end.

(* -------------------------------------------------------------------- *)
Hint Constructors ssem ssem_i : ssem.

(* -------------------------------------------------------------------- *)
Lemma bindW {T U} (v : exec T) (f : T -> exec U) r :
  v >>= f = ok r -> exists2 a, v = ok a & f a = ok r.
Proof. by case E: v => [a|//] /= <-; exists a. Qed.

Lemma st2sst_toval {t} x:
  to_sval (@st2sst_ty t x) = value_to_svalue (to_val x).
Proof. by case: t x. Qed.

Lemma st2sst_getvar s x :
  sget_var (vmap_to_svmap (evm s)) x = value_to_svalue (get_var (evm s) x).
Proof.
by rewrite /sget_var /get_var st2sst_toval.
Qed.

(* TODO: can these 3 lemmas be put together? *)
Lemma st2sst_op2_b f v1 v2 v: sem_op2_b f v1 v2 = ok v ->
  ssem_op2_b f (value_to_svalue v1) (value_to_svalue v2) = value_to_svalue v.
Proof.
rewrite /sem_op2_b /mk_sem_sop2=> h.
case: (bindW h)=> b1 /= {h}.
case: v1=> // b' [<-] h.
case: (bindW h)=> b2 /= {h}.
by case: v2=> // b'' [<-] [<-].
Qed.

Lemma st2sst_op2_i f v1 v2 v: sem_op2_i f v1 v2 = ok v ->
  ssem_op2_i f (value_to_svalue v1) (value_to_svalue v2) = value_to_svalue v.
Proof.
rewrite /sem_op2_i /mk_sem_sop2=> h.
case: (bindW h)=> b1 /= {h}.
case: v1=> // b' [<-] h.
case: (bindW h)=> b2 /= {h}.
by case: v2=> // b'' [<-] [<-].
Qed.

Lemma st2sst_op2_ib f v1 v2 v: sem_op2_ib f v1 v2 = ok v ->
  ssem_op2_ib f (value_to_svalue v1) (value_to_svalue v2) = value_to_svalue v.
Proof.
rewrite /sem_op2_ib /mk_sem_sop2=> h.
case: (bindW h)=> b1 /= {h}.
case: v1=> // b' [<-] h.
case: (bindW h)=> b2 /= {h}.
by case: v2=> // b'' [<-] [<-].
Qed.

Lemma st2sst_op2 s v v1 v2: sem_sop2 s v1 v2 = ok v ->
  ssem_sop2 s (value_to_svalue v1) (value_to_svalue v2) = value_to_svalue v.
Proof.
  case: s=> /=;
  try exact: st2sst_op2_b;
  try exact: st2sst_op2_i;
  try exact: st2sst_op2_ib.
Qed.

(* -------------------------------------------------------------------- *)
Lemma st2sst_pexpr s (p : pexpr) v : sem_pexpr s p = ok v ->
  ssem_pexpr (estate_to_sestate s) p = value_to_svalue v.
Proof.
elim: p v=> //=.
+ by move=> x v [<-].
+ by move=> x v [<-].
+ move=> p Hv v h.
  case: (bindW h)=> z h' [<-].
  case: (bindW h')=> x /Hv ->.
  case: x=> // z0 /= [<-] //.
+ by move=> x v [<-]; rewrite st2sst_getvar.
+ move=> v p Hv v0.
  admit.
+ move=> ? p Hv v h.
  case: (bindW h)=> w {h}h [<-].
  case: (bindW h)=> x {h}h.
  case: (bindW h)=> y /Hv ->.
  case: y=> // w0 [<-].
  by rewrite /= /sread_mem => ->.
+ move=> p Hv v h.
  case: (bindW h)=> b {h}h [<-].
  case: (bindW h)=> x /Hv ->.
  by case: x=> // x0 [<-].
+ move=> s0 p Hv1 p0 Hv2 v h.
  case: (bindW h)=> v1 /Hv1 -> {h}h.
  case: (bindW h)=> v2 /Hv2 -> {h}.
  exact: st2sst_op2.
Admitted.

(* -------------------------------------------------------------------- *)
Lemma st2sst_vmap_get (s : vmap) (x : var) :
  (vmap_to_svmap s).[x]%vmap = st2sst_ty s.[x]%vmap.
Proof. by []. Qed.

Lemma st2sst_vmap_set (s : vmap) (x : var) v :
  (vmap_to_svmap s).[x <- st2sst_ty v]%vmap = vmap_to_svmap s.[x <- v]%vmap.
Proof.
apply/Fv.map_ext=> y; rewrite /Fv.get /Fv.set /=.
by case: eqP=> // eq; case: y / eq.
Qed.

(* -------------------------------------------------------------------- *)
(*
Lemma st2sst_write {t} s (x : rval) v :
    vmap_to_svmap (write_rval s x v)
  = swrite_rval (vmap_to_svmap s) x (st2sst_ty v).
Proof.
elim: x s v => /= [x|st1 st2 r1 ih1 r2 ih2] s v; last first.
  by rewrite !(ih1, ih2).
by apply/Fv.map_ext=> y /=; rewrite st2sst_vmap_set.
Qed.
*)

(* -------------------------------------------------------------------- *)
Section SEM.

(* -------------------------------------------------------------------- *)
Lemma st2sst_cmd : forall p s1 c s2, sem p s1 c s2 -> ssem p s1 c s2.
Proof.
(*
pose Pi s1 i s2 := ssem_i s1 i s2.
pose Pf rv d lo hi s1 c s2 := ssem_for rv d lo hi s1 c s2.
pose Pc sta str m1 (fd : fundef sta str) ag m2 res :=
  ssem_fun fd m1 (st2sst_ty ag) m2 (st2sst_ty res).
apply: (@sem_Ind _ Pi Pf Pc); rewrite {}/Pi {}/Pf {}/Pc;
  try by (move=> *; eauto with ssem).
+ by move=> s1 s2 c /st2sst_bcmd h; constructor.
+ move=> s1 s2 pe cd c1 c2 h _; case: (boolP cd) h => cdP h ih.
  * by apply/SEifTrue => //; apply/(@st2sst_pexpr sbool).
  * by apply/SEifFalse=> //; apply/negbT/(@st2sst_pexpr sbool).
+ move=> sta srt m1 vm1 m2 rvr fd a r.
  case E: (sem_pexpr _ _) => /= [va|//] _ _ ih /=.
  rewrite {2}/estate_to_sestate st2sst_write.
  by constructor=> /=; move/st2sst_pexpr: E => ->.
+ move=> s1 s2 iv d lo hi c vlo vhi h1 h2 _ ih.
  case Elo: (sem_pexpr _ lo) h1 => /= [vlo'|//] [vlo'E].
  case Ehi: (sem_pexpr _ hi) h2 => /= [vhi'|//] [vhi'E].
  case: (leqP vlo' vhi') => [le|gt].
  + apply/SEforDone;
      rewrite (st2sst_pexpr (t := sword) Elo) ;
      rewrite (st2sst_pexpr (t := sword) Ehi) //.
    by rewrite vlo'E vhi'E.
*)
Admitted.

End SEM.
