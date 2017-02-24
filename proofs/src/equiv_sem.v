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
  {| semem := mem_to_smem s.(emem); sevm := vmap_to_svmap s.(evm); |}.

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
Lemma st2sst_toval {t} x:
  to_sval (@st2sst_ty t x) = value_to_svalue (to_val x).
Proof. by case: t x. Qed.

Lemma st2sst_ofval x v v':
  of_val (vtype x) v = ok v' -> of_sval (vtype x) (value_to_svalue v) = ok (st2sst_ty v').
Proof.
case: v=> //; case: (vtype x) v'=> //= p v' n a.
case: (CEDecStype.pos_dec n p)=> // H [<-].
by case: _ / H.
Qed.

Lemma st2sst_ofword v y:
  of_val sword v = ok y -> sto_word (value_to_svalue v) = ok y.
Proof.
by case: v.
Qed.

Lemma st2sst_ofbool v y:
  of_val sbool v = ok y -> sto_bool (value_to_svalue v) = ok y.
Proof.
by case: v.
Qed.

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

Lemma st2sst_getvar s x :
  sget_var (vmap_to_svmap (evm s)) x = value_to_svalue (get_var (evm s) x).
Proof.
by rewrite /sget_var /get_var st2sst_toval.
Qed.

Lemma st2sst_setvar x v vm vm':
  set_var vm x v = ok vm' ->
  sset_var (vmap_to_svmap vm) x (value_to_svalue v) = ok (vmap_to_svmap vm').
Proof.
rewrite /set_var=> h.
case: (bindW h)=> v' Hv' [<-].
rewrite /sset_var /=.
rewrite (st2sst_ofval Hv')=> //.
by rewrite /= st2sst_vmap_set.
Qed.

(* TODO: can these 3 lemmas be put together? *)
Lemma st2sst_op2_b f v1 v2 v: sem_op2_b f v1 v2 = ok v ->
  ssem_op2_b f (value_to_svalue v1) (value_to_svalue v2) = ok (value_to_svalue v).
Proof.
rewrite /sem_op2_b /mk_sem_sop2=> h.
case: (bindW h)=> b1 /= {h}.
case: v1=> // b' [<-] h.
case: (bindW h)=> b2 /= {h}.
by case: v2=> // b'' [<-] [<-].
Qed.

Lemma st2sst_op2_i f v1 v2 v: sem_op2_i f v1 v2 = ok v ->
  ssem_op2_i f (value_to_svalue v1) (value_to_svalue v2) = ok (value_to_svalue v).
Proof.
rewrite /sem_op2_i /mk_sem_sop2=> h.
case: (bindW h)=> b1 /= {h}.
case: v1=> // b' [<-] h.
case: (bindW h)=> b2 /= {h}.
by case: v2=> // b'' [<-] [<-].
Qed.

Lemma st2sst_op2_ib f v1 v2 v: sem_op2_ib f v1 v2 = ok v ->
  ssem_op2_ib f (value_to_svalue v1) (value_to_svalue v2) = ok (value_to_svalue v).
Proof.
rewrite /sem_op2_ib /mk_sem_sop2=> h.
case: (bindW h)=> b1 /= {h}.
case: v1=> // b' [<-] h.
case: (bindW h)=> b2 /= {h}.
by case: v2=> // b'' [<-] [<-].
Qed.

Lemma st2sst_op2 s v v1 v2: sem_sop2 s v1 v2 = ok v ->
  ssem_sop2 s (value_to_svalue v1) (value_to_svalue v2) = ok (value_to_svalue v).
Proof.
  case: s=> /=;
  try exact: st2sst_op2_b;
  try exact: st2sst_op2_i;
  try exact: st2sst_op2_ib.
Qed.

(* -------------------------------------------------------------------- *)
Lemma st2sst_pexpr s (p : pexpr) v : sem_pexpr s p = ok v ->
  ssem_pexpr (estate_to_sestate s) p = ok (value_to_svalue v).
Proof.
elim: p v=> //=.
+ by move=> x v [<-].
+ by move=> x v [<-].
+ move=> p Hv v h.
  case: (bindW h)=> z h' [<-].
  case: (bindW h')=> x /Hv ->.
  case: x=> // z0 /= [<-] //.
+ by move=> x v [<-]; rewrite st2sst_getvar.
+ move=> v p Hv v0 H.
  admit.
+ move=> ? p Hv v h.
  case: (bindW h)=> w {h}h [<-].
  case: (bindW h)=> x {h}h.
  case: (bindW h)=> y /Hv ->.
  case: y=> // w0 [<-].
  by rewrite /= => /mem2smem_read ->.
+ move=> p Hv v h.
  case: (bindW h)=> b {h}h [<-].
  case: (bindW h)=> x /Hv ->.
  by case: x=> // x0 [<-].
+ move=> s0 p Hv1 p0 Hv2 v h.
  case: (bindW h)=> v1 /Hv1 -> {h}h.
  case: (bindW h)=> v2 /Hv2 -> {h}.
  exact: st2sst_op2.
Admitted.

Lemma st2sst_pexprs s (p : pexprs) v : sem_pexprs s p = ok v ->
  ssem_pexprs (estate_to_sestate s) p = ok (map value_to_svalue v).
Proof.
elim: p v=> //=.
rewrite /sem_pexprs /ssem_pexprs /=.
by move=> v [] <-.
move=> a l IH v.
rewrite /sem_pexprs /ssem_pexprs /=.
have ->: mapM (sem_pexpr s) l = sem_pexprs s l by [].
have ->: mapM (ssem_pexpr s) l = ssem_pexprs s l by [].
move=> h.
case: (bindW h)=> x /st2sst_pexpr -> {h} /= h.
case: (bindW h)=> x0 {h} Hm [<-].
by rewrite (IH x0 Hm).
Qed.

Lemma st2sst_sopn: forall o x v,
  sem_sopn o x = ok v -> ssem_sopn o (map value_to_svalue x) = ok (map value_to_svalue v).
Proof.
move=> o x v.
case: o.
case: x=> // a l h.
case: (bindW h)=> x Hx {h}.
case: l=> //.
move=> [] <- /=.
by case: a Hx=> //= w [->].
all: try (case: x=> // a1 l h1 /=;
case: (bindW h1)=> x /st2sst_ofword -> {h1};
case: l=> // a2 l h2 /=;
case: (bindW h2)=> y /st2sst_ofword -> {h2};
case: l=> //;
by move=> [] <- /=).
case: x=> // a1 l h /=.
case: (bindW h)=> x /st2sst_ofbool -> {h}.
case: l=> // a2 l h /=.
case: (bindW h)=> y /st2sst_ofword -> {h}.
case: l=> // a3 l h /=.
case: (bindW h)=> z /st2sst_ofword -> {h}.
case: l=> //.
by move=> [] <- /=.
all: case: x=> // a1 l h /=;
case: (bindW h)=> x /st2sst_ofword -> {h};
case: l=> // a2 l h /=;
case: (bindW h)=> y /st2sst_ofword -> {h};
case: l=> // a3 l h /=;
case: (bindW h)=> z /st2sst_ofbool -> {h};
case: l=> //;
by move=> [] <- /=.
Qed.

(* -------------------------------------------------------------------- *)

Lemma st2sst_write_var s1 s2 v x:
   write_var x v s1 = ok s2 -> swrite_var x (value_to_svalue v) s1 = ok (estate_to_sestate s2).
Proof.
rewrite /write_var=> h.
case: (bindW h)=> vm Hs [<-].
rewrite /swrite_var /=.
by rewrite (st2sst_setvar Hs).
Qed.

Lemma st2sst_write_rval s1 s2 (x: rval) v :
  write_rval x v s1 = ok s2 ->
  swrite_rval x (value_to_svalue v) s1 = ok (estate_to_sestate s2).
Proof.
elim: x s1 s2 v=> v /=.
+ by move=> s1 s2 v0 [->].
+ move=> s1 s2 v0 /=.
  exact: st2sst_write_var.
+ move=> p s1 s2 v0 h.
  case: (bindW h)=> vx /st2sst_ofword H {h}h.
  rewrite -st2sst_getvar in H; rewrite {}H /=.
  case: (bindW h)=> ve {h} h1 h2.
  case: (bindW h1)=> x {h1} /st2sst_pexpr -> /st2sst_ofword /= -> /=.
  case: (bindW h2)=> w /st2sst_ofword -> {h2}h2 /=.
  by case: (bindW h2)=> m /mem2smem_write <- [] <-.
+ admit.
Admitted.

Lemma st2sst_write_rvals r v s1 s2:
  write_rvals s1 r v = ok s2 ->
  swrite_rvals s1 r (map value_to_svalue v) = ok (estate_to_sestate s2).
Proof.
rewrite /write_rvals /swrite_rvals.
elim: v r s1=> //=.
+ case=> //= s1.
  by move=> [] ->.
+ move=> a l IH.
  case=> // h q s1.
  rewrite /=.
  move=> h'.
  case: (bindW h')=> x Hw Hf.
  rewrite (st2sst_write_rval Hw) /=.
  by apply (IH q).
Qed.

(* -------------------------------------------------------------------- *)
Section SEM.

(* -------------------------------------------------------------------- *)
Lemma st2sst_cmd : forall p s1 c s2, sem p s1 c s2 -> ssem p s1 c s2.
Proof.
move=> P.
pose PI s1 i s2 := ssem_I P s1 i s2.
pose Pi s1 i s2 := ssem_i P s1 i s2.
pose Pf v s s1 c s2 := ssem_for P v s s1 c s2.
pose Pc m1 f vargs m2 vres := ssem_call P (mem_to_smem m1) f (map value_to_svalue vargs) (mem_to_smem m2) (map value_to_svalue vres).
apply: (@sem_Ind P _ Pi PI Pf Pc); try by (move=> *; eauto with ssem).
(* Cassgn *)
+ constructor.
  by case: (bindW H)=> v {H} /st2sst_pexpr -> /st2sst_write_rval <-.
(* Copn *)
+ constructor.
  case: (bindW H)=> v {H}H /st2sst_write_rvals <-.
  case: (bindW H)=> x {H} /st2sst_pexprs -> /st2sst_sopn H'.
  by rewrite /= H' /=.
+ constructor=> //.
  case: (bindW H)=> x /st2sst_pexpr ->.
  by case: x.
+ move=> s1 s2 e c1 c2 H Hs Hss.
  apply: SEif_false=> //.
  case: (bindW H)=> x /st2sst_pexpr ->.
  by case: x.
+ move=> s1 s2 s3 e c H Hs Hss Hs3 HP.
  apply: (@SEwhile_true P s1 s2 s3 e c)=> //.
  case: (bindW H)=> x /st2sst_pexpr ->.
  by case: x.
+ move=> s e c H.
  apply: SEwhile_false.
  case: (bindW H)=> x /st2sst_pexpr ->.
  by case: x.
+ move=> s1 s2 i d lo hi c vlo vhi h1 h2 Hfor Hf.
  apply: (@SEfor P s1 s2 i d lo hi c vlo vhi)=> //.
  case: (bindW h1)=> x /st2sst_pexpr ->.
  by case: x.
  case: (bindW h2)=> x /st2sst_pexpr ->.
  by case: x.
+ move=> s1 m2 s2 ii xs f fd args vargs vs Hfd Hvargs Hcall H Hw.
  apply (@SEcall _ s1 (mem_to_smem m2) s2 ii xs f fd args (map value_to_svalue vargs) (map value_to_svalue vs))=> //.
  by rewrite (st2sst_pexprs Hvargs).
  by rewrite (st2sst_write_rvals Hw).
+ move=> s i c.
  exact: SEForDone.
+ move=> s1 s1' s2 s3 i w ws c Hw Hs Hss Hfor Honce.
  apply: (@SEForOne _ s1 s1' s2)=> //.
  by rewrite (st2sst_write_var Hw).
+ move=> m1 m2 f vargs vres H Hf.
  apply: SEcallRun=> vm0.
  admit.
Admitted.

End SEM.
