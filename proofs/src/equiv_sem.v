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
Require Import ZArith.

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
Definition sval_uincl (t:stype) : sem_t t -> ssem_t t -> Prop :=
  match t as t0 return sem_t t0 -> ssem_t t0 -> Prop with
  | sbool => fun b1 b2 => b1 = b2
  | sint  => fun i1 i2 => i1 = i2
  | sword => fun w1 w2 => w1 = w2
  | sarr n => fun (t1:Array.array n word) (t2:FArray.array word) =>
      (forall i v, Array.get t1 i = ok v -> FArray.get t2 i = v)
  end.

Definition svm_uincl (vm:vmap) (svm:svmap) :=
  forall x, sval_uincl (vm.[x])%vmap (svm.[x])%vmap.

(* -------------------------------------------------------------------- *)
Definition sestate_uincl (s: estate) (ss: sestate) :=
  mem_to_smem s.(emem) = ss.(semem) /\ (svm_uincl s.(evm) ss.(sevm)).

Definition svalue_uincl (v: value) (sv: svalue) :=
  match v, sv with
  | Vbool b1, SVbool b2 => b1 = b2
  | Vint n1, SVint n2   => n1 = n2
  | Varr n1 t1, SVarr n2 t2 =>
    n1 = n2 /\ (forall i v, Array.get t1 i = ok v -> FArray.get t2 i = v)
  | Vword w1, SVword w2 => w1 = w2
  | _, _ => False
  end.

(*******************************************)
(*******************************************)
(*******************************************)
(*******************************************)
(*******************************************)
(*******************************************)

Lemma of_sval_uincl v v' t z:
  svalue_uincl v v' ->
  of_val t v = ok z ->
  exists z', of_sval t v' = ok z' /\ sval_uincl z z'.
Proof.
  case: v v'=> [b | n | n a | w] [b' | n' | n' a' | w'] //=; try (by case: t z=> //= z -> []->; exists z).
  move=> [<- H].
  case: t z => //= p z.
  case: (CEDecStype.pos_dec n p)=> // H' [<-].
  exists a'; split=> //.
  by case: _ / H'.
Qed.

Lemma svalue_uincl_int ve ve' z :
  svalue_uincl ve ve' -> to_int ve = ok z -> ve = z /\ ve' = z.
Proof. by case:ve ve' => //= z0 [] //= z1 -> [] ->. Qed.

Lemma svalue_uincl_word ve ve' w :
  svalue_uincl ve ve' -> to_word ve = ok w -> ve = w /\ ve' = w.
Proof. by case:ve ve' => //= z0 [] //= z1 -> [] ->. Qed.

Lemma svalue_uincl_bool ve ve' b :
  svalue_uincl ve ve' -> to_bool ve = ok b -> ve = b /\ ve' = b.
Proof. by case:ve ve' => //= z0 [] //= z1 -> [] ->. Qed.

Lemma sget_var_uincl x vm1 vm2 :
  svm_uincl vm1 vm2 -> svalue_uincl (get_var vm1 x) (sget_var vm2 x).
Proof. by move=> /(_ x);case x => -[]. Qed.

Lemma sget_vars_uincl (xs:seq var_i) vm1 vm2 :
  svm_uincl vm1 vm2 ->
  List.Forall2 svalue_uincl
      [seq get_var vm1 (v_var x) | x <- xs] [seq sget_var vm2 (v_var x) | x <- xs].
Proof.
  move=> Hvm;elim: xs => //= x xs Hrec;constructor=>//;by apply sget_var_uincl.
Qed.

Lemma svuincl_sem_op2_b o ve1 ve1' ve2 ve2' v1 :
  svalue_uincl ve1 ve1' -> svalue_uincl ve2 ve2' -> sem_op2_b o ve1 ve2 = ok v1 ->
  exists v2 : svalue, ssem_op2_b o ve1' ve2' = ok v2 /\ svalue_uincl v1 v2.
Proof.
  rewrite /sem_op2_b /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(svalue_uincl_bool Hvu1) [] _ ->.
  apply: rbindP => z2 /(svalue_uincl_bool Hvu2) [] _ -> [] <- /=.
  by exists (o z1 z2).
Qed.

Lemma svuincl_sem_op2_i o ve1 ve1' ve2 ve2' v1 :
  svalue_uincl ve1 ve1' -> svalue_uincl ve2 ve2' -> sem_op2_i o ve1 ve2 = ok v1 ->
  exists v2 : svalue, ssem_op2_i o ve1' ve2' = ok v2 /\ svalue_uincl v1 v2.
Proof.
  rewrite /sem_op2_i /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(svalue_uincl_int Hvu1) [] _ ->.
  apply: rbindP => z2 /(svalue_uincl_int Hvu2) [] _ -> [] <- /=.
  by exists (o z1 z2).
Qed.

Lemma svuincl_sem_op2_ib o ve1 ve1' ve2 ve2' v1 :
  svalue_uincl ve1 ve1' -> svalue_uincl ve2 ve2' -> sem_op2_ib o ve1 ve2 = ok v1 ->
  exists v2 : svalue, ssem_op2_ib o ve1' ve2' = ok v2 /\ svalue_uincl v1 v2.
Proof.
  rewrite /sem_op2_ib /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(svalue_uincl_int Hvu1) [] _ ->.
  apply: rbindP => z2 /(svalue_uincl_int Hvu2) [] _ -> [] <- /=.
  by exists (o z1 z2).
Qed.

Lemma ssem_pexpr_uincl s ss e v1:
  sestate_uincl s ss ->
  sem_pexpr s e = ok v1 ->
  exists v2, ssem_pexpr ss e = ok v2 /\ svalue_uincl v1 v2.
Proof.
  move=> [Hu1 Hu2]; elim: e v1=>//= [z | b | e He | x | x p Hp | x p Hp | e Hp | o e1 He1 e2 He2] v1.
  + by move=> [] <-;exists z.
  + by move=> [] <-;exists b.
  + apply: rbindP => z;apply: rbindP => ve /He [] ve' [] -> Hvu Hto [] <-.
    by case: (svalue_uincl_int Hvu Hto) => ??;subst; exists (SVword (I64.repr z)).
  + by move=> [] <-;exists (sget_var ss.(sevm) x);split=> //;apply sget_var_uincl.
  + have := Hu2 x;case x => -[xt xn] xi /= H H';move: H' H.
    apply: on_arr_varP2 => /= n t -> /= /Varr_inj1 <-.
    apply: rbindP => z;apply: rbindP => vp /Hp [] vp' [] Hvp' Hvu Hto.
    case: (svalue_uincl_word Hvu Hto) => ??;subst.
    apply: rbindP=> w Hget [] <- /=.
    by rewrite /son_arr_var Hvp' /= => /(_ _ _ Hget) -> /=;exists w.
  + apply: rbindP => w;apply: rbindP => wp;apply: rbindP => vp /Hp [] vp' [] -> Hvu Hto.
    rewrite -Hu1.
    by case: (svalue_uincl_word Hvu Hto) => ??;subst => /= /mem2smem_read -> [] <-; exists w.
  + apply: rbindP => b;apply: rbindP => vx /Hp [] vp' [] -> Hvu Hto [] <-.
    by case: (svalue_uincl_bool Hvu Hto) => ??;subst => /=;exists (~~b).
  apply: rbindP => ve1 /He1 [] ve1' [] -> Hvu1.
  apply: rbindP => ve2 /He2 [] ve2' [] -> Hvu2 {He1 He2}.
  case:o => /=;eauto using svuincl_sem_op2_i, svuincl_sem_op2_b, svuincl_sem_op2_ib.
Qed.

Lemma ssem_pexprs_uincl s ss es vs1:
  sestate_uincl s ss ->
  sem_pexprs s es = ok vs1 ->
  exists vs2, ssem_pexprs ss es = ok vs2 /\
              List.Forall2 svalue_uincl vs1 vs2.
Proof.
  rewrite /sem_pexprs /ssem_pexprs; move=> Hvm;elim: es vs1 => [ | e es Hrec] vs1 /=.
  + by move=> [] <-;eauto.
  apply: rbindP => ve /(ssem_pexpr_uincl Hvm) [] ve' [] -> ?.
  by apply: rbindP => ys /Hrec [vs2 []] /= -> ? [] <- /=;eauto.
Qed.

Lemma svuincl_oww o vs vs' v :
  List.Forall2 svalue_uincl vs vs' ->
  (oww o) vs = ok v ->
  exists v' : svalues,
     (soww o) vs' = ok v' /\ List.Forall2 svalue_uincl v v'.
Proof.
  move=> [] //= v1 v1' ?? Hv [] //=;last by move=> ??????;apply: rbindP.
  apply: rbindP => z /(svalue_uincl_word Hv) [] _ -> [] <- /=.
  by eexists;split;eauto;constructor.
Qed.

Lemma svuincl_owww o vs vs' v :
  List.Forall2 svalue_uincl vs vs' ->
  (owww o) vs = ok v ->
  exists v' : svalues,
     (sowww o) vs' = ok v' /\ List.Forall2 svalue_uincl v v'.
Proof.
  move=> [] //= v1 v1' ?? Hv [] //=; first by apply: rbindP.
  move=> ???? Hv' [] //=.
  + apply: rbindP => z /(svalue_uincl_word Hv) [] _ ->.
    apply: rbindP => z' /(svalue_uincl_word Hv') [] _ -> [] <- /=.
    by eexists;split;eauto;constructor.
  by move=> ??????;t_rbindP.
Qed.

Lemma svuincl_sem_opn o vs vs' v :
  List.Forall2 svalue_uincl vs vs' -> sem_sopn o vs = ok v ->
  exists v', ssem_sopn o vs' = ok v' /\ List.Forall2 svalue_uincl v v'.
Proof.
  rewrite /sem_sopn /ssem_sopn;case: o;eauto using svuincl_oww, svuincl_owww.
  + move=> [] //= v1 v1' ?? Hv1 [] //=; first by apply: rbindP.
    move=> v2 v2' ?? Hv2 [];first by t_rbindP.
    move=> v3 v3' ?? Hv3 [].
    + apply: rbindP=> ? /(svalue_uincl_bool Hv1) [] _ ->.
      apply: rbindP=> ? /(svalue_uincl_word Hv2) [] _ ->.
      apply: rbindP=> ? /(svalue_uincl_word Hv3) [] _ -> [] <- /=.
      by eexists;split;eauto;do 2 constructor.
    by move=> ??????;t_rbindP.
  + move=> [] //= v1 v1' ?? Hv [] //=; first by apply: rbindP.
    move=> ???? Hv' [] //=.
    + apply: rbindP => z /(svalue_uincl_word Hv) [] _ ->.
      apply: rbindP => z' /(svalue_uincl_word Hv') [] _ -> [] <- /=.
      by eexists;split;eauto;constructor => //;constructor.
    by move=> ??????;t_rbindP.
  + move=> [] //= v1 v1' ?? Hv1 [] //=; first by apply: rbindP.
    move=> v2 v2' ?? Hv2 [];first by t_rbindP.
    move=> v3 v3' ?? Hv3 [].
    + apply: rbindP=> ? /(svalue_uincl_word Hv1) [] _ ->.
      apply: rbindP=> ? /(svalue_uincl_word Hv2) [] _ ->.
      apply: rbindP=> ? /(svalue_uincl_bool Hv3) [] _ -> [] <- /=.
      by eexists;split;eauto;do 2 constructor.
    by move=> ??????;t_rbindP.
  + move=> [] //= v1 v1' ?? Hv1 [] //=; first by apply: rbindP.
    move=> v2 v2' ?? Hv2 [];first by t_rbindP.
    move=> v3 v3' ?? Hv3 [].
    + apply: rbindP=> ? /(svalue_uincl_word Hv1) [] _ ->.
      apply: rbindP=> ? /(svalue_uincl_word Hv2) [] _ ->.
      apply: rbindP=> ? /(svalue_uincl_bool Hv3) [] _ -> [] <- /=.
      by eexists;split;eauto;do 2 constructor.
    by move=> ??????;t_rbindP.
Qed.

Lemma sset_vm_uincl vm vm' x z z' :
  svm_uincl vm vm' ->
  sval_uincl z z' ->
  svm_uincl (vm.[x <- z])%vmap (vm'.[x <- z'])%vmap.
Proof.
  move=> Hvm Hz y; case( x =P y) => [<- | /eqP Hneq];by rewrite ?Fv.setP_eq ?Fv.setP_neq.
Qed.

Lemma sset_var_uincl vm1 vm1' vm2 x v v' :
  svm_uincl vm1 vm1' ->
  svalue_uincl v v' ->
  set_var vm1 x v = ok vm2 ->
  exists vm2', sset_var vm1' x v' = ok vm2' /\ svm_uincl vm2 vm2'.
Proof.
  move=> Hvm Hv;rewrite /set_var /sset_var.
  apply: rbindP=> z /(of_sval_uincl Hv) [z' [-> ?]] [] <- /=.
  by exists (vm1'.[x <- z'])%vmap;split=>//; apply sset_vm_uincl.
Qed.

Lemma SArray_set_uincl n (a1:Array.array n word) (a2: FArray.array word) (a1':Array.array n word) i v:
  @sval_uincl (sarr n) a1 a2 ->
  Array.set a1 i v = ok a1' ->
  exists a2', FArray.set a2 i v = a2' /\ @sval_uincl (sarr n) a1' a2'.
Proof.
  rewrite /Array.set;case:ifP=> //= ? H [] <-.
  exists (FArray.set a2 i v);split => // i' v';move: (H i' v').
  rewrite /Array.get;case:ifP=> //= Hbound.
  rewrite !FArray.setP;case:ifP=> //.
  by move=> ?? [] ->.
Qed.

Lemma swrite_var_uincl s ss s' v1 v2 x :
  sestate_uincl s ss ->
  svalue_uincl v1 v2 ->
  write_var x v1 s = ok s' ->
  exists ss' : sestate,
    swrite_var x v2 ss = ok ss' /\ sestate_uincl s' ss'.
Proof.
  move=> [? Hvm1] Hv;rewrite /write_var /swrite_var;apply: rbindP=> vm2 /=.
  by move=> /(sset_var_uincl Hvm1 Hv) [vm2' [-> ?]] [] <- /=; exists {| semem := semem ss; sevm := vm2' |}.
Qed.

Lemma swrite_vars_uincl s ss s' vs1 vs2 xs :
  sestate_uincl s ss ->
  List.Forall2 svalue_uincl vs1 vs2 ->
  write_vars xs vs1 s = ok s' ->
  exists ss' : sestate,
    swrite_vars xs vs2 ss =
    ok ss' /\ sestate_uincl s' ss'.
Proof.
  elim: xs s ss vs1 vs2 => /= [ | x xs Hrec] s ss vs1 vs2 Hvm [] //=.
  + by move=> [] <-;eauto.
  move=> {vs1 vs2} v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s1'.
  by move=> /(swrite_var_uincl Hvm Hv) [] vm2 [] -> Hvm2 /(Hrec _ _ _ _ Hvm2 Hvs).
Qed.

Lemma swrite_uincl_aux s0 s1 s' ss0 ss1 r v1 v2:
  sestate_uincl s0 ss0 ->
  sestate_uincl s1 ss1 ->
  svalue_uincl v1 v2 ->
  write_rval_aux s0 r v1 s1 = ok s' ->
  exists ss',
    swrite_rval_aux ss0 r v2 ss1 = ok ss' /\ sestate_uincl s' ss'.
Proof.
  move=> Hs0 Hs1 Hv;case:r => [xi | x | x p | x p] /=.
  + by move=> [] <-;exists ss1.
  + rewrite /write_var /swrite_var;apply: rbindP=> vm2 /=.
    move: Hs1=> [Hmem1 Hvm1].
    rewrite -Hmem1.
    by move=> /(sset_var_uincl Hvm1 Hv) [vm2' [-> ?]] [] <- /=;exists {| semem := mem_to_smem (emem s1); sevm := vm2' |}.
  + apply: rbindP => vx /(svalue_uincl_word (@sget_var_uincl x _ _ (proj2 Hs0))) [] _ ->.
    apply: rbindP => ve; apply: rbindP => ve' /(ssem_pexpr_uincl Hs0) [ve''] [] -> Hve.
    move=> /(svalue_uincl_word Hve) [] _ -> /=.
    apply: rbindP => w /(svalue_uincl_word Hv) [] _ -> /=.
    move: Hs1=> [Hmem1 Hvm1].
    rewrite -Hmem1.
    by apply: rbindP => m' /mem2smem_write <- [] <-; exists {| semem := mem_to_smem m'; sevm := sevm ss1 |}.
  apply: on_arr_varP2 => n a;case: x => -[xt xn] xi /= -> /= /Varr_inj1.
  rewrite /on_arr_var /= => <-.
  apply: rbindP => i;apply: rbindP=> vp /(ssem_pexpr_uincl Hs0) [vp' [-> Hvp]].
  move: Hs0=> [Hmem0 Hvm0].
  move=>  /(svalue_uincl_word Hvp) [] _ -> /=.
  apply: rbindP => v /(svalue_uincl_word Hv) [] _ -> /=.
  apply: rbindP => t; set x := {|vtype := _ |}=> /(SArray_set_uincl (Hvm0 x)).
  move=> [] t' [H1 Ht];apply: rbindP=> vm'.
  have Hut: svalue_uincl (Varr t) (SVarr n t') by split.
  move: Hs1=> [Hmem1 Hvm1].
  move=> /(sset_var_uincl Hvm1 Hut) /= [vm2' [Hvm2' ?]] [] <- /=.
  rewrite /son_arr_var /= H1 /=.
  rewrite /sset_var /= in Hvm2'.
  move: Hvm2'=> [] ->.
  by exists {| semem := semem ss1; sevm := vm2' |}.
Qed.

Lemma swrite_uincl s s' ss r v1 v2:
  sestate_uincl s ss ->
  svalue_uincl v1 v2 ->
  write_rval r v1 s = ok s' ->
  exists ss',
    swrite_rval r v2 ss = ok ss' /\
    sestate_uincl s' ss'.
Proof. by move=> ?; apply swrite_uincl_aux. Qed.

Lemma swrites_uincl s s' ss r v1 v2:
  sestate_uincl s ss ->
  List.Forall2 svalue_uincl v1 v2 ->
  write_rvals s r v1 = ok s' ->
  exists ss',
    swrite_rvals ss r v2 = ok ss' /\
    sestate_uincl s' ss'.
Proof.
  rewrite /write_rvals /swrite_rvals => Hs.
  move: {1 3} s {1 3} ss (Hs)=> s0.
  elim: r v1 v2 s0=> [|r rs Hrec] v1 v2 s0 ss0 Hs0 /= [] //=.
  + by move=> [] <-; exists ss0.
  move=> {v1 v2} v1 v2 vs1 vs2 Hv Hforall.
  apply: rbindP=> z /(swrite_uincl_aux Hs Hs0 Hv) [] x [] -> Hz.
  by move=> /(Hrec _ _ _ _ Hz Hforall).
Qed.

Definition value_to_svalue (v: value) : svalue :=
  match v with
  | Vbool b => SVbool b
  | Vint i => SVint i
  | Vword w => SVword w
  | Varr n t => SVarr n (@st2sst_ty (sarr n) t)
  end.

(* -------------------------------------------------------------------- *)
Section SEM.

Variable (p:prog).

Let Pc s1 c s2 :=
  forall ss1,
    sestate_uincl s1 ss1 -> exists ss2, ssem p ss1 c ss2 /\ sestate_uincl s2 ss2.

Let Pi_r s1 c s2 :=
  forall ss1,
    sestate_uincl s1 ss1 -> exists ss2, ssem_i p ss1 c ss2 /\ sestate_uincl s2 ss2.

Let Pi s1 c s2 :=
  forall ss1,
    sestate_uincl s1 ss1 -> exists ss2, ssem_I p ss1 c ss2 /\ sestate_uincl s2 ss2.

Let Pfor i zs s1 c s2 :=
  forall ss1,
    sestate_uincl s1 ss1 -> exists ss2, ssem_for p i zs ss1 c ss2 /\ sestate_uincl s2 ss2.

Let Pfun m1 fd vargs m2 vres :=
  forall vargs' vres',
    List.Forall2 svalue_uincl vargs vargs' ->
    List.Forall2 svalue_uincl vres vres' ->
    ssem_call p (mem_to_smem m1) fd vargs' (mem_to_smem m2) vres'.

Local Lemma Hnil s : Pc s [::] s.
Proof. by move=> vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

Local Lemma Hcons s1 s2 s3 i c :
  sem_I p s1 i s2 -> Pi s1 i s2 ->
  sem p s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
Proof.
  move=> _ Hi _ Hc vm1 /Hi [vm2 []] Hsi /Hc [vm3 []] Hsc ?.
  by exists vm3;split=>//;econstructor;eauto.
Qed.

Local Lemma HmkI ii i s1 s2 : sem_i p s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
Proof. by move=> _ Hi vm1 /Hi [vm2 []] Hsi ?;exists vm2. Qed.

Local Lemma Hasgn s1 s2 x tag e :
  Let v := sem_pexpr s1 e in write_rval x v s1 = ok s2 ->
  Pi_r s1 (Cassgn x tag e) s2.
Proof.
  move=> Hs2 vm1 Hvm1;apply:rbindP Hs2 => z /(ssem_pexpr_uincl Hvm1) [] z' [] Hz' Hz.
  move=> /(swrite_uincl Hvm1 Hz) [vm2 []] Hw ?;exists vm2;split=> //.
  by constructor;rewrite Hz' /= Hw.
Qed.

Local Lemma Hopn s1 s2 o xs es:
  Let x := Let x := sem_pexprs s1 es in sem_sopn o x in
  write_rvals s1 xs x = ok s2 -> Pi_r s1 (Copn xs o es) s2.
Proof.
  move=> H vm1 Hvm1; apply: rbindP H => rs;apply: rbindP => vs.
  move=> /(ssem_pexprs_uincl Hvm1) [] vs' [] H1 H2.
  move=> /(svuincl_sem_opn H2) [] rs' [] H3 H4.
  move=> /(swrites_uincl Hvm1 H4) [] vm2 [] ??.
  exists vm2;split => //;constructor.
  by rewrite H1 /= H3.
Qed.

Local Lemma Hif_true s1 s2 e c1 c2 :
  Let x := sem_pexpr s1 e in to_bool x = ok true ->
  sem p s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
Proof.
  move=> H _ Hc vm1 Hvm1;apply: rbindP H => v.
  move=> /(ssem_pexpr_uincl Hvm1) [] v' [] H1 H2.
  move=> /(svalue_uincl_bool H2) [] ??;subst.
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  by apply SEif_true;rewrite // H1.
Qed.

Local Lemma Hif_false s1 s2 e c1 c2 :
  Let x := sem_pexpr s1 e in to_bool x = ok false ->
  sem p s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
Proof.
  move=> H _ Hc vm1 Hvm1;apply: rbindP H => v.
  move=> /(ssem_pexpr_uincl Hvm1) [] v' [] H1 H2.
  move=> /(svalue_uincl_bool H2) [] ??;subst.
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  by apply SEif_false;rewrite // H1.
Qed.

Local Lemma Hwhile_true s1 s2 s3 e c :
  Let x := sem_pexpr s1 e in to_bool x = ok true ->
  sem p s1 c s2 -> Pc s1 c s2 ->
  sem_i p s2 (Cwhile e c) s3 -> Pi_r s2 (Cwhile e c) s3 -> Pi_r s1 (Cwhile e c) s3.
Proof.
  move=> H _ Hc _ Hw vm1 Hvm1;apply: rbindP H => v.
  move=> /(ssem_pexpr_uincl Hvm1) [] v' [] H1 H2.
  move=> /(svalue_uincl_bool H2) [] ??;subst.
  have [vm2 [H3 /Hw [vm3] [??]]]:= Hc _ Hvm1;exists vm3;split => //.
  by eapply SEwhile_true;eauto;rewrite H1.
Qed.

Local Lemma Hwhile_false s e c :
  Let x := sem_pexpr s e in to_bool x = ok false ->
  Pi_r s (Cwhile e c) s.
Proof.
  move=> H vm1 Hvm1;apply: rbindP H=> v.
  move=> /(ssem_pexpr_uincl Hvm1) [] v' [] H1 H2.
  move=> /(svalue_uincl_bool H2) [] ??;subst.
  by exists vm1;split=> //;apply SEwhile_false;rewrite H1.
Qed.

Local Lemma Hfor s1 s2 (i : var_i) d lo hi c (vlo vhi : Z) :
  Let x := sem_pexpr s1 lo in to_int x = ok vlo ->
  Let x := sem_pexpr s1 hi in to_int x = ok vhi ->
  sem_for p i (wrange d vlo vhi) s1 c s2 ->
  Pfor i (wrange d vlo vhi) s1 c s2 ->
  Pi_r s1 (Cfor i (d, lo, hi) c) s2.
Proof.
  move=> H H' _ Hfor vm1 Hvm1;apply: rbindP H => ?.
  move=> /(ssem_pexpr_uincl Hvm1) [] ? [] H1 H2.
  move=> /(svalue_uincl_int H2) [] ??;subst.
  apply: rbindP H' => ?.
  move=> /(ssem_pexpr_uincl Hvm1) [] ? [] H3 H4.
  move=> /(svalue_uincl_int H4) [] ??;subst.
  have [vm2 []??]:= Hfor _ Hvm1; exists vm2;split=>//.
  by econstructor;eauto;rewrite ?H1 ?H3.
Qed.

Local Lemma Hfor_nil s i c : Pfor i [::] s c s.
Proof. by move=> vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w : Z) (ws : seq Z) c :
  write_var i w s1 = ok s1' ->
  sem p s1' c s2 -> Pc s1' c s2 ->
  sem_for p i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
Proof.
  move=> Hi _ Hc _ Hf vm1 Hvm1.
  have [//|vm1' [Hi' /Hc]] := @swrite_var_uincl _ _ _ _ (SVint w) _ Hvm1 _ Hi.
  move=> [vm2 [Hsc /Hf]] [vm3 [Hsf Hvm3]];exists vm3;split => //.
  by econstructor;eauto.
Qed.

Local Lemma Hcall s1 m2 s2 ii xs fn fd args vargs vs :
  get_fundef p fn = Some fd ->
  sem_pexprs s1 args = ok vargs ->
  sem_call p (emem s1) fd vargs m2 vs ->
  Pfun (emem s1) fd vargs m2 vs ->
  write_rvals {| emem := m2; evm := evm s1 |} xs vs = ok s2 ->
  Pi_r s1 (Ccall ii xs fn args) s2.
Proof.
  move=> Hget Hargs Hcall Hfd Hxs s Hs.
  have [vargs' [Hsa /Hfd Hc]]:= ssem_pexprs_uincl Hs Hargs.
  have Hbla: List.Forall2 svalue_uincl vs [seq value_to_svalue i | i <- vs].
  + clear Hcall Hfd Hxs Hc.
    elim: vs=> [//=|v vs IH].
    rewrite //=.
    apply: List.Forall2_cons.
    rewrite //.
    (* TODO: this should be a separate lemma *)
    case: v=> //.
    move=> n a /=; split=> // i v.
    by rewrite /FArray.get => ->.
    exact: IH.
  have := swrites_uincl _ Hbla Hxs.
  have Hvm1: sestate_uincl {| emem := m2; evm := evm s1 |} {| semem := mem_to_smem m2; sevm := sevm s |}.
    split=> //.
    by move: Hs=> [_ ?].
  have [vm2' [??]]:= swrites_uincl Hvm1 Hbla Hxs.
  exists vm2';split=>//;econstructor;eauto.
  rewrite (proj1 Hvm1) /= in Hc.
  rewrite (proj1 Hs) /= in Hc.
  exact: Hc.
Qed.

Local Lemma Hproc m1 m2 fd vargs vres :
  (forall vm0 : vmap,
     all_empty_arr vm0 ->
     exists (s1 : estate) (vm2 : vmap),
       [/\ write_vars (f_params fd) vargs {| emem := m1; evm := vm0 |} =
           ok s1, sem p s1 (f_body fd) {| emem := m2; evm := vm2 |},
           Pc s1 (f_body fd) {| emem := m2; evm := vm2 |}
           &  map (fun (x:var_i) => get_var vm2 x) fd.(f_res) = vres]) ->
  List.Forall is_full_array vres -> Pfun m1 fd vargs m2 vres.
Proof.
  move=> Hrec Hvres vargs' vres' Hargs Hres.
  constructor=> svm0.
  have vm0: vmap by admit.
  have Hvm0: svm_uincl vm0 svm0 by admit.
  have Hvm0': all_empty_arr vm0 by admit.
  move: (Hrec vm0 Hvm0')=> [s1 [vm2 []]].
  have Hs: sestate_uincl {| emem := m1; evm := vm0 |} {| semem := mem_to_smem m1; sevm := svm0 |} by [].
  move=> /(swrite_vars_uincl Hs Hargs) /= [ss'] [] Hwv Hs1 ?.
  move=> /(_ _ Hs1) [vm3] /= [] Hssem Hvm2 ?;subst.
  eexists;eexists;split;eauto.  
  have Hvm3: vm3 = {| semem := mem_to_smem m2; sevm := sevm vm3 |}.
    admit.
  rewrite Hvm3 in Hssem.
  exact: Hssem.
  admit.
(*
  have := sget_vars_uincl (f_res fd) (proj2 Hvm2).
  by move=> /(is_full_array_uincls Hvres) ->.
*)
  (*
  constructor=> // vm0 /Hrec [s1 [vm2 []]].
  move=> /(write_vars_uincl (vm_uincl_refl _) Hargs) /= [vm1'] [] Hwv Hvm1 ?.
  move=> /(_ _ Hvm1) [vm3] /= [] ? Hvm2 ?;subst.
  eexists;eexists;split;eauto.
  have := get_vars_uincl (f_res fd) Hvm2.
  by move=> /(is_full_array_uincls Hvres) ->.
  *)
Admitted.

(*
Lemma sem_call_uincl vargs m1 fd m2 vres vargs':
  List.Forall2 value_uincl vargs vargs' ->
  sem_call p m1 fd vargs m2 vres ->
  sem_call p m1 fd vargs' m2 vres.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_i_uincl s1 i s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem_i p s1 i s2 ->
  exists vm2,
    sem_i p {|emem := emem s1; evm := vm1|} i {|emem := emem s2; evm := vm2|} /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_i_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_I_uincl s1 i s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem_I p s1 i s2 ->
  exists vm2,
    sem_I p {|emem := emem s1; evm := vm1|} i {|emem := emem s2; evm := vm2|} /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_I_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_uincl s1 c s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem p s1 c s2 ->
  exists vm2,
    sem p {|emem := emem s1; evm := vm1|} c {|emem := emem s2; evm := vm2|} /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.
*)

End SEM.
