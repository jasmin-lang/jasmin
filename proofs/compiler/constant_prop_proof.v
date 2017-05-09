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
Require Import sem.
Require Export constant_prop.

Import ZArith Morphisms Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
Local Open Scope vmap_scope.

Local Notation cpm := (Mvar.t Z).

(* ** proofs
 * -------------------------------------------------------------------- *)

Definition eqok (e1 e2:pexpr) st := 
  forall v, sem_pexpr st e1 = ok v -> sem_pexpr st e2 = ok v.

Notation "e1 '=[' st ']' e2" := (eqok e1 e2 st)
 (at level 70, no associativity).

Definition eeq (e1 e2:pexpr) := forall rho, e1 =[rho] e2.

Notation "e1 '=E' e2" := (eeq e1 e2) (at level 70, no associativity).

Lemma eeq_refl : Reflexive (@eeq).
Proof. by move=> ???. Qed.

Hint Immediate eeq_refl.

Lemma snot_boolP e : Papp1 Onot e =E snot_bool e.
Proof. 
  case: e=> //=;try auto; first by move=> ??.
  move=> []; last by auto.
  move=> p rho v /=;rewrite /eqok.
  apply: rbindP => w;apply:rbindP => w' /= ->.
  apply: rbindP => /= b Hb [<-]. 
  rewrite /sem_op1_b /mk_sem_sop1 /= negbK => [<-].
  by case: w' Hb => //= ? [<-].
Qed.

Lemma snot_wP e : Papp1 Olnot e =E snot_w e.
Proof. auto. Qed.

Lemma s_op1P o e : Papp1 o e =E s_op1 o e.
Proof. case: o;auto using snot_boolP, snot_wP. Qed.


(* * -------------------------------------------------------------------- *)
Lemma sandP e1 e2 : Papp2 Oand e1 e2 =E sand e1 e2.
Proof.
  rewrite /sand. case: is_boolP => [b1 rho v /=| {e1} e1]. 
  + by case:b1;case: sem_pexpr => //= -[].
  case: is_boolP => [b2 rho v /=|{e2}e2];last by auto using eeq_refl.
  by case:b2;case: sem_pexpr => //= -[] //= b [] <-;rewrite ?andbT ?andbF.
Qed.

Lemma sorP e1 e2 : Papp2 Oor e1 e2 =E sor e1 e2.
Proof.
  rewrite /sor. case: is_boolP => [b1 rho v /=| {e1} e1]. 
  + by case:b1;case: sem_pexpr => //= -[].
  case: is_boolP => [b2 rho v /=|{e2}e2];last by auto using eeq_refl.
  by case:b2;case: sem_pexpr => //= -[] //= b [] <-;rewrite ?orbT ?orbF.
Qed.

Lemma sadd_intP e1 e2 : Papp2 (Oadd Op_int) e1 e2 =E sadd_int e1 e2.
Proof.
  rewrite /sadd_int; case: (is_constP e1) => [n1| {e1} e1];
    case: (is_constP e2) => [n2| {e2} e2] rho v //=.
  + by case: eqP => [-> | //];case: sem_pexpr => //= -[].
  case: eqP => [-> | //];case: sem_pexpr => //= -[] //= z <-.
  by rewrite /sem_op2_i /mk_sem_sop2 /= Z.add_0_r.
Qed.

Lemma is_wconstP e : is_reflect wconst e (is_wconst e).
Proof.
  case e => //=;auto using Is_reflect_none.
  move=> e1; case: (is_constP e1);auto using Is_reflect_none.
  move=> z;apply: Is_reflect_some.
Qed.

Lemma sadd_wP e1 e2 : Papp2 (Oadd Op_w) e1 e2 =E sadd_w e1 e2.
Proof.
  rewrite /sadd_w; case: (is_wconstP e1) => [n1| {e1} e1];
    case: (is_wconstP e2) => [n2| {e2} e2] rho v //=.
  + by rewrite /sem_op2_w /mk_sem_sop2 /= iword_addP.
  + case:ifP => [/eqP Heq | //].
    apply:rbindP=> v2 ->;rewrite -repr_mod Heq /sem_op2_w /mk_sem_sop2 /=.
    by case: v2 => //= w2;rewrite I64.add_zero_l => -[<-].
  case:ifP => [/eqP Heq | //].
  apply:rbindP=> v1 ->;rewrite -repr_mod Heq /sem_op2_w /mk_sem_sop2 /=.
  by case: v1 => //= w1;rewrite I64.add_zero => -[<-].
Qed.

Lemma saddP ty e1 e2 : Papp2 (Oadd ty) e1 e2 =E sadd ty e1 e2.
Proof. by case:ty;auto using sadd_intP, sadd_wP. Qed.

Lemma ssub_intP e1 e2 : Papp2 (Osub Op_int) e1 e2 =E ssub_int e1 e2.
Proof.
  rewrite /ssub_int. case: (is_constP e1) => [n1| {e1} e1];
    case: (is_constP e2) => [n2| {e2} e2] rho v //=.
  case: eqP => [-> | //];case: sem_pexpr => //= -[] //= z <-.
  by rewrite /sem_op2_i /mk_sem_sop2 /= Z.sub_0_r.
Qed.

Lemma ssub_wP e1 e2 : Papp2 (Osub Op_w) e1 e2 =E ssub_w e1 e2.
Proof.
  rewrite /ssub_w; case: (is_wconstP e1) => [n1| {e1} e1];
    case: (is_wconstP e2) => [n2| {e2} e2] rho v //=.
  + by rewrite /sem_op2_w /mk_sem_sop2 /= iword_subP.
  case:ifP => [/eqP Heq | //].
  apply:rbindP=> v1 ->;rewrite -repr_mod Heq /sem_op2_w /mk_sem_sop2 /=.
  by case: v1 => //= w1;rewrite I64.sub_zero_l => -[<-].
Qed.

Lemma ssubP ty e1 e2 : Papp2 (Osub ty) e1 e2 =E ssub ty e1 e2.
Proof. by case:ty;auto using ssub_intP, ssub_wP. Qed.

Lemma smul_intP e1 e2 : Papp2 (Omul Op_int) e1 e2 =E smul_int e1 e2.
Proof.
  rewrite /smul_int. case: (is_constP e1) => [n1| {e1} e1];
    case: (is_constP e2) => [n2| {e2} e2] rho v //=.
  + case:eqP => [->|_]; first by  case: sem_pexpr => //= -[].
    case:eqP => [->|//];case: sem_pexpr => //= -[] //= z <-.
    by rewrite /sem_op2_i /mk_sem_sop2 [Z.mul]lock /= -lock Z.mul_1_l.
  case:eqP => [->|_].
  + case: sem_pexpr => //= -[] //= z.
    by rewrite /sem_op2_i /mk_sem_sop2 /= Z.mul_0_r.
  case:eqP => [->|//];case: sem_pexpr => //= -[] //= z.
  by rewrite /sem_op2_i /mk_sem_sop2 [Z.mul]lock /= -lock Z.mul_1_r.
Qed.

Lemma smul_wP e1 e2 : Papp2 (Omul Op_w) e1 e2 =E smul_w e1 e2.
Proof.
  rewrite /smul_w; case: (is_wconstP e1) => [n1| {e1} e1];
    case: (is_wconstP e2) => [n2| {e2} e2] rho v //=.
  + by rewrite /sem_op2_w /mk_sem_sop2 /= iword_mulP.
  + case:ifP => [/eqP Heq | _].
    + apply:rbindP=> v2 _;rewrite -repr_mod Heq /sem_op2_w /mk_sem_sop2 /=.
      by apply:rbindP => ? _;rewrite I64.mul_commut I64.mul_zero.
    case:ifP => [/eqP Heq | //=];last by rewrite repr_mod.
    apply:rbindP=> v2 ->;rewrite -repr_mod Heq /sem_op2_w /mk_sem_sop2 /=.
    by case: v2 => //= w2; rewrite I64.mul_commut I64.mul_one.
  case:ifP => [/eqP Heq | _].
  + apply:rbindP=> v1 _;rewrite -repr_mod Heq /sem_op2_w /mk_sem_sop2 /=.
    by apply:rbindP => ? _;rewrite I64.mul_zero.
  case:ifP => [/eqP Heq | //=];last by rewrite repr_mod.
  apply:rbindP=> v1 ->;rewrite -repr_mod Heq /sem_op2_w /mk_sem_sop2 /=.
  by case: v1 => //= w1; rewrite I64.mul_one.
Qed.

Lemma smulP ty e1 e2 : Papp2 (Omul ty) e1 e2 =E smul ty e1 e2.
Proof. by case:ty;auto using smul_intP, smul_wP. Qed.

(* FIXME: move this *)
Lemma eq_exprP s e1 e2 : eq_expr e1 e2 -> sem_pexpr s e1 = sem_pexpr s e2. 
Proof.
  elim: e1 e2=> [z  | b  | e He | x  | x e He | x e He | o e  He | o e1 He1 e2 He2 | e He e1 He1 e2 He2]
                [z' | b' | e'   | x' | x' e'  | x' e'  | o' e' | o' e1' e2' | e' e1' e2'] //=. 
  + by move=> /eqP ->.   + by move=> /eqP ->.
  + by move=> /He ->.    + by move=> /eqP ->.
  + by move=> /andP [] /eqP -> /He ->.
  + by move=> /andP [] /eqP -> /He ->.
  + by move=> /andP[]/eqP -> /He ->.   
  + by move=> /andP[]/andP[] /eqP -> /He1 -> /He2 ->.
  by move=> /andP[]/andP[] /He -> /He1 -> /He2 ->.
Qed.

Lemma mk_sem_sop2_b b t (o:sem_t t -> sem_t t -> bool) :
   (forall v, o v v = b) ->
   forall v v', @mk_sem_sop2 t t sbool o v v = ok v' -> v' = Vbool b.
Proof.
  by move=> Ho v v';apply: rbindP=> z -> [];rewrite Ho => ->.
Qed.
  
Lemma s_eqP ty e1 e2 : Papp2 (Oeq ty) e1 e2 =E s_eq ty e1 e2.
Proof.
  rewrite /s_eq;case:ifP => [ /eq_exprP Hs s v /=| _ ];last by auto.
  rewrite Hs;case: sem_pexpr => //= ve.
  by case: ty => /(@mk_sem_sop2_b true) -> // ?;
    rewrite (Z.eqb_refl, weq_refl).
Qed.

Lemma sneqP ty e1 e2 : Papp2 (Oneq ty) e1 e2 =E sneq ty e1 e2.
Proof.
  rewrite /sneq;case:ifP => [ /eq_exprP Hs s v /=| _ ];last by auto.
  rewrite Hs;case: sem_pexpr => //= ve.
  by case: ty => /(@mk_sem_sop2_b false) -> // ?;
    rewrite (Z.eqb_refl, weq_refl).
Qed.

Lemma sltP ty e1 e2 : Papp2 (Olt ty) e1 e2 =E slt ty e1 e2.
Proof.
  rewrite /slt;case:ifP => [ /eq_exprP Hs s v /=| _ ].
  + rewrite Hs;apply: rbindP => v' -> /=.
    by case: ty =>  /(@mk_sem_sop2_b false) -> // ?;
      rewrite (Z.ltb_irrefl, wslt_irrefl, wult_irrefl).
  case: (is_constP e1) => [n1| {e1} e1];last by auto.
  case: (is_constP e2) => [n2 ?? /=| {e2} e2];last by auto.
  by case: ty.
Qed.

Lemma sleP ty e1 e2 : Papp2 (Ole ty) e1 e2 =E sle ty e1 e2.
Proof.
  rewrite /sle; case:ifP => [ /eq_exprP Hs s v /=| _ ].
  + rewrite Hs;apply: rbindP => v' -> /=.
    by case: ty =>  /(@mk_sem_sop2_b true) -> // ?;
      rewrite (Z.leb_refl, wsle_refl, wule_refl).
  case: (is_constP e1) => [n1| {e1} e1];last by auto.
  case: (is_constP e2) => [n2 ?? /=| {e2} e2];last by auto.
  by case: ty.
Qed.

Lemma sgtP ty e1 e2 : Papp2 (Ogt ty) e1 e2 =E sgt ty e1 e2.
Proof.
  rewrite /sgt;case:ifP => [ /eq_exprP Hs s v /=| _ ].
  + rewrite Hs;apply: rbindP => v' -> /=.
    by case: ty =>  /(@mk_sem_sop2_b false) -> // ?;
      rewrite ?Z.gtb_ltb (Z.ltb_irrefl, wslt_irrefl, wult_irrefl).
  case: (is_constP e1) => [n1| {e1} e1];last by auto.
  case: (is_constP e2) => [n2 ?? /=| {e2} e2];last by auto.
  by case: ty.
Qed.

Lemma sgeP ty e1 e2 : Papp2 (Oge ty) e1 e2 =E sge ty e1 e2.
Proof.
  rewrite /sge; case:ifP => [ /eq_exprP Hs s v /=| _ ].
  + rewrite Hs;apply: rbindP => v' -> /=.
    by case: ty =>  /(@mk_sem_sop2_b true) -> // ?;
      rewrite ?Z.geb_leb (Z.leb_refl, wsle_refl, wule_refl).
  case: (is_constP e1) => [n1| {e1} e1];last by auto.
  case: (is_constP e2) => [n2 ?? /=| {e2} e2];last by auto.
  by case: ty.
Qed.

Lemma slandP e1 e2 : Papp2 Oland e1 e2 =E sland e1 e2. Proof. auto. Qed.
Lemma slorP e1 e2  : Papp2 Olor  e1 e2 =E slor  e1 e2. Proof. auto. Qed.
Lemma slxorP e1 e2 : Papp2 Olxor e1 e2 =E slxor e1 e2. Proof. auto. Qed.
Lemma slslP e1 e2  : Papp2 Olsl  e1 e2 =E slsl  e1 e2. Proof. auto. Qed.
Lemma slsrP e1 e2  : Papp2 Olsr  e1 e2 =E slsr  e1 e2. Proof. auto. Qed.
Lemma sasrP e1 e2  : Papp2 Oasr  e1 e2 =E sasr  e1 e2. Proof. auto. Qed.

Lemma s_op2P o e1 e2 : Papp2 o e1 e2 =E s_op2 o e1 e2.
Proof.
  case: o;eauto using sandP, sorP, saddP, smulP, ssubP, s_eqP, sneqP, sltP, sleP, sgtP, sgeP,
      slandP, slorP, slxorP, slslP, slsrP, sasrP.
Qed.

Lemma s_ifP e e1 e2 : Pif e e1 e2 =E s_if e e1 e2.
Proof.
  rewrite /s_if;case: is_boolP => [b | ];last by auto.
  by case: b => ?? /=.
Qed.

Definition valid_cpm (vm: vmap)  (m:cpm) := 
  forall x n, Mvar.get m x = Some n -> get_var vm x = ok (Vint n).

Lemma const_prop_eP (e:pexpr) s (m:cpm):  
  valid_cpm (evm s) m ->
  e =[s] const_prop_e m e.
Proof.
  move=> Hvalid;rewrite /eqok.
  elim: e=> [z | b | e He | x | x e He | x e He | o e He | o e1 He1 e2 He2 | e He e1 He1 e2 He2] v //=.
  + by case Heq: sem_pexpr => [ve|] //=;rewrite (He _ Heq).
  + by case Heq: Mvar.get => [n|] //=;rewrite (Hvalid _ _ Heq).
  + apply:on_arr_varP;rewrite /on_arr_var => n t ? -> /=.
    by apply: rbindP => ?;apply: rbindP => ? /He -> /= ->.  
  + apply:rbindP => w -> /=.
    by case Heq: sem_pexpr => [ve|] //=;rewrite (He _ Heq).
  + move=> H;apply /s_op1P;move: H => /=.
    by apply:rbindP => ve1 /He ->.
  + move=> H;apply /s_op2P;move: H => /=.
    by apply:rbindP => ve1 /He1 ->;apply:rbindP => ve2 /He2 ->.
  move=> H;apply /s_ifP;move: H => /=.
  apply:rbindP => b;apply:rbindP => w /He -> /= -> /=.
  by case: b;auto.
Qed.

Definition eqoks (e1 e2:seq pexpr) st := 
  forall v, sem_pexprs st e1 = ok v -> sem_pexprs st e2 = ok v.

Lemma const_prop_esP es s m vs: 
  valid_cpm (evm s) m ->
  sem_pexprs s es = ok vs -> sem_pexprs s (map (const_prop_e m) es) = ok vs.
Proof.
  move=> Hv;elim: es vs => //= e es Hrec /= vs.
  rewrite /sem_pexprs /=;apply : rbindP => v /(const_prop_eP Hv) ->.
  by apply: rbindP => vs' /Hrec /=;rewrite /sem_pexprs => -> [] <-.
Qed.

Lemma remove_cpm1P x v m s1 s1' : 
  write_var x v s1 = ok s1' ->
  valid_cpm (evm s1) m ->
  valid_cpm (evm s1') (Mvar.remove m x).
Proof.
  move=> Hw Hv z n;rewrite Mvar.removeP;case: ifPn => //= ? /Hv.
  move: Hw;apply: rbindP => vm;apply: rbindP => w ? [<-] [<-].
  by rewrite /get_var /=;rewrite Fv.setP_neq.
Qed.

Lemma add_cpmP s1 s1' m x e tag v : 
  sem_pexpr s1 e = ok v -> 
  write_lval x v s1 = ok s1' ->
  valid_cpm (evm s1') m -> 
  valid_cpm (evm s1') (add_cpm m x tag e).
Proof.
  rewrite /add_cpm;case: x => [xi | x | x | x] //= He.
  case: tag => //.
  case: is_constP He => //= n [<-].
  case: x => -[] [] //= xn vi [] <- /= Hv z /= n0.
  have := Hv z n0.
  case: ({| vtype := sint; vname := xn |} =P z).
  + move=> <- /=;rewrite Mvar.setP_eq=> ? -[] <-;by rewrite /get_var Fv.setP_eq.
  by move=> /eqP Hneq;rewrite Mvar.setP_neq.
Qed.

Lemma merge_cpmP rho m1 m2 : 
  valid_cpm rho m1 \/ valid_cpm rho m2 ->  
  valid_cpm rho (merge_cpm m1 m2).
Proof.
  move=> Hv x n;rewrite /merge_cpm Mvar.map2P //. 
  case Heq1 : (Mvar.get m1 x) => [n1|//]; case Heq2 : (Mvar.get m2 x) => [n2|//].
  case: eqP=> //.
  by move=> ? [] ?;do 2 subst;elim: Hv => Hv;apply Hv.
Qed.

Lemma const_prop_rvP s1 s2 m x v: 
  valid_cpm (evm s1) m ->
  write_lval x v s1 = Ok error s2 ->
  valid_cpm (evm s2) (const_prop_rv m x).1 /\
  write_lval (const_prop_rv m x).2 v s1 = ok s2.
Proof.
  case:x => [ii | x | x p | x p] /= Hv.
  + by move=> [<-].
  + by move=> H;split=>//;apply: remove_cpm1P H Hv.
  + apply: rbindP => z Hz;rewrite Hz /=.
    apply: rbindP => z'.
    apply: rbindP => z'' /(@const_prop_eP p _ _ Hv) -> /= -> /=.
    by apply: rbindP => w -> /=;apply: rbindP => m' -> [<-].
  apply: on_arr_varP;rewrite /on_arr_var => n t Htx -> /=. 
  apply: rbindP => z;apply: rbindP => z'' /(@const_prop_eP p _ _ Hv) -> /= -> /=.
  apply: rbindP => w -> /=;apply: rbindP => t' -> /=.
  apply: rbindP => vm Hvm [<-];rewrite Hvm;split=>//=.
  have H : write_var x (Varr t') s1 = ok (Estate (emem s1) vm) by rewrite /write_var Hvm.
  by apply: remove_cpm1P H Hv.
Qed.

Lemma const_prop_rvsP s1 s2 m x v: 
  valid_cpm (evm s1) m ->
  write_lvals s1 x v = Ok error s2 ->
  valid_cpm (evm s2) (const_prop_rvs m x).1 /\
  write_lvals s1 (const_prop_rvs m x).2 v = ok s2.
Proof.
  elim: x v m s1 s2 => [ | x xs Hrec] [ | v vs] //= m s1 s2 Hm.
  + by move=> [<-].
  apply: rbindP => s1' Hw Hws.
  have [/=]:= const_prop_rvP Hm Hw.
  case Hx : const_prop_rv => [m1 rv'] /= Hm1 Hw'.
  have [/=]:= Hrec _ _ _ _ Hm1 Hws.
  by case Hxs : const_prop_rvs => [m2 rvs'] /= ?;rewrite Hw'.
Qed.

Lemma remove_cpm_spec (m : cpm) (xs : Sv.t) (x : CmpVar.t):
  match Mvar.get (remove_cpm m xs) x with 
  | Some n => Mvar.get m x = Some n /\ ~ Sv.In x xs
  | None   => Mvar.get m x = None \/ Sv.In x xs
  end.
Proof.
  rewrite /remove_cpm;apply SvP.MP.fold_rec_bis. 
  + move=> s s' a Heq.
    by case: Mvar.get=> [? [] ??| [? | ?]]; [split=> //;SvD.fsetdec | left | right;SvD.fsetdec].
  + by case: Mvar.get=> [? | ]; [ split => //;SvD.fsetdec | left].
  move=> ?????;rewrite Mvar.removeP;case:ifPn => /eqP Heq.
  + by rewrite Heq=> _;right;SvD.fsetdec. 
  by case: Mvar.get=> [? [] ??| [?|?]];[split=> //;SvD.fsetdec | left | SvD.fsetdec]. 
Qed.

Lemma remove_cpm2 m xs : Mvar_eq (remove_cpm (remove_cpm m xs) xs) (remove_cpm m xs). 
Proof.
  move=> z;have := remove_cpm_spec (remove_cpm m xs) xs z.
  case: Mvar.get=> [? [] | [ | ]] // Hin.   
  have := remove_cpm_spec m xs z.
  by case: Mvar.get=> // ? [] _ H;elim H.
Qed.

Lemma get_remove_cpm m xs x n: 
  Mvar.get (remove_cpm m xs) x = Some n ->  
  Mvar.get m x = Some n /\ ~Sv.In x xs.
Proof. by move=> H;have := remove_cpm_spec m xs x;rewrite H. Qed.

Lemma valid_cpm_rm rho1 rho2 xs m:
  rho1 = rho2 [\ xs] ->
  valid_cpm rho1 m ->
  valid_cpm rho2 (remove_cpm m xs).
Proof.
  move=> Hrho Hval x nx /get_remove_cpm [] Hm Hin.
  rewrite /get_var -Hrho //;apply (Hval _ _ Hm). 
Qed.

Lemma remove_cpmP s s' m x v: 
  write_lval x v s = ok s' ->
  valid_cpm (evm s) m ->
  valid_cpm (evm s') (remove_cpm m (vrv x)).
Proof. move=> Hw Hv; apply: (valid_cpm_rm _ Hv);eapply vrvP;eauto. Qed.

Instance const_prop_e_m : 
  Proper (@Mvar_eq Z ==> eq ==> eq) const_prop_e.
Proof.
  move=> m1 m2 Hm e e' <- {e'}.
  elim: e => //=.
  + by move=> ? ->.
  + by move=> ?;rewrite Hm.
  + by move=> ?? ->.
  + by move=> ?? ->.
  + by move=> ?? ->.
  + by move=> ?? -> ? ->.
  by move=> ? -> ? -> ? ->.
Qed.

Instance const_prop_rv_m : 
  Proper (@Mvar_eq Z ==> eq ==> RelationPairs.RelProd (@Mvar_eq Z) eq) const_prop_rv.
Proof.
  move=> m1 m2 Hm rv rv' <- {rv'}.
  by case: rv => [ v | v | v p | v p] //=;rewrite Hm.
Qed.

Instance const_prop_rvs_m : 
  Proper (@Mvar_eq Z ==> eq ==> RelationPairs.RelProd (@Mvar_eq Z) eq) const_prop_rvs.
Proof.
  move=> m1 m2 Hm rv rv' <- {rv'}.
  elim: rv m1 m2 Hm => //= rv rvs Hrec m1 m2 Hm.
  have [/=]:= const_prop_rv_m Hm (refl_equal rv).
  case: const_prop_rv => ??;case: const_prop_rv => ??.
  rewrite /RelationPairs.RelCompFun /= => /Hrec H ->.
  case: const_prop_rvs H => ??;case: const_prop_rvs => ?? [].
  by rewrite /RelationPairs.RelCompFun /= => -> ->.
Qed.

Instance add_cpm_m : 
  Proper (@Mvar_eq Z ==> eq ==> eq ==> eq ==> @Mvar_eq Z) add_cpm.
Proof.
  move=> m1 m2 Hm x x' <- {x'} t t' <- {t'} e e' <- {e'}.
  case: x t => //= v [];rewrite ?Hm //.
  by case: is_const => [n | ];rewrite Hm.
Qed.

Instance merge_cpm_m : 
  Proper (@Mvar_eq Z ==> @Mvar_eq Z ==> @Mvar_eq Z) merge_cpm.
Proof.
  move=> m1 m2 Hm m1' m2' Hm' z;rewrite /merge_cpm.
  set f :=(X in Mvar.map2 X).
  have Hz : f z None None = None => //.
  have -> := Mvar.map2P m1 m1' Hz.
  have -> := Mvar.map2P m2 m2' Hz.
  by rewrite Hm Hm'. 
Qed.

Instance remove_cpm_m : 
  Proper (@Mvar_eq Z ==> Sv.Equal ==> @Mvar_eq Z) remove_cpm.
Proof.
  move=> m1 m2 Hm s1 s2 Hs z.
  case: Mvar.get (remove_cpm_spec m1 s1 z) => [? |];
   case: Mvar.get (remove_cpm_spec m2 s2 z) => [? |] => //.
  + by rewrite Hm => -[] -> _ [[]] ->.
  + by rewrite Hm Hs => -[ -> | ? ] [].
  by rewrite Hm Hs => -[] -> ? [] .
Qed.

Definition Mvarc_eq T := RelationPairs.RelProd (@Mvar_eq T) (@eq cmd).

Section PROPER.

  Let Pr (i:instr_r) := 
    forall ii m1 m2, Mvar_eq m1 m2 -> Mvarc_eq (const_prop_ir m1 ii i) (const_prop_ir m2 ii i).

  Let Pi (i:instr) := 
    forall m1 m2, Mvar_eq m1 m2 -> Mvarc_eq (const_prop_i m1 i) (const_prop_i m2 i).

  Let Pc (c:cmd) := 
    forall m1 m2, Mvar_eq m1 m2 -> 
    Mvarc_eq (const_prop const_prop_i m1 c) (const_prop const_prop_i m2 c).

  Local Lemma Wmk i ii: Pr i -> Pi (MkI ii i).
  Proof. by move=> Hi m1 m2;apply Hi. Qed.

  Local Lemma Wnil : Pc [::].
  Proof. by move=> m1 m2 /= ->. Qed.

  Local Lemma Wcons i c:  Pi i -> Pc c -> Pc (i::c). 
  Proof.
    move=> Hi Hc m1 m2 /= /Hi.
    case: const_prop_i => m1' i'; case: const_prop_i => m2' i'' [] /Hc.
    rewrite /RelationPairs.RelCompFun /=.
    case: const_prop => m1'' c'; case: const_prop => m2'' c'' [].
    by rewrite /RelationPairs.RelCompFun /= => -> -> ->.
  Qed.

  Local Lemma Wasgn x t e: Pr (Cassgn x t e).
  Proof.
    move=> ii m1 m2 /= Heq; have := const_prop_rv_m Heq (refl_equal x).
    case: const_prop_rv => ??;case: const_prop_rv => ?? [].
    rewrite /RelationPairs.RelCompFun /= => -> ->.
    by split => //=; rewrite /RelationPairs.RelCompFun /= Heq.
  Qed.

  Local Lemma Wopn xs o es: Pr (Copn xs o es).
  Proof.
    move=> ii m1 m2 Heq /=;have := const_prop_rvs_m Heq (refl_equal xs).
    case: const_prop_rvs => ??;case: const_prop_rvs => ?? [].
    rewrite /RelationPairs.RelCompFun /= => -> ->.
    split => //=; rewrite /RelationPairs.RelCompFun /=.
    by do 3 f_equal;apply eq_in_map=> z _;rewrite Heq.
  Qed.

  Local Lemma Wif e c1 c2: Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> Hc1 Hc2 ii m1 m2 Heq /=.
    have -> : const_prop_e m1 e = const_prop_e m2 e by rewrite Heq.
    case: is_bool=> [ [] | ].    
    + by apply Hc1.
    + by apply Hc2.
    have := Hc1 _ _ Heq; have := Hc2 _ _ Heq.
    do 4 case const_prop => ??.
    move=> [];rewrite /RelationPairs.RelCompFun /= => -> ->.
    by move=> [];rewrite /RelationPairs.RelCompFun /= => -> ->.
  Qed.

  Local Lemma Wfor v dir lo hi c: Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Proof.
    move=> Hc ii m1 m2 Heq /=.
    have -> : const_prop_e m1 lo = const_prop_e m2 lo by rewrite Heq.
    have -> : const_prop_e m1 hi = const_prop_e m2 hi by rewrite Heq.
    set ww1 := remove_cpm _ _; set ww2 := remove_cpm _ _.
    have Hw: Mvar_eq ww1 ww2 by rewrite /ww1 /ww2 Heq.
    move: (Hw) => /Hc; case: const_prop => ??; case: const_prop => ?? [].
    by rewrite /RelationPairs.RelCompFun /= Hw => _ ->.
  Qed.

  Local Lemma Wwhile c e c': Pc c -> Pc c' -> Pr (Cwhile c e c').
  Proof.
    move=> Hc Hc' ii m1 m2 Heq /=.
    set ww1 := remove_cpm _ _;set ww2 := remove_cpm _ _. 
    have Hw: Mvar_eq ww1 ww2 by rewrite /ww1 /ww2 Heq.
    move: (Hw) => /Hc; case: const_prop => ??; case: const_prop => ?? [].
    rewrite /RelationPairs.RelCompFun /= => _ ->.
    move: (Hw) => /Hc'; case: const_prop => ??; case: const_prop => ?? [].
    rewrite /RelationPairs.RelCompFun /= => _ ->.
    by have -> : const_prop_e ww1 e = const_prop_e ww2 e by rewrite Hw.
  Qed.

  Local Lemma Wcall i xs f es: Pr (Ccall i xs f es).
  Proof.
    move=> ii m1 m2 Heq /=;have := const_prop_rvs_m Heq (refl_equal xs).
    case: const_prop_rvs => ??;case: const_prop_rvs => ?? [].
    rewrite /RelationPairs.RelCompFun /= => -> ->.
    split => //=; rewrite /RelationPairs.RelCompFun /=.
    by do 3 f_equal;apply eq_in_map=> z _;rewrite Heq.
  Qed.

End PROPER.

Lemma const_prop_i_m : 
  Proper (@Mvar_eq Z ==> eq ==> @Mvarc_eq Z) const_prop_i. 
Proof.
  move=> m1 m2 Hm i1 i2 <-.
  apply : (instr_Rect Wmk Wnil Wcons Wasgn Wopn Wif Wfor Wwhile Wcall i1) Hm.
Qed.

Lemma const_prop_i_r_m : 
  Proper (@Mvar_eq Z ==> eq ==> eq ==> @Mvarc_eq Z) const_prop_ir. 
Proof.
  move=> m1 m2 Hm ii1 ii2 <- i1 i2 <-.
  apply : (instr_r_Rect Wmk Wnil Wcons Wasgn Wopn Wif Wfor Wwhile Wcall i1) Hm.
Qed.

Lemma const_prop_m : 
  Proper (@Mvar_eq Z ==> eq ==> @Mvarc_eq Z) (const_prop const_prop_i). 
Proof.
  move=> m1 m2 Hm c1 c2 <-.
  apply : (cmd_rect Wmk Wnil Wcons Wasgn Wopn Wif Wfor Wwhile Wcall c1) Hm.
Qed.

Lemma valid_cpm_m : 
  Proper (eq ==> @Mvar_eq Z ==> iff) valid_cpm. 
Proof.
  move=> s? <- m m' Hm;split => H z n Hget;apply H.
  by rewrite Hm. by rewrite -Hm.
Qed.

Section PROOF.

  Variable p:prog.

  Let p' := const_prop_prog p.

  Let Pi s (i:instr) s':= 
    forall m, 
      valid_cpm s.(evm) m ->
      valid_cpm s'.(evm) (const_prop_i m i).1 /\
      sem p' s (const_prop_i m i).2 s'.

  Let Pi_r s (i:instr_r) s':= 
    forall m ii, 
      valid_cpm s.(evm) m ->
      valid_cpm s'.(evm) (const_prop_ir m ii i).1 /\
      sem p' s (const_prop_ir m ii i).2 s'.

  Let Pc s (c:cmd) s':= 
    forall m, 
      valid_cpm s.(evm) m ->
      valid_cpm s'.(evm) (const_prop const_prop_i m c).1 /\
      sem p' s (const_prop const_prop_i m c).2 s'.

  Let Pfor (i:var_i) vs s c s' :=
    forall m, 
      Mvar_eq m (remove_cpm m (Sv.union (Sv.singleton i) (write_c c))) ->
      valid_cpm s.(evm) m ->
      sem_for p' i vs s (const_prop const_prop_i m c).2 s'.

  Let Pfun (mem:Memory.mem) fn vargs (mem':Memory.mem) vres :=
    sem_call p' mem fn vargs mem' vres.

  Local Lemma Hskip s: Pc s [::] s.
  Proof. move=> m /= ?;split=>//; constructor. Qed.

  Local Lemma Hcons s1 s2 s3 i c :
    sem_I p s1 i s2 ->
    Pi s1 i s2 -> sem p s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
  Proof.
    move=> _ Hi _ Hc m /Hi [] /=.
    case: const_prop_i => m' i' /Hc [].
    case: const_prop => m'' c' /= Hm'' Hc' Hi';split=> //.
    by apply: sem_app Hi' Hc'.
  Qed.

  Local Lemma HmkI ii i s1 s2 :
    sem_i p s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
  Proof. by move=> _ Hi m /(Hi _ ii). Qed.
 
  Local Lemma Hassgn s1 s2 x tag e :
    Let v := sem_pexpr s1 e in write_lval x v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn x tag e) s2.
  Proof.
    apply: rbindP => v He Hw m ii /= Hm. 
    have H := const_prop_eP Hm He; have [] := const_prop_rvP Hm Hw.
    case: const_prop_rv => m' x' /= Hm' Hw';split;first by eapply add_cpmP;eauto.
    by apply sem_seq1;constructor;constructor;rewrite H.
  Qed.

  Local Lemma Hopn s1 s2 o xs es : 
    Let x := Let x := sem_pexprs s1 es in sem_sopn o x
    in write_lvals s1 xs x = Ok error s2 -> Pi_r s1 (Copn xs o es) s2.
  Proof.
    move=> H m ii Hm; apply: rbindP H => vs.
    apply: rbindP => ves Hes Ho Hw;move: (Hes) (Hw).
    move=> /(const_prop_esP Hm) Hes' /(const_prop_rvsP Hm) [] /=.
    case: const_prop_rvs => m' rvs' /= ??;split=>//.
    by apply sem_seq1;do 2 constructor;rewrite Hes' /= Ho.
  Qed.

  Local Lemma Hif_true s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem p s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move => He _ Hc1 m ii Hm.
    apply: rbindP He => v /(const_prop_eP Hm) He /=.
    case : is_boolP He => [b [] <- [] ->| {e} e He Hv];first by apply Hc1.
    case: (Hc1 _ Hm).
    case Heq1 : const_prop => [m1 c0]; case Heq2 : const_prop => [m2 c3] /= Hval Hs;split.
    + by apply merge_cpmP;left.
    by apply sem_seq1; do 2 constructor=> //;rewrite He.
  Qed.

  Local Lemma Hif_false s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error false ->
    sem p s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move => He _ Hc2 m ii Hm.
    apply: rbindP He => v /(const_prop_eP Hm) He /=.
    case: is_boolP He => [b [] <- [] -> | {e} e He Hv];first by apply Hc2.
    case: (Hc2 _ Hm).
    case Heq1 : const_prop => [m1 c0]; case Heq2 : const_prop => [m2 c3] /= Hval Hs;split.
    + by apply merge_cpmP;right.
    by apply sem_seq1; constructor;apply Eif_false=> //;rewrite He.
  Qed.
    
  Local Lemma Hwhile_true s1 s2 s3 s4 c e c':
    sem p s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr s2 e in to_bool x = Ok error true ->
    sem p s2 c' s3 -> Pc s2 c' s3 ->
    sem_i p s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4 -> 
    Pi_r s1 (Cwhile c e c') s4.
  Proof.
    move=> Hc1 Hc He Hc1' Hc' Hw1 Hw m ii Hm.
    apply: rbindP He => v He /= Hv.
    set ww := write_i _;set m' := remove_cpm _ _.
    case Heq1: const_prop => [m'' c0] /=.
    case Heq2: const_prop => [m_ c0'] /=;split.
    + apply: valid_cpm_rm Hm.
      by apply (@write_iP p); apply: (Ewhile_true Hc1) Hc1' Hw1;rewrite He. 
    apply sem_seq1;constructor.
    have Hm'1 : valid_cpm (evm s1) m' by apply: valid_cpm_rm Hm.
    case: (Hc m')=> //; rewrite Heq1 /= => _ Hc''.
    have Hm'2 : valid_cpm (evm s2) m'.
    + apply: valid_cpm_rm Hm;rewrite /ww write_i_while.
      by apply: vmap_eq_exceptI (writeP Hc1);SvD.fsetdec.
    case: (Hc' m')=> //; rewrite Heq2 /= => _ Hc'''.
    case: (Hw m' ii). 
    + apply: valid_cpm_rm Hm. rewrite /ww write_i_while -write_c_app.
      by apply: (@writeP p);apply: sem_app Hc1 Hc1'.
    move=> _ Hw'; apply Ewhile_true with s2 s3 => //.
    + by move: He=> /(const_prop_eP Hm'2) ->.
    have H1 := remove_cpm2 m ww; move: Hw'.
    have /= : Mvarc_eq (const_prop const_prop_i (remove_cpm m' (write_i (Cwhile c e c'))) c)
               (m'', c0).
    + by have := const_prop_m H1 (refl_equal c); rewrite Heq1.
    case: const_prop => ??.
    have /= : Mvarc_eq (const_prop const_prop_i (remove_cpm m' (write_i (Cwhile c e c'))) c')
               (m_, c0').
    + by have := const_prop_m H1 (refl_equal c'); rewrite Heq2.
    have -> /=: const_prop_e (remove_cpm m' (write_i (Cwhile c e c'))) e = 
              const_prop_e m' e.
    + by rewrite H1.
    case: const_prop => ??.
    move=> [] /=;rewrite /RelationPairs.RelCompFun /= => _ ->.
    move=> [] /=;rewrite /RelationPairs.RelCompFun /= => _ -> Hw'.
    by sinversion Hw';sinversion H5; sinversion H3.
  Qed.

  Local Lemma Hwhile_false s1 s2 c e c':
    sem p s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr s2 e in to_bool x = Ok error false ->
    Pi_r s1 (Cwhile c e c') s2.
  Proof.
    move=> Hc1 Hc He m ii Hm.
    apply: rbindP He => v He /= Hv.
    set ww := write_i _;set m' := remove_cpm _ _.
    case Heq1: const_prop => [m'' c0] /=.
    have Hm'1:  valid_cpm (evm s1) m' by apply: valid_cpm_rm Hm.
  
    have Hm'2:  valid_cpm (evm s2) m'.
    + apply: valid_cpm_rm Hm;rewrite /ww write_i_while.
      by apply: vmap_eq_exceptI (writeP Hc1);SvD.fsetdec.
    case Heq2: const_prop => [m_  c0'] /=;split=>//.
    apply sem_seq1;constructor;apply: Ewhile_false.
    + by case (Hc m') => //;rewrite Heq1.
    by move: He=> /(const_prop_eP Hm'2) ->.
  Qed.
 
  Local Lemma Hfor s1 s2 (i:var_i) d lo hi c vlo vhi :
    Let x := sem_pexpr s1 lo in to_int x = Ok error vlo ->
    Let x := sem_pexpr s1 hi in to_int x = Ok error vhi ->
    sem_for p i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.
  Proof.
    move=> Hlo Hhi Hc Hfor m ii Hm /=.
    set ww := write_i _;set m' := remove_cpm _ _.
    have Hm'1 : valid_cpm (evm s1) m' by apply: valid_cpm_rm Hm.
    have Heqm: Mvar_eq m' (remove_cpm m' (Sv.union (Sv.singleton i) (write_c c))).
    + by have := remove_cpm2 m ww; rewrite /m' /ww write_i_for => ->.
    have := Hfor _ Heqm Hm'1.      
    case Heq1: const_prop => [m'' c'] /= Hsem;split.
    + by apply: valid_cpm_rm Hm;apply (@write_iP p);econstructor;eauto.
    apply sem_seq1;constructor;econstructor.
    + by apply: rbindP Hlo => v /(const_prop_eP Hm) -> /=;eauto.
    + by apply: rbindP Hhi => v /(const_prop_eP Hm) -> /=;eauto.
    done.
  Qed.

  Local Lemma Hfor_nil s i c: Pfor i [::] s c s.
  Proof. by move=> m Hm;constructor. Qed.

  Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w:Z) (ws:seq Z) c :
    write_var i w s1 = Ok error s1' ->
    sem p s1' c s2 ->
    Pc s1' c s2 ->
    sem_for p i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
  Proof.
    move => Hw Hsemc Hc Hsemf Hf m Heqm Hm.
    have Hm' : valid_cpm (evm s1') m.
    + have Hmi : Mvar_eq m (Mvar.remove m i).
      + move=> z;rewrite Mvar.removeP;case:ifPn => [/eqP <- | Hneq //]. 
        rewrite Heqm;move: (remove_cpm_spec m (Sv.union (Sv.singleton i) (write_c c)) i).
        by case: Mvar.get => // a [];SvD.fsetdec.
      have -> := valid_cpm_m (refl_equal (evm s1')) Hmi.
      by apply: remove_cpm1P Hw Hm.
    have [_ Hc']:= Hc _ Hm'.        
    have /(Hf _ Heqm) : valid_cpm (evm s2) m.
    + have -> := valid_cpm_m (refl_equal (evm s2)) Heqm.
      apply: valid_cpm_rm Hm'=> z Hz;apply: (writeP Hsemc);SvD.fsetdec. 
    by apply: EForOne Hc'.
  Qed.

  Local Lemma Hcall s1 m2 s2 ii xs fn args vargs vs:
    sem_pexprs s1 args = Ok error vargs ->
    sem_call p (emem s1) fn vargs m2 vs ->
    Pfun (emem s1) fn vargs m2 vs ->
    write_lvals {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
    Pi_r s1 (Ccall ii xs fn args) s2.
  Proof.
    move=> Hargs Hcall Hfun Hvs m ii' Hm.
    have Hargs' := const_prop_esP Hm Hargs.
    have /(_ _ Hm) [] /=:= const_prop_rvsP _ Hvs.
    case: const_prop_rvs => m' rvs' /= ??;split=>//.
    by apply sem_seq1;constructor;econstructor;eauto.
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
    have := (@get_map_prog _ _ const_prop_fun p fn);rewrite Hget /=.
    have : valid_cpm (evm s1) empty_cpm by move=> x n;rewrite Mvar.get0.
    move=> /Hc [];case: const_prop;econstructor;eauto.
  Qed.

  Lemma const_prop_callP f mem mem' va vr: 
    sem_call p mem f va mem' vr -> 
    sem_call p' mem f va mem' vr.
  Proof.
    apply (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End PROOF.
