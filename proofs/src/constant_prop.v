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
Require Import JMeq Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import  ZArith.

Require Import Coq.Logic.Eqdep_dec.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr 
               memory dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
Local Open Scope vmap_scope.
(* -------------------------------------------------------------------------- *)
(* ** Smart constructors                                                      *)
(* -------------------------------------------------------------------------- *)

Definition snot (e:pexpr) : pexpr := 
  match e with
  | Pbool b => negb b
  | Pnot  e => e 
  | _       => Pnot e
  end.

Definition sand e1 e2 := 
  match is_bool e1, is_bool e2 with
  | Some b, _ => if b then e2 else false
  | _, Some b => if b then e1 else false
  | _, _      => Papp2 Oand e1 e2
  end.

Definition sor e1 e2 := 
   match is_bool e1, is_bool e2 with
  | Some b, _ => if b then Pbool true else e2
  | _, Some b => if b then Pbool true else e1
  | _, _       => Papp2 Oor e1 e2 
  end.


Definition sadd e1 e2:= 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 + n2)
  | Some n, _ => 
    if (n == 0)%Z then e2 else Papp2 Oadd e1 e2
  | _, Some n => 
    if (n == 0)%Z then e1 else Papp2 Oadd e1 e2
  | _, _ => Papp2 Oadd e1 e2
  end.

Definition ssub e1 e2 := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 - n2)
  | _, Some n => 
    if (n == 0)%Z then e1 else Papp2 Osub e1 e2
  | _, _ => Papp2 Osub e1 e2
  end.

Definition smul e1 e2:= 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pconst (n1 * n2)
  | Some n, _ => 
    if (n == 0)%Z then Pconst 0
    else if (n == 1)%Z then e2 
    else Papp2 Omul e1 e2
  | _, Some n => 
    if (n == 0)%Z then Pconst 0
    else if (n == 1)%Z then e1
    else Papp2 Omul e1 e2
  | _, _ => Papp2 Omul e1 e2
  end.

Definition s_eq e1 e2 := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pbool (n1 == n2)
  | _, _             => 
    if (e1 == e2) then Pbool true else Papp2 Oeq e1 e2
  end.

Definition sneq e1 e2 := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pbool (n1 != n2)
  | _, _             => 
    if (e1 == e2) then Pbool false else Papp2 Oneq e1 e2
  end.

Definition slt e1 e2 := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pbool (n1 <? n2)%Z
  | _        , _         => 
    if (e1 == e2) then Pbool false 
    else Papp2 Olt e1 e2 
  end.

Definition sle e1 e2 := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pbool (n1 <=? n2)%Z
  | _        , _     => 
    if (e1 == e2) then Pbool true
    else Papp2 Ole e1 e2 
  end.

Definition sgt e1 e2 := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pbool (n1 >? n2)%Z
  | _        , _         => 
    if (e1 == e2) then Pbool false 
    else Papp2 Ogt e1 e2 
  end.

Definition sge e1 e2 := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => Pbool (n1 >=? n2)%Z
  | _        , _     => 
    if (e1 == e2) then Pbool true
    else Papp2 Oge e1 e2 
  end.

Definition s_op2 o e1 e2 := 
  match o with 
  | Oand        => sand e1 e2 
  | Oor         => sor  e1 e2
  | Oadd        => sadd e1 e2
  | Osub        => ssub e1 e2
  | Omul        => smul e1 e2
  | Oeq         => s_eq e1 e2
  | Oneq        => sneq e1 e2
  | Olt         => slt  e1 e2
  | Ole         => sle  e1 e2
  | Ogt         => sgt  e1 e2
  | Oge         => sge  e1 e2
  end.

(* ** constant propagation 
 * -------------------------------------------------------------------- *)

Local Notation vmap := (Mvar.t Z).

Fixpoint const_prop_e (m:vmap) e :=
  match e with
  | Pconst _  => e
  | Pbool  _  => e
  | Pcast e   => Pcast (const_prop_e m e)
  | Pvar  x   => if Mvar.get m x is Some n then Pconst n else e
  | Pget  x e => Pget x (const_prop_e m e)
  | Pload x e => Pload x (const_prop_e m e)
  | Pnot  e   => snot e
  | Papp2 o e1 e2 => s_op2 o e1 e2
  end.

Definition empty_cpm : vmap := @Mvar.empty Z.

Definition merge_cpm : vmap -> vmap -> vmap := 
  Mvar.map2 (fun _ (o1 o2: option Z) => 
   match o1, o2 with
   | Some n1, Some n2 => 
     if (n1 == n2)%Z then Some n1
     else None
   | _, _ => None
   end).

Definition remove_cpm (m:vmap) (s:Sv.t): vmap :=
  Sv.fold (fun x m => Mvar.remove m x) s m.

Fixpoint const_prop_rv (m:vmap) (rv:rval) : rval := 
  match rv with 
  | Rnone _   => rv
  | Rvar  _   => rv
  | Rmem  x e => Rmem x (const_prop_e m e)
  | Raset x e => Raset x (const_prop_e m e)
  end.

Definition add_cpm (m:vmap) (rv:rval) tag e := 
  if rv is Rvar x then
    if tag is AT_inline then 
      if is_const e is Some n then Mvar.set m x n else Mvar.remove m x
    else Mvar.remove m x
  else m.
                           
Section CMD.

  Variable const_prop_i : vmap -> instr -> vmap * cmd.

  Fixpoint const_prop (m:vmap) (c:cmd) : vmap * cmd :=
    match c with
    | [::] => (m, [::])
    | i::c =>
      let (m,ic) := const_prop_i m i in
      let (m, c) := const_prop m c in
      (m, ic ++ c)
    end.

End CMD.

Fixpoint const_prop_i (m:vmap) (i:instr) : vmap * cmd := 
  let (ii,ir) := i in
  match ir with
  | Cassgn x tag e => 
    let e := const_prop_e m e in 
    let x := const_prop_rv m x in
    let m := add_cpm m x tag e in
    (m, [:: MkI ii (Cassgn x tag e)])

  | Copn xs o es =>
    let es := map (const_prop_e m) es in
    let xs := map (const_prop_rv m) xs in
    let m  := remove_cpm m (write_i ir) in
    (m, [:: MkI ii (Copn xs o es) ])

  | Cif b c1 c2 => 
    let b := const_prop_e m b in
    match is_bool b with
    | Some b => 
      let c := if b then c1 else c2 in 
      const_prop const_prop_i m c
    | None =>
      let (m1,c1) := const_prop const_prop_i m c1 in
      let (m2,c2) := const_prop const_prop_i m c2 in
      (merge_cpm m1 m2, [:: MkI ii (Cif b c1 c2) ])
    end

  | Cfor x (dir, e1, e2) c =>
    let e1 := const_prop_e m e1 in
    let e2 := const_prop_e m e2 in
    let m := remove_cpm m (write_i ir) in
    let (_,c) := const_prop const_prop_i m c in
    (m, [:: MkI ii (Cfor x (dir, e1, e2) c) ])

  | Cwhile e c =>
    let m := remove_cpm m (write_i ir) in
    let (_,c) := const_prop const_prop_i m c in
    (m, [:: MkI ii (Cwhile (const_prop_e m e) c)])

  | Ccall fi xs f es =>
    let es := map (const_prop_e m) es in
    let xs := map (const_prop_rv m) xs in
    let m := remove_cpm m (write_i ir) in
    (m, [:: MkI ii (Ccall fi xs f es) ])
  end.

Definition const_prop_fun (f:funname * fundef) :=
  let (ii,p,c,r) := f.2 in
  let (_, c) := const_prop const_prop_i empty_cpm c in
  (f.1, MkFun ii p c r).

Definition const_prop_prog (p:prog) : prog := map const_prop_fun p.

(* ** proofs
 * -------------------------------------------------------------------- *)
(*
Definition eqok t (e1 e2:pexpr t) st := 
  forall v, sem_pexpr st e1 = ok v -> sem_pexpr st e2 = ok v.

Notation "e1 '=[' st ']' e2" := (eqok e1 e2 st)
 (at level 70, no associativity).

Definition eeq t (e1 e2:pexpr t) := forall rho, e1 =[rho] e2.

Notation "e1 '=E' e2" := (eeq e1 e2) (at level 70, no associativity).

Lemma eeq_refl t : Reflexive (@eeq t).
Proof. by move=> ???. Qed.

Hint Immediate eeq_refl.

Lemma snotP e : Papp1 Onot e =E snot e.
Proof. 
  jm_destr e=> //;try apply eeq_refl.
  + by rewrite /snot=> rho v /=.
  move=> rho.                           
  match goal with |- _ =[_] snot (@Papp1 ?t1 _ ?o ?e') => move: t1 o e' jmeq end.  
  move=> t1 o e1 Hjme1 /=;set E := Papp1 _ _.
  move: (erefl t1) (erefl sbool) (JMeq_refl o).
  set o' := (O in _ -> _ -> JMeq O _ -> _).
  set t1' := (X in X = _ -> _ -> @JMeq (sop1 X _) _ _ _ -> _).
  set t2' := (X in _ -> X = _ -> @JMeq (sop1 _ X) _ _ _ -> _).
  case: t1' t2' / o' => [|??|??] ?? jmeq;subst;rewrite /E -(JMeq_eq jmeq) //=.
  by move=> v /=; case (sem_pexpr _ _) => //= ?;rewrite Bool.negb_involutive.
Qed.

Lemma sfstP t1 t2 e : Papp1 (Ofst t1 t2) e =E sfst e.
Proof. apply eeq_refl. Qed.

Lemma ssndP t1 t2 e : Papp1 (Osnd t1 t2) e =E ssnd e.
Proof. apply eeq_refl. Qed.

Lemma s_op1P t1 tr (op:sop1 t1 tr) e : Papp1 op e =E s_op1 op e.
Proof.
  case: op e;[apply:snotP|apply:sfstP |apply:ssndP].
Qed.

Lemma bind_ok A x : x >>= [eta ok (A:=A)] = x.
Proof. by case: x. Qed.

Lemma sandP (e1 e2:pexpr sbool) : Papp2 Oand e1 e2 =E sand e1 e2.
Proof. 
  move=>?;rewrite /sand;case H: is_bool => [b | ].
  + by rewrite (is_boolP H);case: ifP=> //= Hb v /=;case: sem_pexpr.
  by case H1: is_bool => [[]|] v //=;rewrite (is_boolP H1) /=;
       case: sem_pexpr => //= a;rewrite andbC.
Qed.

Lemma sorP (e1 e2:pexpr sbool) :  Papp2 Oor e1 e2 =E sor e1 e2.
Proof.
  move=>?;rewrite /sor;case H: is_bool => [b | ].
  + by rewrite (is_boolP H);case: ifP=> //= Hb v /=;case: sem_pexpr.
  by case H1: is_bool => [[]|] v //=;rewrite (is_boolP H1) /=;
       case: sem_pexpr => //= a;rewrite orbC.
Qed.

Lemma seqP (e1 e2:pexpr sword): Papp2 Oeq e1 e2 =E seq e1 e2.
Proof.
  rewrite /seq=>rho; case H1:(is_const e1);try apply eeq_refl.
  case H2:(is_const e2);try apply eeq_refl.
  rewrite (is_constP H1) (is_constP H2)=> ? /=; by rewrite iword_eqbP.
Qed.

Lemma spairP t1 t2 e1 e2:  Papp2 (Opair t1 t2) e1 e2 =E spair e1 e2.
Proof. by apply eeq_refl. Qed.

Lemma saddP (e1 e2:pexpr sword): Papp2 Oadd e1 e2 =E sadd e1 e2.
Proof.
  move=> ?;rewrite /sadd;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) // => v /=.
  + by rewrite iword_addP.
  + case: eqP => [->|] //=;case:sem_pexpr => [w|]//=.
    by rewrite I64.add_zero_l.
  case: eqP => [->|] //=;case:sem_pexpr => [w|]//=.
  by rewrite I64.add_zero.
Qed.

Lemma saddcP (e1 e2:pexpr sword): Papp2 Oaddc e1 e2 =E saddc e1 e2 .
Proof. by apply eeq_refl. Qed.

Lemma ssubP (e1 e2:pexpr sword): Papp2 Osub e1 e2 =E ssub e1 e2.
Proof.
  move=> ?;rewrite /ssub;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) // => v /=.
  + by rewrite iword_subP.
  case: eqP => [->|]//=;case sem_pexpr => //= ?.
  by rewrite I64.sub_zero_l.
Qed.

Lemma ssubcP (e1 e2:pexpr sword): Papp2 Osubc e1 e2 =E ssubc e1 e2.
Proof. by apply eeq_refl. Qed.

Lemma sltP (e1 e2:pexpr sword): Papp2 Olt e1 e2 =E slt e1 e2.
Proof.
  move=> ?; rewrite /slt;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) // => v /=.
  case: eqP => //= ->;case sem_pexpr => //= s [] <-.
  by rewrite /wlt /= Z.ltb_antisym le_unsigned. 
Qed.

Lemma sleP (e1 e2:pexpr sword): Papp2 Ole e1 e2 =E sle e1 e2.
Proof.
  move=> ?; rewrite /sle;case H1:is_const => [n1|];last by apply eeq_refl.
  case H2:is_const => [n2|];last by apply eeq_refl.
  by move=> v /=; rewrite ?(is_constP H1) ?(is_constP H2) //=; rewrite iword_lebP.
Qed.

Lemma s_op2P t1 t2 tr (o:sop2 t1 t2 tr) e1 e2: Papp2 o e1 e2 =E s_op2 o e1 e2.
Proof.
  case:o e1 e2.
  + by apply: sandP. + by apply: sorP. 
  + by apply: saddP. + by apply: saddcP. 
  + by apply: ssubP. + by apply: ssubcP. 
  + by apply: seqP.  + by apply: sltP.   + by apply: sleP.
  + by move=> ???;apply eeq_refl. + by apply: spairP.
Qed.

Lemma s_op3P t1 t2 t3 tr (o:sop3 t1 t2 t3 tr) e1 e2 e3: 
   s_op3 o e1 e2 e3 =E Papp3 o e1 e2 e3.
Proof. apply eeq_refl. Qed.

Definition valid_map (vm: vmap)  (m:map) := 
  forall x n, Mvar.get m x = Some n -> 
     match vtype x as t0 return st2ty t0 -> Prop with 
     | sword => fun v => v = I64.repr n 
     | _     => fun v => True
     end vm.[x].

Lemma const_prop_eP t (e:pexpr t) s (m:map):  
  valid_map (evm s) m ->
  e =[s] const_prop_e m e.
Proof.
  move=> Hvalid;rewrite /eqok.
  elim: e=> [x | e He | n | b | ?? o e1 He1 | ??? o e1 He1 e2 He2 | ???? o e1 He1 e2 He2 e3 He3]
     v //=.
  + move=> [] Heq; have := Hvalid x;rewrite Heq.
    case: x v Heq => -[ | | ??|? ] ?? H /=;rewrite ?H //.
    by case Mvar.get => [n /(_ n (erefl _)) -> //| /=]; rewrite H.
  + by case Heq: sem_pexpr => //= Hr;rewrite (He _ Heq).
  + by case Heq1: sem_pexpr=> //= Heqo; apply s_op1P => /=;rewrite (He1 _ Heq1).
  + case Heq1: (sem_pexpr _ e1)=> //=;case Heq2: sem_pexpr=> //= Heqo.
    by apply s_op2P => /=;rewrite (He1 _ Heq1) (He2 _ Heq2).
  case Heq1: (sem_pexpr _ e1)=> //=;case Heq2: (sem_pexpr _ e2)=> //=.
  case Heq3: sem_pexpr=> //= Heqo.
  by apply s_op3P => /=;rewrite (He1 _ Heq1) (He2 _ Heq2) (He3 _ Heq3).
Qed.
  
Lemma get_remove_cpm m xs x n: 
  Mvar.get (remove_cpm m xs) x = Some n ->  
  Mvar.get m x = Some n /\ ~Sv.In x xs.
Proof.
  rewrite /remove_cpm.
  apply SvP.MP.fold_rec_bis. 
  + by move=> s s' a ? H /H [] ??;split => //;SvD.fsetdec. 
  + by move=> ->;split => //;SvD.fsetdec. 
  move=> z m' s1 ?? H; rewrite Mvar.removeP. 
  case: (z =P x) => //= ? /H [];split=> //;SvD.fsetdec. 
Qed.

Lemma valid_map_rm rho1 rho2 xs m:
  rho1 = rho2 [\ xs] ->
  valid_map rho1 m ->
  valid_map rho2 (remove_cpm m xs).
Proof.
  move=> Hrho Hval [] [] //= nx v /get_remove_cpm [] Hm Hin.
  by rewrite -Hrho //; apply (Hval _ _ Hm). 
Qed.

Lemma remove_cpmP_aux s0 s s' m t (x:rval t) rx v: 
  rval2vval s0 x = ok rx ->
  write_vval s rx v = ok s' ->
  valid_map (evm s) m ->
  valid_map (evm s') (remove_cpm m (vrv x)).
Proof. 
  move=> Hr Hw Hv; apply: (valid_map_rm _ Hv);eapply vrvP_aux;eauto.
Qed.

Lemma remove_cpmP s s' m t (x:rval t) v: 
  write_rval s x v = ok s' ->
  valid_map (evm s) m ->
  valid_map (evm s') (remove_cpm m (vrv x)).
Proof. move=> Hw Hv; apply: (valid_map_rm _ Hv);eapply vrvP;eauto. Qed.

Lemma const_prop_rvP t (x:rval t) s (m:map) rv:  
  valid_map (evm s) m ->
  rval2vval s x = ok rv ->
  rval2vval s (const_prop_rv m x) = ok rv.
Proof.
  move=> Hvalid;elim: x rv => [x | e | ?? x1 Hx1 x2 Hx2] //= rv.
  + case Heq: sem_pexpr => [ve|] //=.
    by rewrite (const_prop_eP Hvalid Heq).
  case Heq1: (rval2vval _ x1) => [rv1|]//=.
  case Heq2: (rval2vval _ x2) => [rv2|]//= [] <-.
  by rewrite (Hx1 _ Heq1) (Hx2 _ Heq2).
Qed.

Lemma add_cpmP_aux s1 s1' s2 m t x (e:pexpr t) v: 
  write_rval s1 x v = ok s1' ->
  valid_map (evm s1) m ->
  sem_pexpr s2 e = ok v ->
  valid_map (evm s1') (add_cpm m x e).
Proof.
  rewrite /write_rval.
  case Heq: rval2vval => [rv|] //=. 
  move: {1}s1 Heq => s0.
  elim: x rv e v m s1 s1' s2 => [[] tx nx /=| ep | ?? rv1 Hrv1 rv2 Hrv2] /= rv e v m s1 s1' s2 Heq
    Hw Hvalid; simpl add_cpm.
  + move: Heq Hw=> [] <- [] <- /=.
    case Heq: (is_const e) => [?|] He.
    + case: e v Heq He => //= n v [] <- [] <- z i.
      rewrite Mvar.setP;case (_ =P z) => [<- [] <- /=| /eqP Hneq Hget].
      + by rewrite Fv.setP_eq.
      by rewrite Fv.setP_neq //;apply: Hvalid.  
    eapply valid_map_rm;eauto=> z /=.
    rewrite (vrv_var {| vtype := tx; vname := nx |})=> Hin.
    rewrite Fv.setP_neq //;apply /eqP;SvD.fsetdec.
  + case: sem_pexpr Heq Hw => //= ? [] <- /=.
    by case: write_mem => //= ? [] <-.
  case Heq1 : (rval2vval _ rv1) Heq Hw => [vr1|] //=.
  case Heq2 : (rval2vval _ rv2) => [vr2|] //= [] <- /=.
  case Heq2' : write_vval => [s'|] //= Heq1'.
  case Heq: destr_pair => [ [e1 e2]| ].
  + have He:= destr_pairP Heq;subst e => /=.
    case Heq1'' : (sem_pexpr _ e1) => [v1|] //=.
    case Heq2'' : (sem_pexpr _ e2) => [v2|] //= [] ?;subst.
    apply: (Hrv1 _ _ _ _ _ _ _ Heq1 Heq1' _ Heq1'').
    by apply: (Hrv2 _ _ _ _ _ _ _ Heq2 Heq2' _ Heq2'').
  move=> ?;apply remove_cpmP_aux with s0 s1 (Vpair vr1 vr2) v =>//=.
  + by rewrite Heq1 Heq2.  
  by rewrite Heq2' /= Heq1'.
Qed.

Lemma add_cpmP s s' m t x (e:pexpr t) v: 
  write_rval s x v = ok s' ->
  valid_map (evm s) m ->
  sem_pexpr s e = ok v ->
  valid_map (evm s') (add_cpm m x e).
Proof. apply add_cpmP_aux. Qed.

Lemma merge_cpmP rho m1 m2 : 
  valid_map rho m1 \/ valid_map rho m2 ->  
  valid_map rho (merge_cpm m1 m2).
Proof.
  move=> Hv x n;rewrite /merge_cpm Mvar.map2P //. 
  case Heq1 : (Mvar.get m1 x) => [n1|//]; case Heq2 : (Mvar.get m2 x) => [n2|//].
  case: eqP=> //.
  by move=> ? [] ?;do 2 subst;elim: Hv => Hv;apply Hv.
Qed.

Section PROOF.

  Let Pi (i:instr) := 
    forall s s' m, sem_i s i s' ->
    valid_map s.(evm) m ->
    valid_map s'.(evm) (fst (const_prop_i m i)) /\
    sem s (snd (const_prop_i m i)) s'.

  Let Pc (c:cmd) := 
    forall s s' m, sem s c s' ->
    valid_map s.(evm) m ->
    valid_map s'.(evm) (fst (const_prop const_prop_i m c)) /\
    sem s (snd (const_prop const_prop_i m c)) s'.

  Let Pf ta tr (fd:fundef ta tr) := 
    forall mem mem' va vr, 
    sem_call mem fd va mem' vr ->
    sem_call mem (const_prop_call fd) va mem' vr.

  Let Hskip : Pc [::].
  Proof.
    by move=> s s' m H;inversion_clear H;split=>//=;constructor.
  Qed.

  Let Hseq  : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc s s' m H;inversion H;clear H;subst=> /=.
    move=> /(Hi _ _ m H3) []; case const_prop_i => m' i' /=.
    move=> /(Hc _ _ m' H5) []; case const_prop => m'' c' /= hv Hc' Hi';split=>//.
    by apply (sem_app Hi' Hc').
  Qed.

  Let Hbcmd : forall t (x:rval t) e,  Pi (Cassgn x e).
  Proof.
    move=> t x e s s' m H Hm;sinversion H => /=.
    sinversion H3;sinversion H4.
    case Heq: sem_pexpr H5  => [v|] //=.  
    have H:= const_prop_eP Hm Heq=> H'.
    have : write_rval s (const_prop_rv m x) v = ok s'.
    + move: H';rewrite /write_rval. 
      case Heq': rval2vval => [vr|]//=.
      by rewrite (const_prop_rvP Hm Heq').
    split;first by eapply add_cpmP;eauto.
    by apply sem_seq1;constructor;rewrite H.
  Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 s s' m H Hm;inversion H;clear H;subst=> /=.
    have := @const_prop_eP _ e _ _ Hm _ H5.
    have Hrec : Pc (if cond then c1 else c2).
    + case: (cond);[apply Hc1 | apply Hc2].
    case Heq: is_bool. 
    + by have -> /= := is_boolP Heq;move=> [] ->;apply Hrec.
    case Heq1 : (const_prop const_prop_i m c1) => [m1 c1'].
    case Heq2 : (const_prop const_prop_i m c2) => [m2 c2'] /= Hseme.
    have Hc := Hrec _ _ _ H6 Hm;split.
    + by apply merge_cpmP; case: (cond) Hc;rewrite ?Heq1 ?Heq2 => -[] //=;auto.
    by apply sem_seq1;apply (Eif Hseme);case: (cond) Hc;rewrite ?Heq1 ?Heq2 => -[] //=;auto.
  Qed.

  Let Hfor  : forall i rn c, Pc c -> Pi (Cfor i rn c).
  Proof.
    move=> i [[dir hi] low] c Hc s s' m H Hm /=.
    set m1 := remove_cpm m (write_i (Cfor i (dir, hi,low) c)).
    have Hm1 /= : valid_map (evm s) m1 by apply valid_map_rm with (evm s).
    case Heq: const_prop => [m' c'] /=;split.
    + apply valid_map_rm with (evm s)=> //; by apply (@write_iP).
    apply sem_seq1;inversion H;clear H;subst.  
    apply EFor with vlow vhi.
    + by apply const_prop_eP. + by apply const_prop_eP.
    clear H7 H8.
    move: Hc Heq Hm1;rewrite /m1=> {m1 Hm}.
    elim: H9=> {c s s' i}.
    + by move=> s i c Hc Heq Hv;constructor.
    move=> s1 s1' s2 s3 i w ws c Hw1 Hs1 Hs2 Hrec Hc Heq Hv.
    set m1 := remove_cpm m (write_i (Cfor i (dir, hi,low) c)).
    have H := Hc _ _ _ Hs1.
    apply EForOne with s1' s2 => //.
    + have [] := Hc _ s2 m1 Hs1 .
      + move=> x n Hg; have [? Hin] := get_remove_cpm Hg.
        rewrite -(@vrvP _ i w s1) //;first apply Hv=> //. 
        by move: Hin;rewrite write_i_for;SvD.fsetdec.
      by rewrite Heq /= => Hv2 Hc'.
    apply Hrec => //.
    move=> x n Hg. have [? Hin] := get_remove_cpm Hg.
    move:Hin;rewrite write_i_for => Hin.
    rewrite -(writeP Hs1) /=;last SvD.fsetdec.
    rewrite -(@vrvP _ i w s1) //;first apply Hv=> //. 
    by SvD.fsetdec.
  Qed.

  Let Hwhile  : forall e c, Pc c -> Pi (Cwhile e c).
  Proof.
    move=> e c Hc s s' m H Hm /=.
    set m1 := remove_cpm m (write_i (Cwhile e c)).
    have Hm1 /= : valid_map (evm s) m1 by apply valid_map_rm with (evm s).
    case Heq: const_prop => [m' c'] /=;split.
    + apply valid_map_rm with (evm s)=> //; by apply (@write_iP).
    apply sem_seq1;inversion H;clear H;subst;constructor.
    move: Hc Heq Hm1;rewrite /m1=> {m1 Hm}.
    elim: H4=> {e c s s'}.
    + move=> s e c He Hc Heq Hv;constructor.
      by apply const_prop_eP. 
    move=> s1 s2 s3 e c He Hs1 Hs2 Hrec Hc Heq Hv.
    set m1 := remove_cpm m (write_i (Cwhile e c)).
    have [] //:= Hc _ s2 m1 Hs1.
    rewrite Heq /= => Hv2 Hc'.
    apply EWhileOne with s2 => //.
    + by apply const_prop_eP. 
    apply Hrec => //.
    move=> x n Hg. have [? Hin] := get_remove_cpm Hg.
    move:Hin;rewrite write_i_while => Hin.
    rewrite -(writeP Hs1) /=;last SvD.fsetdec.
    by apply Hv. 
  Qed.

  Let Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Proof.
    move=> ta tr x fd a Hf s s' m H;inversion H;clear H;subst => /=.
    unfold rarg in * => {rarg}.
    sinversion H2;sinversion H6;sinversion H5;sinversion H0.
    move=> Hm;split;first by rewrite write_i_call;eapply remove_cpmP;eauto.
    case Heq: (sem_pexpr s a) H7 H8 => [va /=|//] _ /Hf Hs.
    have Ha:= @const_prop_eP _ a _ _ Hm _ Heq.
    by apply sem_seq1;econstructor;eauto; rewrite Ha.
  Qed.

  Let Hfunc : forall ta tr (x:rval ta) c (re:pexpr tr), Pc c -> Pf (FunDef x c re).
  Proof.
    move=> ta tr x c re Hc mem mem' va vr H;sinversion H;sinversion H0=>/=.
    case Heq: const_prop => [m' c'];constructor=> //= vm0 Hvm0.
    case: (H6 vm0 Hvm0)=> vm2 /= [vm1 []] He /Hc Hr. 
    have {Hr} []:= Hr empty_cpm.
    + by move=> z n;rewrite /empty_cpm Mvar.get0.
    by rewrite Heq /= => ? Hc' Hvr;exists vm2, vm1;split=>//;apply const_prop_eP.
  Qed.

  Lemma const_prop_callP ta tr (f : fundef ta tr) mem mem' va vr: 
    sem_call mem f va mem' vr -> 
    sem_call mem (const_prop_call f) va mem' vr.
  Proof.
    apply (@func_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc).
  Qed.

End PROOF.

*)