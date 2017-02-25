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
Require Import JMeq Setoid Morphisms Classes.RelationClasses.
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

Local Notation cpm := (Mvar.t Z).


Fixpoint const_prop_e (m:cpm) e :=
  match e with
  | Pconst _  => e
  | Pbool  _  => e
  | Pcast e   => Pcast (const_prop_e m e)
  | Pvar  x   => if Mvar.get m x is Some n then Pconst n else e
  | Pget  x e => Pget x (const_prop_e m e)
  | Pload x e => Pload x (const_prop_e m e)
  | Pnot  e   => snot e
  | Papp2 o e1 e2 => s_op2 o (const_prop_e m e1)  (const_prop_e m e2)
  end.

Definition empty_cpm : cpm := @Mvar.empty Z.

Definition merge_cpm : cpm -> cpm -> cpm := 
  Mvar.map2 (fun _ (o1 o2: option Z) => 
   match o1, o2 with
   | Some n1, Some n2 => 
     if (n1 == n2)%Z then Some n1
     else None
   | _, _ => None
   end).

Definition remove_cpm (m:cpm) (s:Sv.t): cpm :=
  Sv.fold (fun x m => Mvar.remove m x) s m.

Definition const_prop_rv (m:cpm) (rv:rval) : rval := 
  match rv with 
  | Rnone _   => rv
  | Rvar  _   => rv
  | Rmem  x e => Rmem x (const_prop_e m e)
  | Raset x e => Raset x (const_prop_e m e)
  end.

Definition add_cpm (m:cpm) (rv:rval) tag e := 
  if rv is Rvar x then
    if tag is AT_inline then 
      if is_const e is Some n then Mvar.set m x n else Mvar.remove m x
    else Mvar.remove m x
  else m. 
                           
Section CMD.

  Variable const_prop_i : cpm -> instr -> cpm * cmd.

  Fixpoint const_prop (m:cpm) (c:cmd) : cpm * cmd :=
    match c with
    | [::] => (m, [::])
    | i::c =>
      let (m,ic) := const_prop_i m i in
      let (m, c) := const_prop m c in
      (m, ic ++ c)
    end.

End CMD.

Fixpoint const_prop_ir (m:cpm) ii (ir:instr_r) : cpm * cmd := 
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
  end

with const_prop_i (m:cpm) (i:instr) : cpm * cmd :=
  let (ii,ir) := i in
  const_prop_ir m ii ir.

Definition const_prop_fun (f:fundef) :=
  let (ii,p,c,r) := f in
  let (_, c) := const_prop const_prop_i empty_cpm c in
  MkFun ii p c r.

Definition const_prop_prog (p:prog) : prog := map_prog const_prop_fun p.

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

Lemma snotP e : Pnot e =E snot e.
Proof. 
  case: e=> //=;try auto; first by move=> ??.
  move=> p rho v /=;rewrite /eqok.
  case: sem_pexpr => //= a; case: a => //= b; by rewrite negbK.
Qed.

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

Lemma saddP e1 e2 : Papp2 Oadd e1 e2 =E sadd e1 e2.
Proof.
  rewrite /sadd. case: (is_constP e1) => [n1| {e1} e1];
    case: (is_constP e2) => [n2| {e2} e2] rho v //=.
  + by case: eqP => [-> | //];case: sem_pexpr => //= -[].
  case: eqP => [-> | //];case: sem_pexpr => //= -[] //= z <-.
  by rewrite /sem_op2_i /mk_sem_sop2 /= Z.add_0_r.
Qed.

Lemma ssubP e1 e2 : Papp2 Osub e1 e2 =E ssub e1 e2.
Proof.
  rewrite /ssub. case: (is_constP e1) => [n1| {e1} e1];
    case: (is_constP e2) => [n2| {e2} e2] rho v //=.
  case: eqP => [-> | //];case: sem_pexpr => //= -[] //= z <-.
  by rewrite /sem_op2_i /mk_sem_sop2 /= Z.sub_0_r.
Qed.

Lemma smulP e1 e2 : Papp2 Omul e1 e2 =E smul e1 e2.
Proof.
  rewrite /smul. case: (is_constP e1) => [n1| {e1} e1];
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

Lemma s_eqP e1 e2 : Papp2 Oeq e1 e2 =E s_eq e1 e2.
Proof.
  rewrite /s_eq;case: (is_constP e1) => [n1| {e1} e1].
  + case: (is_constP e2) => [n2 ?? <- //| {e2} e2].
    case:eqP => [-> rho v /=| _];last by auto.
    by case: sem_pexpr => //= -[] z //=;rewrite /sem_op2_ib /mk_sem_sop2 /= Z.eqb_refl.
  case: eqP => [-> rho v /= |_];last by auto.
  by case:sem_pexpr => //= -[] z //=;rewrite /sem_op2_ib /mk_sem_sop2 /= Z.eqb_refl.
Qed.

Lemma sneqP e1 e2 : Papp2 Oneq e1 e2 =E sneq e1 e2.
Proof.
  rewrite /sneq;case: (is_constP e1) => [n1| {e1} e1].
  + case: (is_constP e2) => [n2 ?? <- //| {e2} e2].
    case:eqP => [-> rho v /=| _];last by auto.
    by case: sem_pexpr => //= -[] z //=;rewrite /sem_op2_ib /mk_sem_sop2 /= Z.eqb_refl.
  case: eqP => [-> rho v /= |_];last by auto.
  by case:sem_pexpr => //= -[] z //=;rewrite /sem_op2_ib /mk_sem_sop2 /= Z.eqb_refl.
Qed.

Lemma sltP e1 e2 : Papp2 Olt e1 e2 =E slt e1 e2.
Proof.
  rewrite /slt;case: (is_constP e1) => [n1| {e1} e1].
  + case: (is_constP e2) => [n2 ?? <- //| {e2} e2].
    case:eqP => [-> rho v /=| _];last by auto.
    by case: sem_pexpr => //= -[] z //=; rewrite /sem_op2_ib /mk_sem_sop2 /= Z.ltb_irrefl. 
  case: eqP => [-> rho v /= |_];last by auto.
  by case:sem_pexpr => //= -[] z //=;rewrite /sem_op2_ib /mk_sem_sop2 /= Z.ltb_irrefl. 
Qed.

Lemma sleP e1 e2 : Papp2 Ole e1 e2 =E sle e1 e2.
Proof.
  rewrite /sle;case: (is_constP e1) => [n1| {e1} e1].
  + case: (is_constP e2) => [n2 ?? <- //| {e2} e2].
    case:eqP => [-> rho v /=| _];last by auto.
    by case: sem_pexpr => //= -[] z //=;rewrite /sem_op2_ib /mk_sem_sop2 /= Z.leb_refl.
  case: eqP => [-> rho v /= |_];last by auto.
  by case:sem_pexpr => //= -[] z //=;rewrite /sem_op2_ib /mk_sem_sop2 /= Z.leb_refl.
Qed.

Lemma sgtP e1 e2 : Papp2 Ogt e1 e2 =E sgt e1 e2.
Proof.
  rewrite /sgt;case: (is_constP e1) => [n1| {e1} e1].
  + case: (is_constP e2) => [n2 ?? <- //=| {e2} e2].
    case:eqP => [-> rho v /=| _];last by auto.
    by case: sem_pexpr => //= -[] z //=; rewrite /sem_op2_ib /mk_sem_sop2 /= Z.gtb_ltb Z.ltb_irrefl.
  case: eqP => [-> rho v /= |_];last by auto.
  by case:sem_pexpr => //= -[] z //=;rewrite /sem_op2_ib /mk_sem_sop2 /= Z.gtb_ltb Z.ltb_irrefl. 
Qed.

Lemma sgeP e1 e2 : Papp2 Oge e1 e2 =E sge e1 e2.
Proof.
  rewrite /sge;case: (is_constP e1) => [n1| {e1} e1].
  + case: (is_constP e2) => [n2| {e2} e2];first by move=> ?? <-.
    case:eqP => [-> rho v /=| _];last by auto.
    by case: sem_pexpr => //= -[] z //=;rewrite /sem_op2_ib /mk_sem_sop2 /= Z.geb_leb Z.leb_refl.
  case: eqP => [-> rho v /= |_];last by auto.
  by case:sem_pexpr => //= -[] z //=;rewrite /sem_op2_ib /mk_sem_sop2 /= Z.geb_leb Z.leb_refl.
Qed.

Lemma s_op2P o e1 e2 : Papp2 o e1 e2 =E s_op2 o e1 e2.
Proof.
  case: o;auto using sandP, sorP, saddP, smulP, ssubP, s_eqP, sneqP, sltP, sleP, sgtP, sgeP.
Qed.

Definition valid_cpm (vm: vmap)  (m:cpm) := 
  forall x n, Mvar.get m x = Some n -> get_var vm x = Vint n.

Lemma on_arr_var_err V (s:estate) x e (v:V) :
  Let (_, _) := s.[x] in Error e <> ok v.
Proof. by rewrite /on_arr_var;case: x => -[]. Qed.

Lemma Let_err {E A V:Type} {e:E} {a: result E A} {v:V}:
  Let _ := a in Error e <> Ok _ v.
Proof. by case a. Qed.

Lemma const_prop_eP (e:pexpr) s (m:cpm):  
  valid_cpm (evm s) m ->
  e =[s] const_prop_e m e.
Proof.
  move=> Hvalid;rewrite /eqok.
  elim: e=> [z | b | e He | x | x e He | x e He | e He | e e1 He1 e2 He2] v //=.
  + by case Heq: sem_pexpr => [ve|] //=;rewrite (He _ Heq).
  + by case Heq: Mvar.get => [n|] //=;rewrite (Hvalid _ _ Heq).
  + case Heq: sem_pexpr => [ve|] //=;first by rewrite (He _ Heq).
    by move=> H;case: (on_arr_var_err H).
  + by case Heq: sem_pexpr => [ve|] //=;rewrite (He _ Heq).
  + by apply snotP.
  move=> H;apply /s_op2P;move: H => /=.
  case Heq2: sem_pexpr => [ve2| ] /=;last by move => /Let_err.
  case Heq1: (sem_pexpr s e1) => [ve1| ] //=.
  by rewrite (He1 _ Heq1) (He2 _ Heq2).
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

Lemma remove_cpm_spec (m : cpm) (xs : Sv.t) (x : CmpVar.t):
  match Mvar.get (remove_cpm m xs) x with 
  | Some n => Mvar.get m x = Some n /\ ~ Sv.In x xs
  | None   => Mvar.get m x = None \/ Sv.In x xs
  end.
Proof.
  rewrite /remove_cpm;apply SvP.MP.fold_rec_bis. 
  + move=> s s' a Heq;case: Mvar.get=> [? [] ??| [? | ?]].
    + by split => //;SvD.fsetdec. 
    + by left.
    by right;SvD.fsetdec. 
  + case: Mvar.get=> [? | ].
    + split => //;SvD.fsetdec. 
    by left.
  move=> ?????;rewrite Mvar.removeP;case:ifPn => /eqP Heq.
  + by rewrite Heq=> _;right;SvD.fsetdec. 
  case: Mvar.get=> [? [] ??| [?|?]].
  + by split=> //;SvD.fsetdec. 
  + by left.
  by SvD.fsetdec. 
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
  write_rval x v s = ok s' ->
  valid_cpm (evm s) m ->
  valid_cpm (evm s') (remove_cpm m (vrv x)).
Proof. move=> Hw Hv; apply: (valid_cpm_rm _ Hv);eapply vrvP;eauto. Qed.

Lemma remove1_cpmP x v s s' m:
  write_var x v s = ok s' ->
  valid_cpm (evm s) m ->
  valid_cpm (evm s') (Mvar.remove m x).
Proof.
  move=> Hw Hv z n. rewrite Mvar.removeP. 
  case:ifPn => /eqP // ? Hz;rewrite /get_var -(vrvP_var Hw); last by SvD.fsetdec.
  by apply: Hv Hz.
Qed.


Lemma add_cpmP_aux s1 s1' s2 m x e v tag: 
  sem_pexpr s2 e = ok v -> 
  write_rval x v s1 = ok s1' ->
  valid_cpm (evm s1) m -> 
  valid_cpm (evm s1') (add_cpm m x tag e).
Proof.
  rewrite /add_cpm;case: x => [xi | x | x | x] //= He.
  + by move=> [] ->.
  + case: tag; try (by apply: remove1_cpmP).
    case: is_constP He; last by move=> ??;apply: remove1_cpmP.
    move=> n /= [] <-;rewrite /write_var /set_var.
    case: x => -[] [] //= xn vi [] <- /= Hv z /= n0.
    case: ({| vtype := sint; vname := xn |} =P z).
    + move=> <- /=;rewrite Mvar.setP_eq=> -[] <-;by rewrite /get_var Fv.setP_eq.
    move=> /eqP Hneq;rewrite Mvar.setP_neq // /get_var /= Fv.setP_neq //.
    by apply Hv.
  + by move=> p;t_rbindP => -[] <-.
  move=> p; apply: on_arr_varP => n t Hx.
  apply: rbindP => vp ?; apply: rbindP => v' ?.
  apply: rbindP => t' ?. 
  case: x Hx => -[] tx x xi /= ->.
  rewrite /set_var /=. 
  case: CEDecStype.pos_dec (@CEDecStype.pos_dec_r n n)=> /=;last 
    by move=> [] /(_ I (refl_equal _)).
  move=> a _ [] <- /= Hv z nz Hz;rewrite /get_var.
  rewrite Fv.setP_neq;first by apply Hv.
  by move: Hz=> /Hv;case z => -[].
Qed.

Lemma add_cpmP s s' m x e tag v: 
  sem_pexpr s e = ok v ->
  write_rval x v s = ok s' ->
  valid_cpm (evm s) m ->
  valid_cpm (evm s') (add_cpm m x tag e).
Proof. apply add_cpmP_aux. Qed.

Lemma merge_cpmP rho m1 m2 : 
  valid_cpm rho m1 \/ valid_cpm rho m2 ->  
  valid_cpm rho (merge_cpm m1 m2).
Proof.
  move=> Hv x n;rewrite /merge_cpm Mvar.map2P //. 
  case Heq1 : (Mvar.get m1 x) => [n1|//]; case Heq2 : (Mvar.get m2 x) => [n2|//].
  case: eqP=> //.
  by move=> ? [] ?;do 2 subst;elim: Hv => Hv;apply Hv.
Qed.

Lemma const_prop_rv_auxP s0 s1 s2 m x v: 
  valid_cpm (evm s0) m ->
  write_rval_aux s0 x v s1 = Ok error s2 ->
  write_rval_aux s0 (const_prop_rv m x) v s1 = ok s2.
Proof.
  case:x => [ii | x | x p | x p] //= Hv. 
  + apply: rbindP => z Hz;rewrite Hz /=.
    apply: rbindP => z'.
    by apply: rbindP => z'' /(@const_prop_eP p _ _ Hv) -> /= ->.
  case: x => -[[]] //= n t _;rewrite /on_arr_var /=.
  apply: rbindP => z.
  by apply: rbindP => z'' /(@const_prop_eP p _ _ Hv) -> /= ->.
Qed.

Lemma const_prop_rvP s1 s2 m x v: 
  valid_cpm (evm s1) m ->
  write_rval x v s1 = Ok error s2 ->
  write_rval (const_prop_rv m x) v s1 = ok s2.
Proof. by apply const_prop_rv_auxP. Qed.

Lemma const_prop_rvsP s1 s2 m x v: 
  valid_cpm (evm s1) m ->
  write_rvals s1 x v = Ok error s2 ->
  write_rvals s1 (map (const_prop_rv m) x) v = ok s2.
Proof.
  rewrite /write_rvals;move: {1 2 4} s1 => s0 Hs0.
  elim: x v s1 s2 => //= x xs Hrec [] //= v vs s1 s2.
  by apply: rbindP => z /(const_prop_rv_auxP Hs0) -> /Hrec.
Qed.

Instance const_prop_e_m : 
  Proper (@Mvar_eq Z ==> eq ==> eq) const_prop_e.
Proof.
  move=> m1 m2 Hm e e' <- {e'}.
  elim: e => //=.
  + by move=> ? ->.
  + by move=> ?;rewrite Hm.
  + by move=> ?? ->.
  + by move=> ?? ->.
  by move=> ?? -> ? ->.
Qed.

Instance const_prop_rv_m : 
  Proper (@Mvar_eq Z ==> eq ==> eq) const_prop_rv.
Proof.
  move=> m1 m2 Hm rv rv' <- {rv'}.
  by case: rv => //= ??;rewrite Hm.
Qed.

Instance add_cpm_m : 
  Proper (@Mvar_eq Z ==> eq ==> eq ==> eq ==> @Mvar_eq Z) add_cpm.
Proof.
  move=> m1 m2 Hm x x' <- {x'} t t' <- {t'} e e' <- {e'}.
  case: x t => //= v [];rewrite ?Hm //.
  by case: is_const => [n | ];rewrite Hm.
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

Definition Mvarc_eq T := RelationPairs.RelProd (@Mvar_eq T) (@eq cmd).

(*Polymorphic Instance equiv_Mvarc_eq T : Equivalence (@Mvarc_eq T).
Proof. 
Admitted. *)

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
    by move=> ii m1 m2 /= Heq;split;rewrite /RelationPairs.RelCompFun /=; rewrite Heq.
  Qed.

  Local Lemma Wopn xs o es: Pr (Copn xs o es).
  Proof.
    move=> ii m1 m2 Heq /=;split;rewrite /RelationPairs.RelCompFun /=.
    + by rewrite Heq.
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

  Local Lemma Wwhile e c: Pc c -> Pr (Cwhile e c).
  Proof.
    move=> Hc ii m1 m2 Heq /=.
    set ww1 := remove_cpm _ _;set ww2 := remove_cpm _ _. 
    have Hw: Mvar_eq ww1 ww2 by rewrite /ww1 /ww2 Heq.
    move: (Hw) => /Hc; case: const_prop => ??; case: const_prop => ?? [].
    rewrite /RelationPairs.RelCompFun /= => _ ->. 
    by have -> : const_prop_e ww1 e = const_prop_e ww2 e by rewrite Hw.
  Qed.

  Local Lemma Wcall i xs f es: Pr (Ccall i xs f es).
  Proof.
    move=> ii m1 m2 Hw /=;split;rewrite /RelationPairs.RelCompFun /=.
    + by rewrite Hw.
    by do 3 f_equal;apply eq_in_map=> z _;rewrite Hw. 
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

  Let Pfor i vs s c s' :=
    forall m, 
      Mvar_eq m (remove_cpm m (Sv.union (Sv.singleton i) (write_c c))) ->
      valid_cpm s.(evm) m ->
      sem_for p' i vs s (const_prop const_prop_i m c).2 s'.

  Let Pfun mem fd vargs mem' vres :=
      sem_call p' mem (const_prop_fun fd) vargs mem' vres.

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
    Let v := sem_pexpr s1 e in write_rval x v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn x tag e) s2.
  Proof.
    apply: rbindP => v He Hw m ii /= Hm. 
    have H := const_prop_eP Hm He; have H' := const_prop_rvP Hm Hw.
    split;first by eapply add_cpmP;eauto.
    by apply sem_seq1;constructor;constructor;rewrite H.
  Qed.

  Local Lemma Hopn s1 s2 o xs es : 
    Let x := Let x := sem_pexprs s1 es in sem_sopn o x
    in write_rvals s1 xs x = Ok error s2 -> Pi_r s1 (Copn xs o es) s2.
  Proof.
    move=> H m ii Hm; apply: rbindP H => vs.
    apply: rbindP => ves Hes Ho Hw;move: (Hes) (Hw).
    move=> /(const_prop_esP Hm) Hes' /(const_prop_rvsP Hm) Hw';split=> /=.
    + by apply: valid_cpm_rm Hm;apply (@write_iP p);constructor; rewrite Hes /= Ho. 
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

  Local Lemma Hwhile_true s1 s2 s3 e c:
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem p s1 c s2 -> Pc s1 c s2 ->
    sem_i p s2 (Cwhile e c) s3 -> Pi_r s2 (Cwhile e c) s3 -> 
    Pi_r s1 (Cwhile e c) s3.
  Proof.
    move=> He Hc1 Hc Hw1 Hw m ii Hm.
    apply: rbindP He => v He /= Hv.
    set ww := write_i _;set m' := remove_cpm _ _.
    case Heq1: const_prop => [m'' c'] /=;split.
    + apply: valid_cpm_rm Hm.
      by apply (@write_iP p);apply: Ewhile_true Hc1 Hw1;rewrite He. 
    apply sem_seq1;constructor.
    have Hm'1 : valid_cpm (evm s1) m' by apply: valid_cpm_rm Hm.
    case: (Hc m')=> //; rewrite Heq1 /= => _ Hc'; case: (Hw m' ii). 
    + by apply: valid_cpm_rm Hm => z;rewrite /ww write_i_while; apply: (writeP Hc1).
    move=> /= _ Hw'; apply Ewhile_true with s2 => //.
    + by move: He=> /(const_prop_eP Hm'1) ->.
    have H1 := remove_cpm2 m ww; move: Hw'.
    have : Mvarc_eq (const_prop const_prop_i (remove_cpm m' (write_i (Cwhile e c))) c)
               (m'', c').
    + by have := const_prop_m H1 (refl_equal c); rewrite Heq1.
    case: const_prop => ??.
    have -> /=: const_prop_e (remove_cpm m' (write_i (Cwhile e c))) e = 
              const_prop_e m' e.
    + by rewrite H1.
    move=> [] /=;rewrite /RelationPairs.RelCompFun /= => _ -> Hw'.
    by sinversion Hw';sinversion H5; sinversion H3.
  Qed.

  Local Lemma Hwhile_false s e c:
    Let x := sem_pexpr s e in to_bool x = Ok error false ->
    Pi_r s (Cwhile e c) s.
  Proof.
    move=> He m ii Hm.
    apply: rbindP He => v He /= Hv.
    set ww := write_i _;set m' := remove_cpm _ _.
    case Heq1: const_prop => [m'' c'] /=;split.
    + by apply: valid_cpm_rm Hm.
    apply sem_seq1;constructor;apply: Ewhile_false.
    have Hm'1 : valid_cpm (evm s) m' by apply: valid_cpm_rm Hm.
    by move: He=> /(const_prop_eP Hm'1) ->.
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
      by apply: remove1_cpmP Hw Hm.
    have [_ Hc']:= Hc _ Hm'.        
    have /(Hf _ Heqm) : valid_cpm (evm s2) m.
    + have -> := valid_cpm_m (refl_equal (evm s2)) Heqm.
      apply: valid_cpm_rm Hm'=> z Hz;apply: (writeP Hsemc);SvD.fsetdec. 
    by apply: EForOne Hc'.
  Qed.

  Local Lemma Hcall s1 m2 s2 ii xs fn fd args vargs vs:
        get_fundef p fn = Some fd ->
        sem_pexprs s1 args = Ok error vargs ->
        sem_call p (emem s1) fd vargs m2 vs ->
        Pfun (emem s1) fd vargs m2 vs ->
        write_rvals {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
        Pi_r s1 (Ccall ii xs fn args) s2.
  Proof.
    move=> Hfn Hargs Hcall Hfun Hvs m ii' Hm /=;split.
    + by apply: valid_cpm_rm Hm;apply (@write_iP p);econstructor;eauto.
    apply sem_seq1;constructor;econstructor;eauto.
    + by rewrite (@get_map_prog const_prop_fun) Hfn.
    + by apply const_prop_esP.
    by apply const_prop_rvsP.
  Qed.

  Local Lemma Hproc m1 m2 (fd : fundef) vargs vres : 
    (forall vm0 : vmap,
       all_empty_arr vm0 ->
       exists (s1 : estate) (vm2 : vmap),
           [/\ write_vars (f_params fd) vargs {| emem := m1; evm := vm0 |} =
               Ok error s1,
               sem p s1 (f_body fd) {| emem := m2; evm := vm2 |},
               Pc s1 (f_body fd) {| emem := m2; evm := vm2 |}
             & map (fun (x:var_i) => get_var vm2 x) fd.(f_res) = vres]) ->
    List.Forall is_full_array vres -> Pfun m1 fd vargs m2 vres.
  Proof.
    case: fd=> fi fparams fc fres. 
    move=> Hrec Hfull;constructor => // vm0 /Hrec [] s1 [] vm2 [] /= Hargs Hsem Hc Hres.
    exists s1, vm2;split => //= {Hrec}.
    + by case : const_prop.
    + have : valid_cpm (evm s1) empty_cpm by move=> x n;rewrite Mvar.get0.
      by move=> /Hc [];case: const_prop.
    by case : const_prop.  
  Qed.

  Lemma const_prop_callP fd mem mem' va vr: 
    sem_call p mem fd va mem' vr -> 
    sem_call p' mem (const_prop_fun fd) va mem' vr.
  Proof.
    apply (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End PROOF.
