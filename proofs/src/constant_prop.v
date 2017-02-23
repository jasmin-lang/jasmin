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

Fixpoint const_prop_rv (m:cpm) (rv:rval) : rval := 
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

Fixpoint const_prop_i (m:cpm) (i:instr) : cpm * cmd := 
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
  
Lemma get_remove_cpm m xs x n: 
  Mvar.get (remove_cpm m xs) x = Some n ->  
  Mvar.get m x = Some n /\ ~Sv.In x xs.
Proof.
  rewrite /remove_cpm; apply SvP.MP.fold_rec_bis. 
  + by move=> s s' a ? H /H [] ??;split => //;SvD.fsetdec. 
  + by move=> ->;split => //;SvD.fsetdec. 
  move=> z m' s1 ?? H; rewrite Mvar.removeP. 
  case: (z =P x) => //= ? /H [];split=> //;SvD.fsetdec. 
Qed.

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

(*Lemma const_prop_rvP t (x:rval t) s (m:map) rv:  
  valid_cpm (evm s) m ->
  rval2vval s x = ok rv ->
  rval2vval s (const_prop_rv m x) = ok rv.
Proof.
  move=> Hvalid;elim: x rv => [x | e | ?? x1 Hx1 x2 Hx2] //= rv.
  + case Heq: sem_pexpr => [ve|] //=.
    by rewrite (const_prop_eP Hvalid Heq).
  case Heq1: (rval2vval _ x1) => [rv1|]//=.
  case Heq2: (rval2vval _ x2) => [rv2|]//= [] <-.
  by rewrite (Hx1 _ Heq1) (Hx2 _ Heq2).
Qed. *)

Lemma remove1_cpmP x v s s' m:
  write_var x v s = ok s' ->
  valid_cpm (evm s) m ->
  valid_cpm (evm s') (Mvar.remove m x).
Proof.
  move=> Hw Hv z n. rewrite Mvar.removeP. 
  case:ifPn => /eqP // ? Hz;rewrite /get_var -(vrvP_var Hw); last by SvD.fsetdec.
  by apply: Hv Hz.
Qed.

Lemma rbindP eT aT rT (e:result eT aT) (body:aT -> result eT rT) v (P:Type):
  (forall z, e = ok z -> body z = Ok _ v -> P) ->
  e >>= body = Ok _ v -> P.
Proof. by case: e=> //= a H /H H';apply H'. Qed.

Lemma on_arr_varP A (f : forall n : positive, Array.array n word -> exec A) v s x P:
  (forall n t, vtype x = sarr n -> f n t = ok v -> P) -> 
  on_arr_var s x f = ok v -> P.
Proof. by rewrite /on_arr_var;case: x => -[] //= ?? H /H H';apply H'. Qed.

Ltac t_rbindP := repeat (apply:rbindP => ??).

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

(*
Section PROOF.

  Let Pi (i:instr) := 
    forall s s' m, sem_i s i s' ->
    valid_cpm s.(evm) m ->
    valid_cpm s'.(evm) (fst (const_prop_i m i)) /\
    sem s (snd (const_prop_i m i)) s'.

  Let Pc (c:cmd) := 
    forall s s' m, sem s c s' ->
    valid_cpm s.(evm) m ->
    valid_cpm s'.(evm) (fst (const_prop const_prop_i m c)) /\
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
    have Hm1 /= : valid_cpm (evm s) m1 by apply valid_cpm_rm with (evm s).
    case Heq: const_prop => [m' c'] /=;split.
    + apply valid_cpm_rm with (evm s)=> //; by apply (@write_iP).
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
    have Hm1 /= : valid_cpm (evm s) m1 by apply valid_cpm_rm with (evm s).
    case Heq: const_prop => [m' c'] /=;split.
    + apply valid_cpm_rm with (evm s)=> //; by apply (@write_iP).
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