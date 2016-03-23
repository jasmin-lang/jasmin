(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple finfun.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import gen_map word dmasm_utils dmasm_type dmasm_var dmasm_sem 
               dmasm_sem_props dmasm_Ssem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.
Local Open Scope seq_scope.

(* TODO: move this *)
Definition eqb_sop1 {t1 tr t1' tr'} (o:sop1 t1 tr) (o':sop1 t1' tr') := 
  match o, o' with
  | Onot    , Onot     => true
  | Ofst _ _, Ofst _ _ => true
  | Osnd _ _, Osnd _ _ => true
  | _       , _        => false
  end.

Definition eqb_sop2 {t1 t2 tr t1' t2' tr'} (o:sop2 t1 t2 tr) (o':sop2 t1' t2' tr') := 
  match o, o' with
| Oand     , Oand      => true
| Oor      , Oor       => true
| Oadd     , Oadd      => true
| Oeq      , Oeq       => true
| Olt      , Olt       => true
| Oget _   , Oget _    => true
| Opair _ _, Opair _ _ => true
| _        , _         => false
end.

Definition eqb_sop3 {t1 t2 t3 tr t1' t2' t3' tr'} 
           (o:sop3 t1 t2 t3 tr) (o':sop3 t1' t2' t3' tr') := 
  match o, o' with
 | Oaddc , Oaddc  => true
 | Oset _, Oset _ => true
 | _     , _      => false
 end.

Lemma eqb_sop1P t1 t1' tr tr' (o:sop1 t1 tr) (o':sop1 t1' tr'):
  t1 = t1' -> eqb_sop1 o o' ->  tr = tr' /\ JMeq o o'.
Proof. by move: o o' => [|??|??] [|??|??] //= [] ->->. Qed. 

Lemma eqb_sop2P t1 t1' t2 t2' tr tr' (o:sop2 t1 t2 tr) (o':sop2 t1' t2' tr'):
  t1 = t1' -> t2 = t2' -> eqb_sop2 o o' -> tr = tr' /\ JMeq o o'.
Proof. by move: o o'=> [|||||?|??] [|||||?|??] //= => [ []->| ->->]. Qed.

Lemma eqb_sop3P t1 t1' t2 t2' t3 t3' tr tr' (o:sop3 t1 t2 t3 tr) (o':sop3 t1' t2' t3' tr'):
  t1 = t1' -> t2 = t2' -> t3 = t3' -> eqb_sop3 o o' ->  tr = tr' /\ JMeq o o'.
Proof. by move: o o'=> [|?] [|?] // [] ->. Qed.


(* -------------------------------------------------------------------------- *)
(* ** Symbolic variables                                                      *)
(* -------------------------------------------------------------------------- *)

(* This is a clone of variables only the type of ident change
 * Maybe we should merge both                                                 *) 

Module Sident.

  Definition ident := [eqType of positive].

  Module Mid := Mp.

End Sident.

Module SVar := MvMake Sident.
Export SVar. (* Enrico: On pert les structures canoniques si pas de import *)
Export Var.
Notation svar   := SVar.var.
Notation svtype := SVar.vtype.
Notation svname := SVar.vname.
Notation SVar   := SVar.Var.
Module Msv := SVar.Mv.

Delimit Scope msvar_scope with msv.
Notation "vm .[ x ]" := (@Msv.get _ vm x) : msvar_scope.
Notation "vm .[ x  <- v ]" := (@Msv.set _ vm x v) : msvar_scope.
Arguments Msv.get to m%msvar_scope x.
Arguments Msv.set to m%msvar_scope x v.
Definition msv0 := Msv.empty (fun v => sdflt_val v.(svtype)).

(* -------------------------------------------------------------------------- *)
(* ** Set of symbolic variables                                               *)
(* -------------------------------------------------------------------------- *)

Module CmpSVar.

  Definition t := [eqType of svar].

  Definition cmp : t -> t -> comparison := SVar.var_cmp.

  Definition cmpO : Cmp cmp := SVar.varO.

End CmpSVar.

Module Ssv := Smake CmpSVar.
Module SsvP := MSetEqProperties.EqProperties Ssv.
Module SsvD := MSetDecide.WDecide Ssv.

Lemma Ssv_memP x s: reflect (Ssv.In x s) (Ssv.mem x s).
Proof. 
  apply: (@equivP (Ssv.mem x s));first by apply idP.
  by rewrite -Ssv.mem_spec.
Qed.

(* -------------------------------------------------------------------------- *)
(* ** Symbolic program expressions                                            *)
(* -------------------------------------------------------------------------- *)

Inductive spexpr : stype -> Type :=
| Evar   :> forall x:var , spexpr x.(vtype)
| Esvar  :> forall x:svar, spexpr x.(svtype)
| Econst :> N    -> spexpr sword
| Ebool  :> bool -> spexpr sbool
| Eapp1  : forall t1 tr: stype, 
  sop1 t1 tr -> spexpr t1 -> spexpr tr
| Eapp2  : forall t1 t2 tr: stype, 
  sop2 t1 t2 tr -> spexpr t1 -> spexpr t2 -> spexpr tr
| Eapp3  : forall t1 t2 t3 tr: stype,
  sop3 t1 t2 t3 tr -> spexpr t1 -> spexpr t2 -> spexpr t3 -> spexpr tr
| Eif    : forall t: stype, 
  spexpr sbool -> spexpr t -> spexpr t -> spexpr t.

(* Semantic *)
Notation smap := (Msv.t sst2ty).

Definition sst2pred t := sst2ty t -> Prop.

Notation pmap := (Msv.t sst2pred).

Record sstate := {
  pm : pmap;
  sm : smap;
  vm : svmap;
}.

Fixpoint ssem_spexpr t (st:sstate) (pe : spexpr t) : sst2ty t :=
  match pe in spexpr t_ return sst2ty t_ with
  | Evar  x  => st.(vm).[x]%vmap
  | Esvar x  => st.(sm).[x]%msv
  | Econst c => n2w c
  | Ebool  b => b
  | Eapp1 _ _ o pe1 =>
      let v1 := ssem_spexpr st pe1 in
      ssem_sop1 o v1
  | Eapp2 _ _ _ o pe1 pe2 =>
      let v1 := ssem_spexpr st pe1 in 
      let v2 := ssem_spexpr st pe2 in
      ssem_sop2 o v1 v2
  | Eapp3 _ _ _ _ o pe1 pe2 pe3 =>
      let v1 := ssem_spexpr st pe1 in
      let v2 := ssem_spexpr st pe2 in
      let v3 := ssem_spexpr st pe3 in
      ssem_sop3 o v1 v2 v3
  | Eif _ b e1 e2 =>
    if ssem_spexpr st b then ssem_spexpr st e1
    else ssem_spexpr st e2
  end.

Notation "e1 '=[' st1 , st2 ']' e2" := (ssem_spexpr st1 e1 = ssem_spexpr st2 e2)
 (at level 70, no associativity).

Notation "e1 '=[' st ']' e2" := (ssem_spexpr st e1 = ssem_spexpr st e2)
 (at level 70, no associativity).

(* Injection from program expression *)
Fixpoint p2sp {t} (e:pexpr t) : spexpr t :=
  match e with
  | Pvar          x           => x
  | Pconst        w           => w
  | Papp1 _ _     op e1       => Eapp1 op (p2sp e1)
  | Papp2 _ _ _   op e1 e2    => Eapp2 op (p2sp e1) (p2sp e2)
  | Papp3 _ _ _ _ op e1 e2 e3 => Eapp3 op (p2sp e1) (p2sp e2) (p2sp e3)
  end.

Lemma sem_p2sp t (e:pexpr t) st : ssem_spexpr st (p2sp e) =  ssem_pexpr st.(vm) e.
Proof.
  by elim: e => //= [ ???? He1 | ????? He1 ? He2 | ?????? He1 ? He2 ? He3];
      rewrite ?He1 ?He2 ?He3.
Qed.

(* -------------------------------------------------------------------------- *)
(* ** program variables occuring in an symbolic expression                    *)
(* -------------------------------------------------------------------------- *)

Fixpoint fv_rec {t} (e:spexpr t) (s:Sv.t) := 
  match e with 
  | Evar   x                 => Sv.add x s
  | Esvar  _                 => s
  | Econst _                 => s
  | Ebool  _                 => s
  | Eapp1 _ _ _     e1       => fv_rec e1 s
  | Eapp2 _ _ _ _   e1 e2    => fv_rec e1 (fv_rec e2 s)
  | Eapp3 _ _ _ _ _ e1 e2 e3 => fv_rec e1 (fv_rec e2 (fv_rec e3 s))
  | Eif   _         e1 e2 e3 => fv_rec e1 (fv_rec e2 (fv_rec e3 s))
  end.

Instance fv_rec_m {t} (e:spexpr t) : Proper (Sv.Equal ==> Sv.Equal) (fv_rec e).
Proof.
  move=> x.
  elim:e x => //= [?| ????? He1 ? He2 | ?????? He1 ? He2 ? He3 | ?? He1 ? He2 ? He3] s1 s2 Heq. 
  + by rewrite Heq.
  + by apply /He1 /He2.
  + by apply /He1 /He2 /He3.
  by apply /He1 /He2 /He3.
Qed.

Definition fv t e := @fv_rec t e Sv.empty.

Lemma fv_recE t (e:spexpr t) s : Sv.Equal (fv_rec e s) (Sv.union (fv e) s).
Proof.
  elim: e s => //=
    [?| ????? He1 ? He2 | ?????? He1 ? He2 ? He3 | ?? He1 ? He2 ? He3] s.  
  + by rewrite !SvP.MP.union_add.
  + by rewrite He1 He2 /fv /= -!/(fv _) He1 SvP.MP.union_assoc.
  + by rewrite He1 He2 He3 /fv /= -!/(fv _) He1 He2 !SvP.MP.union_assoc.
  by rewrite He1 He2 He3 /fv /= -!/(fv _) He1 He2 !SvP.MP.union_assoc.
Qed.

Lemma fv_var (x:var): Sv.Equal (fv x) (Sv.singleton x).
Proof. by rewrite /fv /=; SvD.fsetdec. Qed.

Lemma fv_svar (x:svar): fv x = Sv.empty.
Proof. done. Qed.

Lemma fv_bool (b:bool): fv b = Sv.empty.
Proof. done. Qed.

Lemma fv_const (n:N): fv n = Sv.empty.
Proof. done. Qed.

Lemma fv_op1 t1 tr (o:sop1 t1 tr) (e1:spexpr t1) : 
  Sv.Equal (fv (Eapp1 o e1)) (fv e1).
Proof. by rewrite /fv /= !fv_recE. Qed.

Lemma fv_op2 t1 t2 tr (o:sop2 t1 t2 tr) e1 e2 : 
  Sv.Equal (fv (Eapp2 o e1 e2)) (Sv.union (fv e1) (fv e2)).
Proof. rewrite /fv /= !fv_recE; SvD.fsetdec. Qed.

Lemma fv_op3 t1 t2 t3 tr (o:sop3 t1 t2 t3 tr) e1 e2 e3 : 
  Sv.Equal (fv (Eapp3 o e1 e2 e3)) (Sv.union (fv e1) (Sv.union (fv e2) (fv e3))).
Proof. rewrite /fv /= !fv_recE; SvD.fsetdec. Qed.

Lemma fv_if t e1 (e2 e3:spexpr t) : 
  Sv.Equal (fv (Eif e1 e2 e3)) (Sv.union (fv e1) (Sv.union (fv e2) (fv e3))).
Proof. rewrite /fv /= !fv_recE; SvD.fsetdec. Qed.

(* -------------------------------------------------------------------------- *)
(* ** symbolic variables occuring in an symbolic expression                   *)
(* -------------------------------------------------------------------------- *)

Fixpoint sfv_rec {t} (e:spexpr t) (s:Ssv.t) := 
  match e with 
  | Esvar  x                 => Ssv.add x s
  | Evar   _                 => s
  | Econst _                 => s
  | Ebool  _                 => s
  | Eapp1 _ _ _     e1       => sfv_rec e1 s
  | Eapp2 _ _ _ _   e1 e2    => sfv_rec e1 (sfv_rec e2 s)
  | Eapp3 _ _ _ _ _ e1 e2 e3 => sfv_rec e1 (sfv_rec e2 (sfv_rec e3 s))
  | Eif   _         e1 e2 e3 => sfv_rec e1 (sfv_rec e2 (sfv_rec e3 s))
  end.

Definition sfv t e := @sfv_rec t e Ssv.empty.

Instance sfv_rec_m {t} (e:spexpr t): Proper (Ssv.Equal ==> Ssv.Equal) (sfv_rec e).
Proof.
  move=> x.
  elim:e x=> //= [?| ????? He1 ? He2 | ?????? He1 ? He2 ? He3 | ?? He1 ? He2 ? He3] s1 s2 Heq. 
  + by rewrite Heq.
  + by apply /He1 /He2.
  + by apply /He1 /He2 /He3.
  by apply /He1 /He2 /He3.
Qed.

Lemma sfv_recE t (e:spexpr t) s : Ssv.Equal (sfv_rec e s) (Ssv.union (sfv e) s).
Proof.
  elim: e s => //=
    [?| ????? He1 ? He2 | ?????? He1 ? He2 ? He3 | ?? He1 ? He2 ? He3] s.  
  + by rewrite !SsvP.MP.union_add.
  + by rewrite He1 He2 /sfv /= -!/(sfv _) He1 SsvP.MP.union_assoc.
  + by rewrite He1 He2 He3 /sfv /= -!/(sfv _) He1 He2 !SsvP.MP.union_assoc.
  by rewrite He1 He2 He3 /sfv /= -!/(sfv _) He1 He2 !SsvP.MP.union_assoc.
Qed.

Lemma sfv_var (x:var): sfv x = Ssv.empty.
Proof. done. Qed.

Lemma sfv_svar (x:svar): Ssv.Equal (sfv x) (Ssv.singleton x).
Proof. by rewrite /sfv /=; SsvD.fsetdec. Qed.

Lemma sfv_bool (b:bool): sfv b = Ssv.empty.
Proof. done. Qed.

Lemma sfv_const (n:N): sfv n = Ssv.empty.
Proof. done. Qed.

Lemma sfv_op1 t1 tr (o:sop1 t1 tr) (e1:spexpr t1) : 
  Ssv.Equal (sfv (Eapp1 o e1)) (sfv e1).
Proof. by rewrite /sfv /= !sfv_recE. Qed.

Lemma sfv_op2 t1 t2 tr (o:sop2 t1 t2 tr) e1 e2 : 
  Ssv.Equal (sfv (Eapp2 o e1 e2)) (Ssv.union (sfv e1) (sfv e2)).
Proof. rewrite /sfv /= !sfv_recE; SsvD.fsetdec. Qed.

Lemma sfv_op3 t1 t2 t3 tr (o:sop3 t1 t2 t3 tr) e1 e2 e3 : 
  Ssv.Equal (sfv (Eapp3 o e1 e2 e3)) (Ssv.union (sfv e1) (Ssv.union (sfv e2) (sfv e3))).
Proof. rewrite /sfv /= !sfv_recE; SsvD.fsetdec. Qed.

Lemma sfv_if t e1 (e2 e3:spexpr t) : 
  Ssv.Equal (sfv (Eif e1 e2 e3)) (Ssv.union (sfv e1) (Ssv.union (sfv e2) (sfv e3))).
Proof. rewrite /sfv /= !sfv_recE; SsvD.fsetdec. Qed.

(* -------------------------------------------------------------------------- *)
(* ** The evaluation depend only of the free variables                        *)
(* ---------------------------------------------------------------------------*)

Record eq_on (st1 st2:sstate) sv ss := {
  eq_on_v : forall x, Sv.In x sv ->  st1.(vm).[x]%vmap = st2.(vm).[x]%vmap;
  eq_on_s : forall x, Ssv.In x ss -> st1.(sm).[x]%msv = st2.(sm).[x]%msv;
}.

Notation "st1 '={' sv , ss '}' st2" := (eq_on st1 st2 sv ss)
  (at level 70, no associativity).

Instance eq_on_m st1 st2 : 
  Proper (Sv.Subset ==> Ssv.Subset ==> Basics.flip Basics.impl) (eq_on st1 st2).
Proof.
  move=> sv1 sv2 Hsv ss1 ss2 Hss H;constructor=> x Hx;apply H;
   (SvD.fsetdec || SsvD.fsetdec).
Qed.

Instance eq_on_m_eq st1 st2 : 
  Proper (Sv.Equal ==> Ssv.Equal ==> iff) (eq_on st1 st2).
Proof.
  move=> sv1 sv2 Hsv ss1 ss2 Hss;split=>H;constructor=> x Hx;
    apply H;(SvD.fsetdec || SsvD.fsetdec).
Qed.

Lemma ssem_spexpr_fv t (e:spexpr t) st1 st2: 
  st1 ={fv e, sfv e} st2 ->
  e =[st1, st2] e.
Proof.
  elim:e => //= 
     [?|?|?? o e1 He1 |??? o e1 He1 e2 He2 
     | ???? o e1 He1 e2 He2 e3 He3 | ? e1 He1 e2 He2 e3 He3] Hon. 
  + by apply Hon.(eq_on_v);rewrite /fv /=;SvD.fsetdec.
  + by apply Hon.(eq_on_s);rewrite /sfv /=;SsvD.fsetdec.
  + by rewrite He1.
  + by rewrite He1 ?He2 //;apply: eq_on_m Hon=>//;
     rewrite ?fv_op2 ?sfv_op2;(SvD.fsetdec || SsvD.fsetdec). 
  + by rewrite He1 ?He2 ?He3 //;apply: eq_on_m Hon=>//;
     rewrite ?fv_op3 ?sfv_op3;(SvD.fsetdec || SsvD.fsetdec).
  by rewrite He1 ?He2 ?He3 //;apply: eq_on_m Hon=>//;
   rewrite ?fv_if ?sfv_if;(SvD.fsetdec || SsvD.fsetdec).  
Qed.
 
(* -------------------------------------------------------------------------- *)
(* ** Equality between expressions                                            *)
(* -------------------------------------------------------------------------- *)

Fixpoint eqb_spexpr {t} {t'} (e:spexpr t) (e':spexpr t') := 
  match e, e' with
  | Evar x  , Evar x'   => x == x'
  | Esvar x , Esvar x'  => x == x'
  | Econst c, Econst c' => c == c'
  | Ebool  b, Ebool  b' => b == b'
  | Eapp1 _ _ o e1, Eapp1 _ _ o' e1' => 
    eqb_sop1 o o' && eqb_spexpr e1 e1'
  | Eapp2 _ _ _ o e1 e2, Eapp2 _ _ _ o' e1' e2' => 
    eqb_sop2 o o' && eqb_spexpr e1 e1' && eqb_spexpr e2 e2'
  | Eapp3 _ _ _ _ o e1 e2 e3, Eapp3 _ _ _ _ o' e1' e2' e3' => 
    eqb_sop3 o o' && eqb_spexpr e1 e1' && eqb_spexpr e2 e2' && eqb_spexpr e3 e3'
  | Eif _ b e1 e2, Eif _ b' e1' e2' =>
    eqb_spexpr b b' && eqb_spexpr e1 e1' && eqb_spexpr e2 e2'
  | _, _ => false
  end.

Notation unknown := (@Error unit bool tt).
Notation known   := (Ok unit).

Fixpoint eval_eq {t} {t'} (e:spexpr t) (e':spexpr t') : result unit bool := 
  match e, e' with
  | Evar x  , Evar x'   => if x == x' then known true else unknown
  | Esvar x  , Esvar x' => if x == x' then known true else unknown
  | Econst c, Econst c' => known (iword_eqb c c') 
  | Ebool  b, Ebool  b' => known (b == b')
  | Eapp1 _ _ o e1, Eapp1 _ _ o' e1' => 
    if eqb_sop1 o o' then
      eval_eq e1 e1' >>= (fun b =>
      if b then known true else unknown)                          
    else unknown
  | Eapp2 _ _ _ o e1 e2, Eapp2 _ _ _ o' e1' e2' => 
    if eqb_sop2 o o' then 
      eval_eq e1 e1' >>= (fun b =>
        if b then 
          eval_eq e2 e2' >>= (fun b =>
          if b then known true else unknown)
        else unknown)                          
    else unknown
  | Eapp3 _ _ _ _ o e1 e2 e3, Eapp3 _ _ _ _ o' e1' e2' e3' => 
    if eqb_sop3 o o' then 
      eval_eq e1 e1' >>= (fun b =>
      if b then 
        eval_eq e2 e2' >>= (fun b =>
        if b then 
          eval_eq e3 e3' >>= (fun b =>
          if b then known true else unknown)  
        else unknown)
      else unknown)                          
    else unknown
  | Eif _ b e1 e2, Eif _ b' e1' e2' =>
    eval_eq b b' >>= (fun b =>
    if b then 
      eval_eq e1 e1' >>= (fun b =>
      if b then 
        eval_eq e2 e2' >>= (fun b =>
        if b then known true else unknown)  
      else unknown)
    else 
      eval_eq e1 e2' >>= (fun b =>
      if b then 
        eval_eq e2 e1' >>= (fun b =>
        if b then known true else unknown)  
      else unknown))
  | _, _ => unknown
  end.
 
Lemma eqb_spexprJM t t' (p:spexpr t) (p':spexpr t') : eqb_spexpr p p' -> t = t' /\ JMeq p p' .
Proof.
  elim: p t' p' => 
     [x | x | w | b | ?? o p1 Hp1 |??? o p1 Hp1 p2 Hp2 
     | ???? o p1 Hp1 p2 Hp2 p3 Hp3 | ? p1 Hp1 p2 Hp2 p3 Hp3] t'
     [x' | x' | w' | b' | ?? o' p1' |??? o' p1' p2' 
     | ???? o' p1' p2' p3' | ? p1' p2' p3'] //=.
  + move=> /eqP -> //.
  + move=> /eqP -> //.
  + move=> /eqP -> //.
  + move=> /eqP -> //.
  + by rewrite andbC=> /andP [] /Hp1 [] ??;subst=> /eqb_sop1P []//??;do 2!subst.
  + by rewrite -andbA andbC=> /andP [] /andP [] /Hp1[]?? /Hp2[]??;
       subst=>/eqb_sop2P[]//??;do 2!subst.
  + by rewrite -!andbA andbC=> /andP [] /andP [] /Hp1[]?? /andP [] /Hp2[]?? /Hp3[]??;
       subst=>/eqb_sop3P[]//??;do 2!subst.
  by rewrite andbC=> /andP [] /Hp3[]?? /andP [] /Hp1[]?? /Hp2[]??;do 2!subst.
Qed.

Lemma eqb_spexprP t  (p p':spexpr t) : eqb_spexpr p p' -> p = p'.
Proof. move=> /eqb_spexprJM [] _;apply JMeq_eq. Qed.

(* TODO: move this *)
Lemma contra_p (A B:Prop): (A -> B) -> ~B -> ~A.
Proof. tauto. Qed.
 
Lemma eval_eqJM st b t t' (e:spexpr t) (e':spexpr t'):  
  eval_eq e e' = known b ->
  t = t' /\
  if b then JMeq (ssem_spexpr st e) (ssem_spexpr st e')
  else ~JMeq (ssem_spexpr st e) (ssem_spexpr st e').
Proof.
  elim: e t' e' b => 
     [? | ? | ? | ? | ?? o e1 He1 | ??? o e1 He1 e2 He2 
     | ???? o e1 He1 e2 He2 e3 He3 | ? e1 He1 e2 He2 e3 He3] t'
     [? | ? | ? | ? | ?? o' e1' | ??? o' e1' e2' 
     | ???? o' e1' e2' e3' | ? e1' e2' e3'] b //=.
  + by case: (_ =P _)=> [-> [] <-| ].
  + by case: (_ =P _)=> [-> [] <-| ].
  + move=> [];rewrite iword_eqbP;case:b=> [/eqP -> //|/eqP]=> H;split=>//. 
    by move:H;apply contra_p=>jmeq; apply JMeq_eq.
  + move=> [];case:b=> [/eqP->//|/eqP] H;split=>//.
    by move:H; apply contra_p;apply JMeq_eq.
  + case Ho: eqb_sop1=> //.
    case: eval_eq (He1 _ e1' true)=> -[] // [] //= ? jm;subst=> -[].
    case: (eqb_sop1P _ Ho) => //??;subst=> H;split=>//;subst.
    by rewrite (JMeq_eq jm).
  + case Ho: eqb_sop2=> //.
    case: eval_eq (He1 _ e1' true)=> -[] // [] //= ? jm1;subst=> -[].
    case: eval_eq (He2 _ e2' true)=> -[] // [] //= ? jm2;subst=> -[].
    case: (eqb_sop2P _ _ Ho) => //??;subst=> H;split=>//;subst.
    by rewrite (JMeq_eq jm1) (JMeq_eq jm2).
  + case Ho: eqb_sop3=> //.
    case: eval_eq (He1 _ e1' true)=> -[] // [] //= ? jm1;subst=> -[].
    case: eval_eq (He2 _ e2' true)=> -[] // [] //= ? jm2;subst=> -[].
    case: eval_eq (He3 _ e3' true)=> -[] // [] //= ? jm3;subst=> -[].
    case: (eqb_sop3P _ _ _ Ho) => //??;subst=> H;split=>//;subst.
    by rewrite (JMeq_eq jm1) (JMeq_eq jm2) (JMeq_eq jm3).
  case: eval_eq (He1 _ e1')=> -[] //= H.
  + case: (H true) => // _ jm1.
    case: eval_eq (He2 _ e2' true)=> -[] // [] //= ? jm2;subst=> -[].
    case: eval_eq (He3 _ e3' true)=> -[] // [] //= ? jm3;subst=> -[] ?.
    subst;split=>//.
    by rewrite (JMeq_eq jm1) (JMeq_eq jm2) (JMeq_eq jm3).
  case: (H false) => // _ jm1.
  case: eval_eq (He2 _ e3' true)=> -[] // [] //= ? jm2;subst=> -[].
  case: eval_eq (He3 _ e2' true)=> -[] // [] //= ? jm3;subst=> -[] ?.
  subst;split=>//.
  have : (ssem_spexpr st e1) != (ssem_spexpr st e1').
  + by apply /negP;move:jm1;apply contra_p=>/eqP->.
  case: ifP;rewrite eq_sym => _.
  + by rewrite eqb_id => /negPf ->.
  by rewrite eqbF_neg=> /negPn ->.
Qed.

Lemma eval_eqP b t (e e':spexpr t) st :  
  eval_eq e e' = known b ->
  if b then e =[st] e' else ~(e =[st] e').
Proof.
  move=> /(eval_eqJM st) [] _;case:b;first by apply: JMeq_eq.
  by apply contra_p=> ->.
Qed.

(* -------------------------------------------------------------------------- *)
(* ** Destructor                                                              *)
(* -------------------------------------------------------------------------- *)


Definition destr_pair t1 t2 (p:spexpr (t1 ** t2)) : option (spexpr t1 * spexpr t2).
case H: _ / p => [ ? | ? | ? | ? | ???? | ??? o e1 e2| ???????? | ????].
+ exact None. + exact None. + exact None. + exact None. + exact None.
(case:o H e1 e2 => [||||||??[]<-<- e1 e2];last by exact (Some (e1,e2)))=> *;
 exact None.
+ exact None. + exact None.
Defined.

Lemma destr_pairP t1 t2 (p:spexpr (t1 ** t2)) p1 p2:
   destr_pair p = Some (p1, p2) -> p = Eapp2 (Opair _ _) p1 p2.
Proof.
  move=>Heq;apply JMeq_eq.
  have {Heq}: JMeq (destr_pair p) (Some (p1, p2)) by rewrite Heq.
  rewrite /destr_pair; move:p (erefl (t1 ** t2)). 
  set t12 := (X in forall (p:spexpr X) (e : _ = X), _ -> @JMeq (spexpr X) _ _ _) => p.
  case : t12 / p => // 
     [[]/= ?? <-| []/= ?? <-| ???? _ | t1' t2' tr' o e1 e2 | ???????? _| ???? _];
     try by move=> Heq; have:= JMeq_eq Heq.
  case: o e1 e2 => //= [ e1 e2 [] ??|t t' e1 e2];subst.
  + by move=> e;have := JMeq_eq e.
  move=> e;case: (e)=> ??;subst t t'.
  rewrite (eq_irrelevance e (erefl (t1 ** t2))) /= /eq_rect_r /=.
  move=> Heq;have [-> ->] // := JMeq_eq Heq.
  (*  Enrico have [] -> -> // := JMeq_eq Heq. *)
Qed.

(* -------------------------------------------------------------------------- *)
(* ** Smart constructors                                                      *)
(* -------------------------------------------------------------------------- *)

Definition mk_not (e:spexpr sbool) : spexpr sbool := 
  match e with
  | Ebool b          => negb b
  | Eapp1 _ _ Onot e => e 
  | _                => Eapp1 Onot e
  end.

Definition mk_fst t1 t2 (p:spexpr (t1 ** t2)) : spexpr t1 :=
  match destr_pair p with
  | Some (p1,p2) => p1
  | _            => Eapp1 (Ofst _ _) p
  end.

Definition mk_snd t1 t2 (p:spexpr (t1 ** t2)) : spexpr t2 :=
  match destr_pair p with
  | Some (p1,p2) => p2
  | _            => Eapp1 (Osnd _ _) p
  end.

Definition mk_op1 t1 tr (op:sop1 t1 tr): spexpr t1 -> spexpr tr := 
  match op in sop1 t1 tr return spexpr t1 -> spexpr tr with
  | Onot     => mk_not 
  | Ofst _ _ => @mk_fst _ _ 
  | Osnd _ _ => @mk_snd _ _
  end.

Definition mk_and (e1 e2:spexpr sbool) : spexpr sbool := 
  match e1, e2 with
  | Ebool b, _ => if b then e2 else false
  | _, Ebool b => if b then e1 else false
  | _, _       => Eapp2 Oand e1 e2 
  end.

Definition mk_or (e1 e2:spexpr sbool) : spexpr sbool := 
  match e1, e2 with
  | Ebool b, _ => if b then Ebool true else e2
  | _, Ebool b => if b then Ebool true else e1
  | _, _       => Eapp2 Oor e1 e2 
  end.

Definition mk_eq (e1 e2:spexpr sword) : spexpr sbool := 
  match eval_eq e1 e2 with
  | Ok b    => b
  | Error _ => Eapp2 Oeq e1 e2 
  end.

Definition mk_pair {t t'} (e1:spexpr t) (e2:spexpr t') :=
  Eapp2 (Opair t t') e1 e2.

Definition mk_add (e1 e2:spexpr sword) : spexpr (sbool ** sword) := 
  match e1, e2 with
  | Econst n1, Econst n2 => 
    let (c,n) := iword_add n1 n2 in
    mk_pair c n
  | Econst n, _ =>
    if (n =? 0)%num then mk_pair false e2 else Eapp2 Oadd e1 e2
  | _, Econst n => 
    if (n =? 0)%num then mk_pair false e1 else Eapp2 Oadd e1 e2
  | _, _ => Eapp2 Oadd e1 e2
  end.

Definition mk_lt (e1 e2:spexpr sword) : spexpr sbool := 
  match e1, e2 with
  | Econst n1, Econst n2 => iword_ltb n1 n2 
  | _        , Econst n  => if (n =? 0)%num then Ebool false else Eapp2 Olt e1 e2
  | _        , _         => Eapp2 Olt e1 e2
  end.

(* FIXME: add other simplifications *)
Definition mk_op2 t1 t2 tr (op:sop2 t1 t2 tr): spexpr t1 -> spexpr t2 -> spexpr tr := 
  match op in sop2 t1 t2 tr return spexpr t1 -> spexpr t2 -> spexpr tr with
  | Oand        => mk_and 
  | Oor         => mk_or 
  | Oeq         => mk_eq 
  | Oadd        => mk_add
  | Olt         => mk_lt
  | Oget n      => Eapp2 (Oget n)
  | Opair t1 t2 => Eapp2 (Opair t1 t2)
  end.

(* FIXME: add simplifications *)
Definition mk_op3 t1 t2 t3 tr (op:sop3 t1 t2 t3 tr):
  spexpr t1 -> spexpr t2 -> spexpr t3 -> spexpr tr :=
  Eapp3 op. 

Definition mk_if t (b:spexpr sbool) (e1 e2 : spexpr t) := 
  match b with
  | Ebool b => if b then e1 else e2
  | _       => 
    match eval_eq e1 e2 with
    | Ok true => e1
    | _       => Eif b e1 e2
    end
  end.

Ltac jm_destr e1 := 
  let t := 
      match type of e1 with 
      | spexpr ?t => t 
      | _ => fail 1 "jm_destr: an spexpr is expected" 
      end in
  let e' := fresh "e'" in
  let t' := fresh "t'" in
  let H  := fresh "H" in
  let jmeq := fresh "jmeq" in
  move: (erefl t) (JMeq_refl e1);
  set e' := (e in _ -> @JMeq _ e _ _ -> _);move: e';
  set t' := (X in forall (e':spexpr X), X = _ -> @JMeq (spexpr X) _ _ _ -> _)=> e';
  (case: t' / e'=> [[??]H | [??]H | ?? | ?? | ?????| ???????| ?????????| ?????] jmeq;
     [simpl in H | simpl in H | | | | | | ]);
  subst;try rewrite -(JMeq_eq jmeq).

Lemma mk_notP e st : mk_not e =[st] Eapp1 Onot e.
Proof. 
  jm_destr e=> //. 
  match goal with |- mk_not (@Eapp1 ?t1 _ ?o ?e') =[_] _ => move: t1 o e' jmeq end.  
  move=> t1 o e1 Hjme1 /=. set E := Eapp1 Onot (Eapp1 o e1).
  move: (erefl t1) (erefl sbool) (JMeq_refl o).
  set o' := (O in _ -> _ -> JMeq O _ -> _).
  set t1' := (X in X = _ -> _ -> @JMeq (sop1 X _) _ _ _ -> _).
  set t2' := (X in _ -> X = _ -> @JMeq (sop1 _ X) _ _ _ -> _).
  case: t1' t2' / o' => [|??|??] ?? jmeq;subst;rewrite /E -(JMeq_eq jmeq) //=.
  by rewrite Bool.negb_involutive.
Qed.

Lemma mk_fstP t1 t2 e st : mk_fst e =[st] Eapp1 (Ofst t1 t2) e.
Proof.
  rewrite /mk_fst;case H:destr_pair=> [[e1 e2]|//]; by rewrite (destr_pairP H).
Qed.

Lemma mk_sndP t1 t2 e st : mk_snd e =[st] Eapp1 (Osnd t1 t2) e.
Proof.
  rewrite /mk_snd;case H:destr_pair=> [[e1 e2]|//]; by rewrite (destr_pairP H).
Qed.

Lemma mk_op1P t1 tr (op:sop1 t1 tr) e st : mk_op1 op e =[st] Eapp1 op e.
Proof.
  case: op e st;[apply:mk_notP|apply:mk_fstP |apply:mk_sndP].
Qed.

Lemma mk_andP (e1 e2:spexpr sbool) st : 
  mk_and e1 e2 =[st] Eapp2 Oand e1 e2.
Proof. 
  jm_destr e1;jm_destr e2 => //=;
     try ((by case:ifP) || (by rewrite andbC;case:ifP)).
Qed.

Lemma mk_orP (e1 e2:spexpr sbool) st : 
  mk_or e1 e2 =[st] Eapp2 Oor e1 e2.
Proof. 
  jm_destr e1;jm_destr e2 => //=;
     try ((by case:ifP) || (by rewrite orbC;case:ifP)).
Qed.

Lemma mk_eqP (e1 e2:spexpr sword) st:
  mk_eq e1 e2 =[st] Eapp2 Oeq e1 e2.
Proof.
  rewrite /mk_eq;case H:eval_eq => [b | ]//=.
  apply esym;move:H=> /(eval_eqP st);apply: introTF;apply: eqP.
Qed.

Lemma mk_pairP t1 t2 e1 e2 st:
   mk_pair e1 e2 =[st] Eapp2 (Opair t1 t2) e1 e2.
Proof. by done. Qed.

Lemma mk_addP_ne n (e:spexpr sword) st:
  (if (n =? 0)%num then mk_pair false e else Eapp2 Oadd n e) =[st]
  Eapp2 Oadd n e.
Proof.
  case: N.eqb_spec=> [->|]//=.
  by rewrite /wadd /n2w add0r.
Qed.

Lemma mk_addP_en n (e:spexpr sword) st:
  (if (n =? 0)%num then mk_pair false e else Eapp2 Oadd e n) =[st]
  Eapp2 Oadd e n.
Proof.
  case: N.eqb_spec=> [->|]//=.
  by rewrite /wadd /n2w addr0 ltnn.
Qed.

Lemma mk_addP (e1 e2:spexpr sword) st:
  mk_add e1 e2 =[st] Eapp2 Oadd e1 e2.
Proof.
  jm_destr e1;jm_destr e2 => //;rewrite /mk_add;
   try (apply: mk_addP_ne || apply:mk_addP_en).
  rewrite [iword_add _ _]surjective_pairing mk_pairP.
  (* FIXME: rewrite /=. is looping *)
  by rewrite /ssem_spexpr /ssem_sop2 iword_addP.
Qed.

Lemma mk_ltP_en n (e:spexpr sword) st:
  (if (n =? 0)%num then Ebool false else Eapp2 Olt e n) =[st] Eapp2 Olt e n.
Proof. by case: N.eqb_spec=> [->|]. Qed.

Lemma mk_ltP (e1 e2:spexpr sword) st:
  mk_lt e1 e2 =[st] Eapp2 Olt e1 e2.
Proof.
  jm_destr e1;jm_destr e2 => //;rewrite /mk_lt;
   try (apply: mk_ltP_en).
  by apply iword_ltbP.
Qed.

Lemma mk_op2P t1 t2 tr (o:sop2 t1 t2 tr) e1 e2 st:
  mk_op2 o e1 e2 =[st] Eapp2 o e1 e2.
Proof.
  case:o e1 e2 st.
  + by apply: mk_andP. + by apply: mk_orP. + by apply: mk_addP. 
  + by apply: mk_eqP. + by apply: mk_ltP.
  + done. + done.
Qed.

Lemma mk_op3P t1 t2 t3 tr (o:sop3 t1 t2 t3 tr) e1 e2 e3 st:
  mk_op3 o e1 e2 e3 =[st] Eapp3 o e1 e2 e3.
Proof. done. Qed.

Lemma mk_ifP_aux t b (e1 e2:spexpr t) st:
  match eval_eq e1 e2 with
  | Ok true => e1
  | _       => Eif b e1 e2
  end =[st] Eif b e1 e2.
Proof.                                                     
  case Heq: (eval_eq e1 e2) => [[]|] //.
  by move: Heq=> /(eval_eqP st) /= ->;case: ifP.
Qed.

Lemma mk_ifP t b (e1 e2:spexpr t) st: mk_if b e1 e2 =[st] Eif b e1 e2.
Proof. 
  by (jm_destr b=> //;try by apply:mk_ifP_aux)=> /=;case:ifP.
Qed.

(* -------------------------------------------------------------------------- *)
(* ** Substitution of variables by expressions                                 *)
(* -------------------------------------------------------------------------- *)

Definition vsubst := Mv.t  spexpr.
Definition vsubst_id := Mv.empty (fun x => Evar x).

Definition ssubst := Msv.t spexpr.
Definition ssubst_id := Msv.empty (fun x => Esvar x).

(*
Record asubst := {
  s_fv : Ssv.t; (* The set of symbolic variable occuring in the image of the subst *)
  s_v  : vsubst;
  s_s  : ssubst;
}.

Definition asubst_init fv mv : asubst := 
  {| s_fv := fv;
     s_v  := mv;
     s_s  := ssubst_id; |}.
*)
Fixpoint subst_spexpr st (s : vsubst) (pe : spexpr st) :=
  match pe in spexpr st_ return spexpr st_ with
  | Evar          v              => (*s.(s_v).[v]%mv *) s.[v]%mv
  | Esvar         x              => (*s.(s_s).[x]%msv*) x
  | Econst        c              => Econst c
  | Ebool         b              => Ebool  b
  | Eapp1 _ _     op pe1         =>
    Eapp1 op (subst_spexpr s pe1)
  | Eapp2 _ _ _   op pe1 pe2     => 
    Eapp2 op (subst_spexpr s pe1) (subst_spexpr s pe2)
  | Eapp3 _ _ _ _ op pe1 pe2 pe3 => 
    Eapp3 op (subst_spexpr s pe1) (subst_spexpr s pe2) (subst_spexpr s pe3)
  | Eif _ b pe1 pe2       => 
    Eif (subst_spexpr s b) (subst_spexpr s pe1) (subst_spexpr s pe2)
  end.

Fixpoint ewrite_rval (s:vsubst) {t} (l:rval t) : spexpr t -> vsubst :=
  match l in rval t_ return spexpr t_ -> vsubst with
  | Rvar x => fun v => s.[x <- v]%mv
  | Rpair t1 t2 rv1 rv2 => fun v => 
    ewrite_rval (ewrite_rval s rv2 (mk_snd v)) rv1 (mk_fst v) 
  end.

(*
Module WrInpE.
  Definition to := spexpr.
  Definition fst t1 t2 (e:spexpr (t1 ** t2)) := mk_fst e.
  Definition snd t1 t2 (e:spexpr (t1 ** t2)) := mk_snd e.
End WrInpE.

Module E := WRmake Mv WrInpE.

Lemma p2sp_fst st t1 t2 (e:pexpr (t1 ** t2)): 
   (WrInpE.fst (p2sp e)) =[st] p2sp (Papp1 (Ofst _ _) e).
Proof. by rewrite mk_fstP. Qed.

Lemma p2sp_snd st t1 t2 (e:pexpr (t1 ** t2)): 
   (WrInpE.snd (p2sp e)) =[st] p2sp (Papp1 (Osnd _ _) e).
Proof. by rewrite mk_sndP. Qed.

Definition map_ssem_pe st := 
  map (fun ts:E.tosubst => {|W.ts_to := ssem_spexpr st ts.(E.ts_to) |}).

Lemma map_ssem_pe_morph t (e2:spexpr t) l2 st r (e1:spexpr t) l1: 
   e1 =[st] e2 ->
   map_ssem_pe st l1 = map_ssem_pe st l2 ->
   map_ssem_pe st (E.write_subst r e1 l1) = 
   map_ssem_pe st (E.write_subst r e2 l2).
Proof.
  elim: r e1 e2 l1 l2 => /= [x | ?? r1 Hr1 r2 Hr2] e1 e2 l1 l2;first by move=> -> ->.
  move=> He Hl;apply Hr2;first by rewrite !mk_sndP /= He. 
  by apply Hr1=> //;rewrite !mk_fstP /= He.
Qed.

Lemma write_subst_map l st {t} (rv:rval t) (e:pexpr t) :
  W.write_subst rv (ssem_pexpr st.(vm) e) (map_ssem_pe st l) = 
  map_ssem_pe st (E.write_subst rv (p2sp e) l).
Proof.
  elim: rv e l=> {t} [ ??| ?? r1 Hr1 r2 Hr2 e] l //=.
  + by rewrite sem_p2sp.
  rewrite (@map_ssem_pe_morph _ (p2sp (Papp1 (Osnd _ _) e))
                                (E.write_subst r1 (p2sp (Papp1 (Ofst _ _) e)) l)).
  + by rewrite -Hr2 -Hr1. + by apply p2sp_snd.  
  apply map_ssem_pe_morph=> //;apply p2sp_fst.
Qed.

Lemma ssem_subst_map {t2} (pe:spexpr t2) st l :   
   ssem_spexpr st (subst_spexpr (asubst_init (E.write_vmap vsubst_id l)) pe) =
   ssem_spexpr {|pm := st.(pm); sm := st.(sm);
                 vm:= W.write_vmap st.(vm) (map_ssem_pe st l); |}
                 pe.
Proof.
  elim: pe => //= [| ???? He1 | ????? He1 ? He2 
                   | ?????? He1 ? He2 ? He3 | ?? He1 ? He2 ? He3];
    rewrite ?mk_op1P ?mk_op2P ?mk_op3P ?mk_ifP /= ?He1 ?He2 ?He3 //.
  elim: l => [ | [id e] l Hrec] x //=. 
  case: (boolP (id == x))=> [/eqP <-| ?].
  + by rewrite Fv.setP_eq Mv.setP_eq.
  by rewrite Fv.setP_neq // Mv.setP_neq. 
Qed.
 *)

(*
Fixpoint mk_subst_e t (e:spexpr t): spexpr t -> list E.tosubst -> list E.tosubst := 
  match e in spexpr t_ return spexpr t_ -> list E.tosubst -> list E.tosubst with 
  | Evar x => fun e' s => @E.ToSubst x e' :: s
  | Eapp2 _ _ _ o e1 e2 => 
    match o in sop2 t1 t2 tr return 
      spexpr t1 -> spexpr t2 -> spexpr tr -> list E.tosubst -> list E.tosubst with
    | Opair _ _ => fun e1 e2 e' s => mk_subst_e e2 (mk_snd e') (mk_subst_e e1 (mk_fst e') s)
    | _         => fun e1 e2 e' s => s
    end e1 e2
  | _ => fun _ s => s
  end.

Fixpoint mk_subst_v t (e:spexpr t): sst2ty t -> list W.tosubst -> list W.tosubst := 
  match e in spexpr t_ return sst2ty t_ -> list W.tosubst -> list W.tosubst with 
  | Evar x => fun e' s => @W.ToSubst x e' :: s
  | Eapp2 _ _ _ o e1 e2 => 
    match o in sop2 t1 t2 tr return 
      spexpr t1 -> spexpr t2 -> sst2ty tr -> list W.tosubst -> list W.tosubst with
    | Opair _ _ => fun e1 e2 e' s => mk_subst_v e2 (snd e') (mk_subst_v e1 (fst e') s)
    | _         => fun e1 e2 e' s => s
    end e1 e2
  | _ => fun _ s => s
  end.

Lemma mk_subst_map st {t} (e1 e2:spexpr t) l:
  mk_subst_v e1 (ssem_spexpr st e2) (map_ssem_pe st l) = 
  map_ssem_pe st (mk_subst_e e1 e2 l).
Proof.
  elim: e1 e2 l => {t} //= ??? -[] //= ?? e1 He1 e2 He2 e' l.
  by rewrite -He2 -He1 mk_sndP mk_fstP.
Qed.
*)

(*
(* -------------------------------------------------------------------------- *)
(* ** merge_if b e1 e2                                                        *)
(* -------------------------------------------------------------------------- *)

Fixpoint merge_if (b:spexpr sbool) {t} : spexpr t -> spexpr t ->  spexpr t := 
  match t as t_  return spexpr t_ -> spexpr t_ ->  spexpr t_ with
  | sprod t1 t2 => fun p p' => 
    match destr_pair p, destr_pair p' with
    | Some(p1,p2), Some(p1', p2') => 
      Eapp2 (Opair _ _) (merge_if b p1 p1') (merge_if b p2 p2')
    | _, _ => mk_if b p p'
    end
  | _ => fun p p' => mk_if b p p'
  end.

Lemma merge_ifP t b (e e':spexpr t) st:
  merge_if b e e' =[st] Eif b e e'.
Proof.
  elim:t e e' st=>[ | |t1 Ht1 t2 Ht2 | n t Ht];try apply mk_ifP.
  move=> /= e e' st.
  case He: destr_pair => [[p1 p2] | ];try by rewrite mk_ifP.
  case He': destr_pair => [[p1' p2'] | ];try by rewrite mk_ifP.
  by rewrite /= Ht1 Ht2 (destr_pairP He) (destr_pairP He') /=;case:ifP.
Qed.
*)

(* -------------------------------------------------------------------------- *)
(* ** symbolic formula                                                        *)
(* -------------------------------------------------------------------------- *)

Inductive sform : Type := 
  | Fbool   : spexpr sbool -> sform 
  | Fpred   : forall (p:svar), spexpr p.(svtype) -> sform
  | Fnot    : sform -> sform 
  | Fand    : sform -> sform -> sform 
  | For     : sform -> sform -> sform
  | Fimp    : sform -> sform -> sform
  | Fif     : spexpr sbool -> sform -> sform -> sform
  | Fforall : svar -> sform -> sform.

Fixpoint ssem_sform (st:sstate) f : Prop := 
  match f with
  | Fbool   e     => ssem_spexpr st e 
  | Fpred   p  e  => st.(pm).[p]%msv (ssem_spexpr st e)
  | Fnot    f     => ~ ssem_sform st f
  | Fand    f1 f2 => ssem_sform st f1 /\ ssem_sform st f2
  | For     f1 f2 => ssem_sform st f1 \/ ssem_sform st f2
  | Fimp    f1 f2 => ssem_sform st f1 -> ssem_sform st f2
  | Fif   b f1 f2 => 
    if ssem_spexpr st b then ssem_sform st f1 
    else ssem_sform st f2 
  | Fforall x  f  => 
    forall (v:sst2ty x.(svtype)),
      ssem_sform {| pm := st.(pm); sm := st.(sm).[x <- v]%msv; vm:= st.(vm) |} f
  end.

(* -------------------------------------------------------------------------- *)
(* ** program variables occuring in a formula                                 *)
(* -------------------------------------------------------------------------- *)

Fixpoint ffv_rec  (f:sform) (s:Sv.t) := 
  match f with
  | Fbool   e     => fv_rec e s
  | Fpred   _  e  => fv_rec e s 
  | Fnot    f     => ffv_rec f s
  | Fand    f1 f2 => ffv_rec f1 (ffv_rec f2 s)
  | For     f1 f2 => ffv_rec f1 (ffv_rec f2 s)
  | Fimp    f1 f2 => ffv_rec f1 (ffv_rec f2 s)
  | Fif   b f1 f2 => fv_rec  b  (ffv_rec f1 (ffv_rec f2 s))
  | Fforall _  f  => ffv_rec f s
  end.

Definition ffv f := ffv_rec f Sv.empty.

Add Morphism ffv_rec with 
    signature ((@Logic.eq sform) ==> Sv.Equal ==> Sv.Equal)%signature as ffv_rec_m.
Proof.
  elim=> //= [? | ?? | ? He1 ? He2 | ? He1 ? He2 | ? He1 ? He2 | ?? He1 ? He2 ] ?? Heq.
  + by rewrite Heq.       + by rewrite Heq.
  + by apply /He1 /He2.   + by apply /He1 /He2.   + by apply /He1 /He2. 
  by apply /fv_rec_m /He1 /He2.
Qed.

Lemma ffv_recE (f:sform) s : Sv.Equal (ffv_rec f s) (Sv.union (ffv f) s).
Proof.
  elim: f s => //= [? | ?? | ? He1 ? He2 | ? He1 ? He2 | ? He1 ? He2 | ?? He1 ? He2 ] ?.
  + by rewrite fv_recE.   + by rewrite fv_recE. 
  + by rewrite He1 He2 /ffv /= -!/(ffv _) He1 SvP.MP.union_assoc.
  + by rewrite He1 He2 /ffv /= -!/(ffv _) He1 SvP.MP.union_assoc.
  + by rewrite He1 He2 /ffv /= -!/(ffv _) He1 SvP.MP.union_assoc.
  by rewrite fv_recE He1 He2 /ffv /= -!/(ffv _) fv_recE He1 !SvP.MP.union_assoc.
Qed.

Lemma ffv_bool (e:spexpr sbool) : ffv (Fbool e) = fv e.
Proof. done. Qed.

Lemma ffv_pred  p e : ffv (@Fpred p e) = fv e.
Proof. done. Qed.

Lemma ffv_not f : ffv (Fnot f) = ffv f.
Proof. done. Qed.

Lemma ffv_and f1 f2 : Sv.Equal (ffv (Fand f1 f2)) (Sv.union (ffv f1) (ffv f2)).
Proof. rewrite /ffv /= !ffv_recE;SvD.fsetdec. Qed.

Lemma ffv_or f1 f2 : Sv.Equal (ffv (For f1 f2)) (Sv.union (ffv f1) (ffv f2)).
Proof. rewrite /ffv /= !ffv_recE;SvD.fsetdec. Qed.

Lemma ffv_imp f1 f2 : Sv.Equal (ffv (Fimp f1 f2)) (Sv.union (ffv f1) (ffv f2)).
Proof. rewrite /ffv /= !ffv_recE;SvD.fsetdec. Qed.

Lemma ffv_if e f1 f2 : 
  Sv.Equal (ffv (Fif e f1 f2)) (Sv.union (fv e) (Sv.union (ffv f1) (ffv f2))).
Proof. rewrite /ffv /= !ffv_recE fv_recE;SvD.fsetdec. Qed.

Lemma ffv_forall x f :
  Sv.Equal (ffv (Fforall x f)) (ffv f).
Proof. done. Qed.
  
(* -------------------------------------------------------------------------- *)
(* ** symbolic variables occuring in a formula                                 *)
(* -------------------------------------------------------------------------- *)

Fixpoint sffv_rec  (f:sform) (s:Ssv.t) := 
  match f with
  | Fbool   e     => sfv_rec e s
  | Fpred   _  e  => sfv_rec e s 
  | Fnot    f     => sffv_rec f s
  | Fand    f1 f2 => sffv_rec f1 (sffv_rec f2 s)
  | For     f1 f2 => sffv_rec f1 (sffv_rec f2 s)
  | Fimp    f1 f2 => sffv_rec f1 (sffv_rec f2 s)
  | Fif   b f1 f2 => sfv_rec  b  (sffv_rec f1 (sffv_rec f2 s))
  | Fforall x  f  => sffv_rec f (Ssv.add x s)
(*    let s' := sffv_rec f s in
    if Ssv.mem x s then s' else Ssv.remove x s' *)
  end.

Definition sffv f := sffv_rec f Ssv.empty.

Add Morphism sffv_rec with 
    signature ((@Logic.eq sform) ==> Ssv.Equal ==> Ssv.Equal)%signature as sffv_rec_m.
Proof.
  elim=> //=[? | ?? | ? He1 ? He2 | ? He1 ? He2 | ? He1 ? He2 | ?? He1 ? He2 | x? He1] s1 s2 Heq.
  + by rewrite Heq.       + by rewrite Heq.
  + by apply /He1 /He2.   + by apply /He1 /He2.   + by apply /He1 /He2. 
  + by apply /sfv_rec_m /He1 /He2.
  by apply He1;rewrite Heq.
Qed.

Lemma sffv_recE (f:sform) s : Ssv.Equal (sffv_rec f s) (Ssv.union (sffv f) s).
Proof.
  elim: f s => //= [? | ?? | ? He1 ? He2 | ? He1 ? He2 | ? He1 ? He2 | ?? He1 ? He2 | x? He1] s.
  + by rewrite sfv_recE.   + by rewrite sfv_recE. 
  + by rewrite He1 He2 /sffv /= -!/(sffv _) He1 SsvP.MP.union_assoc.
  + by rewrite He1 He2 /sffv /= -!/(sffv _) He1 SsvP.MP.union_assoc.
  + by rewrite He1 He2 /sffv /= -!/(sffv _) He1 SsvP.MP.union_assoc.
  + by rewrite sfv_recE He1 He2 /sffv /= -!/(sffv _) sfv_recE He1 !SsvP.MP.union_assoc.
  rewrite /sffv /=; rewrite !He1;SsvD.fsetdec.
Qed.

Lemma sffv_bool (e:spexpr sbool) : sffv (Fbool e) = sfv e.
Proof. done. Qed.

Lemma sffv_pred  p e : sffv (@Fpred p e) = sfv e.
Proof. done. Qed.

Lemma sffv_not f : sffv (Fnot f) = sffv f.
Proof. done. Qed.

Lemma sffv_and f1 f2 : Ssv.Equal (sffv (Fand f1 f2)) (Ssv.union (sffv f1) (sffv f2)).
Proof. rewrite /sffv /= !sffv_recE;SsvD.fsetdec. Qed.

Lemma sffv_or f1 f2 : Ssv.Equal (sffv (For f1 f2)) (Ssv.union (sffv f1) (sffv f2)).
Proof. rewrite /sffv /= !sffv_recE;SsvD.fsetdec. Qed.

Lemma sffv_imp f1 f2 : Ssv.Equal (sffv (Fimp f1 f2)) (Ssv.union (sffv f1) (sffv f2)).
Proof. rewrite /sffv /= !sffv_recE;SsvD.fsetdec. Qed.

Lemma sffv_if e f1 f2 : 
  Ssv.Equal (sffv (Fif e f1 f2)) (Ssv.union (sfv e) (Ssv.union (sffv f1) (sffv f2))).
Proof. rewrite /sffv /= !sffv_recE sfv_recE;SsvD.fsetdec. Qed.
 
Lemma sffv_forall x f :  Ssv.Equal (sffv (Fforall x f)) (Ssv.add x (sffv f)).
Proof. rewrite /sffv /= !sffv_recE;SsvD.fsetdec. Qed.

(* -------------------------------------------------------------------------- *)
(* ** Substitution of variables by expressions into formulas                  *)
(* -------------------------------------------------------------------------- *)

Definition fresh_svar (s:Ssv.t) := 
  let add v m := if (v.(svname) <? m)%positive then m else v.(svname) in
  let max := Ssv.fold add s xH in   
  Pos.succ max.

(*
Definition subst_rename s f x :=
 (* if Ssv.mem x s.(s_fv) then *)
    let all := Ssv.union s.(s_fv) (sffv f) in
    let x' := {| svtype := x.(svtype); svname := fresh_svar all; |} in
    (x', {| s_fv := Ssv.add x' s.(s_fv);
            s_v  := s.(s_v);
            s_s  := s.(s_s).[x <- Esvar x']%msv |})
 (* else 
    (x, {| s_fv := s.(s_fv);
           s_v  := s.(s_v);
           s_s  := Msv.remove s.(s_s) x |}) *).
 
Fixpoint subst_sform (s:asubst) (f:sform) := 
  match f with
  | Fbool   e     => Fbool (subst_spexpr s e)
  | Fpred   p  e  => @Fpred p (subst_spexpr s e)
  | Fnot    f     => Fnot  (subst_sform s f)
  | Fand    f1 f2 => Fand  (subst_sform s f1) (subst_sform s f2) 
  | For     f1 f2 => For   (subst_sform s f1) (subst_sform s f2) 
  | Fimp    f1 f2 => Fimp  (subst_sform s f1) (subst_sform s f2) 
  | Fif   b f1 f2 => Fif   (subst_spexpr s b) (subst_sform s f1) (subst_sform s f2) 
  | Fforall x  f  => 
      let (x',s)  := subst_rename s f x in
      Fforall x' (subst_sform s f)
  end.
*)

Fixpoint subst_sform (s:vsubst) (f:sform) := 
  match f with
  | Fbool   e     => Fbool (subst_spexpr s e)
  | Fpred   p  e  => @Fpred p (subst_spexpr s e)
  | Fnot    f     => Fnot  (subst_sform s f)
  | Fand    f1 f2 => Fand  (subst_sform s f1) (subst_sform s f2) 
  | For     f1 f2 => For   (subst_sform s f1) (subst_sform s f2) 
  | Fimp    f1 f2 => Fimp  (subst_sform s f1) (subst_sform s f2) 
  | Fif   b f1 f2 => Fif   (subst_spexpr s b) (subst_sform s f1) (subst_sform s f2) 
  | Fforall x  f  => Fforall x (subst_sform s f)
  end.

Notation "f1 '=_[' st1 , st2 ']' e2" := (ssem_sform st1 f1 <-> ssem_sform st2 e2)
 (at level 70, no associativity).

Notation "f1 '=_[' st ']' f2" := (ssem_sform st f1 <-> ssem_sform st f2)
 (at level 70, no associativity).

(*Class  wf_asubst (s:asubst) := {
  dft_v  : Mv.dft  s.(s_v) = fun x => Evar x;
  dft_s  : Msv.dft s.(s_s) = fun x => Esvar x;
  indom_v : forall x, Mv.indom x s.(s_v)  -> Ssv.Subset (sfv s.(s_v).[x]%mv)  s.(s_fv);
  indom_s : forall x, Msv.indom x s.(s_s) -> Ssv.Subset (sfv s.(s_s).[x]%msv) s.(s_fv);
}. *)

(*
(* TODO: move this *)
Lemma forall_iff A (P1 P2:A-> Prop): 
  (forall x, P1 x <-> P2 x) -> (forall (x:A), P1 x) <-> (forall x, P2 x).
Proof.
  by move=> H;split=> Hx x;move: (Hx x);rewrite H.
Qed.

Lemma ssem_sform_fv f st1 st2 : 
  st1.(pm) = st2.(pm) -> st1 ={ ffv f, sffv f} st2 -> f =_[ st1, st2] f.
Proof.
  elim: f st1 st2=> //= 
    [ ? | ?? | f1 Hf1 | f1 Hf1 f2 Hf2 | f1 Hf1 f2 Hf2 | f1 Hf1 f2 Hf2 
    | ? f1 Hf1 f2 Hf2 | x f1 Hf1] st1 st2 Hpm.
  + by rewrite ffv_bool sffv_bool=> H;rewrite -(ssem_spexpr_fv H).
  + by rewrite Hpm ffv_pred sffv_pred=> H;rewrite -(ssem_spexpr_fv H). 
  + by rewrite ffv_not sffv_not=> H;rewrite (Hf1 _ _ Hpm H).
  + by rewrite ffv_and sffv_and=> H;rewrite (Hf1 _ _ Hpm) ?(Hf2 _ _ Hpm) //;
    apply: eq_on_m H=> //;(SvD.fsetdec || SsvD.fsetdec).
  + by rewrite ffv_or sffv_or=> H;rewrite (Hf1 _ _ Hpm) ?(Hf2 _ _ Hpm) //;
    apply: eq_on_m H=> //;(SvD.fsetdec || SsvD.fsetdec).
  + by rewrite ffv_imp sffv_imp=> H;rewrite (Hf1 _ _ Hpm) ?(Hf2 _ _ Hpm) //;
    apply: eq_on_m H=> //;(SvD.fsetdec || SsvD.fsetdec).
  + rewrite ffv_if sffv_if=> H;rewrite (@ssem_spexpr_fv _ _ st1 st2);
     last by apply: eq_on_m H=> //;(SvD.fsetdec || SsvD.fsetdec).
    (* case: ssem_spexpr.  (Enrico : Bug ?) *)
    case: (ssem_spexpr _);[apply Hf1 | apply Hf2]=>//;apply: eq_on_m H;
    (SvD.fsetdec || SsvD.fsetdec).
  rewrite ffv_forall sffv_forall=> H; apply forall_iff=> v;apply Hf1=> //=.
  constructor=> /= z Hz;first by apply H.
  case: (x =P z) => [<- | /eqP neq];rewrite ?Msv.setP_eq // ?Msv.setP_neq //.
  apply H;move: neq=> /eqP;SsvD.fsetdec.
Qed.

Lemma ssem_subst_spexpr st2 st1 t (e:spexpr t) s: 
  (forall (x:var), Sv.In x (fv e) -> subst_spexpr s x =[st1, st2] x) ->
  (forall (x:svar), Ssv.In x (sfv e) -> subst_spexpr s x =[st1, st2] x) ->
  subst_spexpr s e =[st1,st2] e.
Proof.
  set fve := fv e; set sfve := sfv e. 
  have : Sv.Subset (fv e) fve by done.
  have : Ssv.Subset (sfv e) sfve by done.
  move: fve sfve=> fve sfve Hs Hv Hfv Hsfv. (* Enrico : comment on fait le let *)
  elim: e Hv Hs => //=
   [x | x | ?? o e1 He1 | ??? o e1 He1 e2 He2 
   | ???? o e1 He1 e2 He2 e3 He3 | ? e1 He1 e2 He2 e3 He3] Hv Hs. 
  + by rewrite Hfv //;move:Hv;rewrite fv_var;SvD.fsetdec. 
  + by rewrite Hsfv //;move:Hs;rewrite sfv_svar;SsvD.fsetdec. 
  + rewrite mk_op1P /= He1 //.
  + by rewrite mk_op2P /= He1 ?He2 //;move: Hv Hs;rewrite fv_op2 sfv_op2;
     (SvD.fsetdec || SsvD.fsetdec). 
  + by rewrite He1 ?He2 ?He3 //;move: Hv Hs;rewrite fv_op3 sfv_op3;
     (SvD.fsetdec || SsvD.fsetdec).
  by rewrite mk_ifP /= He1 ?He2 ?He3 //; move: Hv Hs;rewrite fv_if sfv_if;
   (SvD.fsetdec || SsvD.fsetdec).
Qed.

Lemma fresh_svarP t s: ~ Ssv.In {|svtype := t; svname := fresh_svar s|} s.
Proof.
  rewrite /fresh_svar.
  have Hf: forall p x, Ssv.In x s -> 
    (x.(svname) <= (Ssv.fold
                     (fun (v : svar) (m : positive) =>
                      if (svname v <? m)%positive then m else svname v) s p))%positive.
  + move=> p x;apply SsvP.MP.fold_rec.
    + by move=> ? He H;elim (He _ H).
    move=> {p} z p s1 s2 _ Hnin Ha Hrec /Ha [-> | Hn].
    + by case: Pos.ltb_spec0=> [|_];[ apply: Pos.lt_le_incl | apply Pos.le_refl].
    apply (Pos.le_trans _ p);first by auto.
    by case: Pos.ltb_spec0=> [_|?];[apply Pos.le_refl | rewrite Pos.le_nlt].
  by move=> /(Hf xH) /=;rewrite Pos.le_succ_l;apply Pos.lt_irrefl.
Qed.

Lemma ssem_subst_sform st2 st1 f s `{wf_asubst s}  : 
  st1.(pm) = st2.(pm) ->
  (forall (x:var), Sv.In x (ffv f) -> subst_spexpr s x =[st1, st2] x) ->
  (forall (x:svar), Ssv.In x (sffv f) -> subst_spexpr s x =[st1, st2] x) ->
  subst_sform s f =_[st1, st2] f.
Proof.
  elim: f st2 st1 s H => /=
    [ e | ?? | f1 Hf1 | f1 Hf1 f2 Hf2 | f1 Hf1 f2 Hf2 | f1 Hf1 f2 Hf2 
    | ? f1 Hf1 f2 Hf2 | [xt xn] f1 Hf1] st2 st1 s Hwf Hpm => Hfv Hsfv.
  + by rewrite (@ssem_subst_spexpr st2).
  + by rewrite Hpm (@ssem_subst_spexpr st2).
  + by rewrite (Hf1 st2).
  + by rewrite (Hf1 st2) ?(Hf2 st2) // => ??;
     ((apply Hfv;rewrite ffv_and;SvD.fsetdec) || 
      (apply Hsfv;rewrite sffv_and;SsvD.fsetdec)). 
  + by rewrite (Hf1 st2) ?(Hf2 st2) // => ??;
     ((apply Hfv;rewrite ffv_or;SvD.fsetdec) || 
      (apply Hsfv;rewrite sffv_or;SsvD.fsetdec)). 
  + by rewrite (Hf1 st2) ?(Hf2 st2) // => ??;
     ((apply Hfv;rewrite ffv_imp;SvD.fsetdec) || 
      (apply Hsfv;rewrite sffv_imp;SsvD.fsetdec)). 
  + rewrite (@ssem_subst_spexpr st2);
    try (move=> ??;((apply Hfv;rewrite ffv_if;SvD.fsetdec) || 
         (apply Hsfv;rewrite sffv_if;SsvD.fsetdec))).
    by case: (ssem_spexpr _);[apply Hf1 | apply Hf2]=> // ??;
     ((apply Hfv;rewrite ffv_if;SvD.fsetdec) || 
      (apply Hsfv;rewrite sffv_if;SsvD.fsetdec)). 
  case Heq: (subst_rename s f1 (SVar xt xn))=> [x' s'] /=.
  have -> /=: x' = SVar xt x'.(svname).
  + by move: Heq;rewrite /subst_rename /=;case: Ssv.mem => /= -[] <-.
  apply forall_iff=> v;apply Hf1=> //=;
    move:Heq;rewrite /subst_rename /=;case:Ssv_memP=> /= Hin -[] ? <-//=;subst=>/=.
  + constructor => /=.  
    + by apply dft_v.  + by apply dft_s.
    + by move=> x /indom_v;SsvD.fsetdec.
    move=> x;rewrite Msv.indom_setP; case: eqP=> /= [<- _ | /eqP Hne].
    + by rewrite Msv.setP_eq /sfv /=;SsvD.fsetdec.
    by rewrite Msv.setP_neq // => /indom_s;SsvD.fsetdec.
  + constructor => /=. 
    + by apply dft_v. + by rewrite Msv.dft_removeP;apply dft_s.
    + by move=> x /indom_v;SsvD.fsetdec.
    move=> x;rewrite Msv.indom_removeP; case: eqP=> /= [// | /eqP Hne].
    by rewrite Msv.removeP_neq // => /indom_s.
  + move=> x Hx;rewrite -Hfv //; apply ssem_spexpr_fv.
    constructor=> // z Hz /=;rewrite Msv.setP_neq //.
    apply /eqP=> Heq;apply(@fresh_svarP xt (Ssv.union (s_fv s) (sffv f1))).
    have := @indom_v _ Hwf x; have := @Mv.indom_getP _ (s_v s) x.
    rewrite Heq dft_v;case: Mv.indom=>[ _ /(_ (erefl _)) |  /(_ (erefl _)) H _].
    + by SsvD.fsetdec.
    by move: Hz;rewrite H sfv_var;SsvD.fsetdec.
  + move=> x Hx;rewrite -Hfv //; apply ssem_spexpr_fv.
    constructor=> // z Hz /=;rewrite Msv.setP_neq //.
    apply /eqP=> ?;subst.
    have := @indom_v _ Hwf x; have := @Mv.indom_getP _ (s_v s) x.
    rewrite dft_v;case: Mv.indom=>[ _ /(_ (erefl _)) |  /(_ (erefl _)) H _].
    + by SsvD.fsetdec.
    by move: Hz;rewrite H sfv_var;SsvD.fsetdec.
  + move=> z Hz;have Hnin:= @fresh_svarP xt (Ssv.union (s_fv s) (sffv f1)).
    move:Hin; set x  := (SVar _ _)=> Hin.
    move:Hnin;set x' := (SVar _ _)=> Hnin.
    case: (x =P z) => [<- | /eqP Hxz].
    + by rewrite !Msv.setP_eq /= Msv.setP_eq.
    rewrite !Msv.setP_neq //;move: Hxz=> /eqP Hxz.
    rewrite -Hsfv;last by rewrite sffv_forall -/x;SsvD.fsetdec.
    apply ssem_spexpr_fv;constructor=> // y Hy /=;rewrite Msv.setP_neq //.
    apply /eqP=> ?;subst y.
    have := @indom_s _ Hwf z; have := @Msv.indom_getP _ (s_s s) z.
    rewrite dft_s;case: Msv.indom=>[ _ /(_ (erefl _)) |  /(_ (erefl _)) H _].
    + by SsvD.fsetdec.
    by move: Hy;rewrite H sfv_svar;SsvD.fsetdec.
  move=> z Hz;have Hnin:= @fresh_svarP xt (Ssv.union (s_fv s) (sffv f1)).
  move:Hin; set x  := (SVar _ _)=> Hin.
  move:Hnin;set x' := (SVar _ _)=> Hnin.
  case: (x =P z) => [Heq | /eqP Hxz].
  + by subst z;rewrite !Msv.setP_eq Msv.removeP_eq dft_s /= Msv.setP_eq.
  rewrite Msv.setP_neq // Msv.removeP_neq //= -Hsfv.
  + have := @indom_s _ Hwf z; have := @Msv.indom_getP _ (s_s s) z.
    rewrite dft_s;case: Msv.indom=>[ _ /(_ (erefl _)) Hsub|  /(_ (erefl _)) ->/= _].
    + apply ssem_spexpr_fv;constructor=> w Hw //=.
      by rewrite Msv.setP_neq //;apply /eqP=> ?;subst w;SsvD.fsetdec.
    by rewrite Msv.setP_neq.
  by rewrite sffv_forall -/x;move: Hxz=>/eqP;SsvD.fsetdec.
Qed.

 

*)