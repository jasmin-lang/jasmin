(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple finfun.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import gen_map word dmasm_utils dmasm_type dmasm_var dmasm_expr 
               dmasm_Ssem dmasm_Ssem_props.

Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

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

Definition eeq t (e1 e2:spexpr t) := forall rho, e1 =[rho] e2.

Instance eeq_R t: Equivalence (@eeq t).
Proof. 
  constructor => //.
  + by move=> f1 f2 Heq s;rewrite Heq.
  by move=> f1 f2 f3 Heq1 Heq2 s;rewrite Heq1.
Qed.

Notation "e1 '=E' e2" := (eeq e1 e2) (at level 70, no associativity).

Instance Eapp1_m t1 tr (o:sop1 t1 tr) : Proper (@eeq t1 ==> @eeq tr) (Eapp1 o).
Proof. by move=> ?? H rho /=;rewrite (H rho). Qed.

Instance Eapp2_m t1 t2 tr (o:sop2 t1 t2 tr) : 
  Proper (@eeq t1 ==> @eeq t2 ==> @eeq tr) (Eapp2 o).
Proof. by move=> ?? H1 ?? H2 rho /=;rewrite (H1 rho) (H2 rho). Qed.

Instance Eapp3_m t1 t2 t3 tr (o:sop3 t1 t2 t3 tr) : 
  Proper (@eeq t1 ==> @eeq t2 ==> @eeq t3 ==> @eeq tr) (Eapp3 o).
Proof. by move=> ?? H1 ?? H2 ?? H3 rho /=;rewrite (H1 rho) (H2 rho) (H3 rho). Qed.

Instance Eif_m t : 
  Proper (@eeq sbool ==> @eeq t ==> @eeq t ==> @eeq t) (@Eif t).
Proof. by move=> ?? H1 ?? H2 ?? H3 rho /=;rewrite (H1 rho) (H2 rho) (H3 rho). Qed.

Lemma Eif_eq b t (e:spexpr t) : Eif b e e =E e.
Proof. by move=> rho /=;case:ifP. Qed.

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
Lemma fv_rval2pe t (i:rval t): Sv.Equal (fv (p2sp (rval2pe i))) (vrv i).
Proof.
  elim: i => //= ?? r1 Hr1 r2 Hr2.
  by rewrite fv_op2 Hr1 Hr2 vrv_pair.
Qed.

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

Lemma sfv_p2sp t (e:pexpr t) : Ssv.Equal (sfv (p2sp e)) Ssv.empty.
Proof.
  apply SsvP.MP.empty_is_empty_1.
  elim: e => //= *;rewrite ?sfv_var ?sfv_const ?sfv_op2 ?sfv_op3; SsvD.fsetdec.
Qed.

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

Lemma eq_on_fv t (e:spexpr t) st1 st2: 
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

Lemma eq_on_trans st2 st1 st3 fv1 fv2 : 
  st1 ={fv1, fv2} st2 -> st2 ={fv1, fv2} st3 -> st1 ={fv1, fv2} st3.
Proof.
  move=> H1 H2;constructor=> ??.
  + by rewrite (eq_on_v H1) // (eq_on_v H2).
  by rewrite (eq_on_s H1) // (eq_on_s H2).
Qed.
 
(* -------------------------------------------------------------------------- *)
(* ** Parallel Substitution                                                   *)
(* -------------------------------------------------------------------------- *)

Definition vsubst := Mv.t  spexpr.
Definition vs0    := Mv.empty [eta Evar].

Definition pssubst := Msv.t spexpr.
Definition pss0     := Msv.empty [eta Esvar].

Record pvsubst := {
  v_fv : Ssv.t; (* The set of symbolic variable occuring in the image of the subst *)
  v_v  : vsubst;
}.

Record psubst := {
  s_fv : Ssv.t; (* The set of symbolic variable occuring in the image of the subst *)
  s_v  : vsubst;
  s_s  : pssubst;
}.

Class  wf_vsubst (s:pvsubst) := {
  vdft_v  : forall x, Mv.dft s.(v_v) x = Evar x;
  vindom_v : forall x, Mv.indom x s.(v_v)  -> Ssv.Subset (sfv s.(v_v).[x]%mv)  s.(v_fv);
}.

Class  wf_psubst (s:psubst) := {
  dft_v  : forall x, Mv.dft s.(s_v) x = Evar x;
  dft_s  : forall x, Msv.dft s.(s_s) x = Esvar x;
  indom_v : forall x, Mv.indom x s.(s_v)  -> Ssv.Subset (sfv s.(s_v).[x]%mv)  s.(s_fv);
  indom_s : forall x, Msv.indom x s.(s_s) -> Ssv.Subset (sfv s.(s_s).[x]%msv) s.(s_fv);
}.

Definition pvs2ps (s:pvsubst) : psubst := {|
  s_fv := s.(v_fv);
  s_v  := s.(v_v);
  s_s  := pss0;
|}.

Coercion pvs2ps : pvsubst >-> psubst.

Instance wf_pvs2ps s {_: wf_vsubst s} : wf_psubst s.
Proof. by constructor=> //;[apply vdft_v|apply vindom_v]. Qed.

Definition ssubst (s:psubst) (rho:sstate) := 
  {| pm := pm rho; 
     sm := Msv.empty (fun x => ssem_spexpr rho (s.(s_s).[x]%msv)); 
     vm := Fv.empty (fun x => ssem_spexpr rho (s.(s_v).[x]%mv)); |}.

Definition pvs1 := {| v_fv := Ssv.empty; v_v := vs0 |}.

Instance wf_pvs1 : wf_vsubst pvs1.
Proof. by constructor. Qed.

Definition ps1 := {| s_fv := Ssv.empty; s_v := vs0; s_s := pss0 |}.

Instance wf_ps1 : wf_psubst ps1.
Proof. by constructor. Qed.

Lemma ps1P rho sv ss : ssubst ps1 rho ={ sv, ss} rho.
Proof. by constructor => ?? /=;rewrite ?Fv.get0 ?Msv.get0. Qed.

(* -------------------------------------------------------------------------- *)
(* ** Substitution of variables by expressions                                *)
(* -------------------------------------------------------------------------- *)

Fixpoint esubst st (s : psubst) (pe : spexpr st) :=
  match pe in spexpr st_ return spexpr st_ with
  | Evar          v              => s.(s_v).[v]%mv 
  | Esvar         x              => s.(s_s).[x]%msv
  | Econst        c              => Econst c
  | Ebool         b              => Ebool  b
  | Eapp1 _ _     op pe1         =>
    Eapp1 op (esubst s pe1)
  | Eapp2 _ _ _   op pe1 pe2     => 
    Eapp2 op (esubst s pe1) (esubst s pe2)
  | Eapp3 _ _ _ _ op pe1 pe2 pe3 => 
    Eapp3 op (esubst s pe1) (esubst s pe2) (esubst s pe3)
  | Eif _ b pe1 pe2       => 
    Eif (esubst s b) (esubst s pe1) (esubst s pe2)
  end.

Fixpoint ewrite_rval (s:vsubst) {t} (l:rval t) : spexpr t -> vsubst :=
  match l in rval t_ return spexpr t_ -> vsubst with
  | Rvar x => fun v => s.[x <- v]%mv
  | Rpair t1 t2 rv1 rv2 => fun v => 
    ewrite_rval (ewrite_rval s rv2 (Eapp1 (Osnd _ _) v)) rv1 (Eapp1 (Ofst _ _) v) 
  end.

Lemma esubstP rho s t (e:spexpr t) :
  esubst s e =[rho, ssubst s rho] e.
Proof.
  by elim: e => //= [???? ->|????? -> ? ->|?????? -> ? -> ? ->|?? -> ? -> ? ->].
Qed.

Lemma ewrite_rvalP rho vm s t (rv:rval t) e: 
   (forall (x:var), ssem_spexpr rho s.[x]%mv = vm.[x]%vmap) ->
   forall (x:var),  
     ssem_spexpr rho (ewrite_rval s rv e).[x]%mv =
     (swrite_rval vm rv (ssem_spexpr rho e)).[x]%vmap.
Proof.
  elim: rv e s rho vm => [z | ?? r1 Hr1 r2 Hr2] e s rho vm Hrho x /=.
  + case: (z =P x)=> [<- | /eqP neq].
    + by rewrite Mv.setP_eq Fv.setP_eq.
    by rewrite Mv.setP_neq // Fv.setP_neq//;apply Hrho.
  by apply Hr1=> ?;apply Hr2.
Qed.

Definition ewrite t (rv:rval t) e efv :=
  {| v_fv := efv;
     v_v := ewrite_rval vs0 rv e; |}.

Instance wf_ewrite t (rv:rval t) e xs: Ssv.Subset (sfv e) xs -> wf_vsubst (ewrite rv e xs).
Proof. 
  move=> Heq; constructor;rewrite /ewrite /=.
  + move=> x;have : Mv.dft vs0 x = Evar x by done.
    by elim: rv e vs0 {Heq} => //= ?? r1 Hr1 r2 Hr2 e s Hs;auto. 
  pose P vs := forall x : var,  Mv.indom x vs -> Ssv.Subset (sfv vs.[x]%mv) xs.
  rewrite -/(P (ewrite_rval vs0 rv e)).
  have : P vs0.
  + by move=> x;rewrite (negbTE (Mv.indom0 _ x)).
  elim: rv e vs0 Heq => [z | ??? Hr1 ? Hr2] e sv /= Hsub Hsv x.
  + rewrite Mv.indom_setP;case: eqP=> /= [<- _|/eqP ??].
    + by rewrite Mv.setP_eq.
    by rewrite Mv.setP_neq //;apply Hsv.  
  by apply Hr1;rewrite ?sfv_op1 //;apply Hr2;rewrite ?sfv_op2.
Qed.

Lemma indom_ewrite_rval s t(i:rval t) v x : 
   Mv.indom x (ewrite_rval s i v) <->  Sv.In x (vrv i) \/ Mv.indom x s.
Proof.
  elim:i v s => [y | ?? r1 Hr1 r2 Hr2] v s /=.
  + by rewrite Mv.indom_setP vrv_var SvD.F.singleton_iff -(rwP orP) -(rwP eqP).
  rewrite vrv_pair Sv.union_spec Hr1 Hr2;tauto.
Qed.

Lemma ewrite_rval_nin t (r:rval t) e s y : 
   ~ Sv.In y (vrv r) -> (ewrite_rval s r e).[y]%mv = s.[y]%mv.
Proof.
  elim: r e s => //= [x | ?? r1 Hr1 r2 Hr2] e s.
  + by rewrite vrv_var Sv.singleton_spec=> /eqP ?;rewrite Mv.setP_neq // eq_sym.
  rewrite vrv_pair Sv.union_spec => ?. 
  rewrite Hr1 ?Hr2;auto. 
Qed.

Lemma fv_ewrite y t (i:rval t) e s:
   Sv.In y (vrv i) -> Sv.Subset (fv (ewrite_rval s i e).[y]%mv) (fv e).
Proof.
  elim: i e s => //= [x | ?? r1 Hr1 r2 Hr2] e s.
  + by rewrite vrv_var Sv.singleton_spec => ->;rewrite Mv.setP_eq.
  rewrite vrv_pair Sv.union_spec.
  case : (SvP.MP.In_dec y (vrv r1))=> Hin1.
  + have := Hr1 (Eapp1 (Ofst _ _) e) (ewrite_rval s r2 (Eapp1 (Osnd _ _) e)) Hin1.
    SvD.fsetdec.       
  move=> [] // Hin2;rewrite ewrite_rval_nin //.
  have := Hr2 (Eapp1 (Osnd _ _) e) s Hin2; SvD.fsetdec. 
Qed.

(* -------------------------------------------------------------------------- *)
(* ** symbolic formula                                                        *)
(* -------------------------------------------------------------------------- *)

Inductive fop2 := 
  | Fand 
  | For 
  | Fimp
  | Fiff.

Inductive fquant :=
  | Fforall 
  | Fexists.

Definition fop2_eqb o1 o2 := 
  match o1, o2 with
  | Fand , Fand => true  
  | For  , For  => true
  | Fimp , Fimp => true
  | Fiff , Fiff => true
  | _    , _    => false
  end.

Lemma fop2_eqP : Equality.axiom fop2_eqb. 
Proof. by move=> [] [] /=;constructor. Qed.

Definition fop2_eqMixin := EqMixin fop2_eqP.
Canonical  fop2_eqType  := EqType fop2 fop2_eqMixin.

Definition fquant_eqb o1 o2 := 
  match o1, o2 with
  | Fforall , Fforall => true  
  | Fexists , Fexists => true
  | _       , _    => false
  end.

Lemma fquant_eqP : Equality.axiom fquant_eqb. 
Proof. by move=> [] [] /=;constructor. Qed.

Definition fquant_eqMixin := EqMixin fquant_eqP.
Canonical  fquant_eqType  := EqType fquant fquant_eqMixin.

Definition ssem_fop2 o p1 p2 := 
  match o with 
  | Fand => p1 /\ p2
  | For  => p1 \/ p2
  | Fimp => p1 -> p2
  | Fiff => p1 <-> p2
  end.

Definition ssem_fquant t q (f:sst2ty t -> Prop) := 
  match q with
  | Fforall => forall v, f v
  | Fexists => exists v, f v
  end.

Instance ssem_fop2_m : Proper (@eq fop2 ==> iff ==> iff ==> iff) ssem_fop2.
Proof.
  by move=> ? o -> ?? H1 ?? H2;case o => /=;rewrite H1 H2.
Qed.

Lemma forall_iff A (P1 P2:A-> Prop): 
  (forall x, P1 x <-> P2 x) -> (forall (x:A), P1 x) <-> (forall x, P2 x).
Proof. by move=> H;split=> Hx x;move: (Hx x);rewrite H. Qed.

Lemma exists_iff A (P1 P2:A-> Prop): 
  (forall x, P1 x <-> P2 x) -> (exists (x:A), P1 x) <-> (exists x, P2 x).
Proof. by move=> H;split=> -[x Hx];exists x;move: Hx;rewrite H. Qed.

Instance ssem_fquant_m t : 
  Proper (@eq fquant ==> @pointwise_relation (sst2ty t) Prop iff ==> iff) (@ssem_fquant t).
Proof.
  by move=> ? q -> ?? H;case q => /=;[apply forall_iff |apply exists_iff];apply H.
Qed.

Inductive sform : Type := 
  | Fbool   : spexpr sbool -> sform 
  | Fpred   : forall (p:svar), spexpr p.(svtype) -> sform
  | Fnot    : sform -> sform 
  | Fop2    : fop2 -> sform -> sform -> sform 
  | Fif     : spexpr sbool -> sform -> sform -> sform
  | Fquant  : fquant -> svar -> sform -> sform.
 
Fixpoint ssem_sform (st:sstate) f : Prop := 
  match f with
  | Fbool   e     => ssem_spexpr st e 
  | Fpred   p  e  => st.(pm).[p]%msv (ssem_spexpr st e)
  | Fnot    f     => ~ ssem_sform st f
  | Fop2 o  f1 f2 => ssem_fop2 o (ssem_sform st f1) (ssem_sform st f2)
  | Fif   b f1 f2 => 
    if ssem_spexpr st b then ssem_sform st f1 
    else ssem_sform st f2 
  | Fquant q x f  => 
    ssem_fquant q 
      (fun (v:sst2ty x.(svtype)) =>
        ssem_sform {| pm := st.(pm); sm := st.(sm).[x <- v]%msv; vm:= st.(vm) |} f)
  end.

Notation "f1 '=_[' st1 , st2 ']' f2" := (ssem_sform st1 f1 <-> ssem_sform st2 f2)
 (at level 70, no associativity).

Notation "f1 '=_[' st ']' f2" := (ssem_sform st f1 <-> ssem_sform st f2)
 (at level 70, no associativity).

Definition feq (f1 f2:sform) := forall rho, f1 =_[rho] f2.

Instance feq_R : Equivalence feq.
Proof. 
  constructor => //.
  + by move=> f1 f2 Heq s;rewrite Heq.
  by move=> f1 f2 f3 Heq1 Heq2 s;rewrite Heq1.
Qed.

Notation "f1 '=F' f2" := (feq f1 f2) (at level 70, no associativity).

Instance Fbool_m : Proper (@eeq sbool ==> feq) Fbool.
Proof. by move=> ?? H ? /=;rewrite H. Qed.

Instance Fpred_m p : Proper (@eeq p.(svtype) ==> feq) (@Fpred p).
Proof. by move=> ?? H ? /=;rewrite H. Qed.

Instance Fnot_m: Proper (feq ==> feq) Fnot.
Proof. by move=> ?? H1 rho /=;rewrite (H1 rho). Qed.

Instance Fop2_m o: Proper (feq ==> feq ==> feq) (@Fop2 o).
Proof. by move=> ?? H1 ?? H2 rho /=;rewrite (H1 rho) (H2 rho). Qed.

Instance Fif_m: Proper (@eeq sbool==> feq ==> feq ==> feq) Fif.
Proof. by move=> ?? H1 ?? H2 ?? H3 rho /=;rewrite (H1 rho);case: ifP. Qed.

Instance Fquant_m q x: Proper (feq ==> feq) (Fquant q x).
Proof. by move=> ?? H1 rho /=;apply ssem_fquant_m. Qed.

Definition f_not f1    := Fnot f1.
Definition f_and f1 f2 := Fop2 Fand f1 f2.
Definition f_or  f1 f2 := Fop2 For f1 f2.
Definition f_imp f1 f2 := Fop2 Fimp f1 f2.
Definition f_iff f1 f2 := Fop2 Fiff f1 f2.
Definition f_forall x f := Fquant Fforall x f.
Definition f_exists x f := Fquant Fexists x f.

(* -------------------------------------------------------------------------- *)
(* ** program variables occuring in a formula                                 *)
(* -------------------------------------------------------------------------- *)

Fixpoint ffv_rec  (f:sform) (s:Sv.t) := 
  match f with
  | Fbool   e      => fv_rec e s
  | Fpred   _  e   => fv_rec e s 
  | Fnot    f      => ffv_rec f s
  | Fop2  _ f1 f2  => ffv_rec f1 (ffv_rec f2 s)
  | Fif   b f1 f2  => fv_rec  b  (ffv_rec f1 (ffv_rec f2 s))
  | Fquant _ _ f   => ffv_rec f s
  end.

Definition ffv f := ffv_rec f Sv.empty.

Add Morphism ffv_rec with 
    signature ((@Logic.eq sform) ==> Sv.Equal ==> Sv.Equal)%signature as ffv_rec_m.
Proof.
  elim=> //= [? | ?? | ?? He1 ? He2 | ?? He1 ? He2 ] ?? Heq.
  + by rewrite Heq.   + by rewrite Heq.   + by apply /He1 /He2. 
  by apply /fv_rec_m /He1 /He2.
Qed.

Lemma ffv_recE (f:sform) s : Sv.Equal (ffv_rec f s) (Sv.union (ffv f) s).
Proof.
  elim: f s => //= [? | ?? | ?? He1 ? He2 | ?? He1 ? He2 ] ?.
  + by rewrite fv_recE.   + by rewrite fv_recE. 
  + by rewrite He1 He2 /ffv /= -!/(ffv _) He1 SvP.MP.union_assoc.
  by rewrite fv_recE He1 He2 /ffv /= -!/(ffv _) fv_recE He1 !SvP.MP.union_assoc.
Qed.

Lemma ffv_bool (e:spexpr sbool) : ffv (Fbool e) = fv e.
Proof. done. Qed.

Lemma ffv_pred  p e : ffv (@Fpred p e) = fv e.
Proof. done. Qed.

Lemma ffv_not f : ffv (Fnot f) = ffv f.
Proof. done. Qed.

Lemma ffv_op2 o f1 f2 : Sv.Equal (ffv (Fop2 o f1 f2)) (Sv.union (ffv f1) (ffv f2)).
Proof. rewrite /ffv /= !ffv_recE;SvD.fsetdec. Qed.

Lemma ffv_if e f1 f2 : 
  Sv.Equal (ffv (Fif e f1 f2)) (Sv.union (fv e) (Sv.union (ffv f1) (ffv f2))).
Proof. rewrite /ffv /= !ffv_recE fv_recE;SvD.fsetdec. Qed.

Lemma ffv_quant q x f :
  Sv.Equal (ffv (Fquant q x f)) (ffv f).
Proof. done. Qed.
  
(* -------------------------------------------------------------------------- *)
(* ** symbolic variables occuring in a formula                                 *)
(* -------------------------------------------------------------------------- *)

Fixpoint sffv_rec  (f:sform) (s:Ssv.t) := 
  match f with
  | Fbool   e     => sfv_rec e s
  | Fpred   _  e  => sfv_rec e s 
  | Fnot    f     => sffv_rec f s
  | Fop2 _  f1 f2 => sffv_rec f1 (sffv_rec f2 s)
  | Fif   b f1 f2 => sfv_rec  b  (sffv_rec f1 (sffv_rec f2 s))
  | Fquant _ x f  => sffv_rec f (Ssv.add x s) 
  end.

Definition sffv f := sffv_rec f Ssv.empty.

Add Morphism sffv_rec with 
    signature ((@Logic.eq sform) ==> Ssv.Equal ==> Ssv.Equal)%signature as sffv_rec_m.
Proof.
  elim=> //=[?|??|?? He1 ? He2|?? He1 ? He2|??? He1] s1 s2 Heq.
  + by rewrite Heq.   + by rewrite Heq.   + by apply /He1 /He2.  
  + by apply /sfv_rec_m /He1 /He2.
  by apply He1;rewrite Heq.
Qed.

Lemma sffv_recE (f:sform) s : Ssv.Equal (sffv_rec f s) (Ssv.union (sffv f) s).
Proof.
  elim: f s => //= [?|??|?? He1 ? He2|?? He1 ? He2|??? He1] s.
  + by rewrite sfv_recE.   + by rewrite sfv_recE. 
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

Lemma sffv_op2 o f1 f2 : Ssv.Equal (sffv (Fop2 o f1 f2)) (Ssv.union (sffv f1) (sffv f2)).
Proof. rewrite /sffv /= !sffv_recE;SsvD.fsetdec. Qed.

Lemma sffv_if e f1 f2 : 
  Ssv.Equal (sffv (Fif e f1 f2)) (Ssv.union (sfv e) (Ssv.union (sffv f1) (sffv f2))).
Proof. rewrite /sffv /= !sffv_recE sfv_recE;SsvD.fsetdec. Qed.
 
Lemma sffv_quant q x f :  Ssv.Equal (sffv (Fquant q x f)) (Ssv.add x (sffv f)).
Proof. rewrite /sffv /= !sffv_recE;SsvD.fsetdec. Qed.

Lemma feq_on_fv f rho1 rho2 : 
  rho1.(pm) = rho2.(pm) -> rho1 ={ ffv f, sffv f} rho2 -> f =_[rho1,rho2] f.
Proof.
  elim: f rho1 rho2=> //= [?|??|? Hf1|?? Hf1 ? Hf2|?? Hf1 ? Hf2|? x? Hf1] rho1 rho2 Hpm.
  + by rewrite ffv_bool sffv_bool=> H;rewrite -(eq_on_fv H).
  + by rewrite Hpm ffv_pred sffv_pred=> H;rewrite -(eq_on_fv H). 
  + by rewrite ffv_not sffv_not=> H;rewrite (Hf1 _ _ Hpm H).
  + rewrite ffv_op2 sffv_op2=> H;rewrite (Hf1 _ _ Hpm) ?(Hf2 _ _ Hpm) //;
    apply: eq_on_m H=> //;(SvD.fsetdec || SsvD.fsetdec).
  + rewrite ffv_if sffv_if=> H;rewrite (@eq_on_fv _ _ rho1 rho2);
     last by apply: eq_on_m H=> //;(SvD.fsetdec || SsvD.fsetdec).
    (* case: ssem_spexpr.  (Enrico : Bug ?) *)
    by case: (ssem_spexpr _);[apply Hf1 | apply Hf2]=>//;apply: eq_on_m H;
      (SvD.fsetdec || SsvD.fsetdec).
  rewrite ffv_quant sffv_quant=> H;apply ssem_fquant_m=> // v;apply Hf1=> //=.
  constructor=> /= z Hz;first by apply H.
  case: (x =P z) => [<- | /eqP neq];rewrite ?Msv.setP_eq // ?Msv.setP_neq //.
  by apply H;SsvD.fsetdec.
Qed.

(* -------------------------------------------------------------------------- *)
(* ** Substitution of variables by expressions into formulas                  *)
(* -------------------------------------------------------------------------- *)

Definition fresh_svar (s:Ssv.t) := 
  let add v m := Pos.max v.(svname) m in
  let max := Ssv.fold add s xH in   
  Pos.succ max.

Definition rename s f x :=
  if Ssv.mem x s.(s_fv) then 
    let all := Ssv.union s.(s_fv) (sffv f) in
    let x' := {| svtype := x.(svtype); svname := fresh_svar all; |} in
    (x'.(svname), {| s_fv := Ssv.add x' s.(s_fv);
            s_v  := s.(s_v);
            s_s  := s.(s_s).[x <- Esvar x']%msv |})
  else 
    (x.(svname), {| s_fv := s.(s_fv);
           s_v  := s.(s_v);
           s_s  := Msv.remove s.(s_s) x |}).
 
Fixpoint fsubst (s:psubst) (f:sform) := 
  match f with
  | Fbool   e     => Fbool    (esubst s e)
  | Fpred   p  e  => @Fpred p (esubst s e)
  | Fnot    f     => Fnot     (fsubst s f)
  | Fop2 o  f1 f2 => Fop2 o   (fsubst s f1) (fsubst s f2) 
  | Fif   b f1 f2 => Fif      (esubst s b) (fsubst s f1) (fsubst s f2) 
  | Fquant q x f  => 
      let (id,s)  := rename s f x in
      Fquant q (SVar x.(svtype) id) (fsubst s f)
  end.

Instance fresh_svar_m : Proper (Ssv.Equal ==> eq) fresh_svar.
Proof.
  move=> f1 f2 Heq;rewrite /fresh_svar;f_equal.
  apply SsvP.MP.fold_equal; auto; first by move=> ??-> ??->.
  by move=> x y z;rewrite !Pos.max_assoc (Pos.max_comm (svname _)).
Qed.

Lemma fresh_svarP t s: ~ Ssv.In {|svtype := t; svname := fresh_svar s|} s.
Proof.
  rewrite /fresh_svar.
  have Hf: forall p x, Ssv.In x s -> 
    (x.(svname) <= (Ssv.fold
                     (fun (v : svar) (m : positive) => Pos.max (svname v) m) s p))%positive.
  + move=> p x;apply SsvP.MP.fold_rec.
    + by move=> ? He H;elim (He _ H).
    move=> {p} z p s1 s2 _ Hnin Ha Hrec /Ha [-> | Hn];first by apply Pos.le_max_l. 
    by apply (Pos.le_trans _ p);auto using Pos.le_max_r.
  move=> /(Hf xH) /=;rewrite Pos.le_succ_l;apply Pos.lt_irrefl.
Qed.

Lemma renameP s f x {H:wf_psubst s} : 
  [/\ s_v (rename s f x).2 = s_v s, 
      ~Ssv.In (SVar x.(svtype) (rename s f x).1) s.(s_fv),
      ~Ssv.In (SVar x.(svtype) (rename s f x).1) (Ssv.remove x (sffv f)), 
      (s_s (rename s f x).2).[x]%msv = (SVar x.(svtype) (rename s f x).1) &
      forall z, x != z ->  (s_s (rename s f x).2).[z]%msv = (s_s s).[z]%msv].
Proof.
  rewrite /rename;set fv := (Ssv.union _ _).
  have Hfr := @fresh_svarP (svtype x) fv;case: ifPn=> [?|/negP Hin]; split=> //= [||| z ?].
  + by SsvD.fsetdec. + by SsvD.fsetdec.  
  + by apply Msv.setP_eq.
  + by apply Msv.setP_neq.
  + by move: Hin=> /SsvD.F.mem_iff;case x.
  + by case x=> ??/=;SsvD.fsetdec.
  + by rewrite Msv.removeP_eq dft_s;case x.
  by rewrite Msv.removeP_neq.
Qed.

Instance wf_rename s {H:wf_psubst s} f x : wf_psubst (rename s f x).2.
Proof.
  case: H => dftv dfts domv doms.
  rewrite /rename;case : ifPn => Hin;constructor => //=;try (by rewrite Msv.dft_removeP).
  + by move=> z /domv;SsvD.fsetdec.
  + move=> z;rewrite Msv.indom_setP.
    case: (_ =P _) => /= [<- _ | /eqP ? /doms].
    + by rewrite Msv.setP_eq [sfv _]sfv_svar;SsvD.fsetdec.
    rewrite Msv.setP_neq //;SsvD.fsetdec.
  move=> z;rewrite Msv.indom_removeP => /andP [] ? /doms.
  rewrite Msv.removeP_neq //;SsvD.fsetdec.
Qed.

Lemma fsubstP rho s f {H:wf_psubst s} :
  fsubst s f =_[rho, ssubst s rho] f.
Proof.
  elim: f s H rho => /= [?|??|? Hf1|?? Hf1 ? Hf2|?? Hf1 ? Hf2|? x f1 Hf1] s Hwf rho;
    rewrite ?esubstP ?Hf1 ?Hf2 ?Hf3 //.
  + by case: ifP;rewrite ?Hf1 ?Hf2.
  rewrite (surjective_pairing (rename _ _ _)) /=.
  have [Hsv Hnin Hnin' Hssx Hss] := renameP f1 x; apply ssem_fquant_m => // v.
  rewrite Hf1; apply feq_on_fv => //=;constructor=> //= z Hz.
  + rewrite !Fv.get0 /= Hsv.
    case : (boolP (Mv.indom z (s_v s))) => [/indom_v Hsub | /Mv.indom_getP ->].
    + apply eq_on_fv;constructor=> w Hw //=.
      rewrite Msv.setP_neq //;apply /eqP=> ?;subst. 
      by elim Hnin; apply: SsvP.MP.in_subset Hsub.
    by rewrite dft_v.    
  rewrite !Msv.get0 /=;case:(x =P z)=> [<-|/eqP Hneq].
  + by rewrite Msv.setP_eq Hssx /= Msv.setP_eq.
  rewrite Msv.setP_neq // Msv.get0 Hss //=.
  case: (boolP (Msv.indom z (s_s s))) => [/indom_s Hsub| /Msv.indom_getP ->].
  + apply eq_on_fv;constructor=> w Hw //=.
    rewrite Msv.setP_neq //;apply /eqP=> ?;subst. 
    by elim Hnin; apply: SsvP.MP.in_subset Hsub.
  rewrite dft_s /= Msv.setP_neq //;apply /eqP=> ?;subst.
  by move: Hneq=> /eqP Hneq;apply Hnin';apply SsvP.MP.Dec.F.remove_2.
Qed.


(* --------------------------------------------------------------------------- *)
(* -- Free variables of the composition of subtitution                         *)
(* --------------------------------------------------------------------------- *)

Definition fv_subst_body s x :=
  if Mv.indom x s.(v_v) then Sv.union (fv (esubst s x)) else Sv.add x.

Definition sfv_subst_body s x :=
  if Mv.indom x s.(v_v) then Ssv.union (sfv (esubst s x)) else id.

Instance fv_subst_body_m s : Proper (eq ==> Sv.Equal ==> Sv.Equal) (fv_subst_body s).
Proof. by rewrite /fv_subst_body => ?? -> ??;case:ifP => _ ->. Qed.

Instance sfv_subst_body_m s : Proper (eq ==> Ssv.Equal ==> Ssv.Equal) (sfv_subst_body s).
Proof. by rewrite /sfv_subst_body=> ?? -> ??;case:ifP => _ ->. Qed.

Lemma fv_subst_body_t s : SetoidList.transpose Sv.Equal (fv_subst_body s).
Proof. by rewrite /fv_subst_body=> ???;case:ifP;case:ifP=> _ _;SvD.fsetdec. Qed.

Lemma sfv_subst_body_t s : SetoidList.transpose Ssv.Equal (sfv_subst_body s).
Proof. by rewrite /sfv_subst_body=> ???;case:ifP;case:ifP=> _ _;SsvD.fsetdec. Qed.

Hint Immediate fv_subst_body_t sfv_subst_body_t.

Definition fv_subst s vs  := Sv.fold  (fv_subst_body s)  vs Sv.empty. 
Definition sfv_subst s vs := Sv.fold  (sfv_subst_body s) vs Ssv.empty. 

Instance fv_subst_m s : Proper (Sv.Equal ==> Sv.Equal) (fv_subst s).
Proof.
  rewrite /fv_subst=> s1 s2 /Sv.equal_spec.
  apply SvP.fold_equal;auto with typeclass_instances.
Qed.

Instance sfv_subst_m s : Proper (Sv.Equal ==> Ssv.Equal) (sfv_subst s).
Proof.
  rewrite /fv_subst=> s1 s2 /Sv.equal_spec.
  apply SvP.fold_equal;auto with typeclass_instances.
Qed.


Lemma fv_substE s s1 s2 : 
  Sv.Equal (Sv.fold (fv_subst_body s) s1 s2) (Sv.union (fv_subst s s1) s2).
Proof.
  apply SvP.MP.fold_rec.
  + by move=> ??;rewrite /fv_subst SvP.MP.fold_1b.
  move=> ???? ??? Hr.
  rewrite  /fv_subst SvP.MP.fold_2;eauto.
  rewrite Hr {1 2}/fv_subst_body;case:ifP=> _.
  + move=> x; rewrite ?Sv.union_spec ?Sv.add_spec;tauto.
  by rewrite SvP.MP.union_add //.
Qed.

Lemma sfv_substE s s1 s2 : 
  Ssv.Equal (Sv.fold (sfv_subst_body s) s1 s2) (Ssv.union (sfv_subst s s1) s2).
Proof.
  apply SvP.MP.fold_rec.
  + by move=> ??;rewrite /sfv_subst SvP.MP.fold_1b //. 
  move=> ???? ??? Hr.
  rewrite  /sfv_subst SvP.MP.fold_2;eauto.
  rewrite Hr {1 2}/sfv_subst_body;case:ifP=> _ //.
  move=> x; rewrite ?Ssv.union_spec ?Ssv.add_spec;tauto.
Qed.

Lemma fv_subst0 s: fv_subst s Sv.empty = Sv.empty.
Proof. done. Qed.

Lemma sfv_subst0 s: sfv_subst s Sv.empty = Ssv.empty.
Proof. done. Qed.

Lemma fv_subst1 s x: 
  Sv.Equal (fv_subst s (Sv.singleton x))
            (if Mv.indom x s.(v_v) then (fv (esubst s x)) else Sv.singleton x).
Proof.
  rewrite [in X in Sv.Equal X _]SvP.MP.singleton_equal_add.
  rewrite /fv_subst SvP.fold_add //;last by auto.
  rewrite SvP.fold_empty /fv_subst_body;case:ifP;SvD.fsetdec. 
Qed.

Lemma sfv_subst1 s x: 
  Ssv.Equal (sfv_subst s (Sv.singleton x))
            (if Mv.indom x s.(v_v) then (sfv (esubst s x)) else Ssv.empty).
Proof.
  rewrite [in X in Ssv.Equal X _]SvP.MP.singleton_equal_add.
  rewrite /sfv_subst SvP.fold_add //;last by auto.
  rewrite SvP.fold_empty /sfv_subst_body;case:ifP;SsvD.fsetdec. 
Qed.

Lemma fv_substU s s1 s2: 
  Sv.Equal (fv_subst s (Sv.union s1 s2)) (Sv.union (fv_subst s s1) (fv_subst s s2)).
Proof.
  pose s12 := Sv.inter s1 s2.
  have -> : Sv.Equal (Sv.union s1 s2) 
    (Sv.union (Sv.union (Sv.diff s1 s12) (Sv.diff s2 (s12))) s12).
  + rewrite /s12=> x. 
    rewrite !Sv.union_spec !Sv.diff_spec Sv.inter_spec.
    case: (SvP.MP.In_dec x s1);case: (SvP.MP.In_dec x s2);tauto.
  have {2}->: Sv.Equal s1 (Sv.union (Sv.diff s1 s12) s12) by SvD.fsetdec. 
  have {2}->: Sv.Equal s2 (Sv.union (Sv.diff s2 s12) s12).
  + rewrite /s12 => x. 
    rewrite !Sv.union_spec !Sv.diff_spec Sv.inter_spec.
    case: (SvP.MP.In_dec x s1);tauto.
  rewrite /fv_subst ?SvP.MP.fold_union;auto=> x.
  + rewrite !Sv.union_spec ![Sv.fold _ _ (Sv.fold _ _ _)]fv_substE;SsvD.fsetdec.
  + by SvD.fsetdec.   + by SvD.fsetdec.  + by SvD.fsetdec.  by SvD.fsetdec. 
Qed.

Lemma sfv_substU s s1 s2: 
  Ssv.Equal (sfv_subst s (Sv.union s1 s2)) (Ssv.union (sfv_subst s s1) (sfv_subst s s2)).
Proof.
  pose s12 := Sv.inter s1 s2.
  have -> : Sv.Equal (Sv.union s1 s2) 
    (Sv.union (Sv.union (Sv.diff s1 s12) (Sv.diff s2 (s12))) s12).
  + rewrite /s12=> x. 
    rewrite !Sv.union_spec !Sv.diff_spec Sv.inter_spec.
    case: (SvP.MP.In_dec x s1);case: (SvP.MP.In_dec x s2);tauto.
  have {2}->: Sv.Equal s1 (Sv.union (Sv.diff s1 s12) s12) by SvD.fsetdec. 
  have {2}->: Sv.Equal s2 (Sv.union (Sv.diff s2 s12) s12).
  + rewrite /s12 => x. 
    rewrite !Sv.union_spec !Sv.diff_spec Sv.inter_spec.
    case: (SvP.MP.In_dec x s1);tauto.
  rewrite /sfv_subst ?SvP.MP.fold_union;auto=> x.
  + rewrite !Ssv.union_spec ![Sv.fold _ _ (Sv.fold _ _ _)]sfv_substE;SsvD.fsetdec. 
  + by SvD.fsetdec.   + by SvD.fsetdec.  + by SvD.fsetdec.  by SvD.fsetdec. 
Qed.

Lemma sfv_esubst s {Hs: wf_vsubst s} t (e:spexpr t): 
  Ssv.Equal (sfv (esubst s e)) (Ssv.union (sfv_subst s (fv e)) (sfv e)).
Proof.
  elim: e =>
   [?|?|?|?|???? He1|????? He1 ? He2|?????? He1 ? He2 ? He3|?? He1 ? He2 ? He3] /=.  
  + rewrite sfv_var fv_var sfv_subst1 /=. 
    case: ifPn;first by SsvD.fsetdec.
    by move=> /Mv.indom_getP ->;rewrite vdft_v sfv_var.
  + by rewrite fv_svar sfv_subst0 /= Msv.get0; SsvD.fsetdec.
  + by rewrite sfv_const fv_const sfv_subst0.
  + by rewrite sfv_bool fv_bool sfv_subst0.
  + by rewrite !sfv_op1 He1;SsvD.fsetdec.
  + rewrite !(sfv_op2,fv_op2, sfv_substU,He1, He2)=> x.
    rewrite !Ssv.union_spec;tauto.
  + rewrite !(sfv_op3,fv_op3,sfv_substU,He1, He2, He3)=> x.
    rewrite !Ssv.union_spec;tauto.
  rewrite !(sfv_if,fv_if,sfv_substU,He1, He2, He3)=> x.
  rewrite !Ssv.union_spec;tauto.
Qed.

Lemma sfv_subst_I s1 s2 {H1:wf_vsubst s1}: Ssv.Subset (sfv_subst s1 s2) (s_fv s1).
Proof.
  rewrite /sfv_subst;apply SvP.MP.fold_rec;first by SsvD.fsetdec.
  move=> ???? ??? Hr;rewrite /sfv_subst_body;case:ifP=> //= /vindom_v ?;SsvD.fsetdec.
Qed.

Lemma fv_esubst s {Hs: wf_psubst s} t (e:spexpr t): 
  (forall x, Msv.indom x (s_s s) -> Sv.Equal (fv (s_s s).[x]%msv) Sv.empty) ->
  Sv.Equal (fv (esubst s e)) (fv_subst {|v_v := s_v s; v_fv := s_fv s|} (fv e)).
Proof.
  move=> Hin.
  elim: e =>
   [?|x|?|?|???? He1|????? He1 ? He2|?????? He1 ? He2 ? He3|?? He1 ? He2 ? He3] /=.  
  + rewrite fv_var fv_subst1 /=;case: ifPn=> // /Mv.indom_getP ->.
    by rewrite dft_v fv_var.
  + rewrite fv_svar fv_subst0.
    case: (boolP (Msv.indom x (s_s s))) => [/Hin //| /Msv.indom_getP ->].
    by rewrite dft_s fv_svar.
  + by rewrite fv_const fv_subst0.
  + by rewrite fv_bool fv_subst0.
  + by rewrite !(fv_op1, He1);SvD.fsetdec.
  + rewrite !(fv_op2,fv_substU,He1, He2)=> x;rewrite !Sv.union_spec;tauto.
  + rewrite !(sfv_op3,fv_op3,fv_substU,He1, He2, He3)=> x.
    rewrite !Sv.union_spec;tauto.
  rewrite !(sfv_if,fv_if,fv_substU,He1, He2, He3)=> x.
  rewrite !Sv.union_spec;tauto.
Qed.

Lemma fv_fsubst s {Hs: wf_psubst s} f: 
  (forall x, Msv.indom x (s_s s) -> Sv.Equal (fv (s_s s).[x]%msv) Sv.empty) ->
  Sv.Equal (ffv (fsubst s f)) (fv_subst {|v_v := s_v s; v_fv := s_fv s|} (ffv f)).
Proof.
  elim: f s Hs => [?|??|f1 Hf1|o f1 Hf1 f2 Hf2|b f1 Hf1 f2 Hf2|q w f1 Hf1] s Hwf Hin /=.
  + by rewrite !ffv_bool; apply: fv_esubst.
  + by rewrite !ffv_pred; apply: fv_esubst.
  + by rewrite !ffv_not Hf1.
  + by rewrite !ffv_op2 Hf1 // Hf2 // fv_substU.
  + by rewrite !ffv_if Hf1 // Hf2 // !fv_substU fv_esubst.
  rewrite (surjective_pairing (rename _ _ _)).
  rewrite !ffv_quant Hf1 /rename;case:ifP => //= _ x.
  + rewrite ?Msv.indom_setP;case: (w =P x) => [<- | /eqP ?] /=.
    + by rewrite Msv.setP_eq [fv _]fv_svar.
    by rewrite Msv.setP_neq //;apply Hin.  
  rewrite Msv.indom_removeP;case: (w =P x) => [<- | /eqP ?] //=.
  by rewrite Msv.removeP_neq //;apply Hin.    
Qed.

(* -------------------------------------------------------------------------- *)
(* -- Composition of substitutions                                            *)
(* -------------------------------------------------------------------------- *)


Definition osubst (s1 s2: pvsubst) := 
  {| v_fv := Ssv.union s1.(v_fv) s2.(v_fv);
     v_v  := Mv.map2  [eta Evar]  (fun _ _ e => esubst s1 e) s1.(v_v) s2.(v_v); |}.

Instance wf_osubst s1 s2 {H1:wf_vsubst s1} {H2:wf_vsubst s2} : wf_vsubst (osubst s1 s2).
Proof.
  constructor;first by rewrite Mv.dft_map2P.
  + move=> x /=;rewrite Mv.indom_map2P Mv.map2P;
    last by rewrite vdft_v /= => /Mv.indom_getP ->;rewrite vdft_v.
    rewrite orbC;case: (boolP (Mv.indom x (s_v s2)))=> /= [/vindom_v Hs2 _|/Mv.indom_getP ->].
    + rewrite sfv_esubst. 
      have := @sfv_subst_I _ (fv ((s_v s2).[x])%mv) H1; by SsvD.fsetdec.
    move=> /vindom_v;rewrite vdft_v /=;SsvD.fsetdec.
Qed.

Lemma eq_on_osubst s1 s2 {H1:wf_vsubst s1} {H2:wf_vsubst s2} rho fv1 fv2:
   ssubst (osubst s1 s2) rho ={ fv1, fv2} ssubst s2 (ssubst s1 rho).
Proof.
  constructor=> x ? /=.
  + rewrite !Fv.get0 Mv.map2P.
    + by rewrite !esubstP;constructor.
    by rewrite vdft_v /= => /Mv.indom_getP ->;rewrite vdft_v.
  by rewrite !Msv.get0.
Qed.

Lemma osubst_Pe t (e:spexpr t) s1 s2 {H1:wf_vsubst s1} {H2:wf_vsubst s2} : 
  esubst (osubst s1 s2) e =E esubst s1 (esubst s2 e).
Proof.
  by move=> rho;rewrite !esubstP;apply eq_on_fv;apply: eq_on_osubst.
Qed.

Lemma osubstP f s1 s2 {H1:wf_vsubst s1} {H2:wf_vsubst s2}: 
  fsubst (osubst s1 s2) f =F fsubst s1 (fsubst s2 f).
Proof.
  by move=> rho;rewrite !fsubstP;apply feq_on_fv=> //;apply: eq_on_osubst.
Qed.
 
Definition merge_if (e:spexpr sbool) s1 s2 := 
  {| v_fv := Ssv.union (sfv e) (Ssv.union s1.(v_fv) s2.(v_fv));
     v_v  := Mv.map2  [eta Evar]  (fun _ e1 e2 => Eif e e1 e2) s1.(v_v) s2.(v_v); |}.

Instance wf_merge_if (e:spexpr sbool) s1 s2 {H1:wf_vsubst s1} {H2:wf_vsubst s2}:
  wf_vsubst (merge_if e s1 s2).
Proof.
  constructor;first by rewrite Mv.dft_map2P.
  + move=> x /=; rewrite Mv.indom_map2P => Hdom;apply Mv.map2Pred.
    + move=> ???;rewrite sfv_var;SsvD.fsetdec.
    rewrite sfv_if;move: Hdom. 
    case: (boolP (Mv.indom x (v_v s1)))=> /= [/vindom_v ? _|/Mv.indom_getP -> /vindom_v].
    + by case: (boolP (Mv.indom x (v_v s2)))=> /= [/vindom_v ? |/Mv.indom_getP ->];
       rewrite ?vdft_v;SsvD.fsetdec.
    by rewrite vdft_v sfv_var;SsvD.fsetdec.
Qed.
   
Lemma merge_ifP_e e s1 s2 t (e':spexpr t) {H1:wf_vsubst s1} {H2:wf_vsubst s2}: 
  esubst (merge_if e s1 s2) e' =E Eif e (esubst s1 e') (esubst s2 e').
Proof.
  move=> ? /=;case Heq: (ssem_spexpr _ e); rewrite !esubstP;
  apply eq_on_fv;constructor=> z Hz //=;rewrite !Fv.get0;
  by apply Mv.map2Pred=> /=;rewrite Heq // => _ _ <-;rewrite vdft_v.
Qed.

Lemma merge_ifP e s1 s2 f {H1:wf_vsubst s1} {H2:wf_vsubst s2}: 
  fsubst (merge_if e s1 s2) f =F Fif e (fsubst s1 f) (fsubst s2 f).
Proof.
  move=> ? /=;case Heq: (ssem_spexpr _ e); rewrite !fsubstP;
  apply feq_on_fv;constructor=> z Hz //=;rewrite !Fv.get0;
  by apply Mv.map2Pred=> /=;rewrite Heq // => _ _ <-;rewrite vdft_v.
Qed.


