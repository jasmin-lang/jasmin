(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import finmap strings dmasm_utils dmasm_sem dmasm_sem_props dmasm_Ssem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.
Local Open Scope fset.
Local Open Scope fmap.
Local Open Scope list_scope.
(* -------------------------------------------------------------------------- *)
(* ** Hoare Logic                                                             *)
(* -------------------------------------------------------------------------- *)

Definition hpred := Sestate -> Prop.

Definition hoare (Pre:hpred) (c:cmd) (Post:hpred) := 
  forall (s s':Sestate),  Ssem s c s' -> Pre s -> Post s'.

(* -------------------------------------------------------------------------- *)
(* ** Core Rules                                                              *)
(* -------------------------------------------------------------------------- *)

(* Skip *)

Lemma hoare_skip P : hoare P Cskip P.
Proof. 
  by move=> ?? s Hp;case: _ {-1}_ _ / s (erefl Cskip) Hp.
Qed.

Lemma hoare_bcmd (P:hpred) bc: 
  hoare (fun s1 =>  forall s2,  Ssem_bcmd s1 bc = ok s2 -> P s2) (Cbcmd bc) P.
Proof.
  move=> ??;set c := Cbcmd _ => s.
  case: _ {-1}_ _ / s (erefl c) => // ??? e [] ?;subst=> H.
  by apply: (H _ e).
Qed.

Lemma hoare_seq R P Q c1 c2 : 
  hoare P c1 R ->  hoare R c2 Q ->  hoare P (Cseq c1 c2) Q.
Proof.
  move=> H1 H2 ??; set c := Cseq _ _=> s.
  case: _ {-1}_ _ / s (erefl c) => // ????? s1 s2 [] ?? Hp;subst.
  by apply: (H2 _ _ s2 (H1 _ _ s1 Hp)).
Qed.

Lemma hoare_if P Q (e: pexpr sbool) c1 c2 : 
  hoare (fun s => P s /\ Ssem_pexpr s.(sevm) e) c1 Q ->
  hoare (fun s => P s /\ ~~Ssem_pexpr s.(sevm) e) c2 Q ->
  hoare P (Cif e c1 c2) Q.
Proof.
  move=> H1 H2 ??;set c := Cif _ _ _ => s.
  case: _ {-1}_ _ / s (erefl c) => // ?????? s [] ??? Hp;subst.
  + by apply: (H1 _ _ s).
  by apply: (H2 _ _ s).
Qed.

(* -------------------------------------------------------------------------- *)
(* ** Weakest Precondition                                                    *)
(* -------------------------------------------------------------------------- *)

Definition vsubst := subst.

Parameter vsubst_id : vsubst.
Parameter vsubst_add :forall {t}, vsubst -> ident -> pexpr t -> vsubst.

Definition tosubst (s:vsubst) : subst := s.

Notation efst e := (Papp (Ofst _ _) e).
Notation esnd e := (Papp (Osnd _ _) e).

Fixpoint subst_asgn {t}  (s:vsubst) (l:rval t) : pexpr t -> vsubst := 
  match l in rval t_ return pexpr t_ -> vsubst with 
  | Rvar t (Var _ vid) => fun (e:pexpr t) => vsubst_add s vid e
  | Rpair t1 t2 rv1 rv2 => fun (e:pexpr (t1 ** t2)) =>
    let s := subst_asgn s rv1 (efst e) in
    subst_asgn s rv2 (esnd e)
  end.

Definition wp_asgn {t1 t2} (rv:rval t1) (e:pexpr t1) (pe: pexpr t2) := 
  subst_pexpr (tosubst (subst_asgn vsubst_id rv e)) pe.

Definition spred (t:stype) := ((Sst2ty t -> Prop) * pexpr t)%type.

Definition s2h {t} (p:spred t) : hpred := 
  fun s =>
    let (P,e) := p in
    P (Ssem_pexpr s.(sevm) e).

Print Swrite_rval.

Swrite_rval -> subst_for_vm.

Lemma subst_asgn_correct {t1 t2} (rv : rval t1) (e : pexpr t1) (pe : pexpr t2) vm s vm':
   Ssem_pexpr vm (subst_pexpr (tosubst (subst_asgn vsubst_id rv e)) pe) = 
   Ssem_pexpr (Swrite_rval vm rv (Ssem_pexpr vm e)) pe.
Proof.
 elim: rv e => {t1} [ ???| ??? Hr1 ? Hr2 e].
admit.

Print Swrite_rval.


Lemma hoare_asgn {t1 t2} (rv:rval t1) (e:pexpr t1) (P:Sst2ty t2 -> Prop) (pe: pexpr t2):
  hoare (s2h (P, wp_asgn rv e pe)) (Cbcmd (Assgn rv e)) (s2h (P,pe)).
Proof.
  move=> s1_ s2_;set c := Cbcmd _=> s.
  case: _ {-1}_ _ / s (erefl c) => // s1 s2 ? H [] ?; subst=> {c s1_ s2_}.
  case: H=> <- {s2}; rewrite /wp_asgn /s2h /=.




  move=> [v [H1 H2]];exists v;split=> //.
  move:H H1 {H2}=> /=.
  rewrite /wp_asgn /=.
  case E: (sem_pexpr _ _) => [a|] //= [] <-.


  move=> H1 v Hv;apply H1=> {H1};elim: rv e H=> /=.
  rewrite /wp_asgn /=.
  move:H => /= {c s1_ s2_}.
elim: rv e.

  m 
  
 [].

 ????? s1 s2 [] ?? Hp;subst.

rewrite /s2h => s H v.
;rewrite /s2h.

Fixpoint wp_asgn {t1} ((Post :pexpr st)




