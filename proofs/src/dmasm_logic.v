(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple finfun.
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

Definition hpred := sestate -> Prop.

Definition hoare (Pre:hpred) (c:cmd) (Post:hpred) := 
  forall (s s':sestate),  ssem s c s' -> Pre s -> Post s'.

(* -------------------------------------------------------------------------- *)
(* ** Core Rules                                                              *)
(* -------------------------------------------------------------------------- *)

(* Skip *)

Lemma hoare_skip P : hoare P Cskip P.
Proof. 
  by move=> ?? s Hp;case: _ {-1}_ _ / s (erefl Cskip) Hp.
Qed.

Lemma hoare_bcmd (P:hpred) bc: 
  hoare (fun s1 =>  forall s2,  ssem_bcmd s1 bc = ok s2 -> P s2) (Cbcmd bc) P.
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
  hoare (fun s => P s /\ ssem_pexpr s.(sevm) e) c1 Q ->
  hoare (fun s => P s /\ ~~ssem_pexpr s.(sevm) e) c2 Q ->
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

Definition vsubst_id : vsubst := 
  fun t x => Pvar x.

Definition vsubst_add {t} s id e : vsubst := 
  fun t' x =>
     let xid := vname x in
     if xid == id then
       match eq_stype t t' with
       | left p_eq =>
         eq_rect t (fun t => pexpr t) e t' p_eq
       | right _ => s t' x
       end
     else s t' x.

Definition tosubst (s:vsubst) : subst := s.

Lemma tosubst_id {t} (x: var t) : tosubst vsubst_id x = Pvar x.
Proof. by []. Qed.

Notation efst e := (Papp (Ofst _ _) e).
Notation esnd e := (Papp (Osnd _ _) e).

Definition ewrite_subst := @g_write_subst pexpr (fun t1 t2 e => efst e) (fun t1 t2 e => esnd e).

Definition ewrite_vsubst := 
  foldr (fun (ts:g_tosubst pexpr) vm => 
          let (t,id,v) := ts in
          vsubst_add vm id v).

Definition ewrite_rval {st} (vm:vsubst) (l:rval st) (v:pexpr st) :=
   ewrite_vsubst vm (ewrite_subst l v [::]).

Definition wp_asgn {t1 t2} (rv:rval t1) (e:pexpr t1) (pe: pexpr t2) := 
  subst_pexpr (tosubst (ewrite_rval vsubst_id rv e)) pe.

Record spred := Spred { 
   sp_t : stype;
   sp_P : sst2ty sp_t -> Prop;
   sp_e : pexpr sp_t;
}.

Definition s2h (p:spred)  := 
  fun (s:sestate) => sp_P (ssem_pexpr s.(sevm) p.(sp_e)).

Definition map_ssem_pe vm := 
  map (fun ts:g_tosubst pexpr => let (t,id,e) := ts in ToSubst id (ssem_pexpr vm e)).

Lemma swrite_subst_map l vm {t} (rv:rval t) (e:pexpr t) :
  swrite_subst rv (ssem_pexpr vm e) (map_ssem_pe vm l) = 
  map_ssem_pe vm (ewrite_subst rv e l).
Proof.
  elim: rv e l=> {t} [ ? []???| ?? r1 Hr1 r2 Hr2 e] l //=.
  by rewrite -Hr2 -Hr1. 
Qed.

Lemma svmap_set_neq {t1 t2} id x (v:sst2ty t1) vm: id <> x ->
    (svmap_set vm id v t2).[?x] = (vm t2).[?x].
Proof.
  rewrite /svmap_set;case: eq_stype => //= a.
  move: v; case: _ / a=> v.
  by rewrite (lock (_ .[_ <- _])) /= -lock fnd_set eq_sym => /eqP /negPf ->. 
Qed.

Lemma svmap_set_neq_t {t1 t2} id x (v:sst2ty t1) vm: t2 <> t1 ->
    (svmap_set vm id v t2).[?x] = (vm t2).[?x].
Proof.
  by move=> /nesym;rewrite /svmap_set;case: eq_stype. 
Qed.

Lemma vsubst_add_neq {t1 t2} s id (v:var t1) (e:pexpr t2):
   id <> vname v -> 
   tosubst (vsubst_add s id e) v = tosubst s v. 
Proof.
  by rewrite /tosubst/vsubst_add eq_sym => /eqP /negPf ->.
Qed.

Lemma vsubst_add_neq_t {t1 t2} s id (v:var t1) (e:pexpr t2):
   t1 <> t2 -> 
   tosubst (vsubst_add s id e) v = tosubst s v. 
Proof.
  rewrite /tosubst/vsubst_add; case: (_ == _) => //.
  by case eq_stype => // e0 neq;subst.
Qed.
  
Lemma vsubst_add_eq {t} (e : pexpr t) s (v : var t) : 
  tosubst (vsubst_add s (vname v) e) v = e. 
Proof.
  rewrite /tosubst/vsubst_add eq_refl;case: eq_stype => //= a.
  by rewrite ((eq_irrelevance a) (erefl t)).
Qed.

Lemma svmap_set_eq {t} vm id (v:sst2ty t): (svmap_set vm id v t).[? id] = Some v.
Proof.
  rewrite /svmap_set; case: eq_stype => //= a. 
  by rewrite ((eq_irrelevance a) (erefl t))  (lock (_ .[_ <- _])) /= -lock fnd_set eq_refl.
Qed.

Lemma ssem_subst_map {t2} (pe:pexpr t2) vm l :
   ssem_pexpr vm (subst_pexpr (tosubst (ewrite_vsubst vsubst_id l)) pe) =
   ssem_pexpr (swrite_vmap vm (map_ssem_pe vm l)) pe.
Proof.
  elim: pe => //= [tv v| ?? p1 Hp1 p2 Hp2| ??? p Hp];rewrite ?Hp1 ?Hp2 ?Hp //.
  elim: l => [ | [t id e] l Hrec] //=.
  case: (id =P vname v)=> [-> | ?].
  + case (eq_stype tv t) => [eq | neq].
    + by subst tv;rewrite vsubst_add_eq svmap_set_eq.
    by rewrite vsubst_add_neq_t // Hrec svmap_set_neq_t.
  by rewrite svmap_set_neq // vsubst_add_neq // Hrec.
Qed.

Lemma hoare_asgn {t1 t2} (rv:rval t1) (e:pexpr t1) (P:sst2ty t2 -> Prop) (pe: pexpr t2):
  hoare (s2h (Spred P (wp_asgn rv e pe))) (Cbcmd (Assgn rv e)) (s2h (Spred P pe)).
Proof.
  move=> s1_ s2_;set c := Cbcmd _=> s.
  case: _ {-1}_ _ / s (erefl c) => // s1 s2 ? H [] ?; subst=> {c s1_ s2_}.
  case: H=> <- {s2}; rewrite /wp_asgn /s2h /=.
  by rewrite /swrite_rval /ewrite_rval (swrite_subst_map [::]) ssem_subst_map.
Qed.

Definition is_skip (c:cmd) :=
  match c with
  | Cskip => true
  | _     => false
  end.

Fixpoint wp (c:cmd) (P:spred) : cmd * spred := 
 match c with
 | Cskip => (c, P)

 | Cbcmd(Assgn st rv pe) => (Cskip, Spred (@sp_P P) (wp_asgn rv pe P.(sp_e)))

 | Cseq c1 c2 => 
   let (c2_, P2) := wp c2 P in
   if is_skip c2_ then wp c1 P2
   else (Cseq c1 c2_, P2)

 | Cif e c1 c2 =>
   let (c1_, P1) := wp c1 P in
   let (c2_, P2) := wp c2 P in
   if is_skip c1_ && is_skip c2_ then 
     let (t1,P1,e1) := P1 in
     let (t2,P2,e2) := P2 in
     (Cskip, @Spred (sbool**(t1**t2)) 
                    (fun (v:bool * (sst2ty t1 * sst2ty t2)) =>
                       let: (b,(e1,e2)) := v in
                       if b then P1 e1 else P2 e2)
                    (Ppair e (Ppair e1 e2)))
   else (Cseq c1 c2_, P2)
   
 | _     => (c, P)
 end.


