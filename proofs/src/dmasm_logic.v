(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple finfun.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import word dmasm_utils dmasm_type dmasm_var dmasm_sem 
               dmasm_sem_props dmasm_Ssem symbolic_expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------------- *)
(* ** Hoare Logic                                                             *)
(* -------------------------------------------------------------------------- *)

Definition hpred := sestate -> Prop.

Definition hoare (Pre:hpred) (c:cmd) (Post:hpred) := 
  forall (s s':sestate),  ssem s c s' -> Pre s -> Post s'.

(* -------------------------------------------------------------------------- *)
(* ** Core Rules                                                              *)
(* -------------------------------------------------------------------------- *)

(* Consequence *)

Lemma hoare_conseq (P1 Q1:hpred) c (P2 Q2:hpred) : 
  (forall s, P2 s -> P1 s) ->
  (forall s, Q1 s -> Q2 s) -> 
  hoare P1 c Q1 -> hoare P2 c Q2.
Proof.
  move=> HP HQ Hh s s' Hsem Hs.
  by apply: HQ;apply:(Hh _ _ Hsem);apply: HP.
Qed.

(* Skip *)

Lemma hoare_skip_core P : hoare P [::] P.
Proof. 
  by move=> ?? s Hp;case: _ {-1}_ _ / s (erefl ([::]:cmd)) Hp.
Qed.

Lemma hoare_skip (Q P:hpred) : (forall s, Q s -> P s) -> hoare Q [::] P.
Proof. 
  move=> qp;apply: (@hoare_conseq P P)=> //;apply hoare_skip_core.
Qed.

(* Base command *)
Lemma hoare_bcmd (P:hpred) bc: 
  hoare (fun s1 =>  forall s2,  ssem_bcmd s1 bc = ok s2 -> P s2) [::Cbcmd bc] P.
Proof.
  move=> ??;set c := Cbcmd _ => /ssem_iV s.
  case: _ {-1}_ _ / s (erefl c) => // ??? e [] ?;subst=> H.
  by apply: (H _ e).
Qed.

(* Sequence *)

Lemma hoare_seq R P Q c1 c2 : 
  hoare P c1 R ->  hoare R c2 Q ->  hoare P (c1 ++ c2) Q.
Proof.
  move=> H1 H2 ?? /ssem_cV [?[s1 s2]] Hp.
  by apply: (H2 _ _ s2 (H1 _ _ s1 Hp)).
Qed.

Lemma hoare_cons R P Q i c : 
  hoare P [::i] R ->  hoare R c Q ->  hoare P (i :: c) Q.
Proof. by apply:hoare_seq. Qed.

(* Conditionnal *)
Lemma hoare_if P Q (e: pexpr sbool) c1 c2 : 
  hoare (fun s => ssem_pexpr s.(sevm) e /\ P s) c1 Q ->
  hoare (fun s => ~~ssem_pexpr s.(sevm) e /\ P s) c2 Q ->
  hoare P [::Cif e c1 c2] Q.
Proof.
  move=> H1 H2 ??;set c := Cif _ _ _ => /ssem_iV s.
  case: _ {-1}_ _ / s (erefl c) => // ?????? s [] ??? Hp;subst.
  + by apply: (H1 _ _ s).
  by apply: (H2 _ _ s).
Qed.

(* -------------------------------------------------------------------------- *)
(* ** Weakest Precondition                                                    *)
(* -------------------------------------------------------------------------- *)


Definition spred (t:stype) := spexpr t.
  
Definition s2h t (P:sst2ty t -> Prop) (p:spred t) := 
  fun (s:sestate) => P (ssem_spexpr s.(sevm) p).

Definition wp_asgn {t1 t2} (rv:rval t1) (e:pexpr t1) (p: spred t2) := 
  subst_spexpr (E.write_rval vsubst_id rv (p2sp e)) p.

Lemma hoare_asgn {t1 t2} (rv:rval t1) (e:pexpr t1) (P:sst2ty t2 -> Prop) (p: spred t2):
  hoare (s2h P (wp_asgn rv e p)) [:: Cbcmd (Assgn rv e)] (s2h P p).
Proof.
  move=> s1_ s2_;set c := Cbcmd _=> /ssem_iV s.
  case: _ {-1}_ _ / s (erefl c) => // s1 s2 ? H [] ?; subst=> {c s1_ s2_}.
  case: H=> <- {s2}; rewrite /wp_asgn /s2h /=.
  by rewrite /W.write_rval /E.write_rval (write_subst_map [::]) ssem_subst_map.
Qed.

Definition wp_bcmd t bc (p:spred t) := 
  match bc with
  | Assgn st rv e => 
    ([::], (wp_asgn rv e p))
  | Load  _ _ => ([::Cbcmd bc], p)
  | Store _ _ => ([::Cbcmd bc], p)
  end.

Definition wp t := 
  Eval lazy beta delta [cmd_rect instr_rect' list_rect] in
  @cmd_rect (fun _ => spred t -> cmd * spred t)
            (fun _ => spred t -> cmd * spred t)
            (fun _ _ _ => spred t -> unit)
    (fun Q => ([::], Q))
    (fun i _ wpi wpc Q => 
       let (c_, R) := wpc Q in
       if nilp c_ then wpi R
       else (i::c_,R))
    (@wp_bcmd t)
    (fun e c1 c2 wpc1 wpc2 Q =>
       let (c1_, P1) := wpc1 Q in
       let (c2_, P2) := wpc2 Q in
       if nilp c1_ && nilp c2_ then
         ([::], merge_if (p2sp e) P1 P2)
       else ([::Cif e c1 c2], Q))
    (fun i rn c _ Q => ([::Cfor i rn c], Q))
    (fun _ _ x f a _ Q => ([::Ccall x f a], Q))
    (fun _ _ _ _ _ _ _ => tt).

(* TODO: move this *)
Definition cmd_Ind (P : cmd -> Prop) := 
  @cmd_ind P (fun _ _ _ => True).

Lemma r_wp_cons t i c (P:spred t) :
  wp (i :: c) P = 
   if nilp (wp c P).1 then wp [::i] (wp c P).2
   else (i::(wp c P).1 , (wp c P).2).
Proof.
  by move=> /=;case (wp c P) => c_ R /=;case:nilP.
Qed.

Lemma r_wp_if t e c1 c2 (P:spred t) : 
  wp [::Cif e c1 c2] P = 
   if nilp (wp c1 P).1 && nilp (wp c2 P).1 then 
     let P1 := (wp c1 P).2 in
     let P2 := (wp c2 P).2 in
     ([::], merge_if (p2sp e) P1 P2)
   else ([::Cif e c1 c2], P).
Proof.
  move=> /=;fold (wp c1 P) (wp c2 P). 
  by case: (wp c1 P) => ??; case: (wp c2 P) => ??.
Qed.

Lemma wp_tl c t (P:sst2ty t -> Prop) (p:spred t) : exists tl, 
   c = (wp c p).1 ++ tl /\
   hoare (s2h P (wp c p).2) tl (s2h P p).
Proof.
  elim /cmd_Ind : c p => [ | i c Hi Hc| bc| e c1 c2 Hc1 Hc2| i rn c Hc|?? x f a _ | //] p.
  + by exists ([::]);split=>//=;apply hoare_skip.
  + rewrite r_wp_cons;elim (Hc p)=> {Hc} tlc [Heqc Hwpc].
    case: nilP Heqc => Heq Heqc.
    + elim (Hi (wp c p).2)=> tl [Htl Hwp] ;exists (tl ++ c).
      rewrite catA -Htl;split=>//.
      by rewrite {2} Heqc Heq cat0s;apply:hoare_seq Hwp Hwpc.
    by exists tlc=> /=;rewrite -Heqc.
  + case: bc => [? r e | ?? | ??] /=; try 
      by exists [::];split=>//;apply:hoare_skip.
    exists  [:: Cbcmd (Assgn r e)];split=>//.
    by apply hoare_asgn.
  + rewrite r_wp_if;case: andP=> /=;last
      by exists [::];split=>//;apply:hoare_skip.
    move=> [/nilP Heq1 /nilP Heq2].
    elim (Hc1 p) => {Hc1} tl1;elim (Hc2 p) => {Hc2} tl2.
    rewrite Heq1 Heq2 !cat0s=> -[<- Hc2] [<- Hc1].
    exists [:: Cif e c1 c2];split=>//.
    apply: hoare_if.
    + apply: (hoare_conseq _ _ Hc1)=> // s [] He.
      by rewrite /s2h merge_ifP /= sem_p2sp He.
    apply: (hoare_conseq _ _ Hc2)=> // s [] /negPf He.
     by rewrite /s2h merge_ifP /= sem_p2sp He.
  + by exists [::];split=>//;apply:hoare_skip.
  by exists [::];split=>//;apply:hoare_skip.
Qed.
  
Lemma hoare_wp t P Q c (p:spred t) : 
   hoare Q (wp c p).1 (s2h P (wp c p).2) -> 
   hoare Q c (s2h P p).
Proof.
  move=> H1;elim: (wp_tl c P p)=> tl [{2}->];apply: hoare_seq H1.
Qed.


  

(* -------------------------------------------------------------------------- *)
(* ** Tactics                                                                 *)
(* -------------------------------------------------------------------------- *)


Ltac skip := try apply:hoare_skip.

Ltac wp_core P p := 
  match goal with
  | |- hoare ?Q ?c _ => 
    apply: (@hoare_wp _ P Q c p);
    match eval vm_compute in (wp c p) with
    | (?c', ?p') => 
      let c1 := fresh "c" in
      let p1 := fresh "p" in
      set c1 := c';
      set p1 := p';
      (have -> /=: (wp c p) = (c1,p1) by vm_cast_no_check (erefl (c1,p1)));
      rewrite /c1 /p1 => {c1 p1}
    end
  | _ => fail "wp_core: not a hoare judgment"
  end.

(* -------------------------------------------------------------------------- *)
(* ** Tests                                                                   *)
(* -------------------------------------------------------------------------- *)

Definition x := {| vtype := sword; vname := "x" |}.
Definition y := {| vtype := sword; vname := "y" |}.
Definition z := {| vtype := sword; vname := "z" |}.

Definition w0 : N := 0.
Definition w1 : N := 1.

Definition c := 
  [:: assgn x w0;
      assgn y w1;
      Cif (Papp2 Oeq x w1) [::assgn z x] [::assgn z y] ].

Lemma c_ok : 
  hoare (fun _ => True) c (fun s =>  s.(sevm).[x]%vmap = n2w w0 /\ s.(sevm).[y]%vmap = n2w w1).
Proof.
  set P := (fun (v:sst2ty (sword ** sword)) => v.1 = n2w w0 /\ v.2 = n2w w1).
  set p := Eapp2 (Opair _ _) x y.
  wp_core P p.
  by skip.
Qed.

Definition c' := 
  [:: assgn x w0;
      assgn y w1;
      Cif (Papp2 Oeq x x) [::assgn z x] [::assgn z y] ].

Lemma c_ok1 : 
  hoare (fun _ => True) c' (fun s =>  s.(sevm).[x]%vmap = n2w w0 /\ s.(sevm).[z]%vmap = n2w w0).
Proof.
  set P := (fun (v:sst2ty (sword ** sword)) => v.1 = n2w w0 /\ v.2 = n2w w0).
  set p := Eapp2 (Opair _ _) x z.
  wp_core P p.
  by skip.
Qed.


  