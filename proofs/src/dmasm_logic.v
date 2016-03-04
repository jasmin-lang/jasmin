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
Local Open Scope seq_scope.
Local Open Scope svmap_scope.

Lemma ssem_iV s i s' : ssem s [::i] s' -> ssem_i s i s'.
Proof.
  move=> H;inversion H;subst.
  by inversion H5;subst.
Qed.

Lemma ssem_cV c1 c2 s s' : ssem s (c1 ++ c2) s' ->
  exists s'', ssem s c1 s'' /\ ssem s'' c2 s'.
Proof.
  elim: c1 s s' => /=[ | i c Hc] s s'. 
  + by exists s;split => //;constructor.
  set c_ := _ :: _ => H;case: _ {-1}_ _ / H (erefl c_) => //= ? s2 ? ?? Hi Hcat [] ??;subst.
  elim: (Hc _ _ Hcat)=> s1 [H1 H2];exists s1;split=>//;econstructor;eauto.
Qed.

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

Lemma hoare_skip P : hoare P [::] P.
Proof. 
  by move=> ?? s Hp;case: _ {-1}_ _ / s (erefl ([::]:cmd)) Hp.
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
  elim: rv e l=> {t} [ ?[]??| ?? r1 Hr1 r2 Hr2 e] l //=.
  by rewrite -Hr2 -Hr1. 
Qed.

Lemma svmap_set_neq {t1 t2} id x (v:sst2ty t1) vm: id <> x ->
    vm.[id <- v].[t2,x] = vm.[t2,x].
Proof.
  rewrite /svmap_set /svmap_get /=; case: eq_stype => //= a.
  move: v; case: _ / a=> v.
  by rewrite /= => /eqP /negPf ->.
Qed.

Lemma svmap_set_neq_t {t1 t2} id x (v:sst2ty t1) vm: t2 <> t1 ->
    vm.[id <- v].[t2,x] = vm.[t2,x].
Proof.
  by rewrite /svmap_set /svmap_get /= => /nesym; case: eq_stype.
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

Lemma svmap_set_eq {t} vm id (v:sst2ty t): vm.[id <- v].[t,id] = v.
Proof.
  rewrite /svmap_set /svmap_get /=; case: eq_stype => //= a. 
  by rewrite ((eq_irrelevance a) (erefl t))  /= eq_refl.
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
  hoare (s2h (Spred P (wp_asgn rv e pe))) [:: Cbcmd (Assgn rv e)] (s2h (Spred P pe)).
Proof.
  move=> s1_ s2_;set c := Cbcmd _=> /ssem_iV s.
  case: _ {-1}_ _ / s (erefl c) => // s1 s2 ? H [] ?; subst=> {c s1_ s2_}.
  case: H=> <- {s2}; rewrite /wp_asgn /s2h /=.
  by rewrite /swrite_rval /ewrite_rval (swrite_subst_map [::]) ssem_subst_map.
Qed.

Definition is_skip (c:cmd) :=
  match c with
  | [::] => true
  | _    => false
  end.

Lemma skipP c : reflect (c = [::]) (is_skip c).
Proof. case: c => //=;constructor=> //. Qed.

Definition wp_bcmd bc (P:spred) := 
  match bc with
  | Assgn st rv e => 
    let (_,P,pe) := P in
    ([::], Spred P (wp_asgn rv e pe))
  | Load  _ _ => ([::Cbcmd bc], P)
  | Store _ _ => ([::Cbcmd bc], P)
  end.

Definition wp := 
  Eval lazy beta delta [cmd_rect instr_rect' list_rect] in
  @cmd_rect (fun _ => spred -> cmd * spred)
            (fun _ => spred -> cmd * spred)
            (fun _ _ _ => spred -> unit)
    (fun Q => ([::], Q))
    (fun i _ wpi wpc Q => 
       let (c_, R) := wpc Q in
       if is_skip c_ then wpi R
       else (i::c_,R))
    wp_bcmd 
    (fun e c1 c2 wpc1 wpc2 Q =>
       let (c1_, P1) := wpc1 Q in
       let (c2_, P2) := wpc2 Q in
       if is_skip c1_ && is_skip c2_ then
         let (t1,P1,e1) := P1 in
         let (t2,P2,e2) := P2 in
         ([::], @Spred (sbool**(t1**t2)) 
                    (fun (v:bool * (sst2ty t1 * sst2ty t2)) =>
                       let: (b,(e1,e2)) := v in
                       if b then P1 e1 else P2 e2)
                    (Ppair e (Ppair e1 e2)))
       else ([::Cif e c1 c2], Q))
    (fun i rn c _ Q => ([::Cfor i rn c], Q))
    (fun _ _ x f a _ Q => ([::Ccall x f a], Q))
    (fun _ _ _ _ _ _ _ => tt).

Definition cmd_Ind (P : cmd -> Prop) := 
  @cmd_ind P (fun _ _ _ => True).

Lemma r_wp_cons i c P :
  wp (i :: c) P = 
   if is_skip (wp c P).1 then wp [::i] (wp c P).2
   else (i::(wp c P).1 , (wp c P).2).
Proof.
  by move=> /=;case (wp c P) => c_ R /=;case (is_skip _).
Qed.

Lemma r_wp_if e c1 c2 P : 
  wp [::Cif e c1 c2] P = 
   if is_skip (wp c1 P).1 && is_skip (wp c2 P).1 then 
     let Q1 := (wp c1 P).2 in
     let t1 := Q1.(sp_t) in
     let P1 := @sp_P Q1 in
     let e1 := Q1.(sp_e) in
     let Q2 := (wp c2 P).2 in
     let t2 := Q2.(sp_t) in
     let P2 := @sp_P Q2 in
     let e2 := Q2.(sp_e) in
     ([::], @Spred (sbool**(t1**t2)) 
                   (fun (v:bool * (sst2ty t1 * sst2ty t2)) =>
                      let: (b,(e1,e2)) := v in
                      if b then P1 e1 else P2 e2)
                   (Ppair e (Ppair e1 e2)))
   else ([::Cif e c1 c2], P).
Proof.
  move=> /=;fold (wp c1 P) (wp c2 P). 
  by case: (wp c1 P) => [? []]; case: (wp c2 P) => [? []].
Qed.

Lemma wp_tl c P: exists tl, 
   c = (wp c P).1 ++ tl /\
   hoare (s2h (wp c P).2) tl (s2h P).
Proof.
  elim /cmd_Ind : c P => [ | i c Hi Hc| bc| e c1 c2 Hc1 Hc2| i rn c Hc|?? x f a _ | //] P.
  + by exists ([::]);split=>//=;apply hoare_skip.
  + rewrite r_wp_cons;elim (Hc P)=> {Hc} tlc [Heqc Hwpc].
    case: skipP Heqc => Heq Heqc.
    + elim (Hi (wp c P).2)=> tl [Htl Hwp] ;exists (tl ++ c).
      rewrite catA -Htl;split=>//.
      by rewrite {2} Heqc Heq cat0s;apply:hoare_seq Hwp Hwpc.
    by exists tlc=> /=;rewrite -Heqc.
  + case: bc => [? r p | ?? | ??] /=; try 
      by exists [::];split=>//;apply:hoare_skip.
    exists  [:: Cbcmd (Assgn r p)];case P=>???;split=>//.
    by apply hoare_asgn.
  + rewrite r_wp_if;case: andP=> /=;last
      by exists [::];split=>//;apply:hoare_skip.
    move=> [/skipP Heq1 /skipP Heq2].
    elim (Hc1 P) => {Hc1} tl1;elim (Hc2 P) => {Hc2} tl2.
    rewrite Heq1 Heq2 !cat0s=> -[<- Hc2] [<- Hc1].
    exists [:: Cif e c1 c2];split=>//.
    apply: hoare_if.
    + by apply: (hoare_conseq _ _ Hc1)=> // s;rewrite /s2h /= => -[->].
    by apply: (hoare_conseq _ _ Hc2)=> // s;rewrite /s2h /= => -[/negPf->].
  + by exists [::];split=>//;apply:hoare_skip.
  by exists [::];split=>//;apply:hoare_skip.
Qed.
  
Lemma hoare_wp Q c P : 
   hoare Q (wp c P).1 (s2h (wp c P).2) -> 
   hoare Q c (s2h P).
Proof.
  move=> H1;elim: (wp_tl c P)=> tl [{2}->];apply: hoare_seq H1.
Qed.
