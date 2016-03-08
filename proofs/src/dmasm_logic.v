(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple finfun.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import dmasm_utils dmasm_type dmasm_var dmasm_sem 
               dmasm_sem_props dmasm_Ssem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.
Local Open Scope seq_scope.

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

Definition vsubst := Mv.t pexpr.

Definition vsubst_id : vsubst := Mv.empty (fun x => Pvar x).

Definition vsubst_add (s:vsubst) x e : vsubst := (s.[x <- e])%mv.

Definition tosubst (s:vsubst) : subst := Mv.get s.

Lemma tosubst_id (x:var) : tosubst vsubst_id x = Pvar x.
Proof. by rewrite /tosubst /vsubst_id Mv.get0. Qed.

(* TODO: move this *)
Notation efst e := (Papp (Ofst _ _) e).
Notation esnd e := (Papp (Osnd _ _) e).

Definition ewrite_subst :=
  @g_write_subst pexpr (fun t1 t2 e => efst e) (fun t1 t2 e => esnd e).

Definition ewrite_vsubst := 
  foldr (fun (ts:g_tosubst pexpr) vm => @vsubst_add vm ts.(ts_v) ts.(ts_to)).

Definition ewrite_rval {st} (vm:vsubst) (l:rval st) (v:pexpr st) :=
   ewrite_vsubst vm (ewrite_subst l v [::]).

Inductive wppred (t:stype) : stype -> Type :=
  | WPbase : wppred t t
  | WPif   : forall t1 t2, wppred t t1-> wppred t t2-> wppred t (sbool ** (t1 ** t2)).
  
Fixpoint eval_wppred {t t'} (P:sst2ty t -> Prop) (p:wppred t t') : sst2ty t' -> Prop  := 
  match p in wppred _ t_ return sst2ty t_ -> Prop with
  | WPbase  => P
  | WPif t1 t2 p1 p2 => 
    fun (bv:bool * (sst2ty t1 * sst2ty t2)) => 
      if bv.1 then eval_wppred P p1 bv.2.1
      else eval_wppred P p2 bv.2.2
  end.

Record spred (t:stype) := Spred { 
   sp_t : stype;                              
   sp_P : wppred t sp_t;
   sp_e : pexpr sp_t;
}.

Definition s2h t (P:sst2ty t -> Prop) (p:spred t) := 
  fun (s:sestate) => eval_wppred P p.(sp_P) (ssem_pexpr s.(sevm) p.(sp_e)).

Definition map_ssem_pe vm := 
  map (fun ts:g_tosubst pexpr => {|ts_to := ssem_pexpr vm ts.(ts_to) |}).

Lemma swrite_subst_map l vm {t} (rv:rval t) (e:pexpr t) :
  swrite_subst rv (ssem_pexpr vm e) (map_ssem_pe vm l) = 
  map_ssem_pe vm (ewrite_subst rv e l).
Proof.
  elim: rv e l=> {t} [ | ?? r1 Hr1 r2 Hr2 e] l //=.
  by rewrite -Hr2 -Hr1. 
Qed.

Lemma svmap_set_neq id x (v:sst2ty id.(vtype)) vm: id != x ->
    (vm.[id <- v].[x] = vm.[x])%svmap.
Proof.
  by rewrite /svmap_set /svmap_get /=; case: eqP.
Qed.

Lemma vsubst_add_neq s id (v:var) (e:pexpr id.(vtype)):
   id != v -> 
   tosubst (@vsubst_add s id e) v = tosubst s v. 
Proof.
  rewrite /tosubst/vsubst_add;apply: Mv.setP_neq.
Qed.

Lemma vsubst_add_eq v (s:vsubst) (e : pexpr v.(vtype)): 
  tosubst (@vsubst_add s v e) v = e. 
Proof.
  rewrite /tosubst/vsubst_add;apply: Mv.setP_eq.
Qed.

Lemma svmap_set_eq vm id (v:sst2ty id.(vtype)): (vm.[id <- v].[id])%svmap = v.
Proof.
  rewrite /svmap_set /svmap_get /=;case: eqP=>// a.
  by rewrite ((eq_irrelevance a) (erefl id)).
Qed.

Lemma ssem_subst_map {t2} (pe:pexpr t2) vm l :
   ssem_pexpr vm (subst_pexpr (tosubst (ewrite_vsubst vsubst_id l)) pe) =
   ssem_pexpr (swrite_vmap vm (map_ssem_pe vm l)) pe.
Proof.
  elim: pe => //= [ | ?? p1 Hp1 p2 Hp2| ??? p Hp];rewrite ?Hp1 ?Hp2 ?Hp //.
  elim: l => [ | [id e] l Hrec] x //=;first by rewrite tosubst_id //. 
  case: (boolP (id == x))=> [/eqP <-| ?].
  + by rewrite vsubst_add_eq svmap_set_eq.
  rewrite svmap_set_neq // vsubst_add_neq // Hrec.
Qed.

Definition wp_asgn {t1 t2} (rv:rval t1) (e:pexpr t1) (p: spred t2) := 
  {| sp_t := p.(sp_t); sp_P := p.(sp_P);
     sp_e := subst_pexpr (tosubst (ewrite_rval vsubst_id rv e)) p.(sp_e); |}.

Lemma hoare_asgn {t1 t2} (rv:rval t1) (e:pexpr t1) (P:sst2ty t2 -> Prop) (p: spred t2):
  hoare (s2h P (wp_asgn rv e p)) [:: Cbcmd (Assgn rv e)] (s2h P p).
Proof.
  move=> s1_ s2_;set c := Cbcmd _=> /ssem_iV s.
  case: _ {-1}_ _ / s (erefl c) => // s1 s2 ? H [] ?; subst=> {c s1_ s2_}.
  case: H=> <- {s2}; rewrite /wp_asgn /s2h /=.
  by rewrite /swrite_rval /ewrite_rval (swrite_subst_map [::]) ssem_subst_map.
Qed.

(* TODO move this *)
Definition is_skip (c:cmd) :=
  match c with
  | [::] => true
  | _    => false
  end.

Lemma skipP c : reflect (c = [::]) (is_skip c).
Proof. case: c => //=;constructor=> //. Qed.
(* end TODO *)

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
       if is_skip c_ then wpi R
       else (i::c_,R))
    (@wp_bcmd t)
    (fun e c1 c2 wpc1 wpc2 Q =>
       let (c1_, P1) := wpc1 Q in
       let (c2_, P2) := wpc2 Q in
       if is_skip c1_ && is_skip c2_ then
         let (t1,P1,e1) := P1 in
         let (t2,P2,e2) := P2 in
         ([::], {| sp_t := sbool**(t1**t2);
                   sp_P := WPif P1 P2;
                   sp_e := Ppair e (Ppair e1 e2); |})
       else ([::Cif e c1 c2], Q))
    (fun i rn c _ Q => ([::Cfor i rn c], Q))
    (fun _ _ x f a _ Q => ([::Ccall x f a], Q))
    (fun _ _ _ _ _ _ _ => tt).

(* TODO: move this *)
Definition cmd_Ind (P : cmd -> Prop) := 
  @cmd_ind P (fun _ _ _ => True).

Lemma r_wp_cons t i c (P:spred t) :
  wp (i :: c) P = 
   if is_skip (wp c P).1 then wp [::i] (wp c P).2
   else (i::(wp c P).1 , (wp c P).2).
Proof.
  by move=> /=;case (wp c P) => c_ R /=;case (is_skip _).
Qed.

Lemma r_wp_if t e c1 c2 (P:spred t) : 
  wp [::Cif e c1 c2] P = 
   if is_skip (wp c1 P).1 && is_skip (wp c2 P).1 then 
     let Q1 := (wp c1 P).2 in
     let t1 := Q1.(sp_t) in
     let P1 := sp_P Q1 in
     let e1 := Q1.(sp_e) in
     let Q2 := (wp c2 P).2 in
     let t2 := Q2.(sp_t) in
     let P2 := sp_P Q2 in
     let e2 := Q2.(sp_e) in
     ([::], {| sp_t := sbool**(t1**t2);
               sp_P := WPif P1 P2;
               sp_e := Ppair e (Ppair e1 e2); |})
   else ([::Cif e c1 c2], P).
Proof.
  move=> /=;fold (wp c1 P) (wp c2 P). 
  by case: (wp c1 P) => [? []]; case: (wp c2 P) => [? []].
Qed.

Lemma wp_tl c t (P:sst2ty t -> Prop) (p:spred t) : exists tl, 
   c = (wp c p).1 ++ tl /\
   hoare (s2h P (wp c p).2) tl (s2h P p).
Proof.
  elim /cmd_Ind : c p => [ | i c Hi Hc| bc| e c1 c2 Hc1 Hc2| i rn c Hc|?? x f a _ | //] p.
  + by exists ([::]);split=>//=;apply hoare_skip.
  + rewrite r_wp_cons;elim (Hc p)=> {Hc} tlc [Heqc Hwpc].
    case: skipP Heqc => Heq Heqc.
    + elim (Hi (wp c p).2)=> tl [Htl Hwp] ;exists (tl ++ c).
      rewrite catA -Htl;split=>//.
      by rewrite {2} Heqc Heq cat0s;apply:hoare_seq Hwp Hwpc.
    by exists tlc=> /=;rewrite -Heqc.
  + case: bc => [? r e | ?? | ??] /=; try 
      by exists [::];split=>//;apply:hoare_skip.
    exists  [:: Cbcmd (Assgn r e)];case p=>???;split=>//.
    by apply hoare_asgn.
  + rewrite r_wp_if;case: andP=> /=;last
      by exists [::];split=>//;apply:hoare_skip.
    move=> [/skipP Heq1 /skipP Heq2].
    elim (Hc1 p) => {Hc1} tl1;elim (Hc2 p) => {Hc2} tl2.
    rewrite Heq1 Heq2 !cat0s=> -[<- Hc2] [<- Hc1].
    exists [:: Cif e c1 c2];split=>//.
    apply: hoare_if.
    + by apply: (hoare_conseq _ _ Hc1)=> // s;rewrite /s2h /= => -[->].
    by apply: (hoare_conseq _ _ Hc2)=> // s;rewrite /s2h /= => -[/negPf->].
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

(* TODO: move this *)

Coercion Pvar : var >-> pexpr.
Coercion Rvar : var >-> rval.
Coercion Pconst : word >-> pexpr.

Definition x := {| vtype := sword; vname := "x" |}.
Definition y := {| vtype := sword; vname := "y" |}.
Definition z := {| vtype := sword; vname := "z" |}.

Parameter w0 : word.
Parameter w1 : word.

Definition c := 
  [:: assgn x w0;
      assgn y w1;
      Cif (Papp Oeq (Ppair x y)) [::assgn z x] [::assgn z y] ].



Lemma c_ok : hoare (fun _ => True) c (fun s =>  s.(sevm).[x]%svmap = w0 /\ s.(sevm).[y]%svmap = w1).
Proof.
  set P := (fun (v:sst2ty (sword ** sword)) => v.1 = w0 /\ v.2 = w1).
  set p := {| sp_t := sword ** sword;
              sp_P := WPbase (sword ** sword);
              sp_e := Ppair x y; |}.
  wp_core P p.
  skip=> s;rewrite /s2h /p /P /=.
  by move=> _;case :(_ == _).
Qed.

  