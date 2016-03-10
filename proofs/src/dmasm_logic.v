(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith.
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
(* ** Substitution of variable by expressions                                 *)
(* -------------------------------------------------------------------------- *)

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
  
Inductive spexpr : stype -> Type :=
| Evar   : forall x:var, spexpr x.(vtype)
| Econst : N -> spexpr sword
| Ebool  : bool -> spexpr sbool
| Eapp1  : forall t1 tr: stype, 
  sop1 t1 tr -> spexpr t1 -> spexpr tr
| Eapp2  : forall t1 t2 tr: stype, 
  sop2 t1 t2 tr -> spexpr t1 -> spexpr t2 -> spexpr tr
| Eapp3  : forall t1 t2 t3 tr: stype,
  sop3 t1 t2 t3 tr -> spexpr t1 -> spexpr t2 -> spexpr t3 -> spexpr tr
| Eif    : forall t: stype, 
  spexpr sbool -> spexpr t -> spexpr t -> spexpr t.

(* FIXME : Econst : can be c mod base == c' mod base *)

Fixpoint eqb_spexpr {t} {t'} (e:spexpr t) (e':spexpr t') := 
  match e, e' with
  | Evar x  , Evar x'   => x == x'
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

Fixpoint ssem_spexpr st (vm : svmap) (pe : spexpr st) : sst2ty st :=
  match pe with
  | Evar v   => vm.[ v ]%vmap
  | Econst c => n2w c
  | Ebool  b => b
  | Eapp1 _ _ o pe1 =>
      let v1 := ssem_spexpr vm pe1 in
      ssem_sop1 o v1
  | Eapp2 _ _ _ o pe1 pe2 =>
      let v1 := ssem_spexpr vm pe1 in 
      let v2 := ssem_spexpr vm pe2 in
      ssem_sop2 o v1 v2
  | Eapp3 _ _ _ _ o pe1 pe2 pe3 =>
      let v1 := ssem_spexpr vm pe1 in
      let v2 := ssem_spexpr vm pe2 in
      let v3 := ssem_spexpr vm pe3 in
      ssem_sop3 o v1 v2 v3
  | Eif _ b e1 e2 =>
    if ssem_spexpr vm b then ssem_spexpr vm e1
    else ssem_spexpr vm e2
  end.

Fixpoint p2sp {t} (e:pexpr t) : spexpr t :=
  match e with
  | Pvar          x           => Evar x
  | Pconst        w           => Econst w
  | Papp1 _ _     op e1       => Eapp1 op (p2sp e1)
  | Papp2 _ _ _   op e1 e2    => Eapp2 op (p2sp e1) (p2sp e2)
  | Papp3 _ _ _ _ op e1 e2 e3 => Eapp3 op (p2sp e1) (p2sp e2) (p2sp e3)
  end.

Definition vsubst := Mv.t spexpr.

Definition vsubst_id : vsubst := Mv.empty (fun x => Evar x).

Definition destr_pair t1 t2 (p:spexpr (t1 ** t2)) : option (spexpr t1 * spexpr t2).
case H: _ / p => [ ? | ? | ? | ???? | ??? o e1 e2| ???????? | ????].
+ exact None. + exact None. + exact None. + exact None.
(case:o H e1 e2 => [||||||??[]<-<- e1 e2];last by exact (Some (e1,e2)))=> *;
 exact None.
+ exact None. + exact None.
Defined.

Definition mk_not (e:spexpr sbool) : spexpr sbool := 
  match e with
  | Ebool b => Ebool (negb b)
  | _       => Eapp1 Onot e
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
  | Ebool b, _ => if b then e2 else Ebool false
  | _, Ebool b => if b then e1 else Ebool false
  | _, _       => Eapp2 Oand e1 e2 
  end.

Definition mk_or (e1 e2:spexpr sbool) : spexpr sbool := 
  match e1, e2 with
  | Ebool b, _ => if b then Ebool true else e2
  | _, Ebool b => if b then Ebool true else e1
  | _, _       => Eapp2 Oor e1 e2 
  end.

Notation unknown := (@Error unit bool tt).
Notation known   := (Ok unit).

Fixpoint eval_eq {t} {t'} (e:spexpr t) (e':spexpr t') : result unit bool := 
  match e, e' with
  | Evar x  , Evar x'   => if x == x' then known true else unknown
  | Econst c, Econst c' => known (c == c') (* FIXME *)
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
 
Definition mk_eq (e1 e2:spexpr sword) : spexpr sbool := 
  match eval_eq e1 e2 with
  | Ok b => Ebool b
  | Error _ => Eapp2 Oeq e1 e2 
  end.

(* FIXME: add other simplifications *)
Definition mk_op2 t1 t2 tr (op:sop2 t1 t2 tr): spexpr t1 -> spexpr t2 -> spexpr tr := 
  match op in sop2 t1 t2 tr return spexpr t1 -> spexpr t2 -> spexpr tr with
  | Oand  => mk_and 
  | Oor   => mk_or 
  | Oeq   => mk_eq 
  | o     => Eapp2 o
  end.

(* FIXME: add simplifications *)
Definition mk_op3 t1 t2 t3 tr (op:sop3 t1 t2 t3 tr):
  spexpr t1 -> spexpr t2 -> spexpr t3 -> spexpr tr :=
  Eapp3 op. 

Definition mk_if t (b:spexpr sbool) (e1 e2 : spexpr t) := 
  match b with
  | Ebool b => if b then e1 else e2
  | _       => Eif b e1 e2
  end.

Fixpoint subst_spexpr st (s : vsubst) (pe : spexpr st) :=
  match pe in spexpr st_ return spexpr st_ with
  | Evar          v              => s.[v]%mv
  | Econst        c              => Econst c
  | Ebool         b              => Ebool  b
  | Eapp1 _ _     op pe1         =>
    mk_op1 op (subst_spexpr s pe1)
  | Eapp2 _ _ _   op pe1 pe2     => 
    mk_op2 op (subst_spexpr s pe1) (subst_spexpr s pe2)
  | Eapp3 _ _ _ _ op pe1 pe2 pe3 => 
    mk_op3 op (subst_spexpr s pe1) (subst_spexpr s pe2) (subst_spexpr s pe3)
  | Eif _ b pe1 pe2       => 
    mk_if (subst_spexpr s b) (subst_spexpr s pe1) (subst_spexpr s pe2)
  end.

Module WrInpE.
  Definition to := spexpr.
  Definition fst t1 t2 (e:spexpr (t1 ** t2)) := (Eapp1 (Ofst _ _) e).
  Definition snd t1 t2 (e:spexpr (t1 ** t2)) := (Eapp1 (Osnd _ _) e).
End WrInpE.

Module E := WRmake Mv WrInpE.

(* -------------------------------------------------------------------------- *)
(* ** Weakest Precondition                                                    *)
(* -------------------------------------------------------------------------- *)


Definition spred (t:stype) := spexpr t.
  
Definition s2h t (P:sst2ty t -> Prop) (p:spred t) := 
  fun (s:sestate) => P (ssem_spexpr s.(sevm) p).

Definition map_ssem_pe vm := 
  map (fun ts:E.tosubst => {|W.ts_to := ssem_spexpr vm ts.(E.ts_to) |}).

Lemma sem_p2sp vm t (e:pexpr t) : ssem_spexpr vm (p2sp e) =  ssem_pexpr vm e.
Proof.
  by elim: e => //= [ ???? He1 | ????? He1 ? He2 | ?????? He1 ? He2 ? He3];
      rewrite ?He1 ?He2 ?He3.
Qed.

Lemma p2sp_fst t1 t2 (e:pexpr (t1 ** t2)): 
   (WrInpE.fst (p2sp e)) = p2sp (Papp1 (Ofst _ _) e).
Proof. by done. Qed.

Lemma p2sp_snd t1 t2 (e:pexpr (t1 ** t2)): 
   (WrInpE.snd (p2sp e)) = p2sp (Papp1 (Osnd _ _) e).
Proof. by done. Qed.

Lemma write_subst_map l vm {t} (rv:rval t) (e:pexpr t) :
  W.write_subst rv (ssem_pexpr vm e) (map_ssem_pe vm l) = 
  map_ssem_pe vm (E.write_subst rv (p2sp e) l).
Proof.
  elim: rv e l=> {t} [ ??| ?? r1 Hr1 r2 Hr2 e] l //=.
  + by rewrite sem_p2sp.
  by rewrite p2sp_fst p2sp_snd -Hr2 -Hr1.  
Qed.

Lemma ssem_subst_map {t2} (pe:spexpr t2) vm l :
   ssem_spexpr vm (subst_spexpr (E.write_vmap vsubst_id l) pe) =
   ssem_spexpr (W.write_vmap vm (map_ssem_pe vm l)) pe.
Proof.
  elim: pe => //= [| ???? He1 | ????? He1 ? He2 
                   | ?????? He1 ? He2 ? He3 | ?? He1 ? He2 ? He3];
    rewrite ?He1 ?He2 ?He3 //.
  elim: l => [ | [id e] l Hrec] x //=;first by rewrite /vsubst_id Mv.get0.
  case: (boolP (id == x))=> [/eqP <-| ?].
  + by rewrite Fv.setP_eq Mv.setP_eq.
  by rewrite Fv.setP_neq // Mv.setP_neq. 
Admitted. 

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

Lemma destr_pairP t1 t2 (p:spexpr (t1 ** t2)) p1 p2:
   destr_pair p = Some (p1, p2) -> p = Eapp2 (Opair _ _) p1 p2.
Proof.
  move=>Heq;apply JMeq_eq.
  have {Heq}: JMeq (destr_pair p) (Some (p1, p2)) by rewrite Heq.
  rewrite /destr_pair. 
  move:p (erefl (t1 ** t2)). 
  set t12 := (X in forall (p:spexpr X) (e : _ = X), _ -> @JMeq (spexpr X) _ _ _) => p.
  case : t12 / p => // 
     [[]/= ?? <-| ???? _ | t1' t2' tr' o e1 e2 | ???????? _| ???? _];
     try by move=> Heq; have:= JMeq_eq Heq.
  case: o e1 e2 => //= [ e1 e2 [] ??|t t' e1 e2];subst.
  + by move=> e;have := JMeq_eq e.
  move=> e;case: (e)=> ??;subst t t'.
  rewrite (eq_irrelevance e (erefl (t1 ** t2))) /= /eq_rect_r /=.
  move=> Heq;have [-> ->] //:= JMeq_eq Heq.
  (*  Enrico have [] -> -> // := JMeq_eq Heq. *)
Qed.

Fixpoint merge_if (b:spexpr sbool) {t} : spexpr t -> spexpr t ->  spexpr t   := 
  match t as t_  return spexpr t_ -> spexpr t_ ->  spexpr t_ with
  | sprod t1 t2 => fun p p' => 
    match destr_pair p, destr_pair p' with
    | Some(p1,p2), Some(p1', p2') => 
      Eapp2 (Opair _ _) (merge_if b p1 p1') (merge_if b p2 p2')
    | _, _ => if eqb_spexpr p p' then p else Eif b p p'
    end
  | _ => fun p p' => if eqb_spexpr p p' then p else Eif b p p'
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
   if is_skip (wp c P).1 then wp [::i] (wp c P).2
   else (i::(wp c P).1 , (wp c P).2).
Proof.
  by move=> /=;case (wp c P) => c_ R /=;case (is_skip _).
Qed.

Lemma r_wp_if t e c1 c2 (P:spred t) : 
  wp [::Cif e c1 c2] P = 
   if is_skip (wp c1 P).1 && is_skip (wp c2 P).1 then 
     let P1 := (wp c1 P).2 in
     let P2 := (wp c2 P).2 in
     ([::], merge_if (p2sp e) P1 P2)
   else ([::Cif e c1 c2], P).
Proof.
  move=> /=;fold (wp c1 P) (wp c2 P). 
  by case: (wp c1 P) => ??; case: (wp c2 P) => ??.
Qed.

(*Lemma eqb_sopP t1 t2 t1' t2' (o:sop t1 t2) (o':sop t1' t2') : 
   t1 = t1' -> eqb_sop o o' -> t2 = t2' /\ JMeq o o'.
Proof.
  (destruct o;destruct o')=> // [ []-> ->| []-> ->|[]-> |[]-> ] //.
Qed. *)

Lemma eqb_spexprJM t t' (p:spexpr t) (p':spexpr t') : eqb_spexpr p p' -> t = t' /\ JMeq p p' .
Admitted.
(*
Proof.
  elim: p t' p' => [x | w| t1 t2 p1 Hp1 p2 Hp2|t1 t2 o p Hp | t1 p Hp p1 Hp1 p2 Hp2] /= t'
    [x'| w'| t1' t2' p1' p2'|t1' t2' o' p' | t1' p' p1' p2' ] //.
  + move=> /eqP -> //.
  + move=> /eqP -> //.
  + move=> /andP [] /Hp1 [] ? Heq1 /Hp2 [] ? Heq2=> {Hp1 Hp2};subst;split =>//.
    by rewrite (JMeq_eq Heq1) (JMeq_eq Heq2).
  + rewrite andbC => /andP [] /Hp [] ?;subst=> Heq1. 
    rewrite (JMeq_eq Heq1)=> /eqb_sopP [] // ? Heq2;subst.
    by rewrite (JMeq_eq Heq2).    
  move=> /andP [] /andP [] /Hp []_ Heq /Hp1 []? Heq1 /Hp2 []? Heq2;subst.
  by rewrite (JMeq_eq Heq1) (JMeq_eq Heq2).
Qed. *)

Lemma eqb_spexprP t  (p p':spexpr t) : eqb_spexpr p p' -> p = p'.
Proof. move=> /eqb_spexprJM [] _;apply JMeq_eq. Qed.

Lemma merge_if_aux1 s e t P (p1 p2: spexpr t): 
  s2h P (Eif (p2sp e) p1 p2) s ->
  s2h P (if ssem_pexpr (sevm s) e then p1 else p2) s.
Proof.
  by rewrite /s2h /= sem_p2sp;case: (ssem_pexpr _ _).
Qed.
  
Lemma merge_if_aux s e t P (p1 p2: spexpr t): 
  s2h P (if eqb_spexpr p1 p2 then p1 else Eif (p2sp e) p1 p2) s ->
  s2h P (if ssem_pexpr (sevm s) e then p1 else p2) s.
Proof.
  case H: (eqb_spexpr p1 p2).
  + by move: H=> /eqb_spexprP ->;case:(ssem_pexpr _ _).
  apply: merge_if_aux1.
Qed.

Lemma pair_if t1 t2 (b:bool) (a1 b1:t1) (a2 b2:t2) :
  (if b then (a1,a2) else (b1, b2)) = ((if b then a1 else b1), (if b then a2 else b2)).
Proof. by case: b. Qed.

Lemma merge_ifP s e t P (p p': spexpr t):
   s2h P (merge_if (p2sp e) p p') s -> 
   s2h P (if  ssem_pexpr (sevm s) e then p else p') s.
Proof.
(*
  elim: p p' P => [[tx nx] | w| ?? p1 Hp1 p2 Hp2 /=|?? o p _ | ? p _ p1 _ p2 _] p' P;
    try apply: merge_if_aux.
  case Heq: destr_pair=>[ [p1' p2'] | ];try apply: merge_if_aux.
  have {Heq} -> := destr_pairP Heq. (* Enrico: have -> {Heq} := destr_pairP Heq. *)
  rewrite /s2h /= fun_if /= pair_if -!fun_if=> HP.
  apply: (@Hp1 p1' 
     (fun v => P (v,  ssem_spexpr (sevm s) (if ssem_pexpr (sevm s) e then p2 else p2')))) => /=.
  by apply: (@Hp2 p2' 
     (fun v => P (ssem_spexpr (sevm s) (merge_if (p2sp e) p1 p1'), v))).
Qed.
*)
Admitted.

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
    exists  [:: Cbcmd (Assgn r e)];split=>//.
    by apply hoare_asgn.
  + rewrite r_wp_if;case: andP=> /=;last
      by exists [::];split=>//;apply:hoare_skip.
    move=> [/skipP Heq1 /skipP Heq2].
    elim (Hc1 p) => {Hc1} tl1;elim (Hc2 p) => {Hc2} tl2.
    rewrite Heq1 Heq2 !cat0s=> -[<- Hc2] [<- Hc1].
    exists [:: Cif e c1 c2];split=>//.
    apply: hoare_if.
    + by apply: (hoare_conseq _ _ Hc1)=> // s [] He /merge_ifP;rewrite He.
    by apply: (hoare_conseq _ _ Hc2)=> // s [] /negPf He /merge_ifP;rewrite He.
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
Coercion Pconst : N >-> pexpr.
Coercion Evar : var >-> spexpr.
Coercion Econst : N >-> spexpr.

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


  