(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple finfun.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import gen_map word dmasm_utils dmasm_type dmasm_var dmasm_expr dmasm_Ssem 
               symbolic_expr.

Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.


(* -------------------------------------------------------------------------- *)
(* ** Equality between expressions                                            *)
(* -------------------------------------------------------------------------- *)

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
(case:o H e1 e2 => [||||||||||??[]<-<- e1 e2];last by exact (Some (e1,e2)))=> *;
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
  case: o e1 e2 => //= [e1 e2 [] ??|e1 e2 [] ??|t t' e1 e2];subst.
  + by move=> e;have := JMeq_eq e.
  + by move=> e;have := JMeq_eq e.
  move=> e;case: (e)=> ??;subst t t'.
  rewrite (eq_irrelevance e (erefl (t1 ** t2))) /= /eq_rect_r /=.
  move=> Heq;have [-> ->] // := JMeq_eq Heq.
  (*  Enrico have [] -> -> // := JMeq_eq Heq. *)
Qed.

(* -------------------------------------------------------------------------- *)
(* ** Smart constructors                                                      *)
(* -------------------------------------------------------------------------- *)

Definition snot (e:spexpr sbool) : spexpr sbool := 
  match e with
  | Ebool b          => negb b
  | Eapp1 _ _ Onot e => e 
  | _                => Eapp1 Onot e
  end.

Definition sfst t1 t2 (p:spexpr (t1 ** t2)) : spexpr t1 :=
  match destr_pair p with
  | Some (p1,p2) => p1
  | _            => Eapp1 (Ofst _ _) p
  end.

Definition ssnd t1 t2 (p:spexpr (t1 ** t2)) : spexpr t2 :=
  match destr_pair p with
  | Some (p1,p2) => p2
  | _            => Eapp1 (Osnd _ _) p
  end.

Definition s_op1 t1 tr (op:sop1 t1 tr): spexpr t1 -> spexpr tr := 
  match op in sop1 t1 tr return spexpr t1 -> spexpr tr with
  | Onot     => snot 
  | Ofst _ _ => @sfst _ _ 
  | Osnd _ _ => @ssnd _ _
  end.

Definition is_bool (e:spexpr sbool) :=
  match e with Ebool b => Some b | _ => None end.

Definition sand e1 e2 := 
  match is_bool e1, is_bool e2 with
  | Some b, _ => if b then e2 else false
  | _, Some b => if b then e1 else false
  | _, _      => Eapp2 Oand e1 e2
  end.

Definition sor (e1 e2:spexpr sbool) : spexpr sbool := 
   match is_bool e1, is_bool e2 with
  | Some b, _ => if b then Ebool true else e2
  | _, Some b => if b then Ebool true else e1
  | _, _       => Eapp2 Oor e1 e2 
  end.

Definition seq (e1 e2:spexpr sword) : spexpr sbool := 
  match eval_eq e1 e2 with
  | Ok b    => b
  | Error _ => Eapp2 Oeq e1 e2 
  end.

Definition spair {t t'} (e1:spexpr t) (e2:spexpr t') :=
  Eapp2 (Opair t t') e1 e2.

Definition is_const (e:spexpr sword) := 
  match e with
  | Econst n => Some n 
  | _        => None
  end.

Definition sadd (e1 e2:spexpr sword) : spexpr sword := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => iword_add n1 n2 
  | Some n, _ => 
    if (n =? 0)%num then e2 else Eapp2 Oadd e1 e2
  | _, Some n => 
    if (n =? 0)%num then e1 else Eapp2 Oadd e1 e2
  | _, _ => Eapp2 Oadd e1 e2
  end.

Definition saddc (e1 e2:spexpr sword) : spexpr (sbool ** sword) := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => 
    let (c,n) := iword_addc n1 n2 in
    spair c n
  | Some n, _ =>
    if (n =? 0)%num then spair false e2 else Eapp2 Oaddc e1 e2
  | _, Some n => 
    if (n =? 0)%num then spair false e1 else Eapp2 Oaddc e1 e2
  | _, _ => Eapp2 Oaddc e1 e2
  end.

Definition ssub (e1 e2:spexpr sword) : spexpr sword := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => iword_sub n1 n2 
  | _, Some n => 
    if (n =? 0)%num then e1 else Eapp2 Osub e1 e2
  | _, _ => Eapp2 Osub e1 e2
  end.

Definition ssubc (e1 e2:spexpr sword) : spexpr (sbool ** sword) := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => 
    let (c,n) := iword_subc n1 n2 in
    spair c n
  | _, Some n => 
    if (n =? 0)%num then spair false e1 else Eapp2 Osubc e1 e2
  | _, _ => Eapp2 Osubc e1 e2
  end.

Definition slt (e1 e2:spexpr sword) : spexpr sbool := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => iword_ltb n1 n2 
  | _        , Some n  => if (n =? 0)%num then Ebool false else Eapp2 Olt e1 e2
  | _        , _         => Eapp2 Olt e1 e2 (* FIXME : false is e1 = e2 *)
  end.

Definition sle (e1 e2:spexpr sword) : spexpr sbool := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => iword_leb n1 n2 
  | _        , _         => Eapp2 Ole e1 e2 (* FIXME : true is e1 = e2 *)
  end.

(* FIXME: add other simplifications *)
Definition s_op2 t1 t2 tr (op:sop2 t1 t2 tr): spexpr t1 -> spexpr t2 -> spexpr tr := 
  match op in sop2 t1 t2 tr return spexpr t1 -> spexpr t2 -> spexpr tr with
  | Oand        => sand 
  | Oor         => sor 
  | Oeq         => seq 
  | Oadd        => sadd
  | Oaddc       => saddc
  | Osub        => ssub
  | Osubc       => ssubc
  | Olt         => slt
  | Ole         => sle
  | Oget n      => Eapp2 (Oget n)
  | Opair t1 t2 => @spair t1 t2
  end.

(* FIXME: add simplifications *)
Definition s_op3 t1 t2 t3 tr (op:sop3 t1 t2 t3 tr):
  spexpr t1 -> spexpr t2 -> spexpr t3 -> spexpr tr :=
  Eapp3 op. 

Definition sif t (b:spexpr sbool) (e1 e2 : spexpr t) := 
  match is_bool b with
  | Some b => if b then e1 else e2
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

Lemma snotP e : snot e =E Eapp1 Onot e.
Proof. 
  jm_destr e=> // rho. 
  match goal with |- snot (@Eapp1 ?t1 _ ?o ?e') =[_] _ => move: t1 o e' jmeq end.  
  move=> t1 o e1 Hjme1 /=;set E := Eapp1 _ _.
  move: (erefl t1) (erefl sbool) (JMeq_refl o).
  set o' := (O in _ -> _ -> JMeq O _ -> _).
  set t1' := (X in X = _ -> _ -> @JMeq (sop1 X _) _ _ _ -> _).
  set t2' := (X in _ -> X = _ -> @JMeq (sop1 _ X) _ _ _ -> _).
  case: t1' t2' / o' => [|??|??] ?? jmeq;subst;rewrite /E -(JMeq_eq jmeq) //=.
  by rewrite Bool.negb_involutive.
Qed.

Lemma sfv_snot e : Ssv.Equal (sfv (snot e)) (sfv e).
Proof.
  jm_destr e=> //=;rewrite !sfv_op1 /=.
  match type of jmeq with JMeq (Eapp1 ?s ?s') _ => rename s into o;rename s' into s1  end.
  match type of o with sop1 ?t _ => rename t into t1 end.
  move: (erefl t1) (erefl sbool) (JMeq_refl o).
  set o' := (O in _ -> _ -> JMeq O _ -> _).
  set t1' := (X in X = _ -> _ -> @JMeq (sop1 X _) _ _ _ -> _).
  set t2' := (X in _ -> X = _ -> @JMeq (sop1 _ X) _ _ _ -> _).
  by case: t1' t2' / o' => [|??|??] ?? jmeq';subst;rewrite -(JMeq_eq jmeq') //=.
Qed.

Lemma sfstP t1 t2 e : sfst e =E Eapp1 (Ofst t1 t2) e.
Proof.
  rewrite /sfst=>?;case H:destr_pair=> [[e1 e2]|//]; by rewrite (destr_pairP H).
Qed.

Lemma sfv_sfst t1 t2 (e:spexpr (t1 ** t2)) : Ssv.Subset (sfv (sfst e)) (sfv e).
Proof.
  rewrite /sfst=>?;case H:destr_pair=> [[e1 e2]|//].
  rewrite (destr_pairP H) sfv_op2;SsvD.fsetdec.
Qed.

Lemma ssndP t1 t2 e : ssnd e =E Eapp1 (Osnd t1 t2) e.
Proof.
  rewrite /ssnd=>?;case H:destr_pair=> [[e1 e2]|//]; by rewrite (destr_pairP H).
Qed.

Lemma sfv_ssnd t1 t2 (e:spexpr (t1 ** t2)) : Ssv.Subset (sfv (ssnd e)) (sfv e).
Proof.
  rewrite /ssnd=>?;case H:destr_pair=> [[e1 e2]|//].
  rewrite (destr_pairP H) sfv_op2;SsvD.fsetdec.
Qed.

Lemma s_op1P t1 tr (op:sop1 t1 tr) e : s_op1 op e =E Eapp1 op e.
Proof.
  case: op e;[apply:snotP|apply:sfstP |apply:ssndP].
Qed.

Lemma sfv_s_op1 t1 tr (o:sop1 t1 tr) e : Ssv.Subset (sfv (s_op1 o e)) (sfv e).
Proof.
  case: o e => [|??|??] e /=.
  + by rewrite sfv_snot.
  + by apply sfv_sfst.
  by apply sfv_ssnd.
Qed.

Lemma is_boolP e b : is_bool e = Some b -> e = Ebool b.
Proof. by jm_destr e=> //= -[] ->. Qed.

Lemma sandP (e1 e2:spexpr sbool) : sand e1 e2 =E Eapp2 Oand e1 e2.
Proof. 
  move=>?;rewrite /sand;case H: is_bool => [b | ].
  + by rewrite (is_boolP H);case: ifP.
  by case H1: is_bool => [b|] //=;rewrite (is_boolP H1) andbC;case: ifP.
Qed.

Lemma sfv_sand (e1 e2:spexpr sbool) : Ssv.Subset (sfv (sand e1 e2)) (sfv (Eapp2 Oand e1 e2)).
Proof.
  rewrite sfv_op2 /sand;case H: is_bool => [b | ].
  + case: ifP;rewrite ?sfv_bool;SsvD.fsetdec.
  case H1: is_bool => [[] | ];rewrite ?sfv_bool ?sfv_op2;SsvD.fsetdec.
Qed.

Lemma sorP (e1 e2:spexpr sbool) : sor e1 e2 =E Eapp2 Oor e1 e2.
Proof.
  move=>?;rewrite /sor;case H: is_bool => [b | ].
  + by rewrite (is_boolP H);case: ifP.
  by case H1: is_bool => [b|] //=;rewrite (is_boolP H1) orbC;case: ifP.
Qed.

Lemma sfv_sor (e1 e2:spexpr sbool) : Ssv.Subset (sfv (sor e1 e2)) (sfv (Eapp2 Oor e1 e2)).
Proof.
  rewrite sfv_op2 /sor;case H: is_bool => [b | ].
  + case: ifP;rewrite ?sfv_bool;SsvD.fsetdec.
  case H1: is_bool => [[] | ];rewrite ?sfv_bool ?sfv_op2;SsvD.fsetdec.
Qed.

Lemma seqP (e1 e2:spexpr sword): seq e1 e2 =E Eapp2 Oeq e1 e2.
Proof.
  rewrite /seq=>rho;case H:eval_eq => [b | ]//=.
  apply esym;move:H=> /(eval_eqP rho);apply: introTF;apply: eqP.
Qed.

Lemma sfv_seq (e1 e2:spexpr sword) : Ssv.Subset (sfv (seq e1 e2)) (sfv (Eapp2 Oeq e1 e2)).
Proof.
  by rewrite sfv_op2 /seq;case H:eval_eq => [b | ]//=;rewrite ?sfv_bool ?sfv_op2;SsvD.fsetdec.
Qed.

Lemma spairP t1 t2 e1 e2: spair e1 e2 =E Eapp2 (Opair t1 t2) e1 e2.
Proof. by done. Qed.

Lemma sfv_spair t1 t2 e1 e2: Ssv.Equal (sfv (spair e1 e2)) (sfv (Eapp2 (Opair t1 t2) e1 e2)).
Proof. by done. Qed.

Lemma is_constP (e:spexpr sword) n: is_const e = Some n -> e = n.
Proof. by jm_destr e=> //= -[] ->. Qed.

Lemma saddP (e1 e2:spexpr sword): sadd e1 e2 =E Eapp2 Oadd e1 e2.
Proof.
  move=> ?;rewrite /sadd;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) //.
  + by rewrite /= iword_addP.
  + by case: N.eqb_spec=> [->|] //=; rewrite /wadd /n2w add0r.
  by case: N.eqb_spec=> [->|] //=; rewrite /wadd /n2w addr0.
Qed.

Lemma sfv_sadd (e1 e2:spexpr sword): Ssv.Subset (sfv (sadd e1 e2)) (sfv (Eapp2 Oadd e1 e2)).
Proof.
  by rewrite /sadd;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) //; case: N.eqb_spec=> [->|];
   rewrite ?sfv_op2;SsvD.fsetdec.
Qed.

Lemma saddcP (e1 e2:spexpr sword): saddc e1 e2 =E Eapp2 Oaddc e1 e2.
Proof.
  move=> ?;rewrite /saddc;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) //.
  + rewrite [iword_addc _ _]surjective_pairing spairP.
    by rewrite /ssem_spexpr /ssem_sop2 iword_addcP.
  + by case: N.eqb_spec=> [->|] //=; rewrite /waddc /n2w add0r.
  by case: N.eqb_spec=> [->|] //=; rewrite /waddc /n2w addr0 ltnn.
Qed.

Lemma sfv_saddc (e1 e2:spexpr sword): Ssv.Subset (sfv (saddc e1 e2)) (sfv (Eapp2 Oaddc e1 e2)).
Proof.
  by rewrite sfv_op2 /saddc;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) //; try case: N.eqb_spec=> [->|];
   rewrite ?sfv_op2;SsvD.fsetdec.
Qed.

Lemma ssubP (e1 e2:spexpr sword): ssub e1 e2 =E Eapp2 Osub e1 e2.
Proof.
  move=> ?;rewrite /ssub;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) //.
  + by rewrite /ssem_spexpr /ssem_sop2 iword_subP.
  by case: N.eqb_spec=> [->|] //=;by rewrite /wsub /n2w subr0.
Qed.

Lemma sfv_ssub (e1 e2:spexpr sword): Ssv.Subset (sfv (ssub e1 e2)) (sfv (Eapp2 Osub e1 e2)).
Proof.
  by rewrite sfv_op2 /ssub;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) //; try case: N.eqb_spec=> [->|];
   rewrite ?sfv_op2;SsvD.fsetdec.
Qed.

Lemma ssubcP (e1 e2:spexpr sword): ssubc e1 e2 =E Eapp2 Osubc e1 e2.
Proof.
  move=> ?;rewrite /ssubc;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) //.
  + rewrite [iword_subc _ _]surjective_pairing spairP.
    by rewrite /ssem_spexpr /ssem_sop2 iword_subcP.
  by case: N.eqb_spec=> [->|] //=;by rewrite /wsubc /n2w subr0 ltn0.
Qed.

Lemma sfv_ssubc (e1 e2:spexpr sword): Ssv.Subset (sfv (ssubc e1 e2)) (sfv (Eapp2 Osubc e1 e2)).
Proof.
  rewrite sfv_op2 /ssubc;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) //; try case: N.eqb_spec=> [->|];
   rewrite ?sfv_op2;try SsvD.fsetdec.
  by case: iword_subc=> ?? /=. 
Qed.

Lemma sltP (e1 e2:spexpr sword): slt e1 e2 =E Eapp2 Olt e1 e2.
Proof.
  move=> ?; rewrite /slt;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) //.
  + by apply iword_ltbP.
  by case: N.eqb_spec=> [->|].
Qed.

Lemma sfv_slt (e1 e2:spexpr sword): Ssv.Subset (sfv (slt e1 e2)) (sfv (Eapp2 Olt e1 e2)).
Proof.
  rewrite sfv_op2 /slt;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) ?sfv_op2 //.
  by case:ifP;rewrite ?sfv_const ?sfv_bool;SsvD.fsetdec.
Qed.

Lemma sleP (e1 e2:spexpr sword): sle e1 e2 =E Eapp2 Ole e1 e2.
Proof.
  move=> ?; rewrite /sle;case H1:is_const => [n1| //];case H2:is_const => [n2|//];
   rewrite ?(is_constP H1) ?(is_constP H2) //.
  by apply iword_lebP.
Qed.

Lemma sfv_sle (e1 e2:spexpr sword): Ssv.Subset (sfv (sle e1 e2)) (sfv (Eapp2 Ole e1 e2)).
Proof.
  rewrite sfv_op2 /sle;case H1:is_const => [n1|//];last by rewrite sfv_op2.
  case H2:is_const => [n2|];last by rewrite sfv_op2.
  by rewrite ?(is_constP H1) ?(is_constP H2) ?sfv_op2.
Qed.

Lemma s_op2P t1 t2 tr (o:sop2 t1 t2 tr) e1 e2: s_op2 o e1 e2 =E Eapp2 o e1 e2.
Proof.
  case:o e1 e2.
  + by apply: sandP. + by apply: sorP. 
  + by apply: saddP. + by apply: saddcP. 
  + by apply: ssubP. + by apply: ssubcP. 
  + by apply: seqP.  + by apply: sltP.   + by apply: sleP.
  + done. + by apply: spairP.
Qed.

Lemma sfv_s_op2 t1 t2 tr (o:sop2 t1 t2 tr) e1 e2: Ssv.Subset (sfv (s_op2 o e1 e2)) (sfv (Eapp2 o e1 e2)).
Proof.
  case:o e1 e2=> /=. 
  + by apply: sfv_sand. + by apply: sfv_sor. 
  + by apply: sfv_sadd. + by apply: sfv_saddc. 
  + by apply: sfv_ssub. + by apply: sfv_ssubc. 
  + by apply: sfv_seq.  + by apply: sfv_slt.   + by apply: sfv_sle.
  + SsvD.fsetdec. + move=> *;rewrite sfv_spair;SsvD.fsetdec.
Qed.

Lemma s_op3P t1 t2 t3 tr (o:sop3 t1 t2 t3 tr) e1 e2 e3 st:
  s_op3 o e1 e2 e3 =[st] Eapp3 o e1 e2 e3.
Proof. done. Qed.

Lemma sfv_s_op3 t1 t2 t3 tr (o:sop3 t1 t2 t3 tr) e1 e2 e3 :
  Ssv.Subset (sfv (s_op3 o e1 e2 e3)) (sfv (Eapp3 o e1 e2 e3)).
Proof. done. Qed.

Lemma sifP t b (e1 e2:spexpr t): sif b e1 e2 =E Eif b e1 e2.
Proof. 
  rewrite /sif;case H:is_bool => [b1|].
  + by move=> ?;rewrite (is_boolP H) //=;case:ifP.
  case Heq: (eval_eq e1 e2) => [[]|] // rho.
  by move: Heq=> /(eval_eqP rho) /= ->;case: ifP.
Qed.

Lemma sfv_sif  t b (e1 e2:spexpr t): Ssv.Subset (sfv (sif b e1 e2)) (sfv (Eif b e1 e2)).
Proof.
  rewrite sfv_if /sif;case H:is_bool => [b1|].
  + by rewrite (is_boolP H) sfv_bool;case: ifP;SsvD.fsetdec.
  by case Heq: (eval_eq e1 e2) => [[]|];rewrite ?sfv_if //;SsvD.fsetdec.
Qed.
  
(* -------------------------------------------------------------------------- *)
(* ** Simplification of expression                                            *)
(* -------------------------------------------------------------------------- *)

Fixpoint sesubst t (s : psubst) (pe : spexpr t) :=
  match pe in spexpr st_ return spexpr st_ with
  | Evar          v              => s.(s_v).[v]%mv 
  | Esvar         x              => s.(s_s).[x]%msv
  | Econst        c              => Econst c
  | Ebool         b              => Ebool  b
  | Eapp1 _ _     op pe1         => s_op1 op (sesubst s pe1)
  | Eapp2 _ _ _   op pe1 pe2     => s_op2 op (sesubst s pe1) (sesubst s pe2)
  | Eapp3 _ _ _ _ op pe1 pe2 pe3 => s_op3 op (sesubst s pe1) (sesubst s pe2) (sesubst s pe3)
  | Eif _ b pe1 pe2              => sif (sesubst s b) (sesubst s pe1) (sesubst s pe2)
  end.

Definition eopt t := @sesubst t ps1.
  
Lemma sesubstP t (e:spexpr t) s: sesubst s e =E esubst s e.
Proof.
  elim: e => //=
    [???? He1|????? He1 ? He2|?????? He1 ? He2 ? He3|?? He1 ? He2 ? He3];
    rewrite ?s_op1P ?s_op2P ?s_op3P ?sifP /= ?He1 ?He2 ?He3 //.
Qed.

Lemma eoptP t (e:spexpr t) : eopt e =E e.
Proof. 
  rewrite /eopt sesubstP=> rho; rewrite esubstP; apply /eq_on_fv/ps1P. 
Qed.

Lemma sfv_eopt t (e:spexpr t) : Ssv.Subset (sfv (eopt e)) (sfv e).
Proof.
  rewrite /eopt;elim: e => //=
   [?|?|?|?|?? o e1 He1|??? o e1 He1 e2 He2|???? o e1 He1 e2 He2 e3 He3|? e1 He1 e2 He2 e3 He3] //.
  + by have := @sfv_s_op1 _ _ o (sesubst ps1 e1);rewrite sfv_op1;SsvD.fsetdec.
  + by have := @sfv_s_op2 _ _ _ o (sesubst ps1 e1) (sesubst ps1 e2);rewrite !sfv_op2;SsvD.fsetdec.
  + by have := @sfv_s_op3 _ _ _ _ o (sesubst ps1 e1) (sesubst ps1 e2) (sesubst ps1 e3);rewrite !sfv_op3;SsvD.fsetdec.
  have := @sfv_sif _ (sesubst ps1 e1) (sesubst ps1 e2) (sesubst ps1 e3);rewrite !sfv_if;SsvD.fsetdec.
Qed.

Definition sopt s := 
  {| v_fv := s.(v_fv); v_v := Mv.map (fun _ e => eopt e) s.(v_v) |}.

Instance wf_sopt s {H:wf_vsubst s} : wf_vsubst (sopt s).
Proof.
  constructor => [?|?].
  + by rewrite Mv.dft_mapP /eopt vdft_v /= Mv.get0.
  rewrite /sopt /= Mv.mapP /= Mv.indom_mapP => /vindom_v.
  by apply SsvD.F.Subset_trans;apply sfv_eopt.
Qed.

  
(* -------------------------------------------------------------------------- *)
(* ** Smart constructors for formulaes                                        *)
(* -------------------------------------------------------------------------- *)

Fixpoint eval_feq (f f':sform) : bool := 
  match f, f' with
  | Fbool b  , Fbool b' => rdflt false (eval_eq b b') 
  | Fpred p b, Fpred p' b' => 
    if p == p' then rdflt false (eval_eq b b') 
    else false
  | Fnot f      , Fnot f' => eval_feq f f'
  | Fop2 o f1 f2, Fop2 o' f1' f2' =>
    if o == o' then 
      if eval_feq f1 f1' then eval_feq f2 f2'
      else false
    else false
  | Fif b f1 f2, Fif b' f1' f2' =>
    if rdflt false (eval_eq b b') then 
      if eval_feq f1 f1' then eval_feq f2 f2'
      else false
    else false
  | Fquant q x f, Fquant q' x' f' =>
    if q == q' then
      if x == x' then eval_feq f f'
      else false
    else false
  | _, _ => false
  end.

Lemma eval_feqP (f f':sform): eval_feq f f' -> f =F f'.
Proof.
  elim: f f' => 
     [e|? e|? Hf1|?? Hf1 ? Hf2|e ? Hf1 ? Hf2|??? Hf1]
     [e'|? e'|?|???|e' ??|???] //=.
  + case Heq: eval_eq => [[]|] //= _.
    by move: Heq=> /eval_eqP;rewrite -/(eeq e e') => ->.
  + case:eqP e' => // <- e';case Heq: eval_eq => [[]|] //= _.
    by move: Heq=> /eval_eqP;rewrite -/(eeq e e') => ->.
  + by move=> /Hf1 ->.
  + by case: eqP => // <-;case: ifP => // /Hf1 -> /Hf2 ->.
  + case Heq: eval_eq => [[]|] //=.
    move: Heq=> /eval_eqP;rewrite -/(eeq e e') => ->.
    by case: ifP => // /Hf1 -> /Hf2 ->.
  by case: eqP=>//->;case: eqP=>//-> /Hf1 ->.
Qed.
  
Definition sf_not f := 
  match f with
  | Fbool e => Fbool (snot e)
  | _       => Fnot f
  end.

Definition is_fbool f := 
  match f with
  | Fbool e => 
    match e with
    | Ebool b => Some b
    | _       => None
    end
  | _       => None
  end.

Definition sf_and f1 f2 := 
  match is_fbool f1, is_fbool f2 with
  | Some b, _ => if b then f2 else Fbool false
  | _, Some b => if b then f1 else Fbool false
  | _, _ => if eval_feq f1 f2 then f1 else Fop2 Fand f1 f2
  end.

Definition sf_or f1 f2 := 
  match is_fbool f1, is_fbool f2 with
  | Some b, _ => if b then Fbool true else f2
  | _, Some b => if b then Fbool true else f1
  | _, _ => if eval_feq f1 f2 then f1 else Fop2 For f1 f2
  end.

Definition sf_imp f1 f2 := 
  match is_fbool f1, is_fbool f2 with
  | Some b, _ => if b then f2 else Fbool true 
  | _, Some b => if b then Fbool true else sf_not f1
  | _, _ => if eval_feq f1 f2 then Fbool true else Fop2 Fimp f1 f2
  end.

Definition sf_iff f1 f2 := 
  match is_fbool f1, is_fbool f2 with
  | Some b, _ => if b then f2 else sf_not f2 
  | _, Some b => if b then f1 else sf_not f1
  | _, _ => if eval_feq f1 f2 then Fbool true else Fop2 Fiff f1 f2
  end.

Definition sf_op2 o f1 f2 :=
  match o with
  | Fand => sf_and f1 f2
  | For  => sf_or  f1 f2
  | Fimp => sf_imp f1 f2
  | Fiff => sf_iff f1 f2
  end.

Definition sf_if e f1 f2 :=
  match e with
  | Ebool b => if b then f1 else f2
  | _       => if eval_feq f1 f2 then f1 else Fif e f1 f2
  end.

Lemma sf_notP f: sf_not f =F Fnot f.
Proof.
  by case: f => //= ?;rewrite snotP=> ? /=; rewrite (rwP negP).
Qed.

Lemma is_fboolP f b : is_fbool f = Some b -> f = Fbool b.
Proof. by case: f => // e; jm_destr e => // -[] ->. Qed.

Lemma sf_andP f1 f2: sf_and f1 f2 =F Fop2 Fand f1 f2.
Proof.
  rewrite /sf_and;case: (is_fbool f1) (@is_fboolP f1) => [b /(_ b (erefl _)) ->| _] /=.
  + by case b=> ? /=;intuition. 
  case: (is_fbool f2) (@is_fboolP f2) => [b /(_ b (erefl _)) ->| _] //=.
  + by case b=> ? /=;intuition. 
  case: eval_feq (@eval_feqP f1 f2)=> // -> // ? /=;tauto.
Qed.

Lemma sf_orP f1 f2: sf_or f1 f2 =F Fop2 For f1 f2.
Proof.
  rewrite /sf_or;case: (is_fbool f1) (@is_fboolP f1) => [b /(_ b (erefl _)) ->| _] /=.
  + by case b=> ? /=;intuition. 
  case: (is_fbool f2) (@is_fboolP f2) => [b /(_ b (erefl _)) ->| _] //=.
  + by case b=> ? /=;intuition. 
  case: eval_feq (@eval_feqP f1 f2)=> // -> // ? /=;tauto.
Qed.

Lemma sf_impP f1 f2: sf_imp f1 f2 =F Fop2 Fimp f1 f2.
Proof.
  rewrite /sf_imp;case: (is_fbool f1) (@is_fboolP f1) => [b /(_ b (erefl _)) ->| _] /=.
  + by case b=> ? /=;intuition. 
  case: (is_fbool f2) (@is_fboolP f2) => [b /(_ b (erefl _)) ->| _] //=.
  + by case b;rewrite ?sf_notP=> ? /=;intuition. 
  by case: eval_feq (@eval_feqP f1 f2)=> // -> // ? /=;intuition.
Qed.

Lemma sf_iffP f1 f2: sf_iff f1 f2 =F Fop2 Fiff f1 f2.
Proof.
  rewrite /sf_iff;case: (is_fbool f1) (@is_fboolP f1) => [b /(_ b (erefl _)) ->| _] /=.
  + by case b;rewrite ?sf_notP => ? /=;intuition. 
  case: (is_fbool f2) (@is_fboolP f2) => [b /(_ b (erefl _)) ->| _] //=.
  + by case b;rewrite ?sf_notP=> ? /=;intuition. 
  by case: eval_feq (@eval_feqP f1 f2)=> // -> // ? /=;intuition.
Qed.

Lemma sf_op2P o f1 f2 : sf_op2 o f1 f2 =F Fop2 o f1 f2.
Proof. by case o=> /=;rewrite ?(sf_andP,sf_orP,sf_impP, sf_iffP). Qed.

Lemma sf_ifP_eq e f1 f2: (if eval_feq f1 f2 then f1 else Fif e f1 f2) =F Fif e f1 f2.
Proof.
  by case: eval_feq (@eval_feqP f1 f2) => [->|_] // ? /=;case: ifP.
Qed.

Lemma sf_ifP e f1 f2: sf_if e f1 f2 =F Fif e f1 f2.
Proof.
  rewrite /sf_if;jm_destr e => //;try by apply sf_ifP_eq.
  by case:ifP=> ?.
Qed.

Definition f_lt e1 e2 := Fbool (slt e1 e2).

Definition f_le e1 e2 := Fbool (sle e1 e2).

Definition f_eq e1 e2 := Fbool (seq e1 e2).

(* -------------------------------------------------------------------------- *)
(* ** Simplification of formulaes                                             *)
(* -------------------------------------------------------------------------- *)

Fixpoint sfsubst (s:psubst) (f:sform) := 
  match f with
  | Fbool   e     => Fbool    (sesubst s e)
  | Fpred   p  e  => @Fpred p (sesubst s e)
  | Fnot    f     => sf_not    (sfsubst s f)
  | Fop2  o f1 f2 => sf_op2 o  (sfsubst s f1) (sfsubst s f2) 
  | Fif   b f1 f2 => sf_if    (sesubst s b)  (sfsubst s f1) (sfsubst s f2) 
  | Fquant q x f => 
    let (id,s)  := rename s f x in
    Fquant q (SVar x.(svtype) id) (sfsubst s f)
  end.

Lemma sfsubstP f s: sfsubst s f =F fsubst s f.
Proof.
  elim:f s => 
    [?|??|? He1|?? He1 ? He2|?? He1 ? He2|??? He1] s //=;
  rewrite ?sf_notP ?sf_op2P ?sf_ifP ?sesubstP ?He1 ?He2 //.
  by case: rename => ??;rewrite He1.
Qed.
