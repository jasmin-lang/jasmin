(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple finfun.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import word dmasm_utils dmasm_type dmasm_var dmasm_sem 
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
(* ** Symbolic program expressions                                            *)
(* -------------------------------------------------------------------------- *)

Inductive spexpr : stype -> Type :=
| Evar   :> forall x:var, spexpr x.(vtype)
| Econst :> N -> spexpr sword
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

Notation "e1 '=[' vm ']' e2" := (ssem_spexpr vm e1 = ssem_spexpr vm e2)
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

Lemma sem_p2sp t (e:pexpr t) vm : ssem_spexpr vm (p2sp e) =  ssem_pexpr vm e.
Proof.
  by elim: e => //= [ ???? He1 | ????? He1 ? He2 | ?????? He1 ? He2 ? He3];
      rewrite ?He1 ?He2 ?He3.
Qed.

(* -------------------------------------------------------------------------- *)
(* ** Equality between expressions                                            *)
(* -------------------------------------------------------------------------- *)

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

Notation unknown := (@Error unit bool tt).
Notation known   := (Ok unit).

Fixpoint eval_eq {t} {t'} (e:spexpr t) (e':spexpr t') : result unit bool := 
  match e, e' with
  | Evar x  , Evar x'   => if x == x' then known true else unknown
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
     [x | w | b | ?? o p1 Hp1 |??? o p1 Hp1 p2 Hp2 
     | ???? o p1 Hp1 p2 Hp2 p3 Hp3 | ? p1 Hp1 p2 Hp2 p3 Hp3] t'
     [x' | w' | b' | ?? o' p1' |??? o' p1' p2' 
     | ???? o' p1' p2' p3' | ? p1' p2' p3'] //=.
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

Lemma eval_eqJM vm b t t' (e:spexpr t) (e':spexpr t'):  
  eval_eq e e' = known b ->
  t = t' /\
  if b then JMeq (ssem_spexpr vm e) (ssem_spexpr vm e')
  else ~JMeq (ssem_spexpr vm e) (ssem_spexpr vm e').
Proof.
  elim: e t' e' b => 
     [? | ? | ? | ?? o e1 He1 | ??? o e1 He1 e2 He2 
     | ???? o e1 He1 e2 He2 e3 He3 | ? e1 He1 e2 He2 e3 He3] t'
     [? | ? | ? | ?? o' e1' | ??? o' e1' e2' 
     | ???? o' e1' e2' e3' | ? e1' e2' e3'] b //=.
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
  have : (ssem_spexpr vm e1) != (ssem_spexpr vm e1').
  + by apply /negP;move:jm1;apply contra_p=>/eqP->.
  case: ifP;rewrite eq_sym => _.
  + by rewrite eqb_id => /negPf ->.
  by rewrite eqbF_neg=> /negPn ->.
Qed.

Lemma eval_eqP b t (e e':spexpr t) vm :  
  eval_eq e e' = known b ->
  if b then e =[vm] e' else ~(e =[vm] e').
Proof.
  move=> /(eval_eqJM vm) [] _;case:b;first by apply: JMeq_eq.
  by apply contra_p=> ->.
Qed.

(* -------------------------------------------------------------------------- *)
(* ** Destructor                                                              *)
(* -------------------------------------------------------------------------- *)


Definition destr_pair t1 t2 (p:spexpr (t1 ** t2)) : option (spexpr t1 * spexpr t2).
case H: _ / p => [ ? | ? | ? | ???? | ??? o e1 e2| ???????? | ????].
+ exact None. + exact None. + exact None. + exact None.
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
     [[]/= ?? <-| ???? _ | t1' t2' tr' o e1 e2 | ???????? _| ???? _];
     try by move=> Heq; have:= JMeq_eq Heq.
  case: o e1 e2 => //= [ e1 e2 [] ??|t t' e1 e2];subst.
  + by move=> e;have := JMeq_eq e.
  move=> e;case: (e)=> ??;subst t t'.
  rewrite (eq_irrelevance e (erefl (t1 ** t2))) /= /eq_rect_r /=.
  move=> Heq;have [-> ->] //:= JMeq_eq Heq.
  (*  Enrico have [] -> -> // := JMeq_eq Heq. *)
Qed.

(* -------------------------------------------------------------------------- *)
(* ** Smart constructors                                                      *)
(* -------------------------------------------------------------------------- *)

Definition mk_not (e:spexpr sbool) : spexpr sbool := 
  match e with
  | Ebool b => negb b
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
  (case: t' / e'=> [[??]H | ?? | ?? | ?????| ???????| ?????????| ?????] jmeq;
     first simpl in H);
  subst;try rewrite -(JMeq_eq jmeq).

Lemma mk_notP e vm : mk_not e =[vm] Eapp1 Onot e.
Proof. by jm_destr e. Qed.

Lemma mk_fstP t1 t2 e vm : mk_fst e =[vm] Eapp1 (Ofst t1 t2) e.
Proof.
  rewrite /mk_fst;case H:destr_pair=> [[e1 e2]|//]; by rewrite (destr_pairP H).
Qed.

Lemma mk_sndP t1 t2 e vm : mk_snd e =[vm] Eapp1 (Osnd t1 t2) e.
Proof.
  rewrite /mk_snd;case H:destr_pair=> [[e1 e2]|//]; by rewrite (destr_pairP H).
Qed.

Lemma mk_op1P t1 tr (op:sop1 t1 tr) e vm : mk_op1 op e =[vm] Eapp1 op e.
Proof.
  case: op e vm;[apply:mk_notP|apply:mk_fstP |apply:mk_sndP].
Qed.

Lemma mk_andP (e1 e2:spexpr sbool) vm : 
  mk_and e1 e2 =[vm] Eapp2 Oand e1 e2.
Proof. 
  jm_destr e1;jm_destr e2 => //=;
     try ((by case:ifP) || (by rewrite andbC;case:ifP)).
Qed.

Lemma mk_orP (e1 e2:spexpr sbool) vm : 
  mk_or e1 e2 =[vm] Eapp2 Oor e1 e2.
Proof. 
  jm_destr e1;jm_destr e2 => //=;
     try ((by case:ifP) || (by rewrite orbC;case:ifP)).
Qed.

Lemma mk_eqP (e1 e2:spexpr sword) vm:
  mk_eq e1 e2 =[vm] Eapp2 Oeq e1 e2.
Proof.
  rewrite /mk_eq;case H:eval_eq => [b | ]//=.
  apply esym;move:H=> /(eval_eqP vm);apply: introTF;apply: eqP.
Qed.

Lemma mk_pairP t1 t2 e1 e2 vm:
   mk_pair e1 e2 =[vm] Eapp2 (Opair t1 t2) e1 e2.
Proof. by done. Qed.

Lemma mk_addP_ne n (e:spexpr sword) vm :
  (if (n =? 0)%num then mk_pair false e else Eapp2 Oadd n e) =[vm]
  Eapp2 Oadd n e.
Proof.
  case: N.eqb_spec=> [->|]//=.
  by rewrite /wadd /n2w add0n natr_Zp leqNgt ltn_ord.
Qed.

Lemma mk_addP_en n (e:spexpr sword) vm :
  (if (n =? 0)%num then mk_pair false e else Eapp2 Oadd e n) =[vm]
  Eapp2 Oadd e n.
Proof.
  case: N.eqb_spec=> [->|]//=.
  by rewrite /wadd /n2w addn0 natr_Zp leqNgt ltn_ord.
Qed.

Lemma mk_addP (e1 e2:spexpr sword) vm:
  mk_add e1 e2 =[vm] Eapp2 Oadd e1 e2.
Proof.
  jm_destr e1;jm_destr e2 => //;rewrite /mk_add;
   try (apply: mk_addP_ne || apply:mk_addP_en).
  rewrite [iword_add _ _]surjective_pairing mk_pairP.
  (* FIXME: rewrite /=. is looping *)
  by rewrite /ssem_spexpr /ssem_sop2 iword_addP.
Qed.

Lemma mk_ltP_en n (e:spexpr sword) vm :
  (if (n =? 0)%num then Ebool false else Eapp2 Olt e n) =[vm] Eapp2 Olt e n.
Proof. by case: N.eqb_spec=> [->|]. Qed.

Lemma mk_ltP (e1 e2:spexpr sword) vm:
  mk_lt e1 e2 =[vm] Eapp2 Olt e1 e2.
Proof.
  jm_destr e1;jm_destr e2 => //;rewrite /mk_lt;
   try (apply: mk_ltP_en).
  by apply iword_ltbP.
Qed.

Lemma mk_op2P t1 t2 tr (o:sop2 t1 t2 tr) e1 e2 vm:
  mk_op2 o e1 e2 =[vm] Eapp2 o e1 e2.
Proof.
  case:o e1 e2 vm.
  + by apply: mk_andP. + by apply: mk_orP. + by apply: mk_addP. 
  + by apply: mk_eqP. + by apply: mk_ltP.
  + done. + done.
Qed.

Lemma mk_op3P t1 t2 t3 tr (o:sop3 t1 t2 t3 tr) e1 e2 e3 vm:
  mk_op3 o e1 e2 e3 =[vm] Eapp3 o e1 e2 e3.
Proof. done. Qed.

Lemma mk_ifP_aux t b (e1 e2:spexpr t) vm:
  match eval_eq e1 e2 with
  | Ok true => e1
  | _       => Eif b e1 e2
  end =[vm] Eif b e1 e2.
Proof.                                                     
  case Heq: (eval_eq e1 e2) => [[]|] //.
  by move: Heq=> /(eval_eqP vm) /= ->;case: ifP.
Qed.

Lemma mk_ifP t b (e1 e2:spexpr t) vm: mk_if b e1 e2 =[vm] Eif b e1 e2.
Proof. 
  by (jm_destr b=> //;try by apply:mk_ifP_aux)=> /=;case:ifP.
Qed.

(* -------------------------------------------------------------------------- *)
(* ** Substitution of variable by expressions                                 *)
(* -------------------------------------------------------------------------- *)
Definition vsubst := Mv.t spexpr.

Definition vsubst_id : vsubst := Mv.empty (fun x => Evar x).

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

Lemma p2sp_fst t1 t2 (e:pexpr (t1 ** t2)): 
   (WrInpE.fst (p2sp e)) = p2sp (Papp1 (Ofst _ _) e).
Proof. by done. Qed.

Lemma p2sp_snd t1 t2 (e:pexpr (t1 ** t2)): 
   (WrInpE.snd (p2sp e)) = p2sp (Papp1 (Osnd _ _) e).
Proof. by done. Qed.

Definition map_ssem_pe vm := 
  map (fun ts:E.tosubst => {|W.ts_to := ssem_spexpr vm ts.(E.ts_to) |}).

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
    rewrite ?mk_op1P ?mk_op2P ?mk_op3P ?mk_ifP /= ?He1 ?He2 ?He3 //.
  elim: l => [ | [id e] l Hrec] x //=;first by rewrite /vsubst_id Mv.get0.
  case: (boolP (id == x))=> [/eqP <-| ?].
  + by rewrite Fv.setP_eq Mv.setP_eq.
  by rewrite Fv.setP_neq // Mv.setP_neq. 
Qed.

(* -------------------------------------------------------------------------- *)
(* ** merge_if b e1 e2                                                        *)
(* -------------------------------------------------------------------------- *)

Fixpoint merge_if (b:spexpr sbool) {t} : spexpr t -> spexpr t ->  spexpr t   := 
  match t as t_  return spexpr t_ -> spexpr t_ ->  spexpr t_ with
  | sprod t1 t2 => fun p p' => 
    match destr_pair p, destr_pair p' with
    | Some(p1,p2), Some(p1', p2') => 
      Eapp2 (Opair _ _) (merge_if b p1 p1') (merge_if b p2 p2')
    | _, _ => mk_if b p p'
    end
  | _ => fun p p' => mk_if b p p'
  end.

Lemma merge_ifP t b (e e':spexpr t) vm:
  merge_if b e e' =[vm] Eif b e e'.
Proof.
  elim:t e e' vm=>[ | |t1 Ht1 t2 Ht2 | n t Ht];try apply mk_ifP.
  move=> /= e e' vm.
  case He: destr_pair => [[p1 p2] | ];try by rewrite mk_ifP.
  case He': destr_pair => [[p1' p2'] | ];try by rewrite mk_ifP.
  by rewrite /= Ht1 Ht2 (destr_pairP He) (destr_pairP He') /=;case:ifP.
Qed.
