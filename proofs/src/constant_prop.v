(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import JMeq ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import finmap strings word dmasm_utils dmasm_type dmasm_var dmasm_expr dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope fun_scope.
Local Open Scope vmap.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------------- *)
(* ** Smart constructors                                                      *)
(* -------------------------------------------------------------------------- *)

Definition snot (e:pexpr sbool) : pexpr sbool := 
  match e with
  | Pbool b          => negb b
  | Papp1 _ _ Onot e => e 
  | _                => Papp1 Onot e
  end.

Definition sfst t1 t2 (p:pexpr (t1 ** t2)) : pexpr t1 := 
  Papp1 (Ofst _ _) p.

Definition ssnd t1 t2 (p:pexpr (t1 ** t2)) : pexpr t2 :=
  Papp1 (Osnd _ _) p.

Definition s_op1 t1 tr (op:sop1 t1 tr): pexpr t1 -> pexpr tr := 
  match op in sop1 t1 tr return pexpr t1 -> pexpr tr with
  | Onot     => snot 
  | Ofst _ _ => @sfst _ _ 
  | Osnd _ _ => @ssnd _ _
  end.

Definition sand e1 e2 := 
  match is_bool e1, is_bool e2 with
  | Some b, _ => if b then e2 else false
  | _, Some b => if b then e1 else false
  | _, _      => Papp2 Oand e1 e2
  end.

Definition sor (e1 e2:pexpr sbool) : pexpr sbool := 
   match is_bool e1, is_bool e2 with
  | Some b, _ => if b then Pbool true else e2
  | _, Some b => if b then Pbool true else e1
  | _, _       => Papp2 Oor e1 e2 
  end.

Definition spair {t t'} (e1:pexpr t) (e2:pexpr t') :=
  Papp2 (Opair t t') e1 e2.

Definition seq (e1 e2:pexpr sword) : pexpr sbool := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => iword_eqb n1 n2
  | _, _             => Papp2 Oeq e1 e2
  end.

Definition sadd (e1 e2:pexpr sword) : pexpr sword := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => iword_add n1 n2 
  | Some n, _ => 
    if (n =? 0)%num then e2 else Papp2 Oadd e1 e2
  | _, Some n => 
    if (n =? 0)%num then e1 else Papp2 Oadd e1 e2
  | _, _ => Papp2 Oadd e1 e2
  end.

Definition saddc (e1 e2:pexpr sword) : pexpr (sbool ** sword) := 
  Papp2 Oaddc e1 e2.

Definition ssub (e1 e2:pexpr sword) : pexpr sword := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => iword_sub n1 n2 
  | _, Some n => 
    if (n =? 0)%num then e1 else Papp2 Osub e1 e2
  | _, _ => Papp2 Osub e1 e2
  end.

Definition ssubc (e1 e2:pexpr sword) : pexpr (sbool ** sword) := 
  Papp2 Osubc e1 e2.

Definition slt (e1 e2:pexpr sword) : pexpr sbool := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => iword_ltb n1 n2 
  | _        , Some n  => if (n =? 0)%num then Pbool false else Papp2 Olt e1 e2
  | _        , _         => Papp2 Olt e1 e2 (* FIXME : false is e1 = e2 *)
  end.

Definition sle (e1 e2:pexpr sword) : pexpr sbool := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => iword_leb n1 n2 
  | _        , _         => Papp2 Ole e1 e2 (* FIXME : true is e1 = e2 *)
  end.

(* FIXME: add other simplifications *)
Definition s_op2 t1 t2 tr (op:sop2 t1 t2 tr): pexpr t1 -> pexpr t2 -> pexpr tr := 
  match op in sop2 t1 t2 tr return pexpr t1 -> pexpr t2 -> pexpr tr with
  | Oand        => sand 
  | Oor         => sor 
  | Oeq         => seq 
  | Oadd        => sadd
  | Oaddc       => saddc
  | Osub        => ssub
  | Osubc       => ssubc
  | Olt         => slt
  | Ole         => sle
  | Oget n      => Papp2 (Oget n)
  | Opair t1 t2 => @spair t1 t2
  end.

Definition s_op3 t1 t2 t3 tr (op:sop3 t1 t2 t3 tr):=  Papp3 op.

(* ** constant propagation 
 * -------------------------------------------------------------------- *)


Local Notation map := (Mvar.t iword).

Fixpoint const_prop_e t (m:map) (e:pexpr t) : pexpr t :=
  match e in pexpr t0 return pexpr t0 with
  | Pvar x =>
    match vtype x as t0 return pexpr t0 -> pexpr t0 with
    | sword => fun e =>
      match Mvar.get m x with
      | Some n => Pconst n
      | _      => e
      end
    | _ => fun e => e
    end (Pvar x)
  | Pconst n => Pconst n
  | Pbool  b => Pbool b
  | Papp1 _ _ op e1 => 
    s_op1 op (const_prop_e m e1)
  | Papp2 _ _ _ op e1 e2 => 
    s_op2 op (const_prop_e m e1) (const_prop_e m e2)
  | Papp3 _ _ _ _ op e1 e2 e3 => 
    s_op3 op (const_prop_e m e1) (const_prop_e m e2) (const_prop_e m e3) 
  end.

Definition empty_cpm : map := @Mvar.empty iword.

Definition merge_cpm : map -> map -> map := 
  Mvar.map2 (fun _ (o1 o2: option iword) => 
   match o1, o2 with
   | Some n1, Some n2 => 
     if (n1 =? n2)%num then Some n1
     else None
   | _, _ => None
   end).

Definition remove_cpm (m:map) (s:Sv.t): map :=
  Sv.fold (fun x m => Mvar.remove m x) s m.

Fixpoint add_cpm t (m:map) (rv:rval t) : pexpr t -> map := 
  match rv in rval t0 return pexpr t0 -> map with 
  | Rvar x => fun e => 
    match is_const e with
    | Some n => Mvar.set m x n 
    | None   => remove_cpm m (vrv rv)
    end
  | Rpair _ _ rv1 rv2 => fun e => 
     match destr_pair e with
     | Some (e1,e2) => add_cpm (add_cpm m rv2 e2) rv1 e1
     | None   => remove_cpm m (vrv rv)
     end
  end.
                           
Section CMD.

  Variable const_prop_i : map -> instr -> map * cmd.

  Fixpoint const_prop (m:map) (c:cmd) : map * cmd :=
    match c with
    | [::] => (m, [::])
    | i::c =>
      let (m,ic) := const_prop_i m i in
      let (m, c) := const_prop m c in
      (m, ic ++ c)
    end.

End CMD.

Definition const_prop_bcmd (m:map) (i:bcmd) :=
  match i with
  | Assgn t rv e =>
    let e := const_prop_e m e in
    (add_cpm m rv e, Assgn rv e)
  | Load r e => 
    let e := const_prop_e m e in
    (remove_cpm m (vrv r), Load r e)
  | Store e1 e2 =>
    let e1 := const_prop_e m e1 in
    let e2 := const_prop_e m e2 in
    (m, Store e1 e2)
  end.

Fixpoint const_prop_i (m:map) (i:instr) : map * cmd := 
  match i with
  | Cbcmd i     => let (m,i) := const_prop_bcmd m i in (m,[::Cbcmd i])
  | Cif b c1 c2 => 
    let b := const_prop_e m b in
    match is_bool b with
    | Some b => 
      let c := if b then c1 else c2 in 
      const_prop const_prop_i m c
    | None =>
      let (m1,c1) := const_prop const_prop_i m c1 in
      let (m2,c2) := const_prop const_prop_i m c2 in
      (merge_cpm m1 m2, [:: Cif b c1 c2])
    end
  | Cfor fi x (dir, e1, e2) c =>
    let r := write_i i in
    let m := remove_cpm m r in
    let (_,c) := const_prop const_prop_i m c in
    (m,[::Cfor fi x (dir, const_prop_e m e1, const_prop_e m e2) c])
  | Ccall ta tr x fd arg =>
    let arg := const_prop_e m arg in
    let r := write_i i in
    let m := remove_cpm m r in
    let fd := const_prop_call fd in
    (m, [:: Ccall x fd arg])
  end

with const_prop_call ta tr (fd:fundef ta tr) := 
  match fd with
  | FunDef ta tr p c r =>
    let (_, c) := const_prop const_prop_i empty_cpm c in
    FunDef p c r
  end.

(* ** proofs
 * -------------------------------------------------------------------- *)

Definition eqok t (e1 e2:pexpr t) st := 
  forall v, sem_pexpr st e1 = ok v -> sem_pexpr st e2 = ok v.

Notation "e1 '=[' st ']' e2" := (eqok e1 e2 st)
 (at level 70, no associativity).

Definition eeq t (e1 e2:pexpr t) := forall rho, e1 =[rho] e2.

Notation "e1 '=E' e2" := (eeq e1 e2) (at level 70, no associativity).

Lemma eeq_refl t : Reflexive (@eeq t).
Proof. by move=> ???. Qed.

Hint Immediate eeq_refl.

Lemma snotP e : Papp1 Onot e =E snot e.
Proof. 
  jm_destr e=> //;try apply eeq_refl.
  + by rewrite /snot=> rho v /=.
  move=> rho.                           
  match goal with |- _ =[_] snot (@Papp1 ?t1 _ ?o ?e') => move: t1 o e' jmeq end.  
  move=> t1 o e1 Hjme1 /=;set E := Papp1 _ _.
  move: (erefl t1) (erefl sbool) (JMeq_refl o).
  set o' := (O in _ -> _ -> JMeq O _ -> _).
  set t1' := (X in X = _ -> _ -> @JMeq (sop1 X _) _ _ _ -> _).
  set t2' := (X in _ -> X = _ -> @JMeq (sop1 _ X) _ _ _ -> _).
  case: t1' t2' / o' => [|??|??] ?? jmeq;subst;rewrite /E -(JMeq_eq jmeq) //=.
  by move=> v /=; case (sem_pexpr _ _) => //= ?;rewrite Bool.negb_involutive.
Qed.

Lemma sfstP t1 t2 e : Papp1 (Ofst t1 t2) e =E sfst e.
Proof. apply eeq_refl. Qed.

Lemma ssndP t1 t2 e : Papp1 (Osnd t1 t2) e =E ssnd e.
Proof. apply eeq_refl. Qed.

Lemma s_op1P t1 tr (op:sop1 t1 tr) e : Papp1 op e =E s_op1 op e.
Proof.
  case: op e;[apply:snotP|apply:sfstP |apply:ssndP].
Qed.

Lemma bind_ok A x : x >>= [eta ok (A:=A)] = x.
Proof. by case: x. Qed.

Lemma sandP (e1 e2:pexpr sbool) : Papp2 Oand e1 e2 =E sand e1 e2.
Proof. 
  move=>?;rewrite /sand;case H: is_bool => [b | ].
  + by rewrite (is_boolP H);case: ifP=> //= Hb v /=;case: sem_pexpr.
  by case H1: is_bool => [[]|] v //=;rewrite (is_boolP H1) /=;
       case: sem_pexpr => //= a;rewrite andbC.
Qed.

Lemma sorP (e1 e2:pexpr sbool) :  Papp2 Oor e1 e2 =E sor e1 e2.
Proof.
  move=>?;rewrite /sor;case H: is_bool => [b | ].
  + by rewrite (is_boolP H);case: ifP=> //= Hb v /=;case: sem_pexpr.
  by case H1: is_bool => [[]|] v //=;rewrite (is_boolP H1) /=;
       case: sem_pexpr => //= a;rewrite orbC.
Qed.

Lemma seqP (e1 e2:pexpr sword): Papp2 Oeq e1 e2 =E seq e1 e2.
Proof.
  rewrite /seq=>rho; case H1:(is_const e1);try apply eeq_refl.
  case H2:(is_const e2);try apply eeq_refl.
  rewrite (is_constP H1) (is_constP H2)=> ? /=; by rewrite iword_eqbP.
Qed.

Lemma spairP t1 t2 e1 e2:  Papp2 (Opair t1 t2) e1 e2 =E spair e1 e2.
Proof. by apply eeq_refl. Qed.

Lemma saddP (e1 e2:pexpr sword): Papp2 Oadd e1 e2 =E sadd e1 e2.
Proof.
  move=> ?;rewrite /sadd;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) // => v /=.
  + by rewrite iword_addP.
  + case: N.eqb_spec=> [->|] //=;case sem_pexpr => //= ?.
    by rewrite /wadd /n2w add0r.
  case: N.eqb_spec=> [->|] //=; case sem_pexpr => //= ?.
  by rewrite /wadd /n2w addr0.
Qed.

Lemma saddcP (e1 e2:pexpr sword): Papp2 Oaddc e1 e2 =E saddc e1 e2 .
Proof. by apply eeq_refl. Qed.

Lemma ssubP (e1 e2:pexpr sword): Papp2 Osub e1 e2 =E ssub e1 e2.
Proof.
  move=> ?;rewrite /ssub;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) // => v /=.
  + by rewrite iword_subP.
  case: N.eqb_spec=> [->|] //=;case sem_pexpr => //= ?.
  by rewrite /wsub /n2w subr0.
Qed.

Lemma ssubcP (e1 e2:pexpr sword): Papp2 Osubc e1 e2 =E ssubc e1 e2.
Proof. by apply eeq_refl. Qed.

Lemma sltP (e1 e2:pexpr sword): Papp2 Olt e1 e2 =E slt e1 e2.
Proof.
  move=> ?; rewrite /slt;case H1:is_const => [n1|];case H2:is_const => [n2|];
   rewrite ?(is_constP H1) ?(is_constP H2) // => v /=.
  + by rewrite iword_ltbP.
  case: N.eqb_spec=> [->|] //=;case sem_pexpr => //= ?.
Qed.

Lemma sleP (e1 e2:pexpr sword): Papp2 Ole e1 e2 =E sle e1 e2.
Proof.
  move=> ?; rewrite /sle;case H1:is_const => [n1|];last by apply eeq_refl.
  case H2:is_const => [n2|];last by apply eeq_refl.
  by move=> v /=; rewrite ?(is_constP H1) ?(is_constP H2) //=; rewrite iword_lebP.
Qed.

Lemma s_op2P t1 t2 tr (o:sop2 t1 t2 tr) e1 e2: Papp2 o e1 e2 =E s_op2 o e1 e2.
Proof.
  case:o e1 e2.
  + by apply: sandP. + by apply: sorP. 
  + by apply: saddP. + by apply: saddcP. 
  + by apply: ssubP. + by apply: ssubcP. 
  + by apply: seqP.  + by apply: sltP.   + by apply: sleP.
  + by move=> ???;apply eeq_refl. + by apply: spairP.
Qed.

Lemma s_op3P t1 t2 t3 tr (o:sop3 t1 t2 t3 tr) e1 e2 e3: 
   s_op3 o e1 e2 e3 =E Papp3 o e1 e2 e3.
Proof. apply eeq_refl. Qed.

Definition valid_map (vm: vmap)  (m:map) := 
  forall x n, Mvar.get m x = Some n -> 
     match vtype x as t0 return st2ty t0 -> Prop with 
     | sword => fun v => v = n2w n 
     | _     => fun v => True
     end vm.[x].

Lemma const_prop_eP t (e:pexpr t) (rho:vmap) (m:map):  
  valid_map rho m ->
  e =[rho] const_prop_e m e.
Proof.
  move=> Hvalid;rewrite /eqok.
  elim: e=> [x | n | b | ?? o e1 He1 | ??? o e1 He1 e2 He2 | ???? o e1 He1 e2 He2 e3 He3]
     v //=.
  + move=> [] Heq; have := Hvalid x;rewrite Heq.
    case: x v Heq => -[ | | ??|?? ] ?? H /=;rewrite ?H //.
    by case Mvar.get => [n /(_ n (erefl _)) -> //| /=]; rewrite H.
  + by case Heq1: sem_pexpr=> //= Heqo; apply s_op1P => /=;rewrite (He1 _ Heq1).
  + case Heq1: (sem_pexpr rho e1)=> //=;case Heq2: sem_pexpr=> //= Heqo.
    by apply s_op2P => /=;rewrite (He1 _ Heq1) (He2 _ Heq2).
  case Heq1: (sem_pexpr rho e1)=> //=;case Heq2: (sem_pexpr rho e2)=> //=.
  case Heq3: sem_pexpr=> //= Heqo.
  by apply s_op3P => /=;rewrite (He1 _ Heq1) (He2 _ Heq2) (He3 _ Heq3).
Qed.
  
Lemma get_remove_cpm m xs x n: 
  Mvar.get (remove_cpm m xs) x = Some n ->  
  Mvar.get m x = Some n /\ ~Sv.In x xs.
Proof.
  rewrite /remove_cpm.
  apply SvP.MP.fold_rec_bis. 
  + by move=> s s' a ? H /H [] ??;split => //;SvD.fsetdec. 
  + by move=> ->;split => //;SvD.fsetdec. 
  move=> z m' s1 ?? H; rewrite Mvar.removeP. 
  case: (z =P x) => //= ? /H [];split=> //;SvD.fsetdec. 
Qed.

Lemma valid_map_rm rho1 rho2 xs m:
  rho1 = rho2 [\ xs] ->
  valid_map rho1 m ->
  valid_map rho2 (remove_cpm m xs).
Proof.
  move=> Hrho Hval [] [] //= nx v /get_remove_cpm [] Hm Hin.
  by rewrite -Hrho //; apply (Hval _ _ Hm). 
Qed.

Lemma remove_cpmP rho m t (x:rval t) v: 
  valid_map rho m ->
  valid_map (write_rval rho x v) (remove_cpm m (vrv x)).
Proof.
  move=> Hv; apply: (valid_map_rm _ Hv); apply vrvP.
Qed.

Lemma add_cpmP_aux rho1 rho2 m t x (e:pexpr t) v: 
  valid_map rho1 m ->
  sem_pexpr rho2 e = ok v ->
  valid_map (write_rval rho1 x v) (add_cpm m x e).
Proof.
  elim: x e v m rho1 rho2 => [[] tx nx /=| ?? rv1 Hrv1 rv2 Hrv2] e v m rho1 rho2 Hvalid;
    simpl add_cpm.
  + case Heq: (is_const e) => [?|] He;last by apply: remove_cpmP.
    case: e v Heq He => //= n v [] <- [] <- z i.
    rewrite Mvar.setP;case (_ =P z) => [<- [] <- /=| /eqP Hneq Hget].
    + by rewrite Fv.setP_eq.
    by rewrite Fv.setP_neq //;apply: Hvalid.    
  case Heq: destr_pair => [ [e1 e2]| ];last by move=> ?;apply: remove_cpmP.
  have He:= destr_pairP Heq;subst e => /=.
  case Heq1 : (sem_pexpr _ e1) => [v1|] //=.
  case Heq2 : (sem_pexpr _ e2) => [v2|] //= [] <- /=.
  apply (Hrv1 _ _ _ _ rho2) => //.
  apply (Hrv2 _ _ _ _ rho2) => //.
Qed.

Lemma add_cpmP rho m t x (e:pexpr t) v: 
  valid_map rho m ->
  sem_pexpr rho e = ok v ->
  valid_map (write_rval rho x v) (add_cpm m x e).
Proof. by apply add_cpmP_aux. Qed.

Lemma const_prop_bcmdP (s s':estate) (m:map) (i:bcmd) : 
  valid_map s.(evm) m ->
  sem_bcmd s i = ok s' ->
  valid_map s'.(evm) (fst (const_prop_bcmd m i)) /\
  sem_bcmd s (snd (const_prop_bcmd m i)) = ok s'.
Proof.
  case: i => [t x e | x e | e1 e2] Hvalid /=.
  + case Heq : sem_pexpr => [v|] //=.
    have H:= const_prop_eP Hvalid Heq. 
    by rewrite H /= => -[] <-;split=> //=; apply add_cpmP.
  + case Heq : sem_pexpr => [v|] //=.
    case Heq': read_mem => [v'|] //= [] <- /=.
    have H:= const_prop_eP Hvalid Heq;split;first by apply remove_cpmP.    
    by rewrite H /= Heq'.
  case Heq1 : (sem_pexpr _ e1)=> [v1|] //=.
  case Heq2 : (sem_pexpr _ e2)=> [v2|] //=.
  case Heq : write_mem => [?|] //= [] <- /=;split => //.
  by rewrite (const_prop_eP Hvalid Heq1) (const_prop_eP Hvalid Heq2) /= Heq.
Qed.

Lemma merge_cpmP rho m1 m2 : 
  valid_map rho m1 \/ valid_map rho m2 ->  
  valid_map rho (merge_cpm m1 m2).
Proof.
  move=> Hv x n;rewrite /merge_cpm Mvar.map2P //. 
  case Heq1 : (Mvar.get m1 x) => [n1|//]; case Heq2 : (Mvar.get m2 x) => [n2|//].
  case: N.eqb_spec=> //.
  by move=> ? [] ?;do 2 subst;elim: Hv => Hv;apply Hv.
Qed.


Section PROOF.

  Let Pi (i:instr) := 
    forall s s' m, sem_i s i s' ->
    valid_map s.(evm) m ->
    valid_map s'.(evm) (fst (const_prop_i m i)) /\
    sem s (snd (const_prop_i m i)) s'.

  Let Pc (c:cmd) := 
    forall s s' m, sem s c s' ->
    valid_map s.(evm) m ->
    valid_map s'.(evm) (fst (const_prop const_prop_i m c)) /\
    sem s (snd (const_prop const_prop_i m c)) s'.

  Let Pf ta tr (fd:fundef ta tr) := 
    forall mem mem' va vr, 
    sem_call mem fd va mem' vr ->
    sem_call mem (const_prop_call fd) va mem' vr.

  Let Hskip : Pc [::].
  Proof.
    by move=> s s' m H;inversion_clear H;split=>//=;constructor.
  Qed.

  Let Hseq  : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc s s' m H;inversion H;clear H;subst=> /=.
    move=> /(Hi _ _ m H3) []; case const_prop_i => m' i' /=.
    move=> /(Hc _ _ m' H5) []; case const_prop => m'' c' /= hv Hc' Hi';split=>//.
    by apply (sem_app Hi' Hc').
  Qed.

  Let Hbcmd : forall bc,  Pi (Cbcmd bc).
  Proof.
    move=> i s s' m H Hm;inversion H;clear H;subst=> /=.
    have []:= const_prop_bcmdP Hm H2.
    case: const_prop_bcmd=> m' c' /= ??;split=> //.
    by apply sem_seq1;constructor.
  Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 s s' m H Hm;inversion H;clear H;subst=> /=.
    have := @const_prop_eP _ e _ _ Hm _ H5.
    have Hrec : Pc (if cond then c1 else c2).
    + case: (cond);[apply Hc1 | apply Hc2].
    case Heq: is_bool. 
    + by have -> /= := is_boolP Heq;move=> [] ->;apply Hrec.
    case Heq1 : (const_prop const_prop_i m c1) => [m1 c1'].
    case Heq2 : (const_prop const_prop_i m c2) => [m2 c2'] /= Hseme.
    have Hc := Hrec _ _ _ H6 Hm;split.
    + by apply merge_cpmP; case: (cond) Hc;rewrite ?Heq1 ?Heq2 => -[] //=;auto.
    by apply sem_seq1;apply (Eif Hseme);case: (cond) Hc;rewrite ?Heq1 ?Heq2 => -[] //=;auto.
  Qed.

  Let Hfor  : forall fi i rn c, Pc c -> Pi (Cfor fi i rn c).
  Proof.
    move=> fi i [[dir hi] low] c Hc s s' m H Hm /=.
    set m1 := remove_cpm m (write_i (Cfor fi i (dir, hi,low) c)).
    have Hm1 /= : valid_map (evm s) m1 by apply valid_map_rm with (evm s).
    case Heq: const_prop => [m' c'] /=;split.
    + apply valid_map_rm with (evm s)=> //; by apply write_iP.
    apply sem_seq1;inversion H;clear H;subst.  
    apply EFor with vlow vhi.
    + by apply const_prop_eP. + by apply const_prop_eP.
    clear H8 H9.
    move: Hc Heq Hm1;rewrite /m1=> {m1 Hm}.
    elim: H10=> {c s s' i}.
    + move=> s i c Hc Heq Hv;constructor.
    move=> s1 s2 s3 i w ws c Hs1 Hs2 Hrec Hc Heq Hv.
    set m1 := remove_cpm m (write_i (Cfor fi i (dir, hi,low) c)).
    have []:= Hc _ s2 m1 Hs1.
    + move=> x n Hg; have [? Hin] := get_remove_cpm Hg.
      rewrite -(@vrvP _ i w (evm s1));first apply Hv=> //. 
      by move: Hin;rewrite write_i_for;SvD.fsetdec.
    rewrite Heq /= => Hv2 Hc'.
    apply EForOne with s2 => //; apply Hrec => //.
    move=> x n Hg. have [? Hin] := get_remove_cpm Hg.
    move:Hin;rewrite write_i_for => Hin.
    rewrite -(writeP Hs1) /=;last SvD.fsetdec.
    rewrite -(@vrvP _ i w (evm s1));first apply Hv=> //. 
    by SvD.fsetdec.
  Qed.

  Let Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Proof.
    move=> ta tr x fd a Hf s s' m H;inversion H;clear H;subst => /=.
    unfold rarg in * => {rarg}.
    inversion H4;clear H4;subst;inversion H5;clear H5.
    inversion H6;clear H6;subst;inversion H0;clear H0;subst.
    move=> Hm;split;first by rewrite write_i_call;apply remove_cpmP.
    case Heq: (sem_pexpr vm1 a) H7 H8 => [va /=|//] _ /Hf Hs.
    have Ha:= @const_prop_eP _ a _ _ Hm _ Heq.
    by apply sem_seq1;constructor; rewrite Ha.
  Qed.

  Let Hfunc : forall ta tr (x:rval ta) c (re:rval tr), Pc c -> Pf (FunDef x c re).
  Proof.
    move=> ta tr x c re Hc mem mem' va vr H;inversion H;clear H;subst.
    inversion H0;clear H0;subst=> /=. 
    case Heq: const_prop => [m' c'];constructor=> vm0.
    case: (H7 vm0)=> vm2 /= [] /Hc Hr. have {Hr} []:= Hr empty_cpm.
    + by move=> z n;rewrite /empty_cpm Mvar.get0.
    by rewrite Heq /= => _ Hc' Hvr;exists vm2.
  Qed.

  Lemma const_prop_callP ta tr (f : fundef ta tr) mem mem' va vr: 
    sem_call mem f va mem' vr -> sem_call mem (const_prop_call f) va mem' vr.
  Proof.
    apply (@func_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hcall Hfunc).
  Qed.

End PROOF.

