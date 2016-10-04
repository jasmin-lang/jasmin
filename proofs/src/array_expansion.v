(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import JMeq ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr dmasm_sem.
Require Import allocation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Open Scope vmap.

Local Open Scope seq_scope.

Module CmpIndex.

  Definition t := [eqType of (var * Z)%type].

  Definition cmp : t -> t -> comparison := 
    lex CmpVar.cmp Z.compare.

  Lemma cmpO : Cmp cmp.
  Proof. apply LexO;[apply CmpVar.cmpO|apply ZO]. Qed.

End CmpIndex.

Local Notation index:= (var * Z)%type.

Module Mi := gen_map.Mmake CmpIndex.

Module Ma := MakeMalloc Mi.

Module CBEA.

  Module M.

    Definition valid (alloc: Ma.t) (allocated:Sv.t) := 
      forall x n id, Ma.get alloc (x,n) = Some id -> 
        Sv.In x allocated /\ Sv.In ({|vtype := sword; vname := id |}) allocated. 

    Record expansion := mkExpansion {
      initvar   : Sv.t;  
      alloc     : Ma.t;
      allocated : Sv.t;
      Valid     : valid alloc allocated
    }.

    Definition t := expansion.

    Lemma valid_empty : valid Ma.empty Sv.empty.
    Proof. by move=> x n id;rewrite Ma.get0. Qed.

    Definition empty := mkExpansion Sv.empty valid_empty.

    Lemma valid_merge r1 r2 : 
       valid (Ma.merge (alloc r1) (alloc r2)) 
             (Sv.inter (allocated r1) (allocated r2)).
    Proof.
      by move=> x n id => /Ma.mergeP [] /(@Valid r1)[??]/(@Valid r2)[??];SvD.fsetdec.
    Qed.

    Definition merge r1 r2 := 
       mkExpansion (Sv.inter (initvar r1) (initvar r2))
                   (@valid_merge r1 r2).

    Definition incl r1 r2 :=
      Ma.incl (alloc r1) (alloc r2) && Sv.subset (initvar r1) (initvar r2).              

    Lemma incl_refl r: incl r r.
    Proof. rewrite /incl Ma.incl_refl /=;apply SvP.subset_refl. Qed.

    Lemma incl_trans r2 r1 r3: incl r1 r2 -> incl r2 r3 -> incl r1 r3.
    Proof. 
      rewrite /incl=> /andP[]Hi1 Hs1 /andP[] Hi2 Hs2.
      rewrite (Ma.incl_trans Hi1 Hi2) /=.
      apply: SvP.subset_trans Hs1 Hs2.
    Qed.

    Lemma merge_incl_l r1 r2: incl (merge r1 r2) r1.
    Proof. by rewrite /incl /merge /= Ma.merge_incl_l SvP.inter_subset_1. Qed.

    Lemma merge_incl_r r1 r2: incl (merge r1 r2) r2.
    Proof. by rewrite /incl /merge /= Ma.merge_incl_r SvP.inter_subset_2. Qed.

    Lemma valid_set_arr x nx id r:
      valid (Ma.set (alloc r) (x,nx) id) 
         (Sv.add {|vtype := sword; vname := id|} (Sv.add x (allocated r))).
    Proof.
      move=> y ny idy.
      case: ((x,nx) =P (y,ny)) => [[]<- <-|Hne]. 
      + by rewrite Ma.setP_eq=> -[] <-;SvD.fsetdec.
      move=> /Ma.setP_neq [];first by apply /eqP.
      by move=> /Valid []??;SvD.fsetdec.
    Qed.

    Definition set_arr x N id r := mkExpansion (initvar r) (@valid_set_arr x N id r).

    Definition set_var x r := mkExpansion (Sv.add x (initvar r)) (@Valid r).

  End M.

  Definition eq_alloc (r:M.t) (vm vm':vmap) :=
    (forall x, Sv.In x (M.initvar r) -> vm.[x] = vm'.[x]) /\
    (forall x n id, Ma.get (M.alloc r) (x,tobase n) = Some id ->
     match x with
     | Var (sarr s sword) id' => 
       let x := Var (sarr s sword) id' in
       let x' := Var sword id in 
       sem_pexpr vm (Papp2 (Oget s) x (Pconst n)) = ok vm'.[x']
     | _ => False
     end).
 
  Lemma eq_alloc_empty vm: eq_alloc M.empty vm vm.
  Proof. by rewrite /M.empty /eq_alloc. Qed.

  Lemma eq_alloc_incl r1 r2 vm vm':
    M.incl r2 r1 -> 
    eq_alloc r1 vm vm' -> 
    eq_alloc r2 vm vm'. 
  Proof.
    move=> /andP[] Hincl /Sv.subset_spec Hsub [] Hv Ha;split.
    + move=> x Hx;apply Hv;SvD.fsetdec.
    by move=> x n id /(Ma.inclP _ _ Hincl) /Ha.
  Qed.

  Definition is_oget t1 t2 tr (o:sop2 t1 t2 tr) := 
    match o with
    | Oget _ => true
    | _      => false
    end.

  Definition check_var m t1 (e1:pexpr t1) t2 (e2:pexpr t2) x2 := 
    match e1, e2 with
    | Pvar x1, Pconst n2 => 
      (Ma.get (M.alloc m) (x1, tobase n2) == Some (vname x2)) && 
      (vtype x2 == sword)
    | _, _ => false
    end.

  Fixpoint check_e t1 t2 m (e1:pexpr t1) (e2:pexpr t2) : bool := 
    match e1, e2 with
    | Pvar x1  , Pvar x2    => (x1 == x2) && Sv.mem x1 (M.initvar m)
    | Pconst n1, Pconst n2  => n1 == n2
    | Pbool b1 , Pbool b2   => b1 == b2
    | Papp1 _ _ o1 e1, Papp1 _ _ o2 e2 => 
      eqb_sop1 o1 o2 && check_e m e1 e2
    | Papp2 _ _ _ o1 e11 e12   , Papp2 _ _ _ o2 e21 e22     =>  
      eqb_sop2 o1 o2 && check_e m e11 e21 && check_e m e12 e22
    | Papp3 _ _ _ _ o1 e11 e12 e13, Papp3 _ _ _ _ o2 e21 e22 e23 => 
      eqb_sop3 o1 o2 && check_e m e11 e21 &&
      check_e m e12 e22 && check_e m e13 e23
    | Papp2 _ _ _ o1 e11 e12, Pvar x2 => 
      is_oget o1 && check_var m e11 e12 x2
    | _, _ => false
    end.

  Fixpoint check_rval t1 t2 (x1:rval t1) (x2:rval t2) m :=
    match x1, x2 with
    | Rvar x1, Rvar x2 => 
      if (x1 == x2) && ~~Sv.mem x1 (M.allocated m) then Ok unit (M.set_var x1 m) 
      else Error tt
    | Rpair _ _ x11 x12, Rpair _ _ x21 x22 => 
      check_rval x12 x22 m >>= check_rval x11 x21
    | _, _ => Error tt
    end.

  Definition check_imm_set t1 t2 (x1:rval t1) (e1:pexpr t1) (x2:rval t2) (e2:pexpr t2) m :=
    match x1, x2 with
    | Rvar x1, Rvar x2 => 
      if Sv.mem x1 (M.initvar m) || Sv.mem x2 (M.initvar m) then Error tt
      else match e1 with
      | Papp3 _ _ _ _ (Oset _) xe1 en1 e2' =>
        if eqb_pexpr xe1 (Pvar x1) && check_e m e2' e2 then 
          match is_const en1 with 
          | Some n1 => Ok unit (M.set_arr x1 (tobase n1) (vname x2) m)
          | None    => Error tt
          end
        else Error tt
      | _ => Error tt
      end
    | _, _ => Error tt
    end.
 
  Definition check_bcmd i1 i2 m := 
    match i1, i2 with
    | Assgn _ x1 e1, Assgn _ x2 e2 =>
      match check_imm_set x1 e1 x2 e2 m with 
      | Error _ => 
        if check_e m e1 e2 then check_rval x1 x2 m
        else Error tt
      | res => res
      end
    | Load x1 e1   , Load x2 e2    => 
      if check_e m e1 e2 then check_rval x1 x2 m
      else Error tt
    | Store e11 e12, Store e21 e22 =>
      if check_e m e11 e21 && check_e m e12 e22 then Ok unit m
      else Error tt
    | _            , _             => 
      Error tt
    end.
    
  Lemma check_rval_eqt t1 t2 r1 r2 (rv1:rval t1) (rv2:rval t2):
    check_rval rv1 rv2 r1 = Ok unit r2 ->
    t1 = t2.
  Proof.
    elim: rv1 t2 rv2 r1 r2 => [x1 | ?? x11 Hx1 x12 Hx2] t2 [x2 | ?? x21 x22] //= r1 r2.
    + by case:andP => [[]/eqP->|].
    case Heq: check_rval => [r' /=|//] /Hx1 ->.
    by rewrite (Hx2 _ _ _ _ Heq).
  Qed.    

  Lemma is_ogetP t1 t2 tr (o:sop2 t1 t2 tr): 
    is_oget o -> 
    exists n, [/\ t1 = (sarr n sword), t2=sword, tr=sword &
                  JMeq o (Oget n)].
  Proof. by case:o => //= n;exists n;split. Qed.

  Lemma check_varP r t1 (e1:pexpr t1) t2 (e2:pexpr t2) x2:
    check_var r e1 e2 x2 ->
    exists x1 n2, [/\ t1 = vtype x1, t2 = sword, 
                   JMeq e1 (Pvar x1) , JMeq e2 (Pconst n2) & (vtype x2 = sword) /\
                   (Ma.get (M.alloc r) (x1, tobase n2) = Some (vname x2))].
  Proof. 
    by case: e1 e2 => // x1 [] //= n2 /andP[]/eqP ? /eqP ?;exists x1, n2;split. 
  Qed.

  Lemma check_e_eqt r t1 (e1:pexpr t1) t2 (e2:pexpr t2):
    check_e r e1 e2 -> t1 = t2.
  Proof.
   elim: e1 t2 e2 =>
      [ x1 | n1 | b1 | ?? o1 e1 He1
      | ??? o1 e11 He1 e12 He2 | ???? o1 e11 He1 e12 He2 e13 He3] t2
      [ x2 | n2 | b2 | ?? o2 e2
      | ??? o2 e21  e22 | ???? o2 e21 e22 e23] //=.
    + by move=> /andP []/eqP->.
    + by move=> /andP[] Ho /He1 Heqt;case:(eqb_sop1P Heqt Ho).
    + move=> /andP[] /is_ogetP [n [??? Hjm]];subst.
      by move=> /check_varP [x1 [n2 ]] [] ???? [] ->.
    + by move=> /andP[]/andP[] Ho /He1 H1 /He2 H2;case:(eqb_sop2P H1 H2 Ho).
    by move=> /andP[]/andP[]/andP[] Ho /He1 H1 /He2 H2 /He3 H3;case:(eqb_sop3P H1 H2 H3 Ho).
  Qed.    

  Lemma eq_write_aux t1 (rv1:rval t1) t2 (rv2:rval t2) v1 v2 r1 r2 vm vm':
     check_rval rv1 rv2 r1 = Ok unit r2 ->
     eq_alloc r1 vm vm' ->
     JMeq v1 v2 ->
     eq_alloc r2 (write_rval vm rv1 v1) (write_rval vm' rv2 v2).
  Proof.
    elim: rv1 t2 rv2 v1 v2 r1 r2 vm vm' =>[[t1' x1] | ?? x11 Hx1 x12 Hx2] ?
      [[ t2' x2] | ?? x21 x22] //= v1 v2 r1 r2 vm vm'.
    + case:ifP=>//= /andP [] /eqP [] ??;subst.
      move=> /negP;rewrite /is_true -SvD.F.mem_iff=> Hnin [] <- Hvm <-;split.
      + move=> x /=;case:({| vtype := t2'; vname := x2 |} =P x) => [<-| Heq].
        + by rewrite !Fv.setP_eq.
        move: (Heq)=> /eqP Hne Hin;rewrite !Fv.setP_neq //.
        by apply Hvm; SvD.fsetdec.
      case:Hvm=> ? H [tx x] n id /= H1. 
      have {H} := H _ _ _ H1; case:tx H1 => //= n1 [] //=.
      by move=> /M.Valid [Hxin Hidin]; rewrite !Fv.setP_neq //;
        apply /eqP=> Heq;apply Hnin;rewrite Heq.
    case Heq2: check_rval => [r1' |] //= Heq1 Hvm Hjm.
    have ?:= check_rval_eqt Heq1;subst.
    have ?:= check_rval_eqt Heq2;subst.
    have H:= JMeq_eq Hjm;subst v2 => {H}.
    apply (Hx1 _ _ _ _ _ _ _ _ Heq1)=> //.
    by apply (Hx2 _ _ _ _ _ _ _ _ Heq2).
  Qed.

  Lemma eq_write t (rv1 rv2:rval t) v r1 r2 vm vm' : 
     check_rval rv1 rv2 r1 = Ok unit r2 ->
     eq_alloc r1 vm vm' ->
     eq_alloc r2 (write_rval vm rv1 v) (write_rval vm' rv2 v).
  Proof. by move=> Hc Hrn; apply (eq_write_aux Hc Hrn);apply JMeq_refl. Qed.

  Lemma eq_sem_aux r vm1 vm1' t1 (e1:pexpr t1) t2 (e2:pexpr t2):
    eq_alloc r vm1 vm1' ->
    check_e r e1 e2 ->
    JMeq (sem_pexpr vm1 e1) (sem_pexpr vm1' e2).
  Proof.
    move=> Hrn; elim: e1 t2 e2 =>
      [ [tx1 x1] | n1 | b1 | ?? o1 e1 He1
      | ??? o1 e11 He1 e12 He2 | ???? o1 e11 He1 e12 He2 e13 He3] t2
      [ [tx2 x2] | n2 | b2 | ?? o2 e2
      | ??? o2 e21  e22 | ???? o2 e21 e22 e23] //=.
    + move=> /andP[]/eqP[]<- <-;rewrite /is_true -SvD.F.mem_iff.
      by case : Hrn=> H _ /H ->.
    + by move=> /eqP ->.
    + by move=> /eqP ->.
    + move=> /andP[] Ho H1.  
      have ? := check_e_eqt H1;subst;rewrite (He1 _ _ H1).
      by case:(eqb_sop1P _ Ho) => // ?;subst=> ->.
    + move=> /andP[] /is_ogetP [n [??? Hjm]];subst.
      move=> /check_varP [[tx1 x1] [n2 ]] [] /= ??;subst=> H1 H2.
      have {H1}H1:= JMeq_eq H1;have {H2}H2:= JMeq_eq H2 => -[] ?;subst=> /=.
      by case Hrn=> _ H /H /= ->.
    + move=> /andP[]/andP[] Ho H1 H2.
      have ? := check_e_eqt H1;subst;rewrite (He1 _ _ H1).
      have ? := check_e_eqt H2;subst;rewrite (He2 _ _ H2).
      by case:(eqb_sop2P _ _ Ho) => // ?;subst=> ->.
    move=> /andP[]/andP[]/andP[] Ho H1 H2 H3.
    have ? := check_e_eqt H1;subst;rewrite (He1 _ _ H1).
    have ? := check_e_eqt H2;subst;rewrite (He2 _ _ H2).
    have ? := check_e_eqt H3;subst;rewrite (He3 _ _ H3).
    by case:(eqb_sop3P _ _ _ Ho) => // ?;subst=> ->.
  Qed.

  Lemma eq_sem r vm1 vm1' t (e1 e2:pexpr t): 
    eq_alloc r vm1 vm1' ->
    check_e r e1 e2->
    sem_pexpr vm1 e1 = sem_pexpr vm1' e2.
  Proof. by move=> Hrn Hc;rewrite (eq_sem_aux Hrn Hc). Qed.

  Lemma check_imm_setP  t1 (rv1:rval t1) e1 t2 (rv2:rval t2) e2 r1 r2 :
    check_imm_set rv1 e1 rv2 e2 r1 = Ok unit r2 ->
    exists nx1 nx2 n n1 e2',
     let x1 := {| vtype := (sarr n sword); vname := nx1 |} in
     let x2 := {| vtype := sword; vname := nx2 |} in
     [/\ [/\ t1 = (sarr n sword), t2 = sword, 
             JMeq rv1 (Rvar x1),
             JMeq rv2 (Rvar x2) &
             JMeq e1 (Papp3 (Oset n) (Pvar x1) (Pconst n1) e2')], 
          check_e r1 e2' e2, 
          r2 = M.set_arr x1 (tobase n1) (vname x2) r1,
          ~Sv.In x1 (M.initvar r1) &
          ~Sv.In x2 (M.initvar r1)
         ].
  Proof.
    case: rv1 rv2 e1 e2 => //= -[xt1 nx1] [] //= -[xt2 nx2].
    move=> e1 e2;case:ifPn => //=;rewrite negb_or=> /andP[]/negP Hin1 /negP Hin2.
    move: Hin1 Hin2;rewrite /is_true -!SvD.F.mem_iff.
    case: e1 e2 => //= ???? [] //= n p p0 p1 e2.
    case:ifP=> //= /andP[H1 H2].
    case Heq: is_const => [n1|]//= Hin1 Hin2 [] <-.
    rewrite (is_constP Heq);exists nx1, nx2, n, n1, p1.
    have ? := check_e_eqt H2;subst;split=> //;split=>//.
    have -> //: JMeq p (Pvar {| vtype := sarr n sword; vname := nx1 |}).
    by move: H1;case: p=> //= x /eqP ->.
  Qed.

  Lemma check_bcmdP i1 r1 i2 r2:
    check_bcmd i1 i2 r1 = Ok unit r2 ->
    forall m1 m2 vm1 vm2, sem_i (Estate m1 vm1) (Cbcmd i1) (Estate m2 vm2) ->
    forall vm1', eq_alloc r1 vm1 vm1' ->
    exists vm2', eq_alloc r2 vm2 vm2' /\ 
    sem_i (Estate m1 vm1') (Cbcmd i2) (Estate m2 vm2').
  Proof.
    case: i1 i2 =>
      [t1 rv1 e1 | rv1 e1 | e11 e12] [t2 rv2 e2 | rv2 e2 | e21 e22] //=.
    + case Himm: check_imm_set => [r1'|] /=. 

      + move=> [] ? m1 m2 vm1 vm2 H vm1' Hvm1;subst r1'.
        inversion H;clear H;subst. 
        move:Himm H2=> /= /check_imm_setP [nx1 [nx2 [n [n1 [e2']]]]] /= [] [].
        move=> ??;subst => -> -> -> Hce -> /= Hnin1 Hnin2.
        case He2' : sem_pexpr => [v2'|] //=.
        rewrite /Array.set; case: ifP => [Hbound|] //= [] <- <-.
        exists (vm1'.[{| vtype := sword; vname := nx2 |} <- v2']);split;last first.
        + by constructor => /=;rewrite -(eq_sem Hvm1 Hce) He2'.
        case Hvm1=>Hvm_1 Hvm_2; split=> /=.
        + move=> x Hin;rewrite !Fv.setP_neq;first by apply Hvm_1.
          + by apply /eqP=> Hx;subst;SvD.fsetdec.
          by apply /eqP=> Hx;subst;SvD.fsetdec.
        move=> x n0 id; set x1 := {| vtype := sarr n sword; vname := nx1 |}.
        case: ((x1,tobase n1) =P (x,tobase n0)) => [[] Hx Hn|/eqP Hneq].
        + subst x;rewrite Hn Ma.setP_eq=> -[] ?;subst=> /=.
          rewrite !Fv.setP_eq; move: Hn Hbound=> /eqP /reqP -> Hbound.
          by rewrite /Array.get Hbound FArray.setP_eq.
        move=> /Ma.setP_neq [] // /Hvm_2.         
        case: x Hneq => -[] //= n2 [] //= xn Hneq.
        case: (x1 =P {| vtype := sarr n2 sword; vname := xn |}).
        + move=> [] ??;subst;rewrite /x1 Fv.setP_eq => H1 Hne.
          rewrite /Array.get Fv.setP_neq;last by apply /eqP=> -[].
          rewrite FArray.setP_neq //. 
          by apply: contra Hneq => /eqP /reqP /eqP ->.
        move=> /eqP Hne H1 H2; rewrite !Fv.setP_neq //. 
        by apply /eqP=> -[].
      case: ifP => //= Hce Hcr.
      have ? := check_e_eqt Hce;subst.
      move=> m1 m2 vm1 vm2 H;inversion H;clear H;subst=> vm1' Hvm1.
      move:H2=> /=;rewrite (eq_sem Hvm1 Hce).
      case Heq : sem_pexpr => [v|]//= [] <- <-.
      exists (write_rval vm1' rv2 v);split.
      + by apply (eq_write _ Hcr)=> //.
      by constructor=> /=;rewrite Heq.
    + case Hce: check_e => //= Hcr.
      have ? := check_e_eqt Hce;subst.
      move=> m1 m2 vm1 vm2 H;inversion H;clear H;subst=> vm1' Hvm1.
      move:H2=> /=;rewrite (eq_sem Hvm1 Hce).
      case Heq : sem_pexpr => [v|]//=.
      case Heqr: read_mem=> [w|]//= []<- <-.
      exists (write_rval vm1' rv2 w);split.
      + by apply (eq_write _ Hcr)=> //.
      by constructor=> /=;rewrite Heq /= Heqr.
    case:ifP => //= /andP[Hce1 Hce2] [] <- m1 m2 vm1 vm2 H;inversion H;clear H;subst.
    move=> vm1' Hvm1;move:H2=> /=. 
    rewrite (eq_sem Hvm1 Hce1) (eq_sem Hvm1 Hce2).
    case Heq1: (sem_pexpr vm1' e21) => [v1|]//=.
    case Heq2: sem_pexpr=> [v2|]//=.
    case Heqw: write_mem=> [m2'|]//= []<- <-.
    exists vm1';split=> //.
    by constructor=> /=;rewrite Heq1 Heq2 /= Heqw.
  Qed.

End CBEA.

Module CheckExpansion :=  MakeCheckAlloc CBEA.

