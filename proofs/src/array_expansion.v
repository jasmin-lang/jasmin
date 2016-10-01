(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import JMeq ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import finmap strings word dmasm_utils dmasm_type dmasm_var dmasm_expr dmasm_sem.
Require Import allocation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope fun_scope.
Local Open Scope vmap.
Local Open Scope fset.
Local Open Scope seq_scope.


Lemma N_eqP : Equality.axiom N.eqb. 
Proof. by move=> p1 p2;apply:(iffP idP);rewrite -N.eqb_eq. Qed.

Definition N_eqMixin := EqMixin N_eqP.
Canonical  N_eqType  := EqType N N_eqMixin.

Instance NO : Cmp N.compare.
Proof.
  constructor.
  + by move=> ??;rewrite N.compare_antisym.
  + move=> ????;case:N.compare_spec=> [->|H1|H1];
    case:N.compare_spec=> H2 //= -[] <- //;subst;
    rewrite ?N.compare_lt_iff ?N.compare_gt_iff //.
  + by apply: N.lt_trans H1 H2. 
  by apply: N.lt_trans H2 H1.
  apply N.compare_eq.
Qed.

Module CmpIndex.

  Definition t := [eqType of (var * N)%type].

  Definition cmp : t -> t -> comparison := 
    lex CmpVar.cmp N.compare.

  Lemma cmpO : Cmp cmp.
  Proof. apply LexO;[apply CmpVar.cmpO|apply NO]. Qed.

End CmpIndex.

Local Notation index:= (var * N)%type.

Module Mi := gen_map.Mmake CmpIndex.

Module Ma := MakeMalloc Mi.

Module CBEA.

  Module M.

    Definition valid (alloc: Ma.t) (allocated:Sv.t) := 
      forall x n id, Ma.get alloc (x,n) = Some id -> Sv.mem x allocated.

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
      move=> x n id;rewrite SvP.inter_mem.
      by move=> /Ma.mergeP [] /(@Valid r1) -> /(@Valid r2).
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

    Lemma valid_set_arr x N id r:
      valid (Ma.set (alloc r) (x,N) id) (Sv.add x (allocated r)).
    Proof.
      move=> y ny idy.
      case: (x =P y) => [<-|Hne]; first by rewrite SvP.add_mem_1.
      move=> /Ma.setP_neq [];first by apply /negP=> /eqP [] ??;apply Hne.
      by move=> /Valid;rewrite SvD.F.add_neq_b.
    Qed.

    Definition set_arr x N id r := mkExpansion (initvar r) (@valid_set_arr x N id r).

    Definition set_var x r := mkExpansion (Sv.add x (initvar r)) (@Valid r).

  End M.

  Definition eq_alloc (r:M.t) (vm vm':vmap) :=
    (forall x, Sv.mem x (M.initvar r) -> vm.[x] = vm'.[x]) /\
    (forall x n id, Ma.get (M.alloc r) (x,n) = Some id ->
     match x with
     | Var (sarr s sword) id' => 
       let x := Var (sarr s sword) id' in
       let x' := Var sword id in 
       sem_pexpr vm (Papp2 (Oget s) x (Pconst n)) = ok vm'.[x']
     | _ => False
     end).
 
  Lemma eq_alloc_empty vm: eq_alloc M.empty vm vm.
  Proof.
    rewrite /M.empty /eq_alloc /=; split.
    + by move=> ?;rewrite SvP.empty_mem.
    by move=> ???;rewrite Ma.get0.
  Qed.

  Lemma eq_alloc_incl r1 r2 vm vm':
    M.incl r2 r1 -> 
    eq_alloc r1 vm vm' -> 
    eq_alloc r2 vm vm'. 
  Proof.
    move=> /andP[] Hincl Hsub [] Hv Ha;split.
    + move=> x Hx;apply Hv; by apply: SvP.subset_mem_2 Hx.
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
      (Ma.get (M.alloc m) (x1, n2) == Some (vname x2)) &&
      match t1 with
      | sarr _ t => t == t2
      | _        => false
      end                                     
    | _, _ => false
    end.

  Fixpoint check_e t1 t2 m (e1:pexpr t1) (e2:pexpr t2) : bool := 
    match e1, e2 with
    | Pvar x1  , Pvar x2    => (x1 == x2) && ~~Sv.mem x1 (M.allocated m)
    | Pconst n1, Pconst n2  => (n1 =? n2)%num
    | Pbool b1 , Pbool b2   => b1 == b2
    | Papp1 _ _ o1 e1, Papp1 _ _ o2 e2 => 
      eqb_sop1 o1 o2 && check_e m e1 e2
    | Papp2 _ _ _ o1 e11 e12   , Papp2 _ _ _ o2 e21 e22     =>  
      eqb_sop2 o1 o2 && check_e m e11 e21 && check_e m e12 e22
    | Papp3 _ _ _ _ o1 e11 e12 e13, Papp3 _ _ _ _ o2 e21 e22 e23 => 
      eqb_sop3 o1 o2 && check_e m e11 e21 &&
      check_e m e12 e22 && check_e m e13 e23
    | Papp2 _ _ _ o1 e11 e12, Pvar x2 => 
      is_oget o1 && check_var m e1 e2 x2
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
      match e1 with
      | Papp3 _ _ _ _ (Oset _) xe1 (Pconst n1) e2' =>
        if eqb_pexpr xe1 (Pvar x1) && check_e m e2' e2 then 
          Ok unit (M.set_arr x1 n1 (vname x2) m)
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

    
  Parameter check_rval_eqt : forall t1 t2 (r1 r2:M.t) (rv1:rval t1) (rv2:rval t2),
    check_rval rv1 rv2 r1 = Ok unit r2 ->
    t1 = t2.
    
  Parameter check_e_eqt : forall r t1 (e1:pexpr t1) t2 (e2:pexpr t2),
    check_e r e1 e2 -> t1 = t2.
    
  Parameter eq_write_aux : forall t1 (rv1:rval t1) t2 (rv2:rval t2) v1 v2 r1 r2 vm vm',
     check_rval rv1 rv2 r1 = Ok unit r2 ->
     eq_alloc r1 vm vm' ->
     JMeq v1 v2 ->
     eq_alloc r2 (write_rval vm rv1 v1) (write_rval vm' rv2 v2).

  Parameter eq_sem_aux : forall r vm1 vm1' t1 (e1:pexpr t1) t2 (e2:pexpr t2),
    eq_alloc r vm1 vm1' ->
    check_e r e1 e2 ->
    JMeq (sem_pexpr vm1 e1) (sem_pexpr vm1' e2).

  Parameter check_bcmdP : forall i1, 
    forall r1 i2 r2, check_bcmd i1 i2 r1 = Ok unit r2 ->
    forall m1 m2 vm1 vm2, sem_i (Estate m1 vm1) (Cbcmd i1) (Estate m2 vm2) ->
    forall vm1', eq_alloc r1 vm1 vm1' ->
    exists vm2', eq_alloc r2 vm2 vm2' /\ sem_i (Estate m1 vm1') (Cbcmd i2) (Estate m2 vm2').

End CBEA.

Module CheckExpansion :=  MakeCheckAlloc CBEA.
