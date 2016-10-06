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
Local Open Scope fset.
Local Open Scope seq_scope.

Module MakeMalloc(M:gen_map.MAP).

  Definition valid (mvar: M.t Ident.ident) (mid: Ms.t M.K.t) :=
    forall x id, M.get mvar x = Some id <-> Ms.get mid id = Some x.
 
  Lemma valid_uniqx mvar mid : valid mvar mid ->
     forall x x' id , M.get mvar x = Some id -> M.get mvar x' = Some id ->
                      x = x'.
  Proof. by move=> H x x' id /H Hx /H;rewrite Hx=> -[]. Qed.

  Lemma valid_uniqid mvar mid : valid mvar mid ->
     forall id id' x, Ms.get mid id = Some x -> Ms.get mid id' = Some x ->
                      id = id'.
  Proof. by move=> H id id' x /H Hx /H;rewrite Hx=> -[]. Qed.

  Record t_ := mkT { mvar : M.t Ident.ident; mid : Ms.t M.K.t; mvalid: valid mvar mid }.
  Definition t := t_.

  Definition get (m:t) (x:M.K.t) := M.get (mvar m) x.

  Lemma mvalid_uniqx m x x' id: get m x = Some id -> get m x' = Some id -> x = x'.
  Proof. rewrite /get;apply valid_uniqx with (mid m);apply mvalid. Qed.

  Definition rm_id (m:t) id := 
    match Ms.get (mid m) id with
    | Some x => M.remove (mvar m) x
    | None   => mvar m
    end.

  Definition rm_x (m:t) x := 
    match M.get (mvar m) x with
    | Some id => Ms.remove (mid m) id
    | None    => mid m
    end.

  Lemma rm_idP m id x : M.get (rm_id m id) x <> Some id.
  Proof.
    rewrite /rm_id. case Heq: ((mid m).[id])%ms => [x'|];last first.
    + by move=> /mvalid;rewrite Heq.   
    by rewrite M.removeP; case: (x' =P x) => // Hne /mvalid;rewrite Heq=> -[] ?;elim Hne.
  Qed. 

  Lemma rm_xP m x id : Ms.get (rm_x m x) id <> Some x.
  Proof.
    rewrite /rm_x. case Heq: (M.get (mvar m) x) => [id'|];last first.
    + by move=> /mvalid;rewrite Heq.   
    by rewrite Ms.removeP; case: (id'=Pid) => // Hne /mvalid;rewrite Heq=> -[] ?;elim Hne.
  Qed. 

  Lemma valid_set m x id : valid (M.set (rm_id m id) x id) (Ms.set (rm_x m x) id x).
  Proof.
    move=> y idy; case (x =P y) => [->|/eqP Hne]. 
    + rewrite M.setP_eq.
      case (id =P idy) => [<-| Hnei];first by rewrite Ms.setP_eq.
      split => [[]/Hnei | ] //. 
      by rewrite Ms.setP_neq => [/rm_xP//| ]; apply /eqP.
    rewrite M.setP_neq //.
    case (id =P idy) => [<-| /eqP Hnei].
    + by rewrite Ms.setP_eq;split=> [/rm_idP//|[] H];move: Hne;rewrite H eq_refl.
    rewrite Ms.setP_neq // /rm_id /rm_x.
    case Heq: ((mid m).[id])%ms => [z|];case Heq':(M.get (mvar m) x) => [i|];
    rewrite ?M.removeP ?Ms.removeP;last by apply mvalid.
    + case:(_ =P _) => H;case:(_ =P _)=> H'; subst => //;last by apply mvalid.
      + split=>// /(valid_uniqid (mvalid m) Heq) H. 
        by move: Hnei;rewrite H eq_refl.
      split=> // /(valid_uniqx (mvalid m) Heq') H'. 
      by move: Hne;rewrite H' eq_refl.
    + case:(_ =P _) => H;last by apply mvalid.
      subst;split=> // /(valid_uniqid (mvalid m) Heq) H. 
      by move: Hnei;rewrite H eq_refl.
    case:(_ =P _) => H;last by apply mvalid.
    subst;split=> // /(valid_uniqx (mvalid m) Heq') H. 
    by move: Hne;rewrite H eq_refl.
  Qed.

  Definition set m x id := mkT (valid_set m x id).

  Lemma valid_empty : valid (@M.empty _) (@Ms.empty _).
  Proof. by move=> x id;rewrite M.get0 Ms.get0. Qed.

  Definition empty := mkT valid_empty.

  Definition merge m1 m2 := 
    M.fold 
     (fun x idx m => 
        match get m2 x with    
        | Some idx' => if idx == idx' then set m x idx else m
        | None      => m
        end) (mvar m1) empty.

  Lemma get0 x : get empty x = None.
  Proof. by rewrite /get M.get0. Qed.

  Lemma setP_eq m x id: get (set m x id) x = Some id.
  Proof. by rewrite /get /set /=;rewrite M.setP_eq. Qed.

  Lemma setP_neq m x y id id': 
    x != y -> get (set m x id) y = Some id' ->
    get m y = Some id' /\ id <> id'.
  Proof.
    move=> Hne;rewrite /get /set /= M.setP_neq // /rm_id.
    case Heq: ((mid m).[id])%ms => [x'|] //=. 
    + rewrite M.removeP;case:ifP => // /eqP Hne' H;split=>// ?;subst.
      by move/mvalid :H;rewrite Heq => -[].
    move=> H;split=>// ?;subst.
    by move/mvalid:H;rewrite Heq.
  Qed.

  Lemma mergeP m1 m2 x id: 
    get (merge m1 m2) x = Some id -> get m1 x = Some id /\ get m2 x = Some id.
  Proof.
    rewrite /merge M.foldP;set f := (f in foldl f).
    pose P := fun m => 
      get m x = Some id -> get m1 x = Some id /\ get m2 x = Some id.
    have H : forall (l:list (M.K.t * Ident.ident)) m, 
      (forall p, p \in l -> get m1 p.1 = Some p.2) ->
      P m -> P (foldl f m l).
    + elim=> [|p l Hrec] //= m Hl Hm;apply Hrec.
      + by move=> ? H;apply Hl;rewrite in_cons H orbC.
      rewrite /f /P;case Heq2: (get m2 p.1) => [id'|];last by apply Hm.
      case: (_=P_) => Heq;last by apply Hm.
      subst;case: (p.1 =P x) => [| /eqP] Heq.
      + by subst;rewrite setP_eq=> [] <-;split=>//;apply /Hl /mem_head.
      by move=> /setP_neq [] // ??;apply Hm.
    apply H;first by move=> p /M.elementsP.
    by rewrite /P get0. 
  Qed.

  Definition incl m1 m2 :=
    M.fold (fun x id b => b && (get m2 x == Some id))
              (mvar m1) true.
  
  Lemma inclP m1 m2 : 
    reflect (forall x id, get m1 x = Some id -> get m2 x = Some id) (incl m1 m2).
  Proof.
    rewrite /incl M.foldP;set f := (f in foldl f).
    set l := (M.elements _); set b := true.
    have : forall p, p \in l -> get m1 p.1 = Some p.2.
    + by move=> p /M.elementsP.
    have : uniq [seq x.1 | x <- l]. apply M.elementsU.
    have : 
      reflect (forall x id, (x,id) \notin l -> get m1 x = Some id -> get m2 x = Some id) b.
    + by constructor=> x id /M.elementsP. 
    elim:l b=> /= [|p ps Hrec] b Hb => [Hu | /andP[Hnin Hu]] Hin.
    + by apply (equivP Hb);split=> H ?? => [|_];apply H.
    apply Hrec=> //;first last.
    + by move=> ? Hp0;apply Hin;rewrite in_cons Hp0 orbC.
    rewrite /f;case: Hb=> {Hrec} /= Hb.
    + case: (_ =P _) => Heq;constructor.
      + move=> x id Hnx;case : ((x,id) =P p)=> [|/eqP/negbTE]Hp;first by subst.
        by apply Hb;rewrite in_cons Hp.
      move=> H;apply/Heq/H;last by apply/Hin/mem_head.
      by move: Hnin;apply: contra;apply: map_f.
    constructor=> H;apply Hb=> x id.
    rewrite in_cons negb_or=> /andP [] _;apply H.     
  Qed.    

  Lemma incl_refl r : incl r r.
  Proof. by apply/inclP. Qed.

  Lemma incl_trans r2 r1 r3  : incl r1 r2 -> incl r2 r3 -> incl r1 r3.
  Proof. by move=> /inclP H1 /inclP H2;apply/inclP=> x id /H1 /H2. Qed.

  Lemma merge_incl_l r1 r2 : incl (merge r1 r2) r1.
  Proof. by apply/inclP=> x id /mergeP []. Qed.

  Lemma merge_incl_r r1 r2 : incl (merge r1 r2) r2.
  Proof. by apply/inclP=> x id /mergeP []. Qed.

End MakeMalloc.

Module Type CheckB.

  Module M.
    Parameter t : Type.
    Parameter empty : t.
    Parameter merge : t -> t -> t.
    Parameter incl  : t -> t -> bool.

    Parameter incl_refl : forall r, incl r r.
    Parameter incl_trans: forall r2 r1 r3, incl r1 r2 -> incl r2 r3 -> incl r1 r3.

    Parameter merge_incl_l: forall r1 r2, incl (merge r1 r2) r1.
    Parameter merge_incl_r: forall r1 r2, incl (merge r1 r2) r2.

  End M.

  Parameter check_e : forall t1 t2, M.t -> pexpr t1 -> pexpr t2 -> bool.
  Parameter check_rval : forall t1 t2, rval t1 -> rval t2 -> M.t -> result unit M.t.
  Parameter check_bcmd : bcmd -> bcmd -> M.t -> result unit M.t.

  Parameter eq_alloc : M.t -> vmap -> vmap -> Prop.

  Parameter eq_alloc_empty: forall vm, eq_alloc M.empty vm vm.

  Parameter eq_alloc_incl: forall r1 r2 vm vm',
    M.incl r2 r1 -> 
    eq_alloc r1 vm vm' -> 
    eq_alloc r2 vm vm'.
    
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

  Parameter check_bcmdP : forall valid_addr i1, 
    forall r1 i2 r2, check_bcmd i1 i2 r1 = Ok unit r2 ->
    forall m1 m2 vm1 vm2, sem_i valid_addr (Estate m1 vm1) (Cbcmd i1) (Estate m2 vm2) ->
    forall vm1', eq_alloc r1 vm1 vm1' ->
    exists vm2',   
      eq_alloc r2 vm2 vm2' /\ 
      sem_i valid_addr (Estate m1 vm1') (Cbcmd i2) (Estate m2 vm2').

End CheckB.

Module MakeCheckAlloc (C:CheckB).

Import C.

Section LOOP.

  Variable check_c : M.t -> result unit M.t.
 
  Fixpoint loop (n:nat) (m:M.t) := 
    match n with
    | O => Error tt
    | S n =>
      check_c m >>= (fun m' =>
       if M.incl m m' then Ok unit m else loop n (M.merge m m'))
    end.

End LOOP.

Definition nb_loop := 100%coq_nat.

Fixpoint check_i i1 i2 m := 
  match i1, i2 with
  | Cbcmd i1, Cbcmd i2 => check_bcmd i1 i2 m
  | Cif e1 c11 c12, Cif e2 c21 c22 =>
    if check_e m e1 e2 then 
      fold2 tt check_i c11 c21 m >>= (fun m1 =>
      fold2 tt check_i c12 c22 m >>= (fun m2 => Ok unit (M.merge m1 m2)))
    else Error tt
  | Cfor i1 (dir1,lo1,hi1) c1, Cfor i2 (dir2,lo2,hi2) c2 =>
    if eqb_dir dir1 dir2 && check_e m lo1 lo2 && check_e m hi1 hi2 then
      let check_c m := 
        check_rval i1 i2 m >>= fold2 tt check_i c1 c2 in
      loop check_c nb_loop m 
    else Error tt 
  | Cwhile e1 c1, Cwhile e2 c2 =>
    loop (fold2 tt check_i c1 c2) nb_loop m >>= (fun m =>
      if check_e m e1 e2 then Ok unit m
      else Error tt)
  | Ccall _ _ x1 fd1 arg1, Ccall _ _ x2 fd2 arg2 => 
    if check_fd fd1 fd2 && check_e m arg1 arg2 then 
      check_rval x1 x2 m
    else Error tt
  | _, _ => Error tt
  end

with check_fd ta1 tr1 (fd1:fundef ta1 tr1) ta2 tr2 (fd2:fundef ta2 tr2) :=
  match fd1, fd2 with
  | FunDef _ _ p1 c1 r1, FunDef _ _ p2 c2 r2 =>
    isOk (
      check_rval p1 p2 M.empty >>= (fun m =>
      fold2 tt check_i c1 c2 m >>= (fun m =>
        if check_e m (rval2pe r1) (rval2pe r2) then Ok unit tt
        else Error tt)))
  end.

Section PROOF.

  Variable valid_addr : word -> bool.

  Let Pi (i1:instr) := 
    forall r1 i2 r2, check_i i1 i2 r1 = Ok unit r2 ->
    forall m1 m2 vm1 vm2, sem_i valid_addr (Estate m1 vm1) i1 (Estate m2 vm2) ->
    forall vm1', eq_alloc r1 vm1 vm1' ->
    exists vm2', eq_alloc r2 vm2 vm2' /\ 
     sem_i valid_addr (Estate m1 vm1') i2 (Estate m2 vm2').

  Let Pc (c1:cmd) := 
    forall r1 c2 r2, fold2 tt check_i c1 c2 r1 = Ok unit r2 ->
    forall m1 m2 vm1 vm2, sem valid_addr (Estate m1 vm1) c1 (Estate m2 vm2) ->
    forall vm1', eq_alloc r1 vm1 vm1' ->
    exists vm2', eq_alloc r2 vm2 vm2' /\ 
     sem valid_addr (Estate m1 vm1') c2 (Estate m2 vm2').

  Let Pf ta tr (fd1:fundef ta tr) := 
    forall fd2, check_fd fd1 fd2 ->
    forall mem mem' va vr, 
    sem_call valid_addr mem fd1 va mem' vr ->
    sem_call valid_addr mem fd2 va mem' vr.

  Let Hskip : Pc [::].
  Proof.
    move=> r1 [] //= r2 [] <- m1 m2 vm1 vm2 H;inversion H;clear H;subst.
    move=> vm1' Hvm1;exists vm1';split=>//=;constructor.
  Qed.

  Let Hseq  : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i1 c1 Hi Hc r1 [//|i2 c2] r2 /=.
    case Hci : check_i => [ri|] //= Hcc m1 m3 vm1 vm3 H;inversion H;clear H;subst.
    move=> vm1' Hvm1;case: s2 H3 H5 => m2 vm2 H3 H5. 
    have [vm2' [Hvm2 Hi2]]:= Hi _ _ _ Hci _ _ _ _ H3 _ Hvm1.
    have [vm3' [Hvm3 Hc2]]:= Hc _ _ _ Hcc _ _ _ _ H5 _ Hvm2.
    by exists vm3';split=> //;apply (Eseq Hi2 Hc2).
  Qed.
 
  Lemma eq_write t (rv1 rv2:rval t) v r1 r2 vm vm' : 
     check_rval rv1 rv2 r1 = Ok unit r2 ->
     eq_alloc r1 vm vm' ->
     eq_alloc r2 (write_rval vm rv1 v) (write_rval vm' rv2 v).
  Proof. by move=> Hc Hrn; apply (eq_write_aux Hc Hrn);apply JMeq_refl. Qed.
 
  Lemma eq_sem r vm1 vm1' t (e1 e2:pexpr t): 
    eq_alloc r vm1 vm1' ->
    check_e r e1 e2->
    sem_pexpr vm1 e1 = sem_pexpr vm1' e2.
  Proof. by move=> Hrn Hc;rewrite (eq_sem_aux Hrn Hc). Qed.
 
  Lemma eq_alloc_merge r1 r2 vm vm': 
    eq_alloc r1 vm vm' \/ eq_alloc r2 vm vm' ->
    eq_alloc (M.merge r1 r2) vm vm'.
  Proof. 
    by move=> [];apply eq_alloc_incl;[apply M.merge_incl_l | apply M.merge_incl_r].
  Qed.

  Let Hbcmd : forall i1, Pi (Cbcmd i1).
  Proof. by move=> i1 r1 [] //;apply check_bcmdP. Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Proof.
    move=> e1 c11 c12 Hc1 Hc2 r1 []// e2 c21 c22 r2 /=.
    case:ifP => //= Heq.
    case Heq2: fold2 => [rf|]//=;case Heq1: fold2 => [rt|]//= [] <-.
    move=> m1 m2 vm1 vm2 H;inversion H;clear H;subst=> vm1' Hvm1.
    move: H5;rewrite (eq_sem Hvm1 Heq).
    case:cond H6=> H6 H5. 
    + case (Hc1 _ _ _ Heq1 _ _ _ _ H6 _ Hvm1)=> vm2' [Hvm2 Hsem].
      exists vm2';split;last by apply Eif with true.
      by apply eq_alloc_merge;auto.
    case (Hc2 _ _ _ Heq2 _ _ _ _ H6 _ Hvm1)=> vm2' [Hvm2 Hsem].
    exists vm2';split;last by apply Eif with false.
    by apply eq_alloc_merge;auto.
  Qed.

  Lemma loopP check n r1 r1': 
    loop check n r1 = Ok unit r1' ->
    exists r2, [/\ check r1' = Ok unit r2 , M.incl r1' r1 & M.incl r1' r2].
  Proof.
    elim : n r1 => //= n Hrec r1.    
    case Heq: check => [r2|]//=.
    case: ifP => Hincl.
    + move => [] ?;subst r1';exists r2;split=>//;apply M.incl_refl.
    move=> /Hrec [r3 [H1 H2 H3]];exists r3;split=>//.
    apply/(M.incl_trans H2)/M.merge_incl_l.
  Qed.

  Opaque nb_loop.
 
  Let Hfor  : forall i rn c, Pc c -> Pi (Cfor i rn c).
  Proof.
    move=> i1 [[dir1 hi1] low1] c1 Hc r1 []//= i2 [[dir2 hi2] low2] c2 r2'.
    case:ifP=> //= /andP[]/andP[] /eqb_dirP <- {dir2} Hhi Hlo.
    move=> /loopP [r1'] [].
    case Hcr : check_rval=> [ri|]//= Hcc Hincl Hincl' m1 m2 vm1 vm2 H.
    inversion H;clear H;subst.
    have Hfor: forall vm1', eq_alloc r2' vm1 vm1' ->
          exists vm2', eq_alloc r2' vm2 vm2' /\
          sem_for valid_addr i2 [seq n2w i | i <- wrange dir1 vlow vhi]
             {| emem := m1; evm := vm1' |} c2 {| emem := m2; evm := vm2' |}.
    + elim: [seq n2w i | i <- _] m1 vm1 H9 {H8 H7}=> [ | w ws Hws] m1 vm1 H10;
      inversion H10;clear H10;subst.
      + by move=> vm2' Hvm2;exists vm2';split=>//;constructor.
      move=> vm1' Hvm1;case: s2 H2 H6=> m3 vm3 /= H2 H6.
      have [] := Hc _ _ _ Hcc _ _ _ _ H2 (write_rval vm1' i2 w).
      + by apply (eq_write _ Hcr Hvm1).
      move=> vm3' [Hvm3 Hsc].
      have []:= Hws _ _ H6 vm3';first by apply: eq_alloc_incl Hvm3.
      by move=> vm2' [Hvm2 Hsf];exists vm2';split=>//; apply: EForOne Hsf.
    move=> vm1' Hvm1;have []:= Hfor vm1';first by apply: eq_alloc_incl Hvm1.
    move=> vm2' [Hvm2 Hsf];exists vm2';split=>//.
    apply: EFor Hsf;rewrite -?H7 -?H8 /=;symmetry;first by apply (eq_sem Hvm1 Hhi).
    by apply (eq_sem Hvm1 Hlo).
  Qed.

  Let Hwhile  : forall e c, Pc c -> Pi (Cwhile e c).
  Proof.
    move=> e1 c1 Hc r1 []//= e2 c2 r2.
    case Hloop: loop => [r2'|] //=.
    case: ifP => //= Hce [] ?;subst r2'.
    case/loopP: Hloop=> r2' [ Hcc Hincl Hincl'] m1 m2 vm1 vm2 H.
    inversion H;clear H;subst.
    have Hwhile: forall vm1', eq_alloc r2 vm1 vm1' ->
          exists vm2', eq_alloc r2 vm2 vm2' /\
          sem_while valid_addr {| emem := m1; evm := vm1' |} e2 c2
                    {| emem := m2; evm := vm2' |}.
    + move: H4 Hcc Hce Hc.
      set st1 := {| emem := m1; evm := vm1 |}; set st2 := {| emem := m2; evm := vm2 |}.
      rewrite (_: m1 = emem st1) // (_: m2 = emem st2) //.
      rewrite (_: vm1 = evm st1) // (_: vm2 = evm st2) //.
      move: st1 st2=> st1 st2 {m1 vm1 m2 vm2}.
      elim=> {e1 c1} [ st e1 c1 He1 | [m1 vm1] [m2 vm2] [m3 vm3] e1 c1 He1 Hc1 Hw Hrec]
         Hcc Hce Hc vm1' Hvm1.
      + exists vm1';split=>//;constructor=> /=.
        by rewrite -He1;symmetry;apply: (eq_sem Hvm1 Hce).
      case :(Hc _ _ _ Hcc _ _ _ _ Hc1 _ Hvm1) => vm2' [Hvm2 Hsc].
      have []:= Hrec Hcc Hce Hc vm2';first by apply:(eq_alloc_incl _ Hvm2).
      move=> vm3' /= [Hvm3 Hsw];exists vm3';split=>//.
      apply: EWhileOne Hsw=> //;rewrite -He1 /=;symmetry.
      by apply: (eq_sem Hvm1 Hce).
    move=> vm1' Hvm1;have []:= Hwhile vm1';first by apply: eq_alloc_incl Hvm1.
    by move=> vm2' [Hvm2 Hsw];exists vm2';split=> //;constructor.
  Qed.

  Let Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Proof.
    move=> ta tr x1 fd1 a1 Hf r1 [] //= ?? x2 fd2 a2 r2.
    case:ifP=> [/andP[Hcf Hca]|] //= Hcx m1 m2 vm1 vm2 H.
    inversion H;clear H;subst.   
    unfold rarg in * => {rarg}.
    inversion H5;clear H5;subst;inversion H6;clear H6.
    inversion H7;clear H7;subst;inversion H0;clear H0;subst.
    have ? := check_e_eqt Hca; have ?:= check_rval_eqt Hcx;subst.
    move=> vm1' Hvm1.
    exists (write_rval vm1' x2 res);split;first by apply (eq_write _ Hcx).
    have Heq := eq_sem Hvm1 Hca; constructor;rewrite -Heq //.
    by apply: Hf H10.
  Qed.

  Let Hfunc : forall ta tr (x:rval ta) c (re:rval tr), Pc c -> Pf (FunDef x c re).
  Proof.
    move=> ta tr x1 c1 re1 Hc fd2. 
    have ->/= : fd2 = FunDef (fd_arg fd2) (fd_body fd2) (fd_res fd2) by case fd2.
    case Hcx: check_rval => [r1|]//=.   
    case Hcc: fold2 => [r2|]//=.
    case:ifP => //= Hcr _ mem mem' va vr H;inversion H;clear H;subst.
    inversion H0;clear H0;subst.
    constructor=> vm0.
    case: (H7 vm0) => vm2 /= [] Hsem Hvr {H7}.
    have [] := Hc _ _ _ Hcc _ _ _ _ Hsem (write_rval vm0 (fd_arg fd2) va).
    + by apply (eq_write _ Hcx);apply eq_alloc_empty.
    move=> vm2' [Hvm2 Hsb];exists vm2';split=>//.
    by have := eq_sem Hvm2 Hcr;rewrite Hvr !sem_rval2pe => -[].
  Qed.

  Lemma check_fdP ta tr (f1 f2 : fundef ta tr) mem mem' va vr: 
    check_fd f1 f2 -> 
    sem_call valid_addr mem f1 va mem' vr -> sem_call valid_addr mem f2 va mem' vr.
  Proof.
    have H := (@func_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc _ _ f1 f2).
    by move=> ?;apply H.
  Qed.

End PROOF.

End MakeCheckAlloc.


Module CBA <: CheckB.

  Module M := MakeMalloc Mvar.
 
  Definition check_v (m:M.t) x1 x2 : bool :=
    if vtype x1 == vtype x2 then
      match M.get m x1 with
      | None     => false 
      | Some id' => vname x2 == id'
      end
    else false.
  
  Fixpoint check_e t1 t2 (m:M.t) (e1:pexpr t1) (e2:pexpr t2) : bool := 
    match e1, e2 with
    | Pvar x1  , Pvar x2    => check_v m x1 x2
    | Pconst n1, Pconst n2  => n1 == n2
    | Pbool b1 , Pbool b2   => b1 == b2
    | Papp1 _ _ o1 e1, Papp1 _ _ o2 e2 => 
      eqb_sop1 o1 o2 && check_e m e1 e2
    | Papp2 _ _ _ o1 e11 e12   , Papp2 _ _ _ o2 e21 e22     =>  
      eqb_sop2 o1 o2 && check_e m e11 e21 && check_e m e12 e22
    | Papp3 _ _ _ _ o1 e11 e12 e13, Papp3 _ _ _ _ o2 e21 e22 e23 => 
      eqb_sop3 o1 o2 && check_e m e11 e21 &&
      check_e m e12 e22 && check_e m e13 e23
    | _, _ => false
    end.
  
  Fixpoint check_rval t1 t2 (x1:rval t1) (x2:rval t2) m :=
    match x1, x2 with
    | Rvar x1, Rvar x2 => 
      if vtype x1 == vtype x2 then Ok unit (M.set m x1 (vname x2))
      else Error tt 
    | Rpair _ _ x11 x12, Rpair _ _ x21 x22 => 
      check_rval x12 x22 m >>= check_rval x11 x21
    | _                , _                 => Error tt
    end.
   
  Definition check_bcmd i1 i2 m := 
    match i1, i2 with
    | Assgn _ x1 e1, Assgn _ x2 e2 =>
      if check_e m e1 e2 then check_rval x1 x2 m
      else Error tt                                               
    | Load x1 e1   , Load x2 e2    => 
      if check_e m e1 e2 then check_rval x1 x2 m
      else Error tt
    | Store e11 e12, Store e21 e22 =>
      if check_e m e11 e21 && check_e m e12 e22 then Ok unit m
      else Error tt
    | _            , _             => 
      Error tt
    end.
  

  Definition eq_alloc (r:M.t) (vm1 vm2:vmap) := 
    forall x id, M.get r x = Some id ->
    vm1.[x] = vm2.[Var (vtype x) id].

  Lemma eq_alloc_empty vm: eq_alloc M.empty vm vm.
  Proof. by move=> ??;rewrite M.get0. Qed.

  Lemma eq_alloc_incl r1 r2 vm vm':
    M.incl r2 r1 -> 
    eq_alloc r1 vm vm' -> 
    eq_alloc r2 vm vm'.
  Proof. move=> /M.inclP Hi H x id /Hi;apply H. Qed.

  Lemma check_rval_eqt t1 t2 (r1 r2:M.t) (rv1:rval t1) (rv2:rval t2):
    check_rval rv1 rv2 r1 = Ok unit r2 ->
    t1 = t2.
  Proof.
    elim: rv1 t2 rv2 r1 r2 => [x1 | ?? x11 Hx1 x12 Hx2] t2 [x2 | ?? x21 x22] //= r1 r2.
    + by case:ifP => [/eqP|].
    case Heq: check_rval => [r' /=|//] /Hx1 ->.
    by rewrite (Hx2 _ _ _ _ Heq).
  Qed.
    
  Lemma check_e_eqt r t1 (e1:pexpr t1) t2 (e2:pexpr t2):
    check_e r e1 e2 -> t1 = t2.
  Proof.
    elim: e1 t2 e2 =>
      [ x1 | n1 | b1 | ?? o1 e1 He1
      | ??? o1 e11 He1 e12 He2 | ???? o1 e11 He1 e12 He2 e13 He3] t2
      [ x2 | n2 | b2 | ?? o2 e2
      | ??? o2 e21  e22 | ???? o2 e21 e22 e23] //=.
    + by rewrite /check_v;case:ifP => [/eqP|].
    + by move=> /andP[] Ho /He1 Heqt;case:(eqb_sop1P Heqt Ho).
    + by move=> /andP[]/andP[] Ho /He1 H1 /He2 H2;case:(eqb_sop2P H1 H2 Ho).
    by move=> /andP[]/andP[]/andP[] Ho /He1 H1 /He2 H2 /He3 H3;case:(eqb_sop3P H1 H2 H3 Ho).
  Qed.
    
  Lemma eq_write_aux t1 (rv1:rval t1) t2 (rv2:rval t2) v1 v2 r1 r2 vm vm' : 
     check_rval rv1 rv2 r1 = Ok unit r2 ->
     eq_alloc r1 vm vm' ->
     JMeq v1 v2 ->
     eq_alloc r2 (write_rval vm rv1 v1) (write_rval vm' rv2 v2).
  Proof.
    elim: rv1 t2 rv2 v1 v2 r1 r2 vm vm' =>[[t1' x1] | ?? x11 Hx1 x12 Hx2] ?
      [[ t2' x2] | ?? x21 x22] //= v1 v2 r1 r2 vm vm'.
    + case: ifP => //= /eqP ?;subst t2' => -[] <- Hvm Hjm.
      rewrite -(JMeq_eq Hjm) => x id.
      case: ({| vtype := t1'; vname := x1 |} =P x) => [<-/=| /eqP Hne].
      + by rewrite M.setP_eq=> -[] <-;rewrite !Fv.setP_eq.
      move=> Hget;have [Hx Hne2] := M.setP_neq Hne Hget.
      rewrite !Fv.setP_neq //;first by apply Hvm.
      by apply /eqP => -[] ??;apply Hne2.            
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
 
  Lemma eq_sem_aux r vm1 vm1' t1 (e1:pexpr t1) t2 (e2:pexpr t2) : 
    eq_alloc r vm1 vm1' ->
    check_e r e1 e2 ->
    JMeq (sem_pexpr vm1 e1) (sem_pexpr vm1' e2).
  Proof.
    move=> Hrn; elim: e1 t2 e2 =>
      [ [tx1 x1] | n1 | b1 | ?? o1 e1 He1
      | ??? o1 e11 He1 e12 He2 | ???? o1 e11 He1 e12 He2 e13 He3] t2
      [ [tx2 x2] | n2 | b2 | ?? o2 e2
      | ??? o2 e21  e22 | ???? o2 e21 e22 e23] //=.
    + rewrite /check_v /=;case:(_ =P _) => Heqt //=.
      by subst; case Hget: M.get=> [id'|] //= /eqP ?;subst;rewrite (Hrn _ _ Hget).
    + by move=> /eqP ->.
    + by move=> /eqP ->.
    + move=> /andP[] Ho H1.  
      have ? := check_e_eqt H1;subst;rewrite (He1 _ _ H1).
      by case:(eqb_sop1P _ Ho) => // ?;subst=> ->.
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

  Lemma check_bcmdP valid_addr i1 r1 i2 r2:
    check_bcmd i1 i2 r1 = Ok unit r2 ->
    forall m1 m2 vm1 vm2, sem_i valid_addr (Estate m1 vm1) (Cbcmd i1) (Estate m2 vm2) ->
    forall vm1', eq_alloc r1 vm1 vm1' ->
    exists vm2', eq_alloc r2 vm2 vm2' /\ 
      sem_i valid_addr (Estate m1 vm1') (Cbcmd i2) (Estate m2 vm2').
  Proof.
    case: i1 i2 =>
      [t1 rv1 e1 | rv1 e1 | e11 e12] [t2 rv2 e2 | rv2 e2 | e21 e22] //=.
    + case Hce: check_e => //= Hcr.
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

End CBA.

Module CheckAlloc :=  MakeCheckAlloc CBA.



