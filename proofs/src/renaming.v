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

(* ** check renaming before inlining
 * -------------------------------------------------------------------- *)

Local Notation map := (Mvar.t Ident.ident).

Definition check_rename_var (m:map) x1 x2 : result unit map :=
  if vtype x1 == vtype x2 then
    match Mvar.get m x1 with
    | None     => 
      let id := vname x2 in
      if Mvar.in_codom id m then Error tt
      else Ok unit (Mvar.set m x1 id) 
    | Some id' => if vname x2 == id' then Ok unit m else Error tt
    end
  else Error tt.

Fixpoint check_rename_e (m:map) t1 t2 (e1:pexpr t1) (e2:pexpr t2) : result unit map := 
  match e1, e2 with
  | Pvar x1  , Pvar x2    => check_rename_var m x1 x2
  | Pconst n1, Pconst n2  => if (n1 =? n2)%num then Ok unit m else Error tt
  | Pbool b1 , Pbool b2   => if b1 == b2 then Ok unit m else Error tt
  | Papp1 _ _ o1 e1         , Papp1 _ _ o2 e2          => 
    if eqb_sop1 o1 o2 then check_rename_e m e1 e2
    else Error tt
  | Papp2 _ _ _ o1 e11 e12   , Papp2 _ _ _ o2 e21 e22     =>  
    if eqb_sop2 o1 o2 then
      check_rename_e m e11 e21 >>= (fun m => check_rename_e m e12 e22)
    else Error tt
  | Papp3 _ _ _ _ o1 e11 e12 e13, Papp3 _ _ _ _ o2 e21 e22 e23 => 
    if eqb_sop3 o1 o2 then
      check_rename_e m e11 e21 >>= (fun m => 
      check_rename_e m e12 e22 >>= (fun m => check_rename_e m e13 e23))
    else Error tt
  | _, _ => Error tt
  end.

Fixpoint check_rename_rval m t1 (x1:rval t1) t2 (x2:rval t2) :=
  match x1, x2 with
  | Rvar x1          , Rvar x2           => check_rename_var m x1 x2
  | Rpair _ _ x11 x12, Rpair _ _ x21 x22 => 
    check_rename_rval m x11 x21 >>= (fun m => check_rename_rval m x12 x22)
  | _                , _                 => Error tt
  end.
 
Definition check_rename_bcmd m i1 i2 := 
  match i1, i2 with
  | Assgn _ x1 e1, Assgn _ x2 e2 =>
    check_rename_rval m x1 x2 >>= (fun m => check_rename_e m e1 e2)
  | Load x1 e1   , Load x2 e2    => 
    check_rename_rval m x1 x2 >>= (fun m => check_rename_e m e1 e2)
  | Store e11 e12, Store e21 e22 =>
    check_rename_e m e11 e21 >>= (fun m => check_rename_e m e12 e22)
  | _            , _             => Error tt
  end.

Section FOLD2.

  Variable A E R:Type.
  Variable e: E.
  Variable f : R -> A -> A -> result E R.
 
  Fixpoint fold2 r (l1 l2: seq A) := 
    match l1, l2 with
    | [::]  , [::]   => Ok E r 
    | a1::l1, a2::l2 =>
      f r a1 a2 >>= (fun r => fold2 r l1 l2)
    | _     , _      => Error e
    end.

End FOLD2.

Fixpoint check_rename_i m i1 i2 := 
  match i1, i2 with
  | Cbcmd i1, Cbcmd i2 => check_rename_bcmd m i1 i2
  | Cif e1 c11 c12, Cif e2 c21 c22 =>
    check_rename_e m e1 e2 >>= (fun m =>
    fold2 tt check_rename_i m c11 c21 >>= (fun m =>
    fold2 tt check_rename_i m c12 c22))
  | Cfor i1 (dir1,lo1,hi1) c1, Cfor i2 (dir2,lo2,hi2) c2 =>
    if eqb_dir dir1 dir2 then
      check_rename_rval m i1 i2 >>= (fun m =>
      check_rename_e m lo1 lo2 >>= (fun m =>
      check_rename_e m hi1 hi2 >>= (fun m => fold2 tt check_rename_i m c1 c2)))
    else Error tt 
  | Cwhile e1 c1, Cwhile e2 c2 =>
    check_rename_e m e1 e2 >>= (fun m => fold2 tt check_rename_i m c1 c2)
  | Ccall _ _ x1 fd1 arg1, Ccall _ _ x2 fd2 arg2 => 
    if check_rename_fd fd1 fd2 then 
      check_rename_rval m x1 x2 >>= (fun m => check_rename_e m arg1 arg2)
    else Error tt
  | _, _ => Error tt
  end

with check_rename_fd ta1 tr1 (fd1:fundef ta1 tr1) ta2 tr2 (fd2:fundef ta2 tr2) :=
  match fd1, fd2 with
  | FunDef _ _ p1 c1 r1, FunDef _ _ p2 c2 r2 =>
    isOk (
      check_rename_rval (Mvar.empty Ident.ident) p1 p2 >>= (fun m =>
      check_rename_rval m r1 r2 >>= (fun m =>
      fold2 tt check_rename_i m c1 c2)))
  end.

Section PROOF.

  Definition eq_rename (r:map) (vm1 vm2:vmap) := 
    forall x id, Mvar.get r x = Some id ->
    vm1.[x] = vm2.[Var (vtype x) id].
    
  Definition incl_map (r1 r2:map) :=
    forall x id, Mvar.get r1 x = Some id -> Mvar.get r2 x = Some id.

  Lemma incl_mapT (r1 r2 r3:map) : incl_map r1 r2 -> incl_map r2 r3 -> incl_map r1 r3.
  Proof. by move=> H1 H2 x id /H1 /H2. Qed.

  Definition valid (r:map) :=
     forall x y id, Mvar.get r x = Some id ->  Mvar.get r y = Some id -> x = y.

  Let Pi (i1:instr) := 
    forall r1 i2 r2, valid r1 -> check_rename_i r1 i1 i2 = Ok unit r2 ->
    [/\ valid r2 , incl_map r1 r2 &
    (forall m1 m2 vm1 vm2, sem_i (Estate m1 vm1) i1 (Estate m2 vm2) ->
    forall vm1' r, valid r -> incl_map r2 r -> eq_rename r vm1 vm1' ->
    exists vm2', eq_rename r vm2 vm2' /\ sem_i (Estate m1 vm1') i2 (Estate m2 vm2'))].

  Let Pc (c1:cmd) := 
    forall r1 c2 r2, valid r1 -> fold2 tt check_rename_i r1 c1 c2 = Ok unit r2 ->
    [/\ valid r2, incl_map r1 r2 &
    forall m1 m2 vm1 vm2, sem (Estate m1 vm1) c1 (Estate m2 vm2) ->
    forall vm1' r, valid r -> incl_map r2 r -> eq_rename r vm1 vm1' ->
    exists vm2', eq_rename r vm2 vm2' /\ sem (Estate m1 vm1') c2 (Estate m2 vm2')].

  Let Pf ta tr (fd1:fundef ta tr) := 
    forall fd2, check_rename_fd fd1 fd2 ->
    forall mem mem' va vr, 
    sem_call mem fd1 va mem' vr ->
    sem_call mem fd2 va mem' vr.

  Let Hskip : Pc [::].
  Proof.
    move=> r1 [] //= r2 Hv [] <-;split=> //. 
    move=> m1 m2 vm1 vm2 H;inversion H;clear H;subst.
    move=> vm1' r Hvm1;exists vm1';split=>//=;constructor.
  Qed.

  Let Hseq  : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i1 c1 Hi Hc r1 [//|i2 c2] r2 /=.
    case Hci : check_rename_i => [ri|] //= Hv Hcc.
    have {Hci Hi} [Hvi Hii Hi] := Hi _ _ _ Hv Hci.
    have {Hcc Hc} [Hv2 Hic Hc] := Hc _ _ _ Hvi Hcc;split=> //.
    + apply: incl_mapT Hic=> //.
    move=> m1 m3 vm1 vm3 H.
    inversion H;clear H;subst=> /= vm1' r Hvr Hincl Hvm1.                  
    move: H3 H5;case: s2 => m2 vm2 H3 H5.
    case :(Hi _ _ _ _ H3 _ _ Hvr (incl_mapT Hic Hincl) Hvm1)=> vm2' [Hvm2 Hsi].
    case :(Hc _ _ _ _ H5 _ _ Hvr Hincl Hvm2)=> vm3' [Hvm3 Hsc].
    by exists vm3';split=> //;apply (Eseq Hsi Hsc).
  Qed.

  Lemma check_rename_rval_eqt t1 t2 (r1 r2:map) (rv1:rval t1) (rv2:rval t2):
    check_rename_rval r1 rv1 rv2 = Ok unit r2 ->
    t1 = t2.
  Proof.
    elim: rv1 t2 rv2 r1 r2 => [x1 | ?? x11 Hx1 x12 Hx2] t2 [x2 | ?? x21 x22] //= r1 r2.
    + by rewrite /check_rename_var;case:ifP => [/eqP|].
    case Heq: check_rename_rval => [r' /=|//] /Hx2 ->.
    by rewrite (Hx1 _ _ _ _ Heq).
  Qed.

  Lemma check_rename_v_incl r1 r2 x1 x2: 
    check_rename_var r1 x1 x2 = Ok unit r2 -> incl_map r1 r2.
  Proof.
    rewrite /check_rename_var.
    case: ifP=> // /eqP Heqt.
    case Heq: Mvar.get => [id|]. 
    + by case:ifP => // /eqP Heqi [] ->. 
    case : Mvar.in_codom=> //.
    move=> [] <- x id Hx;rewrite Mvar.setP_neq=> //.
    by apply /eqP=> H;move: Heq;rewrite H Hx.
  Qed.

  Lemma check_rename_v_valid r1 r2 x1 x2: 
    check_rename_var r1 x1 x2 = Ok unit r2 -> valid r1 -> valid r2. 
  Proof.
    rewrite /check_rename_var.
    case: ifP=> // /eqP Heqt.
    case Heq: Mvar.get => [id|]. 
    + by case:ifP => // /eqP Heqi [] ->.
    case: (boolP (Mvar.in_codom _ _)) => // /negP Hinc.
    move=> [] <- Hv1 x y id.
    case: (x1 =P x) => [-> | /eqP Hneqx].
    rewrite Mvar.setP_eq=> [] <-.
    + case: (x =P y) => [//| /eqP Hneqy].
      rewrite Mvar.setP_neq // => Hget.
      by elim Hinc;rewrite Mvar.in_codomP;exists y.
    rewrite Mvar.setP_neq //.
    case: (x1 =P y) => [-> | /eqP Hneqy].
    + rewrite Mvar.setP_eq=> Hx [] ?;subst.
      by elim Hinc;rewrite Mvar.in_codomP;exists x.
    by rewrite Mvar.setP_neq //;apply Hv1.
  Qed.
    
  Lemma check_rename_e_incl r1 r2 t1 (e1:pexpr t1) t2 (e2:pexpr t2):
    check_rename_e r1 e1 e2 = Ok unit r2 ->
    incl_map r1 r2.
  Proof.
    elim: e1 t2 e2 r1 r2 =>
      [ x1 | n1 | b1 | ?? o1 e1 He1
      | ??? o1 e11 He1 e12 He2 | ???? o1 e11 He1 e12 He2 e13 He3] t2
      [ x2 | n2 | b2 | ?? o2 e2
      | ??? o2 e21  e22 | ???? o2 e21 e22 e23] //= r1 r2.
    + by apply check_rename_v_incl.
    + by case:ifP => // _ [] ->.
    + by case:ifP => // _ [] ->.
    + by case:ifP => // _;apply: He1.
    + case:ifP => // _.
      by case Heq: check_rename_e=> [r3|]//= /He2;apply incl_mapT;apply: He1 Heq.
    case:ifP => // _.
    case Heq1: check_rename_e=> [r3|]//=.
    case Heq2: check_rename_e=> [r4|]//= /He3.
    by apply incl_mapT; apply: incl_mapT (He2 _ _ _ _ Heq2);apply: He1 Heq1.
  Qed.

  Lemma check_rename_e_valid r1 r2 t1 (e1:pexpr t1) t2 (e2:pexpr t2):
    check_rename_e r1 e1 e2 = Ok unit r2 ->
    valid r1 -> valid r2.
  Proof.
    elim: e1 t2 e2 r1 r2 =>
      [ x1 | n1 | b1 | ?? o1 e1 He1
      | ??? o1 e11 He1 e12 He2 | ???? o1 e11 He1 e12 He2 e13 He3] t2
      [ x2 | n2 | b2 | ?? o2 e2
      | ??? o2 e21  e22 | ???? o2 e21 e22 e23] //= r1 r2.
    + by apply check_rename_v_valid.
    + by case:ifP => // _ [] ->. 
    + by case:ifP => // _ [] ->. 
    + by case:ifP => // _;apply: He1.
    + case:ifP => // _.
      case Heq: check_rename_e=> [r3|]//= /He2 H3 H1;apply H3.
      apply: He1 Heq H1.
    case:ifP => // _.
    case Heq1: check_rename_e=> [r3|]//=.
    case Heq2: check_rename_e=> [r4|]//= /He3 H4 H1.
    apply H4;apply (He2 _ _ _ _ Heq2);apply: He1 Heq1 H1.
  Qed.

  Lemma check_rename_e_eqt r1 r2 t1 (e1:pexpr t1) t2 (e2:pexpr t2):
    check_rename_e r1 e1 e2 = Ok unit r2 -> t1 = t2.
  Proof.
    elim: e1 t2 e2 r1 r2 =>
      [ x1 | n1 | b1 | ?? o1 e1 He1
      | ??? o1 e11 He1 e12 He2 | ???? o1 e11 He1 e12 He2 e13 He3] t2
      [ x2 | n2 | b2 | ?? o2 e2
      | ??? o2 e21  e22 | ???? o2 e21 e22 e23] //= r1 r2.
    + by rewrite /check_rename_var;case:ifP => [/eqP|].
    + by case:ifP => // Ho /He1 Heqt;case:(eqb_sop1P Heqt Ho).
    + case:ifP=> // Ho.
      case Heq1: check_rename_e => [r'|]//=.
      by have := He1 _ _ _ _ Heq1=> ? /He2 ?;case : (eqb_sop2P _ _ Ho).
    case:ifP=> // Ho.
    case Heq1: check_rename_e => [r'|]//=.
    case Heq2: check_rename_e => [r''|]//=.
    have := He1 _ _ _ _ Heq1;have := He2 _ _ _ _ Heq2=> ?? /He3 ?.
    by case : (eqb_sop3P _ _ _ Ho).
  Qed.
    
  Lemma check_rename_rv_incl t1 (rv1:rval t1) t2 (rv2:rval t2) r1 r2: 
    check_rename_rval r1 rv1 rv2 = Ok unit r2 ->
    incl_map r1 r2.
  Proof.
    elim: rv1 t2 rv2 r1 r2 => [x1 | ?? x11 Hx1 x12 Hx2] ? [x2 | ?? x21 x22] //= r1 r2.
    + by apply check_rename_v_incl.
    case Heq: check_rename_rval => [r3|] //= /Hx2.
    by apply incl_mapT;apply: Hx1 Heq.
  Qed.

  Lemma check_rename_rv_valid t1 (rv1:rval t1) t2 (rv2:rval t2) r1 r2: 
    check_rename_rval r1 rv1 rv2 = Ok unit r2 ->
    valid r1 -> valid r2.
  Proof.
    elim: rv1 t2 rv2 r1 r2 => [x1 | ?? x11 Hx1 x12 Hx2] ? [x2 | ?? x21 x22] //= r1 r2.
    + by apply check_rename_v_valid.
    case Heq: check_rename_rval => [r3|] //= /Hx2 H2 H1.
    by apply H2;apply: Hx1 Heq H1.
  Qed.

  Lemma eq_rn_write_aux t1 (rv1:rval t1) t2 (rv2:rval t2) v1 v2 r1 r2 r vm vm' : 
     check_rename_rval r1 rv1 rv2 = Ok unit r2 ->
     valid r -> incl_map r2 r ->
     eq_rename r vm vm' ->
     JMeq v1 v2 ->
     eq_rename r (write_rval vm rv1 v1) (write_rval vm' rv2 v2).
  Proof.
    elim: rv1 t2 rv2 v1 v2 r1 r2 vm vm' =>[[t1' x1] | ?? x11 Hx1 x12 Hx2] ?
      [[ t2' x2] | ?? x21 x22] //= v1 v2 r1 r2 vm vm'.
    + rewrite /check_rename_var.
      case: ifP => //= /eqP ?;subst t2'.
      case Heq: Mvar.get => [id|] /=.
      + case: ifP => // /eqP Heqi [] ?;subst r2;subst id.
        move=> Hv Hincl Hrn Hjm;rewrite (JMeq_eq Hjm)=> x idx.
        case : ({| vtype := t1'; vname := x1 |} =P x) => [<- /=| /eqP Hdiff Hget].
        + by rewrite (Hincl _ _ Heq)=> -[] ?;subst;rewrite !Fv.setP_eq.
        rewrite !Fv.setP_neq //;first by apply Hrn.
        apply /eqP=> -[] ??;subst.
        by move:Hdiff;rewrite (Hv _ _ _ Hget (Hincl _ _ Heq)) /= eq_refl.
      case Hin: Mvar.in_codom => // -[] ?;subst=> Hv Hincl Hrn Hjm.
      rewrite (JMeq_eq Hjm)=> x idx.
      case : ({| vtype := t1'; vname := x1 |} =P x) => [<- /=| /eqP Hdiff Hget].
      + rewrite Fv.setP_eq (Hincl {| vtype := t1'; vname := x1 |} x2) ?Fv.setP_eq //.
        + by move=> []?;subst;rewrite Fv.setP_eq.
        by rewrite Mvar.setP_eq.     
      rewrite !Fv.setP_neq //;first by apply Hrn.
      apply /eqP=> -[] ??;subst.
      move:Hdiff;rewrite (Hv _ ({| vtype := vtype x; vname := x1 |}) _ Hget) ?eq_refl //.
      by apply: Hincl;rewrite Mvar.setP_eq.
    case Heq1: check_rename_rval => [v1' |] //= Heq2 Hv Hincl Hrn.
    have ?:= check_rename_rval_eqt Heq1;subst.
    have ?:= check_rename_rval_eqt Heq2;subst=> Hjm.
    have H:= JMeq_eq Hjm;subst v2 => {H}.
    apply (Hx1 _ _ _ _ _ _ _ _ Heq1)=> //.
    + apply: incl_mapT Hincl;apply: check_rename_rv_incl Heq2.
    by apply (Hx2 _ _ _ _ _ _ _ _ Heq2).
  Qed.

  Lemma eq_rn_write t (rv1 rv2:rval t) v r1 r2 r vm vm' : 
     check_rename_rval r1 rv1 rv2 = Ok unit r2 ->
     valid r -> incl_map r2 r ->
     eq_rename r vm vm' ->
     eq_rename r (write_rval vm rv1 v) (write_rval vm' rv2 v).
  Proof.
    move=> Hc Hv Hrn /(eq_rn_write_aux Hc Hv Hrn) H;apply H;apply JMeq_refl.
  Qed.

  Lemma eq_rn_sem_aux r1 r2 r vm1 vm1' t1 (e1:pexpr t1) t2 (e2:pexpr t2) : 
    valid r -> incl_map r2 r ->
    eq_rename r vm1 vm1' ->
    check_rename_e r1 e1 e2 = Ok unit r2 ->
    JMeq (sem_pexpr vm1 e1) (sem_pexpr vm1' e2).
  Proof.
    elim: e1 t2 e2 r1 r2=>
      [ [tx1 x1] | n1 | b1 | ?? o1 e1 He1
      | ??? o1 e11 He1 e12 He2 | ???? o1 e11 He1 e12 He2 e13 He3] t2
      [ [tx2 x2] | n2 | b2 | ?? o2 e2
      | ??? o2 e21  e22 | ???? o2 e21 e22 e23] //= r1 r2.
    + rewrite /check_rename_var /=;case:(_ =P _) => Heqt //=.
      subst; case Hget: Mvar.get=> [id|] //=.
      + case:(_ =P _) => //= ? Hv Hincl Hrn [] ?;subst.
        by rewrite (Hrn _ _ (Hincl _ _ Hget)) //.
      case Hinc: Mvar.in_codom => //= Hv Hincl Hrn [] ?;subst.
      by rewrite (Hrn _ x2) //; apply Hincl;rewrite Mvar.setP_eq.
    + by case Heq: (_ =? _)%num => //;rewrite (Neqb_ok _ _ Heq).
    + by case:eqP => //= ->.
    + move=> Hv Hincl Hrn;case:ifP=> //= Ho He.
      have ? := check_rename_e_eqt He;subst.
      have -> := He1 _ _ _ _ Hv Hincl Hrn He.
      have [] // := eqb_sop1P _ Ho=> Heqt.
      by move: {Ho} o2;rewrite <- Heqt => o2 ->.
    + move=> Hv Hincl Hrn;case:ifP=> //= Ho.
      case Heq1: check_rename_e => [r1'|] //= Heq2.
      have ? := check_rename_e_eqt Heq1;subst.
      have ? := check_rename_e_eqt Heq2;subst.
      have -> := He2 _ _ _ _ Hv Hincl Hrn Heq2.
      have -> := He1 _ _ _ _ Hv _ Hrn Heq1;last first.
      + by apply: incl_mapT Hincl;apply: check_rename_e_incl Heq2.
      have [] // := eqb_sop2P _ _ Ho=> Heqt.
      by move: {Ho} o2;rewrite <- Heqt => o2 ->.
    move=> Hv Hincl Hrn;case:ifP=> //= Ho.
    case Heq1: check_rename_e => [r1'|] //=.
    case Heq2: check_rename_e => [r1''|] //= Heq3.
    have ? := check_rename_e_eqt Heq1;subst.
    have ? := check_rename_e_eqt Heq2;subst.
    have ? := check_rename_e_eqt Heq3;subst.
    have -> := He3 _ _ _ _ Hv Hincl Hrn Heq3.
    have -> := He2 _ _ _ _ Hv _ Hrn Heq2;last first.
    + by apply: incl_mapT Hincl;apply: check_rename_e_incl Heq3.
    have -> := He1 _ _ _ _ Hv _ Hrn Heq1;last first.
    + apply: incl_mapT Hincl. 
      apply: (incl_mapT (check_rename_e_incl Heq2)).
      apply: check_rename_e_incl Heq3.
    have [] // := eqb_sop3P _ _ _ Ho=> Heqt.
    by move: {Ho} o2;rewrite <- Heqt => o2 ->.
  Qed.

  Lemma eq_rn_sem r1 r2 r vm1 vm1' t (e1 e2:pexpr t): 
    valid r -> incl_map r2 r ->
    eq_rename r vm1 vm1' ->
    check_rename_e r1 e1 e2 = Ok unit r2 ->
    sem_pexpr vm1 e1 = sem_pexpr vm1' e2.
  Proof. 
    by move=> Hv Hincl Hrn Hc;rewrite (eq_rn_sem_aux Hv Hincl Hrn Hc). 
  Qed.
  
  Let Hbcmd : forall bc,  Pi (Cbcmd bc).
  Proof.
    move=> i1 r1 [i2 | | | | ] //=.
    case: i1 i2  =>
      [t1 rv1 e1 | rv1 e1 | e11 e12] [t2 rv2 e2 | rv2 e2 | e21 e22] //= r2.
    + case Hcr: check_rename_rval => [r'|]//= Hv Hce.
      have Hincl' := check_rename_e_incl Hce.
      have Hincl1 := check_rename_rv_incl Hcr.
      have Hv' := check_rename_rv_valid Hcr Hv.
      have Hv1 := check_rename_e_valid Hce Hv';split=> //.
      + by apply: incl_mapT Hincl'.
      move=> m1 m2 vm1 vm2 H;inversion H;clear H;subst.
      move: H2=> /=.
      case Heq: sem_pexpr=> [v1|]//= [] <- <- vm1' r Hvr Hincl Hvm1.
      have ? := check_rename_rval_eqt Hcr;subst t2.
      exists (write_rval vm1' rv2 v1);split.
      + by apply (eq_rn_write _ Hcr)=> //; apply: incl_mapT Hincl.
      constructor=> /=.
      by rewrite -(eq_rn_sem Hvr Hincl Hvm1 Hce) Heq.
    + case Hcr: check_rename_rval => [r'|]//= Hv Hce.
      have Hincl' := check_rename_e_incl Hce.
      have Hincl1 := check_rename_rv_incl Hcr.
      have Hv' := check_rename_rv_valid Hcr Hv.
      have Hv1 := check_rename_e_valid Hce Hv';split=> //.
      + by apply: incl_mapT Hincl'.
      move=> m1 m2 vm1 vm2 H;inversion H;clear H;subst.
      move: H2=> /=.
      case Heq: sem_pexpr=> [v1|]//=.
      case Heqr: read_mem=> [w|]//= []<- <- vm1' r Hvr Hincl Hvm1.
      exists (write_rval vm1' rv2 w);split.
      + by apply (eq_rn_write _ Hcr)=> //; apply: incl_mapT Hincl.
      constructor=> /=.
      by rewrite -(eq_rn_sem Hvr Hincl Hvm1 Hce) Heq /= Heqr.
    case Hce1: check_rename_e => [r'|]//= Hv Hce2.
    have Hincl1 := check_rename_e_incl Hce1.
    have Hincl' := check_rename_e_incl Hce2.
    have Hv' := check_rename_e_valid Hce1 Hv.
    have Hv1 := check_rename_e_valid Hce2 Hv';split=> //.
    + by apply: incl_mapT Hincl'.
    move=> m1 m2 vm1 vm2 H;inversion H;clear H;subst.
    move: H2=> /=.
    case Heq1: (sem_pexpr vm1 e11) => [v1|]//=.
    case Heq2: sem_pexpr=> [v2|]//=.
    case Heqw: write_mem=> [m2'|]//= []<- <- vm1' r Hvr Hincl Hvm1.
    exists vm1';split=> //.
    constructor=> /=.
    rewrite -(eq_rn_sem Hvr Hincl Hvm1 Hce2).
    rewrite -(eq_rn_sem Hvr _ Hvm1 Hce1);last by apply: incl_mapT Hincl.
    by rewrite Heq1 Heq2 /= Heqw.
  Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Proof.
    move=> e1 c11 c12 Hc1 Hc2 r1 []// e2 c21 c22 r2 Hvr /=.
    case Heq: check_rename_e => [r'|]//=.          
    case Heq1: fold2 => [r''|]//= Heq2.
    have Hvr' := check_rename_e_valid Heq Hvr.
    have Hincl' := check_rename_e_incl Heq.
    have [Hvr1 Hincl1 Hsem1]:= Hc1 _ _ _ Hvr' Heq1.
    have [Hvr2 Hincl2 Hsem2]:= Hc2 _ _ _ Hvr1 Heq2;split=> //.
    + by apply: incl_mapT Hincl2;apply: incl_mapT Hincl1.
    move=> m1 m2 vm1 vm2 H;inversion H;clear H;subst=> vm1' r Hr Hincl Hrn.
    case:cond H5 H6=> H5 H6. 
    + case: (Hsem1 _ _ _ _ H6 _ _ Hr _ Hrn);first by apply: incl_mapT Hincl.
      move=> vm2' [Hrn' Hsem'];exists vm2';split=>//.
      apply Eif with true=>//.
      rewrite -(eq_rn_sem Hr _ Hrn Heq) //. 
      by apply: incl_mapT Hincl;apply: incl_mapT Hincl2.
    case: (Hsem2 _ _ _ _ H6 _ _ Hr _ Hrn);first by apply: incl_mapT Hincl.
    move=> vm2' [Hrn' Hsem'];exists vm2';split=>//.
    apply Eif with false=>//.
    rewrite -(eq_rn_sem Hr _ Hrn Heq) //. 
    by apply: incl_mapT Hincl;apply: incl_mapT Hincl2.
  Qed.

  Lemma eqb_dirP d1 d2 : reflect (d1 = d2) (eqb_dir d1 d2).
  Proof. by case: d1 d2 => -[] /=;constructor. Qed.

  Let Hfor  : forall i rn c, Pc c -> Pi (Cfor i rn c).
  Proof.
    move=> i1 [[dir1 hi1] low1] c1 Hc r1 []//= i2 [[dir2 hi2] low2] c2 r2 Hvr1.
    case: eqb_dirP => [<-|] //=.
    case Hi : check_rename_rval => [r0|]//=.
    case Hhi: check_rename_e => [r'|]//=.
    case Hlo: check_rename_e => [r''|]//= Hfc.
    have Hvr0 := check_rename_rv_valid Hi Hvr1.
    have Hincl0 := check_rename_rv_incl Hi.
    have Hvr' := check_rename_e_valid Hhi Hvr0.
    have Hincl' := check_rename_e_incl Hhi.
    have Hvr'' := check_rename_e_valid Hlo Hvr'.
    have Hincl'' := check_rename_e_incl Hlo.
    have {Hc} [ Hvr2 Hincl2 Hc] := Hc _ _ _ Hvr'' Hfc;split=>//.
    + by apply: incl_mapT Hincl2;apply: incl_mapT Hincl'';apply: incl_mapT Hincl'.
    move=> m1 m2 vm1 vm2 H;inversion H;clear H;subst.
    move=> vm1' r Hvr Hincl.
    have Hfor: forall vm1', eq_rename r vm1 vm1' ->
          exists vm2' : vmap, eq_rename r vm2 vm2' /\
          sem_for i2 [seq n2w i | i <- wrange dir1 vlow vhi]
             {| emem := m1; evm := vm1' |} c2 {| emem := m2; evm := vm2' |}.
    + elim: [seq n2w i | i <- wrange dir1 vlow vhi] m1 vm1 H9 {H8 H7}=>
       [ | w ws Hws] m1 vm1 H10;
       inversion H10;clear H10;subst.
      + move=> vm2' Hvm2;exists vm2';split=>//;constructor.
      move=> {vm1'} vm1' Hrn;case: s2 H2 H6=> m3 vm3 /= H2 H6.
      have []:= Hc _ _ _ _ H2 (write_rval vm1' i2 w) _ Hvr Hincl. 
      + apply : (eq_rn_write _ Hi Hvr _ Hrn).
        by apply: incl_mapT Hincl;apply: incl_mapT Hincl2;apply: incl_mapT Hincl''.
      move=> vm3' [Hvm3 Hsem3]. 
      have [vm2' [Hrn2 Hsem']]:= Hws _ _ H6 _ Hvm3.
      by exists vm2';split=>//;apply: EForOne Hsem'.
    move=> Hrn;case: (Hfor _ Hrn)=> [vm2' [Hrn2 Hsem']];exists vm2';split=>//.
    apply: EFor Hsem';rewrite -?H7 -?H8 /=;symmetry.
    + apply: (eq_rn_sem Hvr _ Hrn Hhi).
      by apply: incl_mapT Hincl;apply: incl_mapT Hincl2.
    by apply: (eq_rn_sem Hvr _ Hrn Hlo); apply: incl_mapT Hincl.
  Qed.

  Let Hwhile  : forall e c, Pc c -> Pi (Cwhile e c).
  Proof.
    move=> e1 c1 Hc r1 []//= e2 c2 r2 Hvr1.
    case He: check_rename_e => [r'|]//= Hfc.
    have Hvr' := check_rename_e_valid He Hvr1.
    have Hincl' := check_rename_e_incl He.
    have {Hc} [Hvr2 Hincl2 Hc] := Hc _ _ _ Hvr' Hfc;split=>//.
    + by apply: incl_mapT Hincl2.
    move=> m1 m2 vm1 vm2 H;inversion H;clear H;subst.
    move=> vm1' r Hvr Hincl.
    have Hwhile: forall vm1', eq_rename r vm1 vm1' ->
          exists vm2' : vmap, eq_rename r vm2 vm2' /\
          sem_while {| emem := m1; evm := vm1' |} e2 c2 {| emem := m2; evm := vm2' |}.
    + move: H4 Hc Hfc He.
      set st1 := {| emem := m1; evm := vm1 |}; set st2 := {| emem := m2; evm := vm2 |}.
      rewrite (_: m1 = emem st1) // (_: m2 = emem st2) //.
      rewrite (_: vm1 = evm st1) // (_: vm2 = evm st2) //.
      move: st1 st2=> st1 st2 {m1 vm1 m2 vm2 vm1'}.
      elim => {e1 c1} [ st e1 c1 He1 | [m1 vm1] [m2 vm2] [m3 vm3] e1 c1 He1 Hc1 Hw Hrec]
        Hc Hfc He vm1' Hvm1.
      + exists vm1';split => //;constructor.
        rewrite -He1 /=;symmetry.
        by apply: (eq_rn_sem Hvr _ Hvm1 He); apply: incl_mapT Hincl.
      have [vm2' [Hvm2 Hc2]]:= Hc _ _ _ _ Hc1 _ _ Hvr Hincl Hvm1.
      have [vm3' [Hvm3 Hw2]]:= Hrec Hc Hfc He _ Hvm2.
      exists vm3';split => //.
      apply: EWhileOne Hw2=> //.
      rewrite -He1 /=;symmetry.
      by apply: (eq_rn_sem Hvr _ Hvm1 He); apply: incl_mapT Hincl.     
    by move=> /Hwhile [vm2' [Hvm2 Hw]];exists vm2';split=>//; constructor.
  Qed.

  Let Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Proof.
    move=> ta tr x1 fd1 a1 Hf r1 [] //= ?? x2 fd2 a2 r2 Hvr1.
    case:ifP=> [Heqf|] //=.
    case Heqx: check_rename_rval => [r0|]//= Heqa.
    have Hvr0 := check_rename_rv_valid Heqx Hvr1.
    have Hincl0 := check_rename_rv_incl Heqx.
    have Hvr2 := check_rename_e_valid Heqa Hvr0.
    have Hincl' := check_rename_e_incl Heqa;split=> //=.
    + by apply: incl_mapT Hincl'.
    move=> m1 m2 vm1 vm2 H;inversion H;clear H;subst.  
    unfold rarg in * => {rarg}.
    inversion H5;clear H5;subst;inversion H6;clear H6.
    inversion H7;clear H7;subst;inversion H0;clear H0;subst.
    move=> vm1' r Hvr Hincl Hrn.
    have ?:= check_rename_rval_eqt Heqx;subst.
    exists (write_rval vm1' x2 res);split.
    + apply: (eq_rn_write _ Heqx) => //;by apply: incl_mapT Hincl.
    have ?:= check_rename_e_eqt Heqa;subst.
    have Heq := eq_rn_sem Hvr Hincl Hrn Heqa.
    constructor;rewrite -Heq //.
    by apply: Hf H10.
  Qed.

  Definition inv_map (r:map) (vm:vmap) :=
    Mvar.fold (fun x id vm' => vm'.[x <- vm.[{|vtype := vtype x; vname := id|}]]) r vm. 

  Lemma inv_mapP r vm: valid r -> eq_rename r (inv_map r vm) vm.
  Proof.
    move=> Hv x id Hx.
    pose P := fun vm vm' =>
     (foldl
        (fun (a : vmap) (kv : CmpVar.t * Ident.ident) =>
         a.[kv.1 <- vm.[{| vtype := vtype kv.1; vname := kv.2 |}]]) vm'
         (Mvar.elements r)).[x] =
     (if (x, id) \in Mvar.elements r
       then vm.[{| vtype := vtype x; vname := id |}]
       else vm'.[x]).
    have : forall vm',P vm vm'.
    + have : forall id', (x,id') \in Mvar.elements r -> id = id'.
      + by move=> id' /Mvar.elementsP /=;rewrite Hx => -[].
      rewrite /P=> {P}.
      elim: Mvar.elements => //= -[y idy] elts Hrec Hinj vm'.
      rewrite in_cons Hrec;last first.
      + by move=> ? H;apply Hinj;rewrite in_cons H orbC.
      case:eqP => /= [[<- <-] | Hdiff].
      + by case:ifP => Hin //;rewrite Fv.setP_eq. 
      case:(boolP (_ \in _))=> Hin //.
      case: (y =P x) => [| /eqP] H;last by rewrite Fv.setP_neq.
      by subst;elim Hdiff;rewrite (Hinj idy) // in_cons eq_refl.
    move=> /(_ vm);rewrite /P /inv_map Mvar.foldP=> {P}.    
    by move /(Mvar.elementsP (x,id)): Hx => ->.
  Qed.

  Lemma check_rename_rvar_e r t1 (rv1:rval t1) t2 (rv2:rval t2):
    check_rename_rval r rv1 rv2 = 
    check_rename_e r (rval2pe rv1) (rval2pe rv2).
  Proof.
    elim:rv1 r t2 rv2 => [x1 | ?? x11 Hx1 x12 Hx2] r ? [x2| ?? x21 x22] //=.
    rewrite Hx1;case: check_rename_e => //=.
  Qed.

  Let Hfunc : forall ta tr (x:rval ta) c (re:rval tr), Pc c -> Pf (FunDef x c re).
  Proof.
    move=> ta tr x1 c1 re1 Hc fd2. 
    have ->/= : fd2 = FunDef (fd_arg fd2) (fd_body fd2) (fd_res fd2) by case fd2.
    case Hrvx: check_rename_rval => [r1|]//=.   
    case Hrvr: check_rename_rval => [r2|]//=.
    case Hf : fold2 => [r3|]//= _ mem mem' va vr H;inversion H;clear H;subst.
    inversion H0;clear H0;subst.
    constructor=> vm0.
    case: (H7 (inv_map r3 vm0)) => vm2 /= [] Hsem Hvr {H7}.
    have [] := Hc _ _ _ _ Hf.
    + apply (check_rename_rv_valid Hrvr).
      by apply (check_rename_rv_valid Hrvx)=> x y id;rewrite Mvar.get0.
    move=> Hvr3 Hincl3 Hsem'.
    have []:= Hsem' _ _ _ _ Hsem (write_rval vm0 (fd_arg fd2) va) r3 Hvr3 => //.
    + apply: (eq_rn_write _ Hrvx) => //.
      + by apply: incl_mapT Hincl3;apply: check_rename_rv_incl Hrvr.
      by apply inv_mapP.
    move=> vm2' [Hrn Hsembody]; exists vm2'; split=> //; rewrite Hvr.
    move: Hrvr;rewrite check_rename_rvar_e => Hrvr.
    have := eq_rn_sem Hvr3 Hincl3 Hrn Hrvr.  
    by rewrite !sem_rval2pe=> -[].
  Qed.

  Lemma check_rename_fdP ta tr (f1 f2 : fundef ta tr) mem mem' va vr: 
    check_rename_fd f1 f2 -> 
    sem_call mem f1 va mem' vr -> sem_call mem f2 va mem' vr.
  Proof.
    have H := (@func_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc _ _ f1 f2).
    by move=> ?;apply H.
  Qed.

End PROOF.




