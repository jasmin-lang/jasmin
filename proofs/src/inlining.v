(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr 
               memory dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

(* ** inlining
 * -------------------------------------------------------------------- *)

Fixpoint assgn_tuple t (rv:rval t) : pexpr t -> cmd :=
  match rv in rval t0 return pexpr t0 -> cmd with
  | Rvar x              => fun e => [:: assgn (Rvar x) e]
  | Rpair t1 t2 rv1 rv2 => fun e => assgn_tuple rv2 (esnd e) ++ assgn_tuple rv1 (efst e)
  end.

Definition inline_cmd (inline_i: instr -> cmd) (c:cmd) := 
  List.fold_right (fun i c' => inline_i i ++ c') [::] c.

Fixpoint inline_i (i:instr) : cmd := 
  match i with
  | Cbcmd _              => [::i]
  | Cif b c1 c2          => [::Cif b (inline_cmd inline_i c1) (inline_cmd inline_i c2)]
  | Cfor i rn c          => [::Cfor i rn (inline_cmd inline_i c)]
  | Cwhile e c           => [::Cwhile e (inline_cmd inline_i c)]
  | Ccall ta tr x fd arg => 
    match inline_fd fd in fundef sta str return pexpr sta -> rval str -> cmd with
    | FunDef sta str fa fc fr =>
      fun pe_arg rv_res => 
        assgn_tuple fa pe_arg ++ 
        (fc ++ assgn_tuple rv_res (rval2pe fr))
    end arg x
  end

with inline_fd ta tr (fd:fundef ta tr) :=
  match fd with
  | FunDef sta str fa fc fr => FunDef fa (inline_cmd inline_i fc) fr
  end.

Section CMD.

  Variable check_inline_i : instr ->  Sv.t -> result unit Sv.t.

  Fixpoint check_inline (c:cmd) (s:Sv.t) : result unit Sv.t :=
    match c with
    | [::] => Ok unit s
    | i::c => check_inline c s >>= (check_inline_i i)
    end.

End CMD.

Section LOOP.

  Variable check_inline_c : Sv.t -> result unit Sv.t.

  Fixpoint loop (n:nat) (wx:Sv.t) (s:Sv.t) : result unit Sv.t :=
    match n with
    | O => Error tt
    | S n =>
      check_inline_c s >>=  (fun s' => 
      let s' := Sv.diff s' wx in
      if Sv.subset s' s then Ok unit s 
      else loop n wx (Sv.union s s'))
    end.

  Fixpoint wloop (n:nat) (re:Sv.t) (s:Sv.t) : result unit Sv.t :=
    match n with
    | O => Error tt
    | S n =>
      check_inline_c s >>=  (fun s' => 
      let s' := Sv.union re s' in
      if Sv.subset s' s then Ok unit s 
      else wloop n re (Sv.union s s'))
    end.

End LOOP.

Definition check_inline_bcmd (i:bcmd) (s:Sv.t) :=
  match i with
  | Assgn t rv e =>
    let w := write_bcmd i in
    read_e_rec e (Sv.diff s w)
  | Load r e => 
    let w := write_bcmd i in
    read_e_rec e (Sv.diff s w)
  | Store e1 e2 =>
    read_e_rec e1 (read_e_rec e2 s)
  end.

Definition nb_loop := 100%coq_nat.
Opaque nb_loop.

Fixpoint check_inline_i (i:instr) (s:Sv.t) {struct i} : result unit Sv.t := 
  match i with
  | Cbcmd i     => Ok unit (check_inline_bcmd i s) 
  | Cif b c1 c2 => 
    check_inline check_inline_i c1 s >>= (fun s1 => 
    check_inline check_inline_i c2 s >>= (fun s2 =>
    Ok unit (read_e_rec b (Sv.union s1 s2))))
  | Cfor x (dir, e1, e2) c =>
    loop (check_inline check_inline_i c) nb_loop (vrv x) s >>= (fun s =>
    Ok unit (read_e_rec e1 (read_e_rec e2 s)))
  | Cwhile e c =>
    let re := read_e e in
    wloop (check_inline check_inline_i c) nb_loop re (Sv.union re s)  
  | Ccall ta tr x fd arg =>
    let p := fd_arg fd in
    let c := fd_body fd in
    let r := fd_res fd in
    let sx := vrv x in
    let sr := vrv r in
    let sa := read_e arg in
    let sp := vrv p in
    let s := Sv.diff s sx in  
    if disjoint sx sr && disjoint sp sa && disjoint s (write_c_rec sp c) then
      check_inline check_inline_i c (Sv.union s sr) >>= (fun s' =>
        if Sv.subset s' (Sv.union s sp) then Ok unit (Sv.union s sa)
        else Error tt)    
    else Error tt
  end.

Definition check_inline_fd ta tr (fd:fundef ta tr) := 
  check_inline check_inline_i (fd_body fd) (vrv (fd_res fd)).
          
Section PROOF.

  Lemma assgn_tupleP m vm t (e:pexpr t) x v:
     disjoint (vrv x) (read_e e) ->  
     sem_pexpr vm e = Ok error v ->
     sem {| emem := m; evm := vm |} (assgn_tuple x e)
         {| emem := m; evm := write_rval vm x v |}.
  Proof.
    elim: x vm e v=> [x | ?? rv1 Hrv1 rv2 Hrv2] vm e v /= Hdisj He.
    + by apply sem_seq1;constructor => /=;rewrite He.
    have disj2 : disjoint (vrv rv2) (read_e (esnd e)).
    + move: Hdisj;rewrite /disjoint vrv_pair /is_true !Sv.is_empty_spec.
      by have := @read_e_esnd _ _ e;SvD.fsetdec.
    apply (sem_app (Hrv2 _ _ _ disj2 (sem_esnd He))); apply Hrv1.
    + move: Hdisj;rewrite /disjoint vrv_pair /is_true !Sv.is_empty_spec.
      by have := @read_e_efst _ _ e;SvD.fsetdec.
    apply: sem_efst;rewrite -He;apply read_e_eq_on with Sv.empty.
    rewrite -/(read_e e);apply disjoint_eq_on.
    by move: Hdisj;rewrite /disjoint vrv_pair /is_true !Sv.is_empty_spec;SvD.fsetdec.
  Qed.

  Let Pi (i:instr) := 
    forall m1 m2 vm1 vm2, sem_i (Estate m1 vm1) i (Estate m2 vm2) ->
    forall s1 s2, check_inline_i i s2 = Ok unit s1 ->
    forall vm1', vm1 =[s1] vm1' -> 
    exists vm2', vm2 =[s2] vm2' /\ 
      sem (Estate m1 vm1') (inline_i i) (Estate m2 vm2').

  Let Pc (c:cmd) := 
    forall m1 m2 vm1 vm2, sem (Estate m1 vm1) c (Estate m2 vm2) ->
    forall s1 s2,  check_inline check_inline_i c s2 = Ok unit s1 ->
    forall vm1', vm1 =[s1] vm1' -> 
    exists vm2', vm2 =[s2] vm2' /\ 
      sem (Estate m1 vm1') (inline_cmd inline_i c) (Estate m2 vm2').

  Let Hskip : Pc [::].
  Proof. 
    move=> m1 m2 vm1 vm2 /= H;inversion H;subst=> s1 s2 [] -> vm1' Hvm1'.
    exists vm1';split=> //;constructor.
  Qed.

  Let Hseq  : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc m1 m3 vm1 vm3 H;inversion H;clear H;subst=> /= s1 s3.
    case: s2 H3 H5  => m2 vm2 H3 H5.
    case Hcc: check_inline => [s2|]//= Hci vm1' Hvm1.
    case : (Hi _ _ _ _ H3 _ _ Hci _ Hvm1) => vm2' [Hvm2 Hsi].
    case : (Hc _ _ _ _ H5 _ _ Hcc _ Hvm2) => vm3' [Hvm3 Hsc].
    exists vm3';split=> //.
    by apply: sem_app Hsi Hsc.
  Qed.

  Let Hbcmd : forall bc,  Pi (Cbcmd bc).
  Proof. 
    move=> i m1 m2 vm1 vm2 H;inversion H;clear H;subst=> /= s1 s2 [].
    case: i H2=> /=.
    + move=> t r e;case He: (sem_pexpr _ e) => [v|]//= [] <- /= <- <- vm1' Hvm1.
      exists (write_rval vm1' r v);split;last first.
      + apply sem_seq1;constructor=> /=.
        rewrite -(@read_e_eq_on _ e Sv.empty vm1 vm1') ?He //.
        by rewrite -/(read_e e);apply: eq_onI Hvm1;rewrite read_eE;SvD.fsetdec.
      by apply write_rval_eq_on;apply: eq_onI Hvm1;rewrite read_eE;SvD.fsetdec.
    + move=> r e;case He: (sem_pexpr _ e) => [v|]//=.
      case Hre : (read_mem m1 v) => [v'|]//= [] <- <- /= <- vm1' Hvm1.
      exists (write_rval vm1' r v');split.
      + by apply write_rval_eq_on;apply: eq_onI Hvm1;rewrite read_eE;SvD.fsetdec.
      apply sem_seq1;constructor=> /=.
      rewrite -(@read_e_eq_on _ e Sv.empty vm1 vm1') ?He /= ?Hre //=.
      by rewrite -/(read_e e);apply: eq_onI Hvm1;rewrite read_eE;SvD.fsetdec.
    move=> e1 e2;case He1: (sem_pexpr _ e1) => [v1|]//=.
    case He2: (sem_pexpr _ e2) => [v2|]//=.
    case Hw: (write_mem m1 v1 v2) => [m|]//= [] <- <- <- vm1' Hvm1.
    exists vm1';split=> //.
    + apply: eq_onI Hvm1;rewrite !read_eE;SvD.fsetdec.
    apply sem_seq1;constructor => /=.
    rewrite -(@read_e_eq_on _ e1 Sv.empty vm1 vm1') ?He1 /=;last first.
    + by rewrite -/(read_e e1);apply: eq_onI Hvm1;rewrite !read_eE;SvD.fsetdec.
    rewrite -(@read_e_eq_on _ e2 Sv.empty vm1 vm1') ?He2 /= ?Hw //.
    by rewrite -/(read_e e1);apply: eq_onI Hvm1;rewrite !read_eE;SvD.fsetdec. 
  Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 m1 m2 vm1 vm2 H;inversion H;clear H;subst.
    move=> s s3 /=.
    case Heq1 : (check_inline check_inline_i c1 s3) => [s1|//].
    case Heq2 : (check_inline check_inline_i c2 s3) => [s2|] //= [] <- vm1' Hr.
    case: cond H5 H6 => H5 H6.
    + have [] := Hc1 m1 m2 vm1 vm2 H6 _ _ Heq1 vm1'.
      + by apply: eq_onI Hr;rewrite read_eE;SvD.fsetdec.
      move=> vm2' [Heq' Hsem];exists vm2';split => //.
      by apply sem_seq1;apply Eif with true => //=; rewrite -(read_e_eq_on Hr).
    have [] := Hc2 m1 m2 vm1 vm2 H6 _ _ Heq2 vm1'.
    + by apply: eq_onI Hr;rewrite read_eE;SvD.fsetdec.
    move=> vm2' [Heq' Hsem];exists vm2';split => //.
    by apply sem_seq1;apply Eif with false => //=; rewrite -(read_e_eq_on Hr).
  Qed.

  Let Hfor  : forall i rn c, Pc c -> Pi (Cfor i rn c).
  Proof.
    move=> i [[dir low] hi] c Hc m1 m2 vm1 vm2 H;inversion H;clear H;subst=> /=.
    elim: nb_loop => //= n Hrec s1 s2.
    case Heq : (check_inline check_inline_i c s2) => [s1'|] //=.
    case:ifP=> /= [/Sv.subset_spec Hsub [] <-| _].
    + pose st1 := {| emem := m1; evm := vm1 |}; pose st2:= {| emem := m2; evm := vm2 |}.
      rewrite (_:vm1 = evm st1) // (_:vm2 = evm st2) //.
      rewrite (_:m1 = emem st1) // (_:m2 = emem st2) //.
      have: sem_for i [seq n2w i | i <- wrange dir vlow vhi] st1 c st2 ->
            check_inline check_inline_i c s2 = Ok unit s1' -> Pc c -> 
            Sv.Subset (Sv.diff s1' (vrv i)) s2 ->
            forall vm1',  evm st1 =[s2]  vm1' ->
             exists vm2' : vmap, 
             evm st2 =[s2]  vm2' /\
             sem_for i [seq n2w i | i <- wrange dir vlow vhi]
                {| emem := emem st1; evm := vm1' |} (inline_cmd inline_i c)
                {| emem := emem st2; evm := vm2' |}.
      + move: st1 st2 => {Hrec H7 H8 H9 Hc Heq Hsub vm1 vm2 m1 m2} st1 st2.
        elim=> {st1 st2 c i} [s i c
                             | [m1 vm1] [m2 vm2] [m3 vm3] i w ws c Hsc Hsf Hrec] /=
            Heq Hc Hsub vm1' Hvm1.  
        + exists vm1';split=> //;constructor.
        have /= []:= Hc m1 m2 _ vm2 Hsc _ _ Heq (write_rval vm1' i w).
        + by apply write_rval_eq_on;apply: eq_onI Hvm1.
        move=> /= vm2' [Hvm2 Hsem2].
        elim (Hrec Heq Hc Hsub vm2' Hvm2) => vm3' /= [Hvm3 Hsem3].
        by exists vm3';split=> //;apply: EForOne Hsem3.
      move=> /(_ H9 Heq Hc Hsub) H vm1' Hvm1;case: (H vm1').
      + by apply: eq_onI Hvm1;rewrite !read_eE;SvD.fsetdec.
      move=> vm2' [Hvm2 Hsem];exists vm2';split => //.
      apply sem_seq1;apply EFor with vlow vhi => //=.
      + by rewrite -(read_e_eq_on Hvm1).
      have Hvm: evm st1 =[read_e_rec hi s2]  vm1'.
      + by apply: eq_onI Hvm1;rewrite (read_eE low);SvD.fsetdec.
      by rewrite -(read_e_eq_on Hvm).
    have := Hrec _ (Sv.union s2 (Sv.diff s1' (vrv i))).
    case: loop => [s'|] //= H [] <- vm1' /H [] // vm2' [Hvm Hsem].
    exists vm2';split=> //.
    by apply : eq_onI Hvm;SvD.fsetdec.
  Qed.

  Let Hwhile : forall e c, Pc c -> Pi (Cwhile e c).
  Proof.
    move=> e c Hc m1 m2 vm1 vm2 H;inversion H;clear H;subst=> /=.
    move=> s1 s2; set s2' := (Sv.union (read_e e) s2).
    have : Sv.Subset (Sv.union (read_e e) s2) s2' by SvD.fsetdec. 
    elim: nb_loop s1 s2 s2' => //= n Hrec s1 s2 s2' Hsub2.
    case Heq : (check_inline check_inline_i c s2') => [s1'|] //=.
    case:ifP=> /= [/Sv.subset_spec Hsub [] <-| _].
    + have: 
        forall vm1' : vmap,
        vm1 =[s2']  vm1' ->
        exists vm2' : vmap,
          vm2 =[s2']  vm2' /\
          sem_while {| emem := m1; evm := vm1' |} e (inline_cmd inline_i c)
                    {| emem := m2; evm := vm2' |}.
      + move: H4 Hsub Heq Hc.
        set st1 := {| emem := m1; evm := vm1 |}; set st2:= {| emem := m2; evm := vm2 |}.
        rewrite (_:vm1 = evm st1) // (_:vm2 = evm st2) //.
        rewrite (_:m1 = emem st1) // (_:m2 = emem st2) //.   
        move: st1 st2 => {Hrec vm1 vm2 m1 m2} st1 st2.
        elim=> {Hsub2 st1 st2 e c} 
           [st e c He | [m1 vm1] [m2 vm2] [m3 vm3] e c He Hsc Hsw Hrec] /= 
           Hsub Heq Hc vm1' Hvm1.
        + exists vm1';split=> //;constructor.
          rewrite -He /=;symmetry.
          have /read_e_eq_on //: evm st =[read_e_rec e s1']  vm1'.
          by apply: eq_onI Hvm1;rewrite read_eE.
        have /= [] := Hc m1 m2 _ vm2 Hsc _ _ Heq vm1'. 
        + by apply: eq_onI Hvm1;SvD.fsetdec.
        move=> /= vm2' [Hvm2 Hsem2].
        case (Hrec Hsub Heq Hc vm2' Hvm2) => vm3' /= [Hvm3 Hsem3].
        exists vm3';split=> //;apply: EWhileOne Hsem3=> //.
        rewrite -He /=;symmetry.
        have /read_e_eq_on //: vm1 =[read_e_rec e s1']  vm1'.
        by apply: eq_onI Hvm1;rewrite read_eE.
      move=> Hw vm1' /Hw [vm2' [Hvm2 Hsem]];exists vm2';split.
      + by apply: eq_onI Hvm2;SvD.fsetdec.
      by apply sem_seq1;constructor.
    by move=> Hw vm1' Hvm1; apply: (Hrec s1 s2 _ _ Hw _ Hvm1);SvD.fsetdec.
  Qed.

  Let Hcall1 : forall ta tr x (f:fundef ta tr) a, Pc (fd_body f) -> Pi (Ccall x f a).
  Proof.
    move=> ta tr x fd a Hfc m1 m2 vm1 vm2 H;inversion H;clear H;subst=> /=.
    unfold rarg in * => {rarg}.
    inversion H5;clear H5;subst;inversion H7;clear H7.
    inversion H6;clear H6;subst;inversion H1;clear H1;subst.
    case Heq: sem_pexpr H3 H10 => [va /=|//] _ Hsem {fd2}.
    case:Hsem a x Hfc Heq=> {m1 m2 res va fd ta tr}.
    move=> ta tr m1 m2 vr fd;case:fd vr => /= {ta tr} ta tr fa fc fr vr va Hfc.
    move=> a x Hcf Heq /= s1 s2.
    case: ifP=> //= /andP [/andP[Hdisjx Hdisja] Hdisj].
    case Hcc: check_inline => [s'|] //=.
    case: ifP=> Hsub //= [] <- vm1' Hvm1.
    case: (Hfc vm1) => vm2 [Hsem Hvr] {Hfc}.
    move /SvD.F.subset_iff: Hsub => Hsub.
    case : (Hcf _ _ _ _ Hsem _ _ Hcc (write_rval vm1' fa va))=> [ | vm2' [Hvm2 Hsem2]].
    + by apply write_rval_eq_on;apply: eq_onI Hvm1; SvD.fsetdec.
    exists (write_rval vm2' x vr);split.
    + apply write_rval_eq_on; apply (@eq_onT _ _ vm2);last first.
      + by apply: eq_onI Hvm2;SvD.fsetdec.
      apply (@eq_onT _ _ (write_rval vm1 fa va)).
      + apply eq_onS;apply disjoint_eq_on.
        move: Hdisj;rewrite /disjoint /is_true !Sv.is_empty_spec write_c_recE.
        by SvD.fsetdec.
      have /= Hex := writeP Hsem. 
      move=> z Hin;rewrite Hex //.   
      by move: Hdisj;rewrite /disjoint /is_true !Sv.is_empty_spec write_c_recE;SvD.fsetdec.
    apply sem_app with {| emem := m1; evm := write_rval vm1' fa va |}.
    + apply assgn_tupleP=>//.
      rewrite <- Heq;apply read_e_eq_on with Sv.empty.
      by rewrite -/(read_e a);apply:eq_onS;apply: eq_onI Hvm1;SvD.fsetdec.
    apply (sem_app Hsem2);apply assgn_tupleP.
    + by rewrite /disjoint read_rval2pe.
    rewrite -(@read_e_eq_on _ (rval2pe fr) Sv.empty vm2 vm2');last first.
    + rewrite -/(read_e (rval2pe fr));apply: eq_onI Hvm2.
      by rewrite read_rval2pe;SvD.fsetdec.
    by rewrite Hvr sem_rval2pe.
  Qed.
  
  Lemma inlineP ta tr (fd:fundef ta tr) mem mem' va vr s: 
    sem_call mem fd va mem' vr ->
    check_inline_fd fd = Ok unit s ->
    sem_call mem (inline_fd fd) va mem' vr.
  Proof.
    rewrite /check_inline_fd=> H;inversion H;clear H;subst.
    inversion H0;clear H0;subst. 
    have -> /= : fd = FunDef (fd_arg fd) (fd_body fd) (fd_res fd) by case: (fd).
    move=> Hcc;constructor=> /= vm0.
    case: (H7 vm0) => vm2 [Hsem Hvr].
    case: 
      (cmd_rect1 Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall1 (fd_body fd)
                 _ _ _ _ Hsem _ _ Hcc (write_rval vm0 (fd_arg fd) va))
       => // vm2' [ Hvm2 Hsem'].
    exists vm2';split=> //. rewrite Hvr.
    have H: vm2 =[read_e_rec (rval2pe (fd_res fd)) Sv.empty]  vm2'.
    + by apply: eq_onI Hvm2;rewrite read_eE read_rval2pe;SvD.fsetdec.
    have := (@read_e_eq_on _ (rval2pe (fd_res fd)) Sv.empty vm2 vm2' H).
    by rewrite !sem_rval2pe => -[].
  Qed.

End PROOF.
