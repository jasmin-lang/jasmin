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
  | Rmem p              => fun e => [:: assgn (Rmem p) e]
  | Rpair t1 t2 rv1 rv2 => fun e => assgn_tuple rv2 (esnd e) ++ assgn_tuple rv1 (efst e)
  end.

Definition inline_cmd (inline_i: instr -> cmd) (c:cmd) := 
  List.fold_right (fun i c' => inline_i i ++ c') [::] c.

Fixpoint inline_i (i:instr) : cmd := 
  match i with
  | Cassgn _ _ _         => [::i]
  | Cif b c1 c2          => [::Cif b (inline_cmd inline_i c1) (inline_cmd inline_i c2)]
  | Cfor i rn c          => [::Cfor i rn (inline_cmd inline_i c)]
  | Cwhile e c           => [::Cwhile e (inline_cmd inline_i c)]
  | Ccall ta tr x fd arg => 
    match inline_fd fd in fundef sta str return pexpr sta -> rval str -> cmd with
    | FunDef sta str fa fc fr =>
      fun pe_arg rv_res => 
        assgn_tuple fa pe_arg ++ 
        (fc ++ assgn_tuple rv_res fr)
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

  Fixpoint loop (n:nat) (rx wx:Sv.t) (s:Sv.t) : result unit Sv.t :=
    match n with
    | O => Error tt
    | S n =>
      check_inline_c s >>=  (fun s' => 
      let s' := Sv.union rx (Sv.diff s' wx) in
      if Sv.subset s' s then Ok unit s 
      else loop n rx wx (Sv.union s s'))
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

Fixpoint check_inline_rv t (x:rval t) := 
  match x with
  | Rvar _ => true
  | Rmem _ => false
  | Rpair _ _ x1 x2 => check_inline_rv x1 && check_inline_rv x2
  end.

Definition check_inline_bcmd t (x:rval t) (e:pexpr t) s := 
  Ok unit (read_rv_rec x (read_e_rec e (Sv.diff s (vrv x)))).

Definition nb_loop := 100%coq_nat.
Opaque nb_loop.

Fixpoint check_inline_i (i:instr) (s:Sv.t) {struct i} : result unit Sv.t := 
  match i with
  | Cassgn t x e => check_inline_bcmd x e s
  | Cif b c1 c2 => 
    check_inline check_inline_i c1 s >>= (fun s1 => 
    check_inline check_inline_i c2 s >>= (fun s2 =>
    Ok unit (read_e_rec b (Sv.union s1 s2))))
  | Cfor x (dir, e1, e2) c =>
    loop (check_inline check_inline_i c) nb_loop (read_rv x) (vrv x) s >>= (fun s =>
    Ok unit (read_e_rec e1 (read_e_rec e2 s)))
  | Cwhile e c =>
    let re := read_e e in
    wloop (check_inline check_inline_i c) nb_loop re (Sv.union re s)  
  | Ccall ta tr x fd arg =>
    let p := fd_arg fd in
    let c := fd_body fd in
    let r := fd_res fd in
    let sx := vrv x in
    let sr := read_e r in
    let sa := read_e arg in
    let sp := vrv p in
    let s := Sv.diff s sx in  
    if check_inline_rv (fd_arg fd) && check_inline_rv x && 
       disjoint sx sr && disjoint sp sa && disjoint s (write_c_rec sp c) then
      check_inline check_inline_i c (Sv.union s sr) >>= (fun s' =>
        if Sv.subset s' (Sv.union s sp) then Ok unit (Sv.union s sa)
        else Error tt)    
    else Error tt
  end.

Definition check_inline_fd ta tr (fd:fundef ta tr) := 
  check_inline check_inline_i (fd_body fd) (read_e (fd_res fd)).
          
Section PROOF.
 
  Lemma check_rval2 s1 s2 t (x:rval t) vr:  
    check_inline_rv x ->
    rval2vval s1 x = Ok error vr ->
    rval2vval s2 x = Ok error vr.
  Proof.
    elim: x s1 s2 vr => [x | | t1 t2 x1 Hx1 x2 Hx2] //= s1 s2 vr /andP[H1 H2].
    case Heq1: (rval2vval _ x1) => [vr1|]//=.
    case Heq2: (rval2vval _ x2) => [vr2|]//= [] <-.
    by rewrite (Hx1 _ _ _ H1 Heq1) (Hx2 _ _ _ H2 Heq2).
  Qed.

  Lemma check_mem s1 s2 t (x:rval t) vx v: 
     check_inline_rv x -> 
     rval2vval s1 x = Ok error vx ->
     write_vval s1 vx v = Ok error s2 ->
     s1.(emem) = s2.(emem).
  Proof.
    elim: x s1 s2 vx v => [x | | t1 t2 x1 Hx1 x2 Hx2]//= s1 s2 vx v.
    + by move=> _ [] <- [] <-.
    move=> /andP[H1 H2];case Heq1: (rval2vval _ x1) => [rv1|]//=.
    case Heq2: (rval2vval _ x2) => [rv2|]//= [] <- /=.
    case Hw2: (write_vval s1 rv2 v.2) => [?|] //= Hw1.
    rewrite (Hx2 _ _ _ _ H2 Heq2 Hw2) (Hx1 _ _ _ _ H1 _  Hw1) //.
    by apply: check_rval2 Heq1.
  Qed.

  Lemma check_rv_empty t (x:rval t) : check_inline_rv x -> Sv.Empty (read_rv x).
  Proof.
    elim: x => //= [x _|?? x1 Hx1 x2 Hx2 /andP[] /Hx1 ? /Hx2 ?].
    + by rewrite /read_rv /=;SvD.fsetdec.
    by rewrite read_rv_pair;SvD.fsetdec.
  Qed.

  Lemma assgn_tupleP t v s s' (e:pexpr t) (x:rval t):
     check_inline_rv x ->
     disjoint (vrv x) (read_e e) ->  
     sem_pexpr s e = ok v ->
     write_rval s x v = ok s' ->
     sem s (assgn_tuple x e) s'.
  Proof.
    rewrite /write_rval;case Heq : rval2vval => [w|] //=.
    elim: x s s' e v w Heq => [x | p | ?? rv1 Hrv1 rv2 Hrv2] s s' e v w //=.
    + by move=> [] <- _ /= ? Heq [] <-;apply sem_seq1;constructor;rewrite Heq.
    case Heq1: (rval2vval s rv1) => [vr1|]//=.
    case Heq2: (rval2vval s rv2) => [vr2|]//= [] <- /andP [Hc1 Hc2] Hdisj /= He.
    case Hv2: write_vval => [s2|]//= Hv1.
    apply sem_app with s2.
    + apply: Hrv2 Hv2=>//;last by apply sem_esnd.
      move: Hdisj;rewrite /disjoint vrv_pair /is_true !Sv.is_empty_spec.
      by have := @read_e_esnd _ _ e;SvD.fsetdec.
    apply: Hrv1 Hv1=>//;first by apply: check_rval2 Heq1.
    + move: Hdisj;rewrite /disjoint vrv_pair /is_true !Sv.is_empty_spec.
      by have := @read_e_efst _ _ e;SvD.fsetdec.
    apply sem_efst.
    case: (s) (s2) Heq2 Hv2 (check_mem Hc2 Heq2 Hv2) He  => m vm [m' vm'] /= Heq2 Hv2 Heq;subst m'.
    rewrite /ok => Hs;rewrite -Hs;symmetry; apply (@read_e_eq_on _ e Sv.empty m vm vm').
    rewrite -/(read_e e).
    apply (@disjoint_eq_on (read_e e) _ rv2 {| emem := m; evm := vm |} {| emem := m; evm := vm' |} v.2).
    + by move: Hdisj;rewrite /disjoint vrv_pair /is_true !Sv.is_empty_spec;SvD.fsetdec.
    by rewrite /write_rval Heq2 /= Hv2.
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

  Let Hbcmd : forall t (x:rval t) e,  Pi (Cassgn x e).
  Proof. 
    move=> t x e m1 m2 vm1 vm2 H;sinversion H => /= s1 s2 [] <- vm1' Hvm.
    sinversion H5;sinversion H3;sinversion H4;move: H0.
    rewrite (@read_e_eq_on _ e (Sv.diff s2 (vrv x)) m1 vm1 vm1');last first.
    + by apply: eq_onI Hvm;rewrite read_rvE;SvD.fsetdec.
    case Hs: sem_pexpr => [ve|] //= Hw.
    have /(_ s2 vm1') [|vm3 [Hvm3 Hw3]]:= write_rval_eq_on Hw. 
    + by apply: eq_onI Hvm;rewrite !read_rvE read_eE;SvD.fsetdec.
    exists vm3;split=> //;apply sem_seq1;constructor;by rewrite Hs /= Hw3.
  Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 m1 m2 vm1 vm2 H;sinversion H.
    move=> s s3 /=.
    case Heq1 : (check_inline check_inline_i c1 s3) => [s1|//].
    case Heq2 : (check_inline check_inline_i c2 s3) => [s2|] //= [] <- vm1' Hr.
    case: cond H5 H6 => H5 H6.
    + have [] := Hc1 m1 m2 vm1 vm2 H6 _ _ Heq1 vm1'.
      + by apply: eq_onI Hr;rewrite read_eE;SvD.fsetdec.
      move=> vm2' [Heq' Hsem];exists vm2';split => //.
      by apply sem_seq1;apply Eif with true => //=; rewrite -(read_e_eq_on m1 Hr).
    have [] := Hc2 m1 m2 vm1 vm2 H6 _ _ Heq2 vm1'.
    + by apply: eq_onI Hr;rewrite read_eE;SvD.fsetdec.
    move=> vm2' [Heq' Hsem];exists vm2';split => //.
    by apply sem_seq1;apply Eif with false => //=; rewrite -(read_e_eq_on m1 Hr).
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
            Sv.Subset (Sv.union (read_rv i) (Sv.diff s1' (vrv i))) s2 ->
            forall vm1',  evm st1 =[s2]  vm1' ->
             exists vm2' : vmap, 
             evm st2 =[s2]  vm2' /\
             sem_for i [seq n2w i | i <- wrange dir vlow vhi]
                {| emem := emem st1; evm := vm1' |} (inline_cmd inline_i c)
                {| emem := emem st2; evm := vm2' |}.
      + move: st1 st2 => {Hrec H7 H8 H9 Hc Heq Hsub vm1 vm2 m1 m2} st1 st2.
        elim=> {st1 st2 c i} [s i c
                             | [m1 vm1] [m2 vm2] [m3 vm3] s0 i w ws c Hw Hsc Hsf Hrec] /=
            Heq Hc Hsub vm1' Hvm1.  
        + exists vm1';split=> //;constructor.
        have /(_ s1' vm1' ) [|vm4 [Hvm4 Hw4]]:= write_rval_eq_on Hw.
        + by apply: eq_onI Hvm1;rewrite read_rvE;SvD.fsetdec.
        have [vm2' [Hvm2 Hsem2]] := Hc _ _ _ _ Hsc _ _ Heq vm4 Hvm4.
        elim (Hrec Heq Hc Hsub vm2' Hvm2) => vm3' /= [Hvm3 Hsem3].
        by exists vm3';split=> //; apply: EForOne Hsem3;eauto.
      move=> /(_ H9 Heq Hc Hsub) H vm1' Hvm1;case: (H vm1').
      + by apply: eq_onI Hvm1;rewrite !read_eE;SvD.fsetdec.
      move=> vm2' [Hvm2 Hsem];exists vm2';split => //.
      apply sem_seq1;apply EFor with vlow vhi => //=.
      + by rewrite -(read_e_eq_on m1 Hvm1).
      have Hvm: evm st1 =[read_e_rec hi s2]  vm1'.
      + by apply: eq_onI Hvm1;rewrite (read_eE low);SvD.fsetdec.
      by rewrite -(read_e_eq_on m1 Hvm).
    have := Hrec _ (Sv.union s2 (Sv.union (read_rv i) (Sv.diff s1' (vrv i)))).
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
           [[m vm] e c He | [m1 vm1] [m2 vm2] [m3 vm3] e c He Hsc Hsw Hrec] /= 
           Hsub Heq Hc vm1' Hvm1.
        + exists vm1';split=> //;constructor.
          rewrite -He /=;symmetry.
          have /read_e_eq_on //: vm =[read_e_rec e s1']  vm1'.
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

  Fixpoint set_empty (t:stype) : st2ty t -> st2ty t := 
    match t return st2ty t -> st2ty t with
    | sword => fun w => w
    | sbool => fun b => b
    | sprod t1 t2 => fun v => (@set_empty t1 v.1, @set_empty t2 v.2)
    | sarr n => fun v => Array.empty n
    end.
    
  Lemma all_empty_arr_set vm : 
    all_empty_arr (Fv.empty (fun x0 : var => set_empty vm.[x0])).
  Proof. by move=> x;rewrite Fv.get0; elim: (vtype x) (vm.[x])=> //=. Qed.

  Lemma vm_uincl_set vm : 
    vm_uincl (Fv.empty (fun x0 : var => set_empty vm.[x0])) vm.
  Proof.
    move=> x;rewrite Fv.get0;elim: (vtype x) (vm.[x])=> //=. 
    by move=> ? t i v;rewrite /Array.empty /Array.get;case:ifP.
  Qed.

  Let Hcall1 : forall ta tr x (f:fundef ta tr) a, Pc (fd_body f) -> Pi (Ccall x f a).
  Proof.
    move=> ta tr x fd a Hfc m1 m2 vm1 vm2 H;sinversion H=> /=.
    unfold rarg in * => {rarg}. sinversion H2;sinversion H6;sinversion H5;sinversion H0.
    case Heq: sem_pexpr H9 H7 H8 => [va /=|//] Hwx _ Hsem {fd2}.
    sinversion Hsem;sinversion H.
    case: fd a x va res Heq Hwx H7 H5 Hfc => /= {ta tr} ta tr fa fc fr a x va res.
    move=> Ha Hres Hfull Hfc Hc /= s1 s2.
    case: ifP=> //= /andP[]/andP[]/andP[]/andP[] cia cix Hdisjx Hdisja Hdisj.
    case Hcc: check_inline => [s'|] //=.
    case: ifP=> Hsub //= [] <- vm1' Hvm1.
    case: (Hfc _ (all_empty_arr_set vm1)).
    move=> [m3 vm3] [vm3' [Hwa Hsem3 Heq3]].
    have Hu1 := vm_uincl_set vm1.
    have /(_ _ Hu1) [vm4 /= [Hw4 Hu4]] := write_uincl _ (val_uincl_refl va) Hwa.
    have /(_ _ Hu4) [vm5 /=[Hsem5 Hu5]]:= sem_uincl _ Hsem3.
    move /SvD.F.subset_iff: Hsub => Hsub.
    have  /(_ s' vm1') [|vm6 /= [Hvm6 Hw6]]:= write_rval_eq_on Hw4.
    + by apply: eq_onI Hvm1;rewrite read_rvE; have := check_rv_empty cia;SvD.fsetdec.
    have [vm7 [Hvm7 Hsem7]] := Hc _ _ _ _ Hsem5 _ _ Hcc _ Hvm6.
    have := write_rval_eq_on Hres.
    move=> /(_ s2 vm7) [].
    + apply eq_onI with  (Sv.diff s2 (vrv x)).
      + by rewrite read_rvE;have := check_rv_empty cix;SvD.fsetdec.
      apply:(@eq_onT _ _ vm5); last by apply: eq_onI Hvm7;SvD.fsetdec.
      apply: (@eq_onT _ _ vm4).
      + apply: (disjoint_eq_on _ Hw4);move: Hdisj.
        by rewrite /disjoint write_c_recE /is_true !Sv.is_empty_spec;SvD.fsetdec.
      have /= Hex := writeP Hsem5.
      move=> z Hin;rewrite Hex //.   
      by move: Hdisj;rewrite /disjoint /is_true !Sv.is_empty_spec write_c_recE;SvD.fsetdec.
    move=> vm8 [Hvm8 Hw8];exists vm8;split=>//.
    apply sem_app with {| emem := m3; evm := vm6 |}.
    + eapply assgn_tupleP;eauto. 
      rewrite /ok - Ha;apply read_e_eq_on with Sv.empty.
      by rewrite -/(read_e a);apply:eq_onS;apply: eq_onI Hvm1;SvD.fsetdec.  
    apply (sem_app Hsem7);eapply assgn_tupleP;eauto.
    have /(_ _ Hu5) /= [res' [Hres' Hures]] := sem_expr_uincl _ Heq3.
    have ? := is_full_array_uincl Hfull Hures;subst res';rewrite -Hres';symmetry.
    apply read_e_eq_on with (Sv.diff s2 (vrv x)).
    by apply: eq_onI Hvm7;rewrite read_eE;SvD.fsetdec.
  Qed.
  
  Lemma inlineP ta tr (fd:fundef ta tr) mem mem' va vr s: 
    sem_call mem fd va mem' vr ->
    check_inline_fd fd = Ok unit s ->
    sem_call mem (inline_fd fd) va mem' vr.
  Proof.
    rewrite /check_inline_fd=> H;sinversion H;sinversion H0.
    have -> /= : fd = FunDef (fd_arg fd) (fd_body fd) (fd_res fd) by case: (fd).
    move=> Hcc;constructor=> //= vm0 Hvm0.
    case: (H6 vm0 Hvm0) => -[m2 vm2] [vm3 [Hw Hsem]].
    case: 
      (cmd_rect1 Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall1 (fd_body fd)
                 _ _ _ _ Hsem _ _ Hcc vm2) => // vm2' [Hvm2 Hsem' Hvr].
    exists {| emem := m2; evm := vm2 |}, vm2';split=>//.
    rewrite -Hvr;symmetry;apply read_e_eq_on with Sv.empty.
    apply: eq_onI Hvm2; rewrite read_eE;SvD.fsetdec.
  Qed.

End PROOF.
