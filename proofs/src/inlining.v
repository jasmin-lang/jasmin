(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr 
               memory dmasm_sem compiler_util allocation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

(* ** inlining
 * -------------------------------------------------------------------- *)

Definition assgn_tuple iinfo (xs:rvals) (es:pexprs) :=
  let assgn xe := MkI iinfo (Cassgn xe.1 AT_rename xe.2) in
  map assgn (zip xs es).

Definition depend x e s :=
  read_rv_rec (read_e_rec s e) x.

Definition depends xs es s :=
  read_rvs_rec (read_es_rec s es) xs.

Definition inline_c (inline_i: instr -> Sv.t -> ciexec (Sv.t * cmd)) c s := 
  foldr (fun i r =>
    Let r := r in
    Let ri := inline_i i r.1 in
    ciok (ri.1, ri.2 ++ r.2)) (ciok (s,[::])) c.

Definition check_rename iinfo f fd1 fd2 (s:Sv.t) := 
  Let _ := add_infun iinfo (CheckAllocReg.check_fundef (f,fd1) (f,fd2) tt) in
  let s2 := read_es (map Pvar fd2.(f_res)) in
  let s2 := read_c_rec s2 fd2.(f_body) in
  let s2 := write_c_rec s2 fd2.(f_body) in
  let s2 := vrvs_rec s2 (map Rvar fd2.(f_res)) in
  if disjoint s s2 then ciok tt 
  else cierror iinfo (Cerr_inline s s2).

Definition get_fun (p:prog) iinfo (f:funname) :=
  match get_fundef p f with
  | Some fd => ciok fd 
  | None    => cierror iinfo (Cerr_unknown_fun f "inlining")
  end.

Section INLINE.

Variable rename_fd : fundef -> fundef.

Fixpoint inline_i (p:prog) (i:instr) (s:Sv.t) : ciexec (Sv.t * cmd) := 
  match i with
  | MkI iinfo ir =>
    match ir with 
    | Cassgn x t e => ciok (depend x e s, [::i])
    | Copn xs o es => ciok (depends xs es s, [::i])
    | Cif e c1 c2  =>
      Let c1 := inline_c (inline_i p) c1 s in
      Let c2 := inline_c (inline_i p) c2 s in
      ciok (read_e_rec (Sv.union c1.1 c2.1) e, [::MkI iinfo (Cif e c1.2 c2.2)])
    | Cfor x (d,lo,hi) c =>
      Let c := inline_c (inline_i p) c s in
      let r := read_e_rec (read_e_rec (Sv.add x c.1) lo) hi in
      ciok (r, [::MkI iinfo (Cfor x (d, lo, hi) c.2)])
    | Cwhile e c =>
      Let c := inline_c (inline_i p) c s in
      let s := read_e_rec c.1 e in
      ciok (s, [::MkI iinfo (Cwhile e c.2)])
    | Ccall inline xs f es =>
      if inline is InlineFun then
        Let fd := get_fun p iinfo f in 
        let fd' := rename_fd fd in
        Let _ := check_rename iinfo f fd fd' s in
        ciok (s,  assgn_tuple iinfo (map Rvar fd'.(f_params)) es ++ 
                  (fd'.(f_body) ++ assgn_tuple iinfo xs (map Pvar fd'.(f_res))))
      else ciok (depends xs es s, [::i])        
    end
  end.
  
Definition inline_fd (ffd:funname * fundef) (p:cfexec prog) :=
  Let p := p in
  match ffd with 
  | (f, MkFun ii params c res) =>
    let s := read_es (map Pvar res) in
    Let c := add_finfo f f (inline_c (inline_i p) c s) in 
    cfok ((f, MkFun ii params c.2 res)::p)
  end.

Definition inline_prog (p:prog) := foldr inline_fd (cfok [::]) p.

(*          
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
*)

End INLINE.
