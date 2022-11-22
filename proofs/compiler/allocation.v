(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import psem.
Require Import compiler_util ZArith.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

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

  Parameter check_e : pexpr -> pexpr -> M.t -> cexec (M.t * leak_e_tr).

  Parameter check_lval : option (stype * pexpr) -> lval -> lval -> M.t -> cexec (M.t * leak_e_tr).

  Parameter eq_alloc : M.t -> vmap -> vmap -> Prop.

  Parameter eq_alloc_empty : eq_alloc M.empty vmap0 vmap0.

  Parameter eq_alloc_incl : forall r1 r2 vm vm',
    M.incl r2 r1 ->
    eq_alloc r1 vm vm' ->
    eq_alloc r2 vm vm'.

  Section Section.
  Context {LO:LeakOp}.

  Parameter check_eP : forall gd e1 e2 r re lte vm1 vm2 stk,
    check_e e1 e2 r = ok (re, lte) ->
    eq_alloc r vm1 vm2 ->
    eq_alloc re vm1 vm2 /\
    forall m v1 l1,  sem_pexpr gd (Estate m vm1) e1 = ok (v1, l1) ->
                     exists v2, sem_pexpr gd (Estate m vm2) e2 = ok (v2, leak_E stk lte l1) /\ value_uincl v1 v2.

  Parameter check_lvalP : forall gd r1 r1' ltr1' x1 x2 e2 s1 s1' l1' vm1 v1 v2 stk,
    check_lval e2 x1 x2 r1 = ok (r1', ltr1') ->
    eq_alloc r1 s1.(evm) vm1 ->
    value_uincl v1 v2 ->
    oapp (fun te2 =>
            Let vl := sem_pexpr gd (Estate s1.(emem) vm1) te2.2 in
            truncate_val te2.1 vl.1 = ok v2) true e2 ->
        (*sem_pexpr gd (Estate s1.(emem) vm1) te2.2 >>= truncate_val te2.1 = ok v2) true e2 ->*)
    write_lval gd x1 v1 s1 = ok (s1', l1') ->
    exists vm1',
      write_lval gd x2 v2 (Estate s1.(emem) vm1) = ok (Estate s1'.(emem) vm1', leak_E stk ltr1' l1') /\
      eq_alloc r1' s1'.(evm) vm1'.
  End Section.

End CheckB.

Definition salloc : string := "allocation".

Module MakeCheckAlloc (C:CheckB).

Import C.

Section LOOP.

  Variable ii:instr_info.
  Variable check_c : M.t -> ciexec (M.t * leak_c_tr).

  Fixpoint loop (n:nat) (m:M.t) : ciexec (M.t * leak_c_tr) :=
    match n with
    | O => cierror ii (Cerr_Loop "allocation")
    | S n =>
      Let m' := check_c m in
      if M.incl m m'.1 then ok (m, m'.2)
      else loop n (M.merge m m'.1)
    end.

  Variable A : Type.
  Variable check_c2 : M.t -> ciexec (M.t * M.t * A).
  
  Fixpoint loop2 (n:nat) (m:M.t) :=
    match n with
    | O => cierror ii (Cerr_Loop "allocation")
    | S n =>
      Let rc := check_c2 m in
      let: (m', m'', ltm') := rc in 
      if M.incl m m'' then ok (m', ltm')
      else loop2 n (M.merge m m'')
    end.

End LOOP.

Definition check_e_error := Cerr_fold2 "allocation:check_e".

Definition cmd2_error := Cerr_fold2 "allocation:check_cmd".

Fixpoint check_es es1 es2 r : cexec (M.t * seq leak_e_tr) :=
  match es1, es2 with
  | [::], [::] => ok (r, [::])
  | e::es, e'::es' =>
    Let ce := check_e e e' r in
    Let ces := check_es es es' ce.1 in 
    ok (ces.1, ce.2::ces.2)
  | _, _ => cerror check_e_error                
  end.

Fixpoint check_lvals ls1 ls2 r : cexec (M.t * seq leak_e_tr) :=
  match ls1, ls2 with
  | [::], [::] => ok (r, [::])
  | l::ls, l'::ls' =>
    Let lv := check_lval None l l' r in
    Let lvs := check_lvals ls ls' lv.1 in 
    ok (lvs.1, lv.2::lvs.2)
  | _, _ => cerror check_e_error                
  end.

Definition check_var x1 x2 r := check_lval None (Lvar x1) (Lvar x2) r.

Definition check_vars xs1 xs2 r := check_lvals (map Lvar xs1) (map Lvar xs2) r.

Section CMD.

Context (check_I : instr -> instr -> M.t -> ciexec (M.t * leak_i_tr)).
Fixpoint check_c (ii: instr_info) (c1 c2 : cmd) (r:M.t) : ciexec (M.t * seq leak_i_tr) := 
  match c1, c2 with 
  | [::], [::] => ok (r, [::])
  | i1::c1, i2::c2 => 
    Let rli := check_I i1 i2 r in
    Let rlc := check_c ii c1 c2 rli.1 in
    ok (rlc.1, rli.2 :: rlc.2)
  | _, _ => Error (ii, cmd2_error)
  end.

End CMD.

Fixpoint check_i iinfo i1 i2 r : ciexec (M.t * leak_i_tr) :=
  match i1, i2 with
  | Cassgn x1 _ ty1 e1, Cassgn x2 _ ty2 e2 =>
    if ty1 == ty2 then
      Let res := add_iinfo iinfo (check_e e1 e2 r) in
      Let rls := add_iinfo iinfo (check_lval (Some (ty2, e2)) x1 x2 res.1) in 
      ciok (rls.1, LT_ile (LT_map [:: res.2 ; rls.2]))                  
    else cierror iinfo (Cerr_neqty ty1 ty2 salloc)
  | Copn xs1 _ o1 es1, Copn xs2 _ o2 es2 =>
    if o1 == o2 then
      Let res := add_iinfo iinfo (check_es es1 es2 r) in
      Let rls := add_iinfo iinfo (check_lvals xs1 xs2 res.1) in
      ciok (rls.1, LT_ile (LT_map [:: LT_map res.2 ; LT_id; LT_map rls.2]))
      (*add_iinfo iinfo (check_es es1 es2 r >>= check_lvals xs1 xs2)*)
    else cierror iinfo (Cerr_neqop o1 o2 salloc)
  | Ccall _ x1 f1 arg1, Ccall _ x2 f2 arg2 =>
    if f1 == f2 then
      Let res := add_iinfo iinfo (check_es arg1 arg2 r) in
      Let rls := add_iinfo iinfo (check_lvals x1 x2 res.1) in 
      ciok (rls.1, (LT_icall f2 (LT_map res.2) (LT_map rls.2)))
    else cierror iinfo (Cerr_neqfun f1 f2 salloc)
  | Cif e1 c11 c12, Cif e2 c21 c22 =>
    Let res := add_iinfo iinfo (check_e e1 e2 r) in
    Let r1 := check_c check_I iinfo c11 c21 res.1 in 
    Let r2 := check_c check_I iinfo c12 c22 res.1 in 
    ok (M.merge r1.1 r2.1, LT_icond res.2 r1.2 r2.2)
  | Cfor x1 (d1,lo1,hi1) c1, Cfor x2 (d2,lo2,hi2) c2 =>
    if d1 == d2 then
      Let rlo := add_iinfo iinfo (check_e lo1 lo2 r) in
      Let rhi := add_iinfo iinfo (check_e hi1 hi2 rlo.1) in 
      let check_c r :=
        Let r' := add_iinfo iinfo (check_var x1 x2 r) in
        check_c check_I iinfo c1 c2 r'.1 in
      Let res := loop iinfo check_c Loop.nb rhi.1 in
      ok (res.1, LT_ifor (LT_map [:: rlo.2; rhi.2]) res.2)
    else cierror iinfo (Cerr_neqdir salloc)
  | Cwhile a1 c1 e1 c1', Cwhile a2 c2 e2 c2' =>
    let check_c r :=
      Let rc := check_c check_I iinfo c1 c2 r in
      Let re := add_iinfo iinfo (check_e e1 e2 rc.1) in
      Let rc' := check_c check_I iinfo c1' c2' re.1 in 
      ok (re.1, rc'.1, (rc.2, re.2, rc'.2)) in
    Let r := loop2 iinfo check_c Loop.nb r in
    let: (r, (ltc, lte, ltc')) := r in
    ok (r, LT_iwhile ltc lte ltc')

  | _, _ => cierror iinfo (Cerr_neqinstr i1 i2 salloc)
  end

with check_I i1 i2 r :=
  match i1, i2 with
  | MkI _ i1, MkI ii i2 => check_i ii i1 i2 r
  end.

Definition check_cmd iinfo c1 c2 r := check_c check_I iinfo c1 c2 r.

Definition check_fundef (f1 f2: funname * fundef):=
  let (f1,fd1) := f1 in
  let (f2,fd2) := f2 in
  if (f1 == f2) && (fd1.(f_tyin) == fd2.(f_tyin)) && (fd1.(f_tyout) == fd2.(f_tyout)) then
    add_finfo f1 f2 (
    Let rvs := add_iinfo fd1.(f_iinfo) (check_vars fd1.(f_params) fd2.(f_params) M.empty) in
    Let rcs := check_cmd fd1.(f_iinfo) fd1.(f_body) fd2.(f_body) rvs.1 in
    let es1 := map Pvar fd1.(f_res) in
    let es2 := map Pvar fd2.(f_res) in
    Let res := add_iinfo fd1.(f_iinfo) (check_es es1 es2 rcs.1) in
    ok (f1, rcs.2))
  else cferror (Ferr_neqfun f1 f2).


Definition check_fundefs fs1 fs2: cfexec leak_f_tr := mapM2 Ferr_uniqfun check_fundef fs1 fs2.

Definition check_prog_aux prog1 prog2 := check_fundefs (p_funcs prog1) (p_funcs prog2). 

Definition check_prog prog1 prog2 :=
  if prog1.(p_globs) == prog2.(p_globs) then check_prog_aux prog1 prog2
  else cferror Ferr_glob_neq.

Lemma check_lvalsP {LO:LeakOp} gd xs1 xs2 vs1 vs2 r1 r2 lts s1 s2 l2 vm1 stk:
  check_lvals xs1 xs2 r1 = ok (r2, lts) ->
  eq_alloc r1 s1.(evm) vm1 ->
  List.Forall2 value_uincl vs1 vs2 ->
  write_lvals gd s1 xs1 vs1 = ok (s2, l2) ->
  exists vm2,
    write_lvals gd (Estate s1.(emem) vm1) xs2 vs2 =
    ok (Estate s2.(emem) vm2, map2 (leak_E stk) lts l2) /\
    eq_alloc r2 s2.(evm) vm2.
Proof.
  elim: xs1 xs2 vs1 vs2 r1 r2 lts s1 s2 l2 vm1=> 
  [ | x1 xs1 Hrec] [ | x2 xs2] //= vs1 vs2 r1 r2 lts s1 s2 l2 vm1.
  + by move=> [] <- <- /= Hvm1 [] //= [] <- hl; exists vm1.
  t_xrbindP. move=> [m1 lt1] hce [m2 lt2] /= hcs <- <- /= Hvm1 [] //= vs1' vs2' l l' Hv Hvs.
  t_xrbindP. move=> [s1' lt1'] Hw [s2' lt2'] /= Hws <- <-.
  have  [ //| vm3 [->/= Hvm3]] := check_lvalP (e2:= None) stk hce Hvm1 Hv _ Hw.
  move: (Hrec xs2 l l' m1 m2 lt2 s1' s2' lt2' vm3 hcs Hvm3 Hvs Hws).
  move=> [] vm3' [] Hws'. rewrite Hws' /=. move=> Hvm3'. by exists vm3'.
Qed.

Section PROOF.

  Context {LO:LeakOp}.

  Variable p1 p2:prog.
  Variable Fs: seq (funname * seq leak_i_tr).
  Notation gd := (p_globs p1).
  Variable stk : pointer.
  Hypothesis eq_globs : p_globs p1 = p_globs p2.

  Let Pi_r s1 (i1:instr_r) li s2:=
    forall ii r1 i2 r2 lti vm1, eq_alloc r1 (evm s1) vm1 ->
    check_i ii i1 i2 r1 = ok (r2, lti) ->
    exists vm2, eq_alloc r2 (evm s2) vm2 /\
                sem p2 (Estate (emem s1) vm1) [:: MkI ii i2] (leak_I (leak_Fun Fs) stk li lti)
                                                         (Estate (emem s2) vm2).

  Let Pi s1 (i1:instr) li s2:=
     forall r1 i2 r2 lti vm1, eq_alloc r1 (evm s1) vm1 ->
     check_I i1 i2 r1 = ok (r2, lti) ->
      exists vm2, eq_alloc r2 (evm s2) vm2 /\
                sem p2 (Estate (emem s1) vm1) [:: i2] (leak_I (leak_Fun Fs) stk li lti)
                                                          (Estate (emem s2) vm2).
  Let Pc s1 (c1:cmd) lc s2:=
    forall ii r1 c2 r2 ltc vm1, eq_alloc r1 (evm s1) vm1 ->
    check_cmd ii c1 c2 r1 = ok (r2, ltc) ->
    exists vm2, eq_alloc r2 (evm s2) vm2 /\
      sem p2 (Estate (emem s1) vm1) c2 (leak_Is (leak_I (leak_Fun Fs)) stk ltc lc) (Estate (emem s2) vm2).

  Let Pfor (i1:var_i) vs s1 c1 lf s2:=
    forall i2 ii r1 r1' ltv c2 r2 ltf vm1, eq_alloc r1 (evm s1) vm1 ->
    check_var i1 i2 r1 = ok (r1', ltv) ->
    check_cmd ii c1 c2 r1' = ok (r2, ltf) -> M.incl r1 r2 ->
    exists vm2, eq_alloc r1 (evm s2) vm2 /\
                sem_for p2 i2 vs (Estate (emem s1) vm1) c2 (leak_Iss (leak_I (leak_Fun Fs)) stk ltf lf)
                        (Estate (emem s2) vm2).

  Let Pfun m fn vargs1 lf m' vres:=
    forall vargs2, List.Forall2 value_uincl vargs1 vargs2 ->
    exists vres',
       sem_call p2 m fn vargs2 (lf.1, (leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs lf.1) lf.2)) m' vres' /\
       List.Forall2 value_uincl vres vres'.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    move=> s ii r1 [ | ??] //= r2 ltc vm1 Heq [] Hr.
    rewrite Hr in Heq. rewrite /= in Heq.
    exists vm1. split=> //; constructor.
  Qed.

  Local Lemma Hcons : sem_Ind_cons p1 Pc Pi.
  Proof.
    move=> s1 s2 s3 i c li lc Hsi Hi Hsc Hc ii r1 [ | i2 c2] //= r2 lt vm1 Hvm1.
    t_xrbindP => -[ri lti] /Hi -/(_ _ Hvm1) [vm2 [Hvm2 hsi]].
    move=> [rc ltc] /Hc -/(_ _ Hvm2) [vm3 [Hvm3 hsc]] /= ??; subst r2 lt.
    exists vm3; split => //=. 
    apply: (sem_app hsi hsc).
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p1 Pi_r Pi.
  Proof.
    move=> ii i s1 s2 li Hsi Hi r1 [i2i i2] r2 lti vm1 /Hi Hvm /= /Hvm [vm2 [Hvm2 Hsc]].
    by exists vm2;split=>//;constructor.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn p1 Pi_r.
  Proof.
    move => s1 s2 x tag ty e v v' le lw.
    case: s1 => sm1 svm1 He Htr Hw ii r1 [] //= x2 tag2 ty2 e2 r2 lti vm1 Hvm1.
    case: eqP => // <- {ty2}. t_xrbindP. move=> [re lte]. apply: add_iinfoP.
    move=> /check_eP Hce [rv ltv]. apply: add_iinfoP. move=>Hcv [] <- <-. 
    move: (Hce gd svm1 vm1 stk Hvm1). move=> [] Hvm2 He'. move: (He' sm1 v le He).
    move=> [] v'' [] {He'} He' Hv. move: truncate_value_uincl.
    move=> Ht. move: (Ht ty v v'' v' Hv Htr). move=> [] v''' Htr' {Ht} Hv'.

    move: (@check_lvalP LO) => Hcv'.
    move: (Hcv' gd re rv ltv x x2 (Some (ty, e2)) {|emem := sm1; evm := svm1|}
                s2 lw vm1 v' v''' stk Hcv Hvm2 Hv').
    move=> /= {Hcv'}. rewrite He' /=. move=> H. move: (H Htr' Hw). move=> {H} [] vm2 [] Hcv' Hvm3.
    exists vm2. split=> // /=; apply sem_seq1; econstructor. econstructor. replace (p_globs p2) with gd.
    auto. auto. replace (p_globs p2) with gd. apply He'. apply Htr'.
     replace (p_globs p2) with gd. apply Hcv'.
  Qed.

  Lemma check_esP e1 e2 r re lte s vm:
    check_es e1 e2 r = ok (re, lte) ->
    eq_alloc r s.(evm) vm ->
    eq_alloc re s.(evm) vm /\
    forall vs,  sem_pexprs gd s e1 = ok vs ->
    exists vs', sem_pexprs (p_globs p2) (Estate s.(emem) vm) e2 = ok vs' /\
               List.Forall2 value_uincl (unzip1 vs) (unzip1 vs') /\
               unzip2 vs' = map2 (leak_E stk) lte (unzip2 vs).
  Proof.
    rewrite -eq_globs;case: s => sm svm.
    rewrite /check_es; elim: e1 e2 r re [::] lte => [ | e1 es1 Hrec] [ | e2 es2] r re lte1 lte2 //=.
    + move=> [] <- <- Hvm. split=> // -[] //= ?; exists [::]. split. auto. split=> //.
      rewrite /=. constructor. rewrite /=. case: lte1. constructor. constructor.
    t_xrbindP. move=> [re' lte'] /(check_eP gd) /= He [rh lth] Hce <- <- Hvm /=.
    move: (He svm vm stk Hvm). move=> {He} [] Hvm2 He. split.
    move: (Hrec es2 re' rh lte1 lth Hce Hvm2). move=> [] Hvm3 Hrec'. apply Hvm3.
    move: (Hrec es2 re' rh lte1 lth Hce Hvm2). move=> [] Hvm3 Hrec'.
    t_xrbindP. move=> vs [ve le] He' vs' Hes <- /=. move: (He sm ve le He'). move=> [] ve' [] -> Hv /=.
    move: (Hrec' vs' Hes). move=> [] vs'' [] -> [] Hvs1 Hvs2 /=. exists ((ve', leak_E stk lte' le) :: vs''). split=> //.
    split. rewrite /=. apply List.Forall2_cons; auto. by rewrite /= Hvs2.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p1 Pi_r.
  Proof.
    move => s1 s2 t o xs es lo. rewrite /sem_sopn.
    t_xrbindP. move=> ves Hes [vo lo'] Hex [vw vl] Hws <- <- /=.
    rewrite /Pi_r. move=> ii r1 [] //= xs1 t' o1 es1 r2 lti vm1 Hvm1.
    case: ifPn => //= /eqP <-. t_xrbindP. move=> [yv yl]. apply: add_iinfoP.
    move=> Hces [rv ltv]. apply: add_iinfoP. move=> Hcvs [] <- <-.
    move: check_esP. move=> Hces'. move: (Hces' es es1 r1 yv yl s1 vm1 Hces Hvm1).
    move=> {Hces'} [] Hvm2 Hes'. move: (Hes' ves Hes). move=> {Hes} [] ves' [] Hes [] Hvs Hls.
    move: (@check_lvalsP LO). move=> Hcvs'.
    move: (@vuincl_exec_opn LO). move=> Hex'. move: (Hex' o (unzip1 ves) (unzip1 ves') (vo, lo') Hvs Hex).
    move=> [] [vo' lo''] [] {Hex'} Hex' /= [Hvo ->].
    move: (Hcvs' gd xs xs1 vo vo' yv rv ltv s1 vw vl vm1 stk Hcvs Hvm2 Hvo Hws).
    move=> {Hcvs'} [] vm2 [] Hws' Hvm3. exists vm2; split=> //; apply sem_seq1. econstructor. econstructor.
    rewrite /sem_sopn Hes /= Hex' /=. 
    replace (p_globs p2) with gd. 
    by rewrite Hws' /= Hls.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p1 Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 le lc.
    case: s1 => sm1 svm1 Hve Hc Hc1 ii r1 [] //= e' c1' c2' r2 lti vm1 /= Hvm1.
    t_xrbindP. move=> [re lte]. apply: add_iinfoP. move=> /check_eP  -/(_ gd _ _ stk Hvm1) [] Hr1'.
    move=> /(_ _ _ _ Hve) [ve' [Hve' /value_uincl_bool1 ?]];subst ve'.
    move=> [r3 lt3] Hr3;move => [r4 lt4] Hr4 <- <-. rewrite /Pc in Hc1. rewrite /= in Hc1.
    have [vm2 [Hvm2 Hsem]]:= Hc1 ii re _ r3 lt3 _ Hr1' Hr3;exists vm2;split.
    + rewrite /=. apply eq_alloc_incl with r3. apply M.merge_incl_l. auto. apply sem_seq1.
    econstructor. econstructor. replace (p_globs p2) with gd.
    auto. apply Hsem.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p1 Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 le lc.
    case: s1 => sm1 svm1 Hve Hc Hc1 ii r1 [] //= e' c1' c2' r2 lti vm1 /= Hvm1.
    t_xrbindP. move=> [re lte]. apply: add_iinfoP. move=> /check_eP  -/(_ gd _ _ stk Hvm1) [] Hr1'.
    move=> /(_ _ _ _ Hve) [ve' [Hve' /value_uincl_bool1 ?]];subst ve'.
    move=> [r3 lt3] Hr3;move => [r4 lt4] Hr4 <- <-. rewrite /Pc in Hc1. rewrite /= in Hc1.
    have [vm2 [Hvm2 Hsem]]:= Hc1 ii re _ r4 lt4 _ Hr1' Hr4;exists vm2;split.
    + rewrite /=. apply eq_alloc_incl with r4. apply M.merge_incl_r. auto. apply sem_seq1.
    econstructor. econstructor. replace (p_globs p2) with gd.
    auto. apply Hsem.
  Qed.

  Local Lemma loop2P ii check_c n r1 r2 (ltc: leak_c_tr) (lte: leak_e_tr) (ltc': leak_c_tr):
    loop2 ii check_c n r1 = ok (r2, (ltc, lte, ltc')) ->
      exists r2' r3,
      [/\ check_c r2' = ok (r2, r3, (ltc, lte, ltc')), M.incl r2' r1 & M.incl r2' r3].
  Proof.
    elim: n r1 r2 ltc lte ltc'=> //= n Hrec r1 r2 ltc lte ltc'.
    t_xrbindP. move=> -[[r2_1 r2_2] [[lt1 lt2] lt3]]. case:ifPn.
    + move=> h hc [] <- <- <- <-. exists r1. exists r2_2.
      split=> //. apply M.incl_refl.
    move=> h1 h2 h3. move: (Hrec (M.merge r1 r2_2) r2 ltc lte ltc' h3).
    move=> [] r1' [] r3' [] h2' h1' h2''. exists r1'. exists r3'.
    split=> //. apply: (M.incl_trans h1'); apply M.merge_incl_l.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p1 Pc Pi_r.
  Proof.
    move => s1 s2 s3 s4 a c e c' lc le lc' li.
    case: s2 => sm2 svm2 Hci Hc Hse Hci' Hc' Hwi Hw ii r1 [] //= a2 c2 e1 c2' r2 lti vm1 Hvm1.
    t_xrbindP. move=> [r [[ltc lte] ltc']] /loop2P.
    move=> [] r1' [] r2' [].
    t_xrbindP. move=> [ri ltci] Hi [re lte']. apply: add_iinfoP.
    move=> He [ri' ltci'] Hi' <- <- /= hl /= hl1 /= hl2 hi hi' <- <- /=.
    move: eq_alloc_incl. move=> Hq. move: (Hq r1 r1' (evm s1) vm1 hi Hvm1).
    move=> {Hq} Hvm1'. rewrite /Pc in Hc.
    move: (Hc ii r1' c2 ri ltci vm1 Hvm1' Hi).
    move=> [] vm2 [] Hvm2 /= Hc1 {Hc}.
    move: (@check_eP LO). move=> Hce. move: (Hce gd e e1 ri re lte' svm2 vm2 stk He Hvm2). 
    move=> {Hce} [] Hvme He'. rewrite /Pc in Hc'.
    move: (Hc' ii re c2' ri' ltci' vm2 Hvme Hi').
    move=> {Hc'} [] vm3 [] Hvm3 Hc1'.
    move: eq_alloc_incl. move=> Hq. move: (Hq ri' r1' (evm s3) vm3 hi' Hvm3).
    move=> {Hq} Hvm4.
    have : check_i ii (Cwhile a c e c') (Cwhile a2 c2 e1 c2') r1' =
           ok (re, LT_iwhile ltci lte' ltci').
    + rewrite /= Loop.nbP /=. rewrite Hi /=. rewrite He /=. rewrite Hi' /=.
      rewrite hi' /=. auto. move=> Hw'. rewrite /Pi_r in Hw.
    move: (Hw ii r1' (Cwhile a2 c2 e1 c2') re (LT_iwhile ltci lte' ltci') vm3 Hvm4 Hw').
    move=> [] vm4 [] Hvm5 /= Hc1''. exists vm4. split=> //. apply sem_seq1. econstructor.
    econstructor. rewrite hl in Hc1. apply Hc1.
    move: (He' sm2 true le Hse). move=> {He'} [] v [] Hse' /value_uincl_bool1.
    move=> <- /=. rewrite -hl1. by replace (p_globs p2) with gd.
    rewrite hl2 in Hc1'. apply Hc1'. rewrite hl hl1 hl2 /= in Hc1''. inversion Hc1''. subst.
    inversion H3. subst. rewrite /=. inversion H5. subst. apply H7.
  Qed.

  
  Local Lemma Hwhile_false : sem_Ind_while_false p1 Pc Pi_r.
  Proof.
    move => s1 s2 a c e c' lc le.
    case: s2 => sm2 svm2 Hci Hc Hse ii r1 [] //= a2 c2 e1 c2' r2 lti vm1 Hvm1.
    t_xrbindP. move=> [r [[ltc lte] ltc']] /loop2P.
    move=> [] r1' [] r2' []. t_xrbindP.
    t_xrbindP. move=> [ri ltci] Hi [re lte']. apply: add_iinfoP.
    move=> He [ri' ltci'] Hi' <- <- /= hl /= hl1 /= hl2 hi hi' <- <- /=.
    move: eq_alloc_incl. move=> Hq. move: (Hq r1 r1' (evm s1) vm1 hi Hvm1).
    move=> {Hq} Hvm1'. rewrite /Pc in Hc.
    move: (Hc ii r1' c2 ri ltci vm1 Hvm1' Hi).
    move=> [] vm2 [] Hvm2 /= Hc1 {Hc}.
    move: (@check_eP LO). move=> Hce. move: (Hce gd e e1 ri re lte' svm2 vm2 stk He Hvm2). 
    move=> {Hce} [] Hvme He'. exists vm2.
    split=> //. apply sem_seq1. constructor. econstructor. rewrite hl in Hc1. auto.
    move: (He' sm2 false le Hse). move=> {He'} [] v [] Hse' /value_uincl_bool1.
    move=> <- /=. replace (p_globs p2) with gd. by rewrite -hl1.
  Qed.

  Local Lemma loopP ii check_c n r1 r2 ltc:
    loop ii check_c n r1 = ok (r2, ltc) ->
      exists r2',
      [/\ check_c r2 = ok (r2', ltc), M.incl r2 r1 & M.incl r2 r2'].
  Proof.
    elim: n r1 r2 ltc => //= n Hrec r1 r2 ltc.
    t_xrbindP. move=> [r1' ltc'] Hc; case:ifPn.
    + move=> h [] <- <-. exists r1'. split=> //. apply M.incl_refl.
    move=> h hl. move: (Hrec (M.merge r1 (r1', ltc').1) r2 ltc hl).
    move=> [] r2'. move=> [] Hc' hm hi'.
    exists r2'. split=> //. apply: (M.incl_trans hm).
    apply M.merge_incl_l.
  Qed.

  Local Lemma Hfor : sem_Ind_for p1 Pi_r Pfor.
  Proof.
    move=> s1 s2 i [[d lo] hi] wr c lr lf.
    case: s1 => sm1 svm1. rewrite /sem_range. t_xrbindP.
    move=> [vle lle] Hle vi Hi [vhe lhe] Hhe vi' Hi' <- <- Hf Hfor.
    move=> ii r1 [] //= i2 [[d' lo'] hi'] c2 r2 lti vm1 Hvm1.
    case: eqP=> //= hd; subst d'. t_xrbindP.
    move=> [r1' lte]. apply: add_iinfoP.
    move=> /check_eP -/(_ gd _ _ stk Hvm1) [Hr1'' Heqlo]. move: (Heqlo _ _ _ Hle).
    move=> [] vlo'' [] Hlo2 Hv. move=> [r1'' lte']. apply: add_iinfoP. 
    move=> /check_eP -/(_ gd _ _ stk Hr1'') [Hr1' Heqhi]. move: (Heqhi _ _ _ Hhe).
    move=> [] vhi'' [] Hhi' Hv' [r2' lte2] Hcv /= <- <-. move: Hcv.
    move=> /loopP [r3] []; t_xrbindP. move=> [r3' lt3']; apply: add_iinfoP.
    move=> Hcv Hcc /= Hr2'_r1' Hr2'_r3. rewrite /Pfor in Hfor. rewrite /check_cmd in Hfor.
    move: eq_alloc_incl. move=> H. move: (H r1'' r2' svm1 vm1 Hr2'_r1' Hr1'). move=> Hr1'''.
    move: (Hfor i2 ii r2' r3' lt3' c2 r3 lte2 vm1 Hr1''' Hcv Hcc Hr2'_r3).
    move=> [r4] [] Hr4 {Hfor} Hfor. exists r4; split=>//. apply sem_seq1.
    econstructor. econstructor. rewrite /sem_range. replace (p_globs p2) with gd.
    rewrite Hlo2 /= Hhi' /=. move: (value_uincl_int Hv Hi). move=> [] h1 h2. rewrite -h1 in h2.
    rewrite h2. rewrite Hi /=. move: (value_uincl_int Hv' Hi'). move=> [] h1' h2'. rewrite -h1' in h2'.
    rewrite h2'. by rewrite Hi' /=. apply Hfor.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    rewrite /sem_Ind_for_nil. rewrite /Pfor.
    move=> s i c i2 ii r1 r1' c2 r2 r2' ltf vm1 Hvm1 Hcv Hc Hm.
    exists vm1. split=> //. constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p1 Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c lc lf Hwi Hsc Hc Hsfor Hfor
              i2 ii r1 r1' ltv c2 r2 ltf vm2 Heq Hr1' Hcc Hincl.
    move: (@check_lvalP LO). move=> Hcv. rewrite /check_var in Hr1'.
    move: (Hcv gd r1 r1' ltv i i2 None s1 s1'). rewrite /=. move=> {Hcv} Hcv.
    move: (Hcv LEmpty vm2 w w stk Hr1' Heq (value_uincl_refl _)). rewrite Hwi /=.
    have H : (is_true true). auto. have : (ok (s1', LEmpty) = ok (s1', LEmpty)).
    move=> T. auto. move=> H'.
    move=> {Hcv} Hcv. move: (Hcv H (H' _)). move=> [] vm1' []. t_xrbindP. move=> s2' Hwi' Hs2 Hl Heq'.
    rewrite /Pc in Hc. move: (Hc ii r1' c2 r2 ltf vm1' Heq' Hcc). move=> [] vm1'' [] Heq'' Hs.
    rewrite /Pfor in Hfor. rewrite /check_var in Hfor. 
    move: (Hfor i2 ii r1 r1' ltv c2 r2 ltf vm1'' (eq_alloc_incl Hincl Heq'') Hr1' Hcc Hincl).  
    move=> [] vm1''' [] Heq''' {Hfor} Hfor. exists vm1'''; split=>//; econstructor; eauto.
    by rewrite Hs2.
  Qed.

  Local Lemma Hcall : sem_Ind_call p1 Pi_r Pfun.
  Proof.
    rewrite /sem_Ind_call. rewrite /Pi_r /=.
    move=> s1 m2 s2 ii xs fn args vargs vs lf lw Hes Hsc Hfun Hw ii' r1 [] //= ii2 xs2 fn2
              args2 r2 lti vm1 Hr1.
    case: eqP => //= H. case hlf : lf=> [fn' lfn]. rewrite hlf in Hfun.
    t_xrbindP. move=> [res ltes]. apply: add_iinfoP.
    move=> Hces [rvs ltvs]. apply: add_iinfoP. move=> Hcvs [] <- <- /=.
    move: check_esP. move=> Hces'. move: (Hces' args args2 r1 res ltes s1 vm1 Hces Hr1).
    move=> {Hces'} [] Hr1' Hes''. move: (Hes'' vargs Hes).
    move=> {Hes''} [] vargs' [] Hes' [] Hv Hl. rewrite /Pfun in Hfun.
    move: (Hfun (unzip1 vargs') Hv). move=> {Hfun} [] vs' [] Hcall Hv'.
    move: (@check_lvalsP LO). move=> Hcvs'.
    move: (Hcvs' gd xs xs2 vs vs' res rvs ltvs {| emem := m2; evm := evm s1 |}
           s2 lw vm1 stk Hcvs Hr1' Hv' Hw). move=>  [] vm2 [] Hw' Hr1''.
    exists vm2. split. auto. move: (@Ecall LO). move=> Hcall'. rewrite /= in Hcall. 
    replace gd with (p_globs p2) in Hw'. rewrite /= in Hw'.
    have /(_ LO) {Hcall'} Hcall' := (Hcall' p2 {| emem := emem s1; evm := vm1 |} m2 {| emem := emem s2; evm := vm2 |} ii2 xs2 fn args2 vargs' vs' 
                  (fn', leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs fn') lfn) (map2 (leak_E stk) ltvs lw) Hes'). rewrite /=.
    move: (Hcall' LO Hcall Hw'). move=> {Hcall'} Hcall'. apply sem_seq1. econstructor. 
    by rewrite -H -Hl. 
  Qed.

  Section REFL_PROC.

    Hypothesis eq_prog : p1 = p2.

    Definition leak_fn_id fn := 
      match get_fundef (p_funcs p1) fn with 
      | None => None 
      | Some fd => Some (map (fun _ => LT_ikeep) fd.(f_body))
      end.

    Hypothesis Fs_id : forall fn, get_leak Fs fn = leak_fn_id fn. 

    Lemma leak_map_id lf c s1 s2 : sem p1 s1 c lf s2 ->
      leak_Is (leak_I (leak_Fun Fs)) stk [seq LT_ikeep | _ <- c] lf = lf.
    Proof.
      elim: c s1 lf => /= [ | i c hrec] s1 lf hsem.
      + by inversion_clear hsem.      
      inversion_clear hsem => /=.
      rewrite /leak_Is /=.
      have -> /= : leak_I (leak_Fun Fs) stk li LT_ikeep = [:: li] by case: (li).  
      by f_equal; apply: hrec H0.
    Qed.

    Local Lemma Hproc_eq m1 m2 fn f vargs vargs' s1 vm2 vres vres' lf:
      get_fundef (p_funcs p1) fn = Some f ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
      sem p1 s1 (f_body f) lf {| emem := m2; evm := vm2 |} ->
      Pc s1 (f_body f) lf {| emem := m2; evm := vm2 |} ->
      mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      Pfun m1 fn vargs' (fn, lf) m2 vres'.
    Proof.
      rewrite /Pfun /=.
      move=> Hget Hca Hw Hsem Hpc Hres Hcr vargs2 Hvargs2;rewrite -eq_prog.
      have H : sem_call p1 m1 fn vargs' (fn, lf) m2 vres'. 
      + by apply EcallRun with f vargs s1 vm2 vres; auto.
      have -> : leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs fn) lf = lf.
      + rewrite {2}/leak_Fun; have := Fs_id fn. rewrite /get_leak => -> /=.
        rewrite /leak_fn_id Hget /=; apply: leak_map_id Hsem.
      have [vs [H1 H2]] := sem_call_uincl Hvargs2 H.
      by exists vs.
    Qed.

    Lemma alloc_funP_eq_aux fn f f' m1 vargs vargs' vres s1 s2 vres' ltc lc :
      check_fundef (fn, f) (fn, f') = ok (fn, ltc) ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
      sem p1 s1 (f_body f) lc s2 ->
      mapM (fun x : var_i => get_var (evm s2) x) (f_res f) = ok vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      exists s1' vm2 vres1 vres1',
       [ /\ mapM2 ErrType truncate_val f'.(f_tyin) vargs' = ok vargs,
        write_vars (f_params f') vargs {| emem := m1; evm := vmap0 |} = ok s1',
        sem p2 s1' (f_body f') (leak_Is (leak_I (leak_Fun Fs)) stk ltc lc) (Estate (emem s2) vm2),
        mapM (fun x : var_i => get_var vm2 x) (f_res f') = ok vres1 &
        List.Forall2 value_uincl vres' vres1' /\
        mapM2 ErrType truncate_val f'.(f_tyout) vres1 = ok vres1'].
    Proof.
    rewrite /check_fundef eq_refl=> //=.
    case: ifP=> // /andP [] /eqP htyin /eqP htyout; apply: add_finfoP.
    t_xrbindP. move=> [r1 lt1]. apply: add_iinfoP=> Hcparams. 
    move=> [r2 lt2] Hcc. move=> [r3 lt3]. 
    apply: add_iinfoP=> /= Hcres /= <- Hca /= Hcr.
    have [l /(check_lvalsP stk Hcparams)] := (write_lvals_vars gd Hcr).
    move=> /(_ vargs _ eq_alloc_empty) [ | vm3 /= [Hw2 Hvm3]].
    + by apply: List_Forall2_refl.
    move=> /(sem_Ind Hskip Hcons HmkI Hassgn Hopn Hif_true Hif_false
                Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc_eq) Hc.
   rewrite /Pc in Hc. 
   move: (Hc (f_iinfo f) r1 (f_body f') r2 lt2 vm3 Hvm3 Hcc).
   move=> [] vm4 /= [] Hvm4 Hsc2. move: check_esP. move=> Hes.
   move: (Hes (map Pvar (f_res f)) (map Pvar (f_res f')) r2 r3 lt3 s2 vm4 Hcres Hvm4).
   move=> [] /= Hr3 H {Hes} Hres.
   have /= /(_ LO) H1 := (get_var_sem_pexprs_empty gd Hres).
   move: (H (zip vres [seq LEmpty | _ <- vres]) H1).
   move=> [] vres1'' [] Hes' [] /= Hv Hv'. 
   rewrite unzip1_zip in Hv; last first.
   + apply mapM_size in Hres. rewrite /sem_pexprs in H1.
     apply mapM_size in H1. rewrite !size_map in H1. rewrite H1 in Hres.
     rewrite size_zip in Hres. by apply /minn_idPl.
   move=> Hm.
   move: (mapM2_truncate_val Hm Hv)=> [] vres2 Hm'' Hv''.
   do 4 eexists;split;eauto.
   + by rewrite -htyin.
   + by rewrite (write_vars_lvals Hw2).
   + by apply : (sem_pexprs_get_var Hes').
   split=> //. by apply Hv''. by rewrite -htyout.
   Qed.

  End REFL_PROC.

  Section PROC.
  Hypothesis Hcheck: check_prog_aux p1 p2 = ok Fs.

  Lemma all_checked' : forall fn fd1,
    get_fundef (p_funcs p1) fn = Some fd1 ->
    exists fd2, exists rs,
          get_fundef (p_funcs p2) fn = Some fd2 /\
          check_fundef (fn,fd1) (fn,fd2) = ok (fn, rs) /\
          get_leak Fs fn = Some rs.
  Proof.
    move: Hcheck. rewrite /check_prog_aux; clear Hcheck eq_globs.
    move: (p_funcs p1) (p_funcs p2) Fs.
    elim=> [| [fn1' fd1'] p1' /= Hrec] [| [fn2 fd2] p2'] // Fs0 /=.
    case: ifPn=> // /andP [] /andP [] /eqP hfn /eqP hin /eqP hout.
    subst fn1'. t_xrbindP=> -[fn ltc]; apply: add_finfoP. 
    t_xrbindP=> -[r1 lt1]; apply: add_iinfoP=> hcr [r2 lt2] hcc [r3 lt3]; 
    apply: add_iinfoP=> hes <- <- fds /Hrec {Hrec} Hrec /= <- fn' fd'.
    case: ifP.
    + move=> /eqP <- [] hfd. exists fd2. exists lt2. split=> //.
      case: ifP=> //=. move=> /andP [] /andP [] /eqP hfn' /eqP htyin /eqP htyout. 
      rewrite -hfd hcr /= hcc /= hes /=. split=> //. case: ifP=> //.
      move=> /eqP []; auto. move=> /andP []. split=> //. apply /andP. split=> //; auto.
      by rewrite /eqP -hfd hin. by rewrite /eqP -hfd hout.
    move=> hfn /Hrec [] fd'' [] fdlt [] hg' [] h1 h2.
    exists fd''. exists fdlt. split=> //. split=> //.
    by rewrite /get_leak /= hfn.
  Qed. 

  Local Lemma Hproc : sem_Ind_proc p1 Pc Pfun.
  Proof.
   move=> m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hget Hca Hw Hs Hc Hres Hcr.
   move: (all_checked' Hget)=> -[fd2] [] ltc [] Hget2 [] Hcf Hleak.
   move: Hcf. rewrite /=.
   rewrite eq_refl /=; case: ifP => // /andP []. move=> /eqP htyin /eqP htyout.
   apply: add_finfoP. t_xrbindP. move=> [r1 lt1]. apply: add_iinfoP=> Hcparams.
   move=> [r2 lt2] Hcc. move=> [r3 lt3]. apply: add_iinfoP=> /= Hcres /= Hfn.
   move=> vargs2 Hvargs2.
   have [vs2 htr hall2]:= mapM2_truncate_val Hca Hvargs2.
   have [l /(check_lvalsP stk Hcparams)] := (write_lvals_vars gd Hw).
   move=> /(_ _ _ eq_alloc_empty hall2) [vm3 /= [Hw2 Hvm3]].
   rewrite /Pc in Hc. 
   move: (Hc (f_iinfo f) r1 (f_body fd2) r2 lt2 vm3 Hvm3 Hcc).
   move=> [] vm4 /= [] Hvm4 Hsc2. move: check_esP. move=> Hes.
   move: (Hes (map Pvar (f_res f)) (map Pvar (f_res fd2)) r2 r3 lt3 {| emem := emem s1; evm := vm2 |} vm4 Hcres Hvm4). move=> [] /= Hr3 H {Hes}.
   have hvm : vm2 = evm{| emem := emem s1; evm := vm2 |} by []. 
   rewrite hvm in Hres.
   have /= /(_ LO) H1:= (get_var_sem_pexprs_empty gd Hres).
   move: (H (zip vres [seq LEmpty | _ <- vres]) H1).
   move=> [] vres1'' [] Hes' [] /= Hv Hv'. 
   rewrite unzip1_zip in Hv; last first.
   + apply mapM_size in Hres. rewrite /sem_pexprs in H1.
     apply mapM_size in H1. rewrite !size_map in H1. rewrite H1 in Hres.
     rewrite size_zip in Hres. by apply /minn_idPl.
   move: (mapM2_truncate_val Hcr Hv)=> [] vres2 Hm'' Hv''.
   exists vres2. split=> //.
   econstructor; eauto.
   + by rewrite -htyin; apply htr. 
   + by rewrite (write_vars_lvals Hw2).
   + rewrite /get_leak in Hleak. rewrite /= in Hleak.
     have -> : (leak_Fun Fs fn) = lt2. 
     + by rewrite /leak_Fun Hfn Hleak.
     by apply Hsc2.
   + by apply : (sem_pexprs_get_var Hes').
   by rewrite -htyout.
  Qed.

  Lemma alloc_callP_aux f mem mem' va vr lf:
    sem_call p1 mem f va lf mem' vr ->
    exists vr', sem_call p2 mem f va (lf.1, (leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs lf.1) lf.2)) mem' vr' /\ List.Forall2 value_uincl vr vr'.
  Proof.
    move=>
      /(@sem_call_Ind _ p1 Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
            Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
    move=> H;apply H.
    apply List_Forall2_refl;apply value_uincl_refl.
  Qed.

End PROC.

End PROOF.

Lemma alloc_callP {LO:LeakOp} p1 p2 Fs (H: check_prog p1 p2 = ok Fs) f mem mem' va vr stk lf:
    sem_call p1 mem f va (f, lf) mem' vr ->
    exists vr', sem_call p2 mem f va (f, (leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs f) lf)) mem' vr'
                /\ List.Forall2 value_uincl vr vr'.
Proof.
  move: H;rewrite /check_prog;case: eqP => // heq hc.
  by apply alloc_callP_aux.
Qed.

Section PROOF_WF.
  Context {LO:LeakOp}.

  Variable p1 p2:prog.
  Variable Fs: seq (funname * seq leak_i_tr).
  Notation gd := (p_globs p1).
  Variable stk : pointer.
  Hypothesis eq_globs : p_globs p1 = p_globs p2.
  Hypothesis Hcheck: check_prog_aux p1 p2 = ok Fs.

  Let Pi_r (s1:estate) (i1:instr_r) li (s2:estate):=
    forall ii r1 i2 r2 lti, 
    check_i ii i1 i2 r1 = ok (r2, lti) ->
    leak_WF (leak_Fun Fs) lti li.

  Let Pi (s1:estate) (i1:instr) li (s2:estate):=
     forall r1 i2 r2 lti, 
     check_I i1 i2 r1 = ok (r2, lti) ->
     leak_WF (leak_Fun Fs) lti li.
     
  Let Pc (s1:estate) (c1:cmd) lc (s2:estate):=
    forall ii r1 c2 r2 ltc, 
    check_cmd ii c1 c2 r1 = ok (r2, ltc) ->
    leak_WFs (leak_Fun Fs) ltc lc.
    
  Let Pfor (i1:var_i) (vs:seq Z) (s1:estate) (c1:cmd) lf (s2: estate):=
    forall i2 ii r1 r1' ltv c2 r2 ltf, 
    check_var i1 i2 r1 = ok (r1', ltv) ->
    check_cmd ii c1 c2 r1' = ok (r2, ltf) -> M.incl r1 r2 ->
    leak_WFss (leak_Fun Fs) ltf lf.

  Let Pfun (m:mem) (fn:funname) (vargs1:seq value) lf (m':mem) (vres:seq value):=
    leak_WFs (leak_Fun Fs) (leak_Fun Fs lf.1) lf.2. 

  Local Lemma Hskip_WF : sem_Ind_nil Pc.
  Proof.
    move=> s ii r1 [ | ??] //= r2 ltc [] _ <-. constructor.
  Qed.

  Local Lemma Hcons_WF : sem_Ind_cons p1 Pc Pi.
  Proof.
    move=> s1 s2 s3 i c li lc Hsi Hi Hsc Hc ii r1 [ | i2 c2] //= r2 lt.
    t_xrbindP=> -[ri lti] /= /Hi Hwf -[rc ltc] /Hc Hwf' _ /= <-.
    constructor. apply Hwf. apply Hwf'.
  Qed.

  Local Lemma HmkI_WF : sem_Ind_mkI p1 Pi_r Pi.
  Proof.
    move=> ii i s1 s2 li Hsi Hi r1 [i2i i2] r2 lti /Hi Hwf.
    apply Hwf.
  Qed.

  Local Lemma Hassgn_WF : sem_Ind_assgn p1 Pi_r.
  Proof.
    move => s1 s2 x tag ty e v v' le lw.
    case: s1 => sm1 svm1 He Htr Hw ii r1 [] //= x2 tag2 ty2 e2 r2 lti. 
    case: eqP => // <- {ty2}. t_xrbindP. move=> [re lte]. apply: add_iinfoP.
    move=> /check_eP Hce [rv ltv]. apply: add_iinfoP. move=>Hcv [] _ <-. 
    constructor.
  Qed.

  Local Lemma Hopn_WF : sem_Ind_opn p1 Pi_r.
  Proof.
    move => s1 s2 t o xs es lo. rewrite /sem_sopn.
    t_xrbindP. move=> ves Hes vo Hex [vw vl] Hws <- <- /=.
    rewrite /Pi_r. move=> ii r1 [] //= xs1 t' o1 es1 r2 lti. 
    case: ifPn => //= /eqP _. t_xrbindP. move=> [yv yl]. apply: add_iinfoP.
    move=> Hces [rv ltv]. apply: add_iinfoP. move=> Hcvs [] _ <-.
    constructor.
  Qed.

  Local Lemma Hif_true_WF : sem_Ind_if_true p1 Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 le lc.
    case: s1 => sm1 svm1 Hve Hc Hc1 ii r1 [] //= e' c1' c2' r2 lti. 
    t_xrbindP. move=> [re lte]. apply: add_iinfoP. 
    t_xrbindP. move=> He /= -[rc ltc] /= Hc' -[rc' ltc'] Hc'' _ <-.
    constructor. rewrite /Pc in Hc1. move: (Hc1 ii re c1' rc ltc Hc').
    move=> Hwf. apply Hwf.
  Qed.

  Local Lemma Hif_false_WF : sem_Ind_if_false p1 Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 le lc.
    case: s1 => sm1 svm1 Hve Hc Hc1 ii r1 [] //= e' c1' c2' r2 lti. 
    t_xrbindP. move=> [re lte]. apply: add_iinfoP. 
    move=> He /= -[rc ltc] /= Hc' -[rc' ltc'] Hc'' _ <-.
    constructor. rewrite /Pc in Hc1. move: (Hc1 ii re c2' rc' ltc' Hc'').
    move=> Hwf. apply Hwf.
  Qed.

  Local Lemma Hwhile_true_WF : sem_Ind_while_true p1 Pc Pi_r.
  Proof.
    move => s1 s2 s3 s4 a c e c' lc le lc' li.
    case: s2 => sm2 svm2 Hci Hc Hse Hci' Hc' Hwi Hw ii r1 [] //= a2 c2 e1 c2' r2 lti. 
    t_xrbindP. move=> [r [[ltc lte] ltc']] /loop2P.
    move=> [] r1' [] r2' [].
    t_xrbindP. move=> [ri ltci] Hi [re lte']. apply: add_iinfoP.
    move=> He [ri' ltci'] Hi' /= hi' /= hi'' /= <- <- <- h1 h2 h3 <-. 
    constructor. rewrite /Pc /= in Hc. move: (Hc ii r1' c2 ri ltci Hi).
    move=> Hwf. apply Hwf. 
    rewrite /Pc /= in Hc'. move: (Hc' ii re c2' ri' ltci' Hi').
    move=> Hwf. apply Hwf. rewrite /Pi_r in Hw.
    have : check_i ii (Cwhile a c e c') (Cwhile a2 c2 e1 c2') r1' =
           ok (re, LT_iwhile ltci lte' ltci').
    + rewrite /= Loop.nbP /=. rewrite Hi /=. rewrite He /=. rewrite Hi' /=.
      rewrite hi''. by rewrite h2 /=.
    move=> Hw'. move: (Hw ii r1' (Cwhile a2 c2 e1 c2') re (LT_iwhile ltci lte' ltci') Hw')=> Hwf'.
    apply Hwf'.
  Qed.
  
  Local Lemma Hwhile_false_WF : sem_Ind_while_false p1 Pc Pi_r.
  Proof.
    move => s1 s2 a c e c' lc le.
    case: s2 => sm2 svm2 Hci Hc Hse ii r1 [] //= a2 c2 e1 c2' r2 lti. 
    t_xrbindP. move=> [r [[ltc lte] ltc']] /loop2P.
    move=> [] r1' [] r2' []. t_xrbindP.
    t_xrbindP. move=> [ri ltci] Hi [re lte']. apply: add_iinfoP.
    move=> He [ri' ltci'] Hi' h1 h2 /= h3 /= h4 /= <- hi hi' h5 <- /=. 
    constructor. rewrite /Pc /= in Hc.  move: (Hc ii r1' c2 ri ltci Hi).
    move=> Hwf. rewrite -h3. apply Hwf.
  Qed.

  Local Lemma Hfor_WF : sem_Ind_for p1 Pi_r Pfor.
  Proof.
    move=> s1 s2 i [[d lo] hi] wr c lr lf.
    case: s1 => sm1 svm1. rewrite /sem_range. t_xrbindP.
    move=> [vle lle] Hle vi Hi [vhe lhe] Hhe vi' Hi' <- <- Hf Hfor.
    move=> ii r1 [] //= i2 [[d' lo'] hi'] c2 r2 lti. 
    case: eqP=> //= hd; subst d'. t_xrbindP.
    move=> [r1' lte]. apply: add_iinfoP. move=> He.
    move=> [r1'' lte']. apply: add_iinfoP. move=> He'.
    move=> -[r1''' lte''].
    move=> /loopP [r3] []; t_xrbindP. move=> [r3' lt3']; apply: add_iinfoP.
    move=> Hcv Hcc /= Hr2'_r1' Hr2'_r3 Hr <-. constructor.
    rewrite /Pfor in Hfor. rewrite /check_cmd in Hfor.
    move: (Hfor i2 ii r1''' r3' lt3' c2 r3 lte'' Hcv Hcc Hr2'_r3). 
    move=> Hwf. apply Hwf.
  Qed.

  Local Lemma Hfor_nil_WF : sem_Ind_for_nil Pfor.
  Proof.
    rewrite /sem_Ind_for_nil. rewrite /Pfor.
    move=> s i c i2 ii r1 r1' c2 r2 r2' ltf Hcv Hc Hm.
    constructor.
  Qed.

  Local Lemma Hfor_cons_WF : sem_Ind_for_cons p1 Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c lc lf Hwi Hsc Hc Hsfor Hfor
              i2 ii r1 r1' ltv c2 r2 ltf. 
    move=> Hcv /= Hc' Hm. rewrite /Pc in Hc.
    move: (Hc ii r1' c2 r2 ltf Hc'). move=> Hwf. constructor. apply Hwf.
    rewrite /Pfor in Hfor. 
    move: (Hfor i2 ii r1 r1' ltv c2 r2 ltf Hcv Hc' Hm). move=> Hwf'. 
    apply Hwf'.
  Qed.

  Local Lemma Hcall_WF : sem_Ind_call p1 Pi_r Pfun.
  Proof.
    rewrite /sem_Ind_call. rewrite /Pi_r /=.
    move=> s1 m2 s2 ii xs fn args vargs vs lf lw Hes Hsc Hfun Hw ii' r1 [] //= ii2 xs2 fn2
              args2 r2 lti. 
    case: eqP => //= H. case hlf : lf=> [fn' lfn]. rewrite hlf in Hfun.
    t_xrbindP. move=> [res ltes]. apply: add_iinfoP.
    move=> Hces [rvs ltvs]. apply: add_iinfoP. move=> Hcvs [] h1 <- /=.
    apply sem_eq_fn in Hsc. rewrite -H. rewrite hlf /= in Hsc. rewrite Hsc. constructor.
    rewrite /Pfun /= in Hfun. rewrite Hsc in Hfun. apply Hfun. 
  Qed.

  Local Lemma Hproc_WF : sem_Ind_proc p1 Pc Pfun.
  Proof.
   move=> m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hget Hca Hw Hs Hc Hres Hcr.
   move: (all_checked' Hcheck Hget)=> -[fd2] [] ltc [] Hget2 [] Hcf Hleak.
   move: Hcf. rewrite /=.
   rewrite eq_refl /=; case: ifP => // /andP []. move=> /eqP htyin /eqP htyout.
   apply: add_finfoP. t_xrbindP. move=> [r1 lt1]. apply: add_iinfoP=> Hcparams.
   move=> [r2 lt2] Hcc. move=> [r3 lt3]. apply: add_iinfoP=> /= Hcres /= Hfn.
   rewrite /Pc in Hc. 
   move: (Hc (f_iinfo f) r1 (f_body fd2) r2 lt2 Hcc). move=> Hwf.
   rewrite /Pfun /=. rewrite /get_leak in Hleak. rewrite /= in Hleak.
   rewrite Hfn in Hwf.
   have -> : (leak_Fun Fs fn) = lt2. 
   + by rewrite /leak_Fun Hfn Hleak. by rewrite Hfn.
  Qed.

  Lemma alloc_call_wf_aux f mem mem' va vr lf:
    sem_call p1 mem f va (f,lf) mem' vr ->
    leak_WFs (leak_Fun Fs) (leak_Fun Fs f) lf.
  Proof.
    apply (@sem_call_Ind _ p1 Pc Pi_r Pi Pfor Pfun Hskip_WF Hcons_WF HmkI_WF Hassgn_WF Hopn_WF
             Hif_true_WF Hif_false_WF Hwhile_true_WF Hwhile_false_WF Hfor_WF Hfor_nil_WF Hfor_cons_WF
             Hcall_WF Hproc_WF).
  Qed.

End PROOF_WF. 

Lemma alloc_callP_wf {LO:LeakOp} p1 p2 Fs (H: check_prog p1 p2 = ok Fs) f mem mem' va vr stk lf:
    sem_call p1 mem f va (f, lf) mem' vr ->
    leak_WFs (leak_Fun Fs) (leak_Fun Fs f) lf /\
    exists vr', sem_call p2 mem f va (f, (leak_Is (leak_I (leak_Fun Fs)) stk (leak_Fun Fs f) lf)) mem' vr'
                /\ List.Forall2 value_uincl vr vr'.
Proof.
  move=> hsem; split; last by apply: (alloc_callP H stk hsem).
  move: H hsem; rewrite /check_prog;case: eqP => // heq hcheck hsem.
  by apply (alloc_call_wf_aux hcheck hsem).
Qed.

Section REFL.
Context {LO:LeakOp}.

Context (check_eP_id : forall e1 e2 r rlte stk l,
          check_e e1 e2 r = ok rlte ->
          leak_E stk rlte.2 l = l).

Context (check_lvalP_id : forall r rltr x1 x2 e2 stk l,
          check_lval e2 x1 x2 r = ok rltr ->
          leak_E stk rltr.2 l = l).

Context (p:prog) (stk:pointer).

Definition leak_id :=
  map (fun f => (f.1, [seq LT_ikeep | _ <- f_body f.2])) (p_funcs p).

Lemma Fs_id : forall fn, get_leak leak_id fn = leak_fn_id p fn. 
Proof.
move=> fn. rewrite /leak_id /get_leak /leak_fn_id. 
have -> := assoc_map (fun f => [seq LT_ikeep | _ <- f_body f]) (p_funcs p). rewrite /get_fundef /=. by case: assoc.
Qed.

Let lF := leak_Fun leak_id.

Let Pi (s1:estate) i1 l (s2:estate) :=
  forall i2 r rlt, check_I i1 i2 r = ok rlt -> leak_I lF stk l rlt.2 = [::l].

Let  Pi_r (s1:estate) i1 l (s2:estate) :=
  forall ii i2 r rlt, check_i ii i1 i2 r = ok rlt -> leak_I lF stk l rlt.2 = [::l].

Let Pc (s1:estate) c1 l (s2:estate) := 
  forall ii c2 r rlt, check_cmd ii c1 c2 r = ok rlt -> leak_Is (leak_I lF) stk rlt.2 l = l.

Let Pfor (_:var_i) (_:seq Z) (s1:estate) c1 l (s2:estate) := 
  forall ii c2 r rlt, check_cmd ii c1 c2 r = ok rlt -> leak_Iss (leak_I lF) stk rlt.2 l = l.

Let Pfun (_:mem) (_:funname) (_:seq value) (_:leak_fun) (_:mem) (_:seq value) := True.

Local Lemma Iskip : sem_Ind_nil Pc.
Proof. by move=> ? []. Qed.

Local Lemma Icons : sem_Ind_cons p Pc Pi.
Proof. 
  move=> s1 s2 s3 i1 c1 li lc Hsi Hi Hsc Hc ii [] //= i2 c2 ??.
  by t_xrbindP => ? /Hi hi ? /Hc hc <-; rewrite /leak_Is /= hi -{2}hc.
Qed.

Local Lemma ImkI : sem_Ind_mkI p Pi_r Pi.
Proof. by move=> ii i1 s1 s2 li Hsi Hi [];apply Hi. Qed.

Local Lemma Iassgn : sem_Ind_assgn p Pi_r.
Proof.
  move => s1 s2 x tag ty e v v' le lw _ _ _ ii [] // ?????? /=.
  case: eqP => // _; t_xrbindP => ?.
  apply: add_iinfoP=> /check_eP_id he ?.
  by apply: add_iinfoP => /check_lvalP_id hl [<-] /=; rewrite he hl.
Qed.

Lemma check_esP_id es1 es2 r rlte l :
  size l = size es1 -> 
  check_es es1 es2 r = ok rlte ->
  (map2 (leak_E stk) rlte.2 l) = l.
Proof.
elim: es1 es2 r rlte l => //=.
case => //=. 
+ by move=> r r' [] // _ [] <-.
move=> e1 es1 hrec [] // e2 es2 r r' [] // le les [] /hrec{hrec}hrec.
by t_xrbindP=> -[r1 l1] /check_eP_id hle [r2 l2] /= /hrec{hrec}hrec <- /=; rewrite hrec hle.
Qed.

Lemma check_lvalsP_id es1 es2 r rlte l :
  size l = size es1 -> 
  check_lvals es1 es2 r = ok rlte ->
  (map2 (leak_E stk) rlte.2 l) = l.
Proof.
elim: es1 es2 r rlte l => //=.
case => //=. 
+ by move=> r r' [] // _ [] <-.
move=> e1 es1 hrec [] // e2 es2 r r' [] // le les [] /hrec{hrec}hrec.
by t_xrbindP=> -[r1 l1] /check_lvalP_id hle [r2 l2] /= /hrec{hrec}hrec <- /=; rewrite hrec hle.
Qed.

Local Lemma Iopn : sem_Ind_opn p Pi_r.
Proof.
 move=> [] s1 s1' s2 t o xs es lo. rewrite /sem_sopn /=.
 t_xrbindP. move=> vs Hes vo Hex -[vs' ls] Hws <- <- /=.
 rewrite /Pi_r /=. move=> ii [] // l t' s e' r rlt. case: eqP => // h.
 t_xrbindP. move=> -[r' lr']. apply: add_iinfoP=>/check_esP_id Hes'. move=> -[r'' lr''].
 apply: add_iinfoP=> /check_lvalsP_id Hvs' [] <- /=. move: (Hes' (unzip2 vs)). move=> ->.
 rewrite (Hvs' ls)=>//. by have /= -> := size_write_lvals Hws.
 apply mapM_size in Hes. rewrite Hes. by rewrite /unzip2 size_map.
Qed.

Local Lemma Iif_true : sem_Ind_if_true p Pc Pi_r.
Proof.
 move=> s1 s2 e c1 c2 le lc He Hc Hc'. rewrite /Pi_r.
 move=> ii i2 r -[r' lr'] /=. case: i2=> //. move=> e' c c'. t_xrbindP=> -[r'' lte''].
 apply: add_iinfoP=> /check_eP_id /= he. move=> -[r1 lt1] Hc1 -[r2 lt2] Hc2 Hr' <- /=.
 move: (he stk le). move=> ->. rewrite /Pc in Hc'. rewrite /check_cmd in Hc'.
 move: (Hc' ii c r'' (r1, lt1) Hc1). by move=> ->.
Qed.

Local Lemma Iif_false : sem_Ind_if_false p Pc Pi_r.
Proof.
 move=> s1 s2 e c1 c2 le lc He Hc Hc'. rewrite /Pi_r.
 move=> ii i2 r -[r' lr'] /=. case: i2=> //. move=> e' c c'. t_xrbindP=> -[r'' lte''].
 apply: add_iinfoP=> /check_eP_id /= he. move=> -[r1 lt1] Hc1 -[r2 lt2] Hc2 Hr' <- /=.
 move: (he stk le). move=> ->. rewrite /Pc in Hc'. rewrite /check_cmd in Hc'.
 move: (Hc' ii c' r'' (r2, lt2) Hc2). by move=> ->.
Qed.

Local Lemma Iwhile_true : sem_Ind_while_true p Pc Pi_r.
Proof.
 move=> s1 s2 s3 s4 a c e c' lc le lc' li Hc Hsc He Hc' Hsc' Hi. rewrite /Pi_r.
 move=> Hi' ii i2 r -[r1 lt1] /=. case: i2=> //. move=> a' c1 e' c2 /=. t_xrbindP.
 move=> [r2 [[ltc lte] ltc']] /loop2P. move=> [r3] [r4] []. t_xrbindP.
 move=> -[r1' ltr1'] Hc1 -[r2' ltr2']. apply: add_iinfoP=> /= he.
 move=> -[r3' lt3'] Hc2 <- /= <- <- <- <- Hm Hm' hr <- /=.
 have : check_i ii (Cwhile a c e c') (Cwhile a' c1 e' c2) r3 =
           ok (r2', LT_iwhile ltr1' ltr2' lt3').
 + rewrite /= Loop.nbP /=. rewrite Hc1 /=. rewrite he /= Hc2 /=. case: ifP=> //=.
   rewrite Hm'. by move=>//. 
 move=> Hw. rewrite /Pc in Hsc.
 rewrite /check_cmd in Hsc. move: (Hsc ii c1 r3 (r1', ltr1') Hc1). move=> /= ->.
 rewrite /Pc in Hsc'. rewrite /check_cmd in Hsc'. 
 move: (Hsc' ii c2 r2' (r3', lt3') Hc2). move=> /= ->. move: he. move=> /check_eP_id he. 
 move: (he stk le). move=> -> /=. move: (Hi' ii (Cwhile a' c1 e' c2) r3 (r2', LT_iwhile ltr1' ltr2' lt3') Hw).
 by move=> -> /=.
Qed.

Local Lemma Iwhile_false : sem_Ind_while_false p Pc Pi_r.
Proof.
 move => s1 s2 a c e c' lc le Hci Hc Hse ii i1 r -[r' ltr'] //=.
 case: i1=> // a2 c2 e1 c2'. t_xrbindP. 
 move=> [r'' [[ltc lte] ltc']] /loop2P.
 move=> [] r1' [] r2' []. t_xrbindP.
 move=> [ri ltci] Hi [re lte']. apply: add_iinfoP.
 move=> He [ri' ltci'] Hi' /= <- <- /= <- <- <- h h' h'' <-.
 move: He. move=> /check_eP_id He. move: (He stk le). move=> ->.
 rewrite /Pc in Hc. rewrite /check_cmd in Hc. move: (Hc ii c2 r1' (ri, ltci) Hi).
 by move=> ->.
Qed.

Local Lemma Ifor : sem_Ind_for p Pi_r Pfor.
Proof.
 move=> s1 s2 i [[d lo] hi] wr c lr lf.
 rewrite /sem_range. t_xrbindP.
 move=> [vle lle] Hle vi Hi [vhe lhe] Hhe vi' Hi' <- <- Hf Hfor.
 move=> ii i2 r1 -[r2 ltr2] //=. case: i2=> //. move=> ve [[d' lo'] hi'] c2.
 case: eqP=> //= hd; subst d'. t_xrbindP.
 move=> [r1' lte]. apply: add_iinfoP=> /check_eP_id he.
 move=> [r2' lte']. apply: add_iinfoP=> /check_eP_id he'.
 move=> -[r3 lt3] /loopP [r3'] []; t_xrbindP. move=> [r4 lt4]; apply: add_iinfoP.
 rewrite /check_var. move=> /check_lvalP_id hvl Hc Hm Hm' /= Hr <- /=.
 move: (he stk lle). move=> ->. move: (he' stk lhe). move=> ->.
 rewrite /Pfor /check_cmd in Hfor. move: (Hfor ii c2 r4 (r3', lt3) Hc). by move=> ->.
Qed.

Local Lemma Ifor_nil : sem_Ind_for_nil Pfor.
Proof.
 move=> s1 s2 c /=. rewrite /Pfor.
 by move=> ii c2 r -[r' ltr'] /= _.
Qed.

Local Lemma Ifor_cons : sem_Ind_for_cons p Pc Pfor.
Proof.
 move=> s1 s2 s3 s4 i w ws c lc lf hw Hc Hc' Hf Hf'.
 rewrite /Pfor. move=> ii c2 r rlt. rewrite /check_cmd.
 move=> Hc''. rewrite /Pfor in Hf'. rewrite /check_cmd in Hf'.
 move: (Hf' ii c2 r rlt Hc''). move=> /= ->. rewrite /Pc /check_cmd in Hc'.
 move: (Hc' ii c2 r rlt Hc''). by move=> ->.
Qed.


Lemma leak_map_id' lc c s1 s2 fn vs vs': sem_call p s1 c vs (fn, lc) s2 vs' ->
leak_Is (leak_I lF) stk (lF fn) lc = lc.
Proof.
move=> Hcall. inversion_clear Hcall=> //=.
case: lc H2=> //=.
move=> li lc Hs.
have Heq := leak_map_id. rewrite /lF.
move: (Heq LO p leak_id stk (li :: lc) (f_body f) s0 {| emem := s2; evm := vm2 |} Hs).
move=> Hrec. 
have Heq' : (leak_Fun leak_id fn) =  [seq LT_ikeep | _ <- f_body f].
move: (Fs_id fn). rewrite /get_leak. rewrite /leak_Fun. move=> -> /=.
rewrite /leak_fn_id /=. by rewrite H /=.
by rewrite Heq'.
Qed.
 
Local Lemma Icall : sem_Ind_call p Pi_r Pfun.
Proof.
 move=> s1 s2 s3 ii xs fn args vargs vs lf lw Hes Hcall Hf Hws.
 rewrite /Pi_r /=. move=> ii' i2 r -[r' ltr']. case: i2=> // ini lvs fn' es'.
 case: ifP=> /eqP // hfn. t_xrbindP. move=> -[r'' ltr'']. apply: add_iinfoP=> /check_esP_id Hes''.
 move=> -[r''' ltr''']. apply: add_iinfoP=> /check_lvalsP_id Hes'''. move=> [] <- <- /=.
 case: lf Hcall Hf=> fn'' lc Hcall Hf. move: (Hes'' (unzip2 vargs)). move=> ->.
 rewrite (Hes''' lw).
 have -> : leak_Is (leak_I lF) stk (lF fn'') lc = lc.
 + by have -> := (leak_map_id' Hcall).
 auto.  by have /= -> := size_write_lvals Hws. apply mapM_size in Hes. rewrite Hes. by rewrite /unzip2 size_map.
Qed.

Local Lemma Iproc : sem_Ind_proc p Pc Pfun.
 Proof. done. Qed.

Lemma check_cmd_id ii c1 c2 r rlt lc s1 s2:
   sem p s1 c1 lc s2 ->
   check_cmd ii c1 c2 r = ok rlt ->
   leak_Is (leak_I lF) stk rlt.2 lc = lc.
Proof.
  move=> hsem;
  by apply: (@sem_Ind _ p Pc Pi_r Pi Pfor Pfun Iskip Icons ImkI Iassgn Iopn Iif_true Iif_false 
            Iwhile_true Iwhile_false Ifor Ifor_nil Ifor_cons Icall Iproc _ _ _ _ hsem).
Qed.

Lemma alloc_funP_eq fn fn' f f' m1 vargs vargs' vres vres' s1 s2 ltc lc :
  check_fundef (fn, f) (fn, f') = ok (fn', ltc) ->
  mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
  write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
  sem p s1 (f_body f) lc s2 ->
  mapM (fun x : var_i => get_var (evm s2) x) (f_res f) = ok vres ->
  mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
  exists s1' vm2 vres1 vres1',
   [ /\  mapM2 ErrType truncate_val f'.(f_tyin) vargs' = ok vargs,
    write_vars (f_params f') vargs {| emem := m1; evm := vmap0 |} = ok s1',
    sem p s1' (f_body f') lc (Estate (emem s2) vm2),
    mapM (fun x : var_i => get_var vm2 x) (f_res f') = ok vres1 &
    List.Forall2 value_uincl vres' vres1' /\
    mapM2 ErrType truncate_val f'.(f_tyout) vres1 = ok vres1'
    ].
Proof.
  move=> hc; move: (hc); rewrite /check_fundef; case: ifP => // _. 
  apply: add_finfoP; t_xrbindP => ? _ ? hcc _ _ ? ?; subst fn' ltc.
  move => h1 h2 hsem h4 h5.
  have []:= alloc_funP_eq_aux (Fs:= leak_id) stk refl_equal refl_equal _ hc h1 h2 hsem h4 h5.
  + move=> fn'; rewrite /get_leak /leak_id /leak_fn_id /get_fundef.
    have -> := assoc_map (fun fd => [seq LT_ikeep | _ <- f_body fd]).
    by case: assoc. 
  move=> s1' []vm2[]vres1[]vres1'[] ??.
  by rewrite (check_cmd_id hsem hcc) => ???; exists s1', vm2, vres1, vres1'.
Qed.

End REFL.

End MakeCheckAlloc.

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

  Lemma valid_rm m id : valid (rm_id m id) (Ms.remove (mid m) id).
  Proof.
    move=> x id';rewrite Ms.removeP;case:eqP => [<- | ].
    + rewrite /rm_id; case Heq: ((_).[id])%ms => [xid|].
      + rewrite M.removeP;case:ifPn => //= /eqP ne;split => //.
        by rewrite (mvalid m x id) Heq => -[?];subst x.
      by split=>//;rewrite (mvalid m x id) Heq.
    move=> Hne; rewrite /rm_id; case Heq: ((_).[id])%ms => [xid|].
    + rewrite M.removeP;case:ifPn => //= /eqP Hx.
      + subst xid; split => //.
        by move: Heq; rewrite -(mvalid m x id) -(mvalid m x id') => -> [] /Hne.
      by apply mvalid.
    by apply mvalid.
  Qed.

  Definition remove m id := mkT (valid_rm m id).

  Lemma removeP m id x' :
    get (remove m id) x' =
      match get m x' with
      | Some id' => if id == id' then None else Some id'
      | None     => None
      end.
  Proof.
    rewrite /remove /get /=.
    rewrite /rm_id;case Heq: ((mid m).[id])%ms => [x | ].
    + rewrite M.removeP;case:ifPn => /eqP Hx.
      + subst x;case Heqx: M.get => [id' | ]=> //.
        by move:Heq;rewrite -mvalid Heqx => -[->];rewrite eq_refl.
      case Heqx: M.get => [id' | ]=> //.
      case:ifPn=> // /eqP ?;subst id'.
      by move: Heqx;rewrite mvalid Heq => -[]/Hx.
    case Heqx: M.get => [id' | ]=> //.
    case:ifPn=> // /eqP ?;subst id'.
    by move: Heqx;rewrite mvalid Heq.
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

  Lemma setP_eq m x id : get (set m x id) x = Some id.
  Proof. by rewrite /get /set /=;rewrite M.setP_eq. Qed.

  Lemma setP_neq m x y id id' :
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

  Lemma mergeP m1 m2 x id :
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

Module CBAreg.

  Module M.

  Module Mv.
  
  Definition oget (mid: Mvar.t Sv.t) id := odflt Sv.empty (Mvar.get mid id).

  Definition valid (mvar: Mvar.t var) (mid: Mvar.t Sv.t) :=
    forall x id, Mvar.get mvar x = Some id <-> Sv.In x (oget mid id).

  Record t_ := mkT { mvar : Mvar.t var; mid : Mvar.t Sv.t; mvalid : valid mvar mid }.
  Definition t := t_.

  Definition get (m:t) (x:var) := Mvar.get (mvar m) x.

  Definition rm_id (m:t) id :=
     Sv.fold (fun x m => Mvar.remove m x) (oget (mid m) id) (mvar m).

  Definition ms_upd (m:Mvar.t Sv.t) (f:Sv.t -> Sv.t) id :=
    Mvar.set m id (f (oget m id)).

  Definition rm_x (m:t) x :=
    match Mvar.get (mvar m) x with
    | Some id => ms_upd (mid m) (Sv.remove x) id
    | None    => (mid m)
    end.

  Lemma valid_get_in m id x :
    get m x = Some id -> x \in Sv.elements (oget (mid m) id).
  Proof. by move=> /(mvalid) /Sv_elemsP. Qed.

  Lemma rm_idP m id x :
     Mvar.get (rm_id m id) x =
      if Sv.mem x (oget (mid m) id) then None
      else get m x.
  Proof.
    rewrite /rm_id; have := @valid_get_in m id.
    rewrite Sv.fold_spec /get Sv_elems_eq.
    elim: (Sv.elements _) (mvar m) => //= v vs Hrec mv Hget.
    rewrite Hrec ?inE.
    + rewrite Mvar.removeP eq_sym.
      by case: ( _ \in _);[rewrite orbT | case: (_ == _)].
    by move=> z;rewrite Mvar.removeP;case:ifP => //= H /Hget;rewrite inE eq_sym H.
  Qed.

  Lemma rm_id_eq m id x : Mvar.get (rm_id m id) x <> Some id.
  Proof.
    by rewrite rm_idP;case:ifPn => // /negP; rewrite mvalid => H /Sv_memP -/H.
  Qed.

  Lemma rm_idP_neq m x id id' : id != id' ->
    Mvar.get (rm_id m id) x = Some id' <-> Mvar.get (mvar m) x = Some id'.
  Proof.
    rewrite rm_idP => Hneq.
    case:ifP => //= /Sv_memP Hin;split=>// Hg.
    by move: Hin Hg Hneq; rewrite -mvalid => -> [->];rewrite eq_refl.
  Qed.

  Lemma oget_set m id id' s:
    oget (Mvar.set m id' s) id =
     if id' == id then s else oget m id.
  Proof. by rewrite /oget Mvar.setP;case:ifP. Qed.

  Lemma oget_rm m id id':
    oget (Mvar.remove m id') id =
     if id' == id then Sv.empty else oget m id.
  Proof. by rewrite /oget Mvar.removeP;case:ifP. Qed.

  Lemma rm_xP m x id : Sv.Equal (oget (rm_x m x) id) (Sv.remove x (oget (mid m) id)).
  Proof.
    rewrite /rm_x;case Heq: (Mvar.get (mvar m) x) => [id'|];last first.
    + case: (SvP.MP.In_dec x (oget (mid m) id));last by SvD.fsetdec.
      by rewrite -mvalid Heq.
    rewrite /ms_upd oget_set;case:ifPn => [/eqP -> //| /eqP].
    case: (SvP.MP.In_dec x (oget (mid m) id));last by SvD.fsetdec.
    by rewrite -mvalid Heq => -[->].
  Qed.

  Lemma valid_rm m id : valid (rm_id m id) (Mvar.remove (mid m) id).
  Proof.
    move=> x id';rewrite oget_rm;case:ifPn => [/eqP <- | Hne].
    + by split => [/rm_id_eq | ] //;SvD.fsetdec.
    by rewrite rm_idP_neq // mvalid.
  Qed.

  Definition remove m id := @mkT (rm_id m id) (Mvar.remove (mid m) id) (valid_rm m id).

  Lemma removeP m id x' :
    get (remove m id) x' =
      match get m x' with
      | Some id' => if id == id' then None else Some id'
      | None     => None
      end.
  Proof.
    rewrite /remove /get /= rm_idP /get; case: ifPn.
    + by move=> /Sv_memP;rewrite -mvalid => ->;rewrite eq_refl.
    move=> /Sv_memP;case Hg: Mvar.get => [id'|]//=;case:ifP => //= /eqP ?;subst id'.
    by move:Hg; rewrite mvalid => H /(_ H).
  Qed.

  Lemma valid_set m x id :
    valid (Mvar.set (rm_id m id) x id) (Mvar.set (rm_x m x) id (Sv.singleton x)).
  Proof.
    move=> y idy;rewrite Mvar.setP;case:eqP => [<- | Hne].
    + rewrite oget_set;case:eqP => [<- | Hne'];first by split => //;SvD.fsetdec.
      by rewrite rm_xP;split => [[]/Hne' | ] //;SvD.fsetdec.
    rewrite rm_idP oget_set;case:eqP => [<-| Hne'].
    + split;last by SvD.fsetdec.
      by case:ifPn => // /Sv_memP;rewrite -mvalid => H /H.
    rewrite rm_xP;case: ifPn => /Sv_memP H;split => // H1.
    + by move: H1 H Hne'=> /SvD.F.remove_3;rewrite -!mvalid => -> [->].
    + by move:H1;rewrite mvalid;SvD.fsetdec.
    by move: H1 => /SvD.F.remove_3;rewrite mvalid.
  Qed.

  Definition set m x id := mkT (valid_set m x id).

  Lemma valid_add m x id :
    valid (Mvar.set (mvar m) x id) (ms_upd (rm_x m x) (fun s => Sv.add x s) id).
  Proof.
    move=> y idy;rewrite Mvar.setP;case:eqP => Hxy.
    + subst y; rewrite /ms_upd;rewrite oget_set;split => [ [<-]| ].
      + by rewrite eq_refl;SvD.fsetdec.
      by case:eqP => [<- //| ?];rewrite rm_xP;SvD.fsetdec.
    by rewrite /ms_upd oget_set mvalid;case:eqP => [<- | ]; rewrite rm_xP;SvD.fsetdec.
  Qed.

  Definition add m x id := mkT (valid_add m x id).

  Lemma valid_empty : valid (@Mvar.empty _) (@Mvar.empty _).
  Proof. move=> x id;rewrite Mvar.get0 /oget Mvar.get0;split => //=;SvD.fsetdec. Qed.

  Definition empty := mkT valid_empty.

  End Mv.

  Definition bool_dec (b:bool) : {b} + {~~b} :=
    if b as b0 return ({b0} + {~~ b0}) then left (erefl true)
    else right (erefl true).

  Definition vsubtype x y := subtype (vtype x) (vtype y).

  Definition vsubtypeP x y := bool_dec (vsubtype x y).

  Definition mset_valid (mvar: Mvar.t var) (mset:Sv.t) :=
    forall x id, Mvar.get mvar x = Some id -> Sv.In x mset /\ vsubtype x id.

  Record t_ := mkT {
    mv : Mv.t;
    mset : Sv.t;
    svalid: mset_valid (Mv.mvar mv) mset;
  }.

  Definition t := t_.

  Definition get (m:t) (x:var) := Mv.get (mv m) x.

  Lemma mset_valid_set m x id :
    subtype (vtype x) (vtype id) ->
    mset_valid (Mv.mvar (Mv.set (mv m) x id)) (Sv.add x (mset m)).
  Proof.
    move=> hsub y idy;rewrite Mvar.setP;case: eqP => ?.
    + by move=> [?];subst; split=> //;SvD.fsetdec.
    by rewrite Mv.rm_idP;case:ifPn => //_ /svalid [??];split => //;SvD.fsetdec.
  Qed.

  Definition set m x id h := mkT (@mset_valid_set m x id h).
  Arguments set m x id h : clear implicits.

  Lemma mset_valid_add m x id :
    subtype (vtype x) (vtype id) ->
    mset_valid (Mv.mvar (Mv.add (mv m) x id)) (Sv.add x (mset m)).
  Proof.
    move=> h y idy;rewrite Mvar.setP;case: eqP => ?.
    + by move=> [?];subst; split=> //;SvD.fsetdec.
    by move=> /svalid [??];split=> //;SvD.fsetdec.
  Qed.

  Definition add m x id h := mkT (@mset_valid_add m x id h).
  Arguments add m x id h : clear implicits.

  Definition addc m x id :=
    if vsubtypeP x id is left h then add m x id h
    else m.

  Lemma mset_valid_empty s : mset_valid (Mv.mvar Mv.empty) s.
  Proof. by move=> x id;rewrite Mvar.get0. Qed.

  Definition empty_s s := mkT (mset_valid_empty s).

  Definition empty := empty_s Sv.empty.

  Definition merge_aux m1 m2 :=
    Mvar.map2 (fun x ox ox' =>
      match ox, ox' with
      | Some idx, Some idx' => if idx == idx' then Some idx else None
      | Some idx, None      => if ~~(Sv.mem x (mset m2)) then Some idx else None
      | None, Some idx      => if ~~(Sv.mem x (mset m1)) then Some idx else None
      | None, None          => None
      end) (Mv.mvar m1.(mv)) (Mv.mvar m2.(mv)).

  Definition merge m1 m2 :=
    let mv := merge_aux m1 m2 in
    Mvar.fold (fun x idx m => addc m x idx) mv (empty_s (Sv.union (mset m1) (mset m2))).

  Lemma mset_valid_rm m id : mset_valid (Mv.mvar (Mv.remove (mv m) id)) (mset m).
  Proof.
    move=> y idy.
    have := Mv.removeP (mv m) id y.
    rewrite /Mv.get => ->.
    case: Mvar.get (@svalid m y) => [id'|] //.
    by move=> /(_ _ (refl_equal _));case:eqP => // ?? [<-].
  Qed.

  Definition remove m id :=  mkT (@mset_valid_rm m id).

  Lemma get0_s x s: get (empty_s s) x = None.
  Proof. apply Mvar.get0. Qed.

  Lemma setP m x id y h :
    get (set m x id h) y =
      if x == y then Some id
      else if Sv.mem y (Mv.oget (Mv.mid (mv m)) id) then None
      else get m y.
  Proof. by rewrite /get/set /Mv.get/Mv.set /= Mvar.setP Mv.rm_idP. Qed.

  Lemma setP_mset m x id h : mset (set m x id h) = Sv.add x (mset m).
  Proof. by []. Qed.

  Lemma addP m x id y h :
    get (add m x id h) y = if x == y then Some id else get m y.
  Proof. by rewrite /get/add /Mv.get/Mv.add /= Mvar.setP. Qed.

  Lemma addP_mset m x id h : mset (add m x id h) = Sv.add x (mset m).
  Proof. by []. Qed.

  Lemma addcP m x id y :
    get (addc m x id) y =
     if vsubtype x id && (x == y) then Some id else get m y.
  Proof.
    rewrite /addc;case: vsubtypeP => [ heq | /negbTE -> //].
    by rewrite heq addP.
  Qed.

  Lemma merge_auxP m1 m2 x id :
    Mvar.get (merge_aux m1 m2) x = Some id ->
      get m1 x = Some id /\ get m2 x = Some id \/
      get m1 x = Some id /\ ~Sv.In x (mset m2) \/
      get m2 x = Some id /\ ~Sv.In x (mset m1).
  Proof.
    rewrite /merge_aux Mvar.map2P //.
    rewrite /get /Mv.get;case: Mvar.get => [id1 |];case: Mvar.get => [id2 |];
      last by tauto.
    + case:ifPn => // /eqP ->;tauto.
    + case:ifPn => // /Sv_memP;tauto.
    case:ifPn => // /Sv_memP;tauto.
  Qed.

  Lemma mergeP m1 m2 x id :
    get (merge m1 m2) x = Some id ->
      get m1 x = Some id /\ get m2 x = Some id \/
      get m1 x = Some id /\ ~Sv.In x (mset m2) \/
      get m2 x = Some id /\ ~Sv.In x (mset m1).
  Proof.
    rewrite /merge Mvar.foldP. set f := (f in foldl f).
    pose P := fun m =>
      get m x = Some id ->
       get m1 x = Some id /\ get m2 x = Some id \/
       get m1 x = Some id /\ ~Sv.In x (mset m2) \/
       get m2 x = Some id /\ ~Sv.In x (mset m1).
    have H : forall (l:list (var * var)) m,
      (forall p, p \in l -> Mvar.get (merge_aux m1 m2) p.1 = Some p.2) ->
      P m -> P (foldl f m l).
    + elim=> [|p l Hrec] //= m Hl Hm;apply Hrec.
      + by move=> ? H;apply Hl;rewrite in_cons H orbC.
      rewrite /f /P.
      have /Hl -/merge_auxP Hp := mem_head p l.
      have : vsubtype p.1 p.2.
      + have : get m1 p.1 = Some p.2 \/ get m2 p.1 = Some p.2 by intuition.
        by move=> [] /svalid [].
      by rewrite addcP => ->; case:eqP => [<- [<-] //| ne ];apply Hm.
    apply H;first by move=> p /Mvar.elementsP.
    by rewrite /P get0_s.
  Qed.

  Lemma mergeP_mset m1 m2 : Sv.Subset (Sv.union (mset m1) (mset m2)) (mset (merge m1 m2)).
  Proof.
    rewrite /merge Mvar.foldP. set f := (f in foldl f).
    pose P := fun m => Sv.Subset (Sv.union (mset m1) (mset m2)) (mset m).
    have : P (empty_s (Sv.union (mset m1) (mset m2))).
    + by rewrite /P /empty_s.
    have :
      (forall p, p \in Mvar.elements (merge_aux m1 m2) -> vsubtype p.1 p.2).
    + move=> p /Mvar.elementsP -/merge_auxP ?.
      have : get m1 p.1 = Some p.2 \/ get m2 p.1 = Some p.2 by intuition.
      by move=> [] /svalid [].
    elim : Mvar.elements (empty_s _) => //= -[x idx] l Hl m Hp Hm.
    apply Hl;first by move=> p hin;apply Hp;rewrite in_cons hin orbT.
    move:Hm;rewrite /f /P /addc /=.
    case: vsubtypeP => [? | ].
    + rewrite addP_mset;SvD.fsetdec.
    by have /= -> := Hp _ (mem_head (x, idx) l).
  Qed.

  Lemma removeP m id x :
    get (remove m id) x =
      match get m x with
      | Some id' => if id == id' then None else Some id'
      | None     => None
      end.
  Proof. apply Mv.removeP. Qed.

  Definition incl m1 m2 :=
    Sv.subset (mset m2) (mset m1) &&
    let mv1 := Mv.mvar m1.(mv) in
    let mv2 := Mv.mvar m2.(mv) in
    Sv.for_all (fun x =>
       match Mvar.get mv1 x with
       | Some idx => Mvar.get mv2 x == Some idx
       | None     => true
       end) (mset m2).

  Lemma inclP m1 m2 :
    reflect ((forall x id, Sv.In x (mset m2) -> get m1 x = Some id -> get m2 x = Some id) /\
             Sv.Subset (mset m2) (mset m1))
            (incl m1 m2).
  Proof.
    rewrite /incl andbC; apply (equivP andP).
    match goal with |- (is_true ?A /\ _) <-> (?B /\ _) => have : reflect B A end.
    + apply: (equivP idP).
      rewrite /is_true -SvD.F.for_all_iff;split => [ H x id| H x] /H;
        rewrite /get /Mv.get.
      + by move=> H1 H2;move: H1; rewrite H2 => /eqP.
      by case: Mvar.get => // idx /(_ _ (refl_equal _)) /eqP.
    by move=> /rwP ->;rewrite SvD.F.subset_iff.
  Qed.

  Lemma incl_refl r : incl r r.
  Proof. by apply/inclP;split. Qed.

  Lemma incl_trans r2 r1 r3 : incl r1 r2 -> incl r2 r3 -> incl r1 r3.
  Proof.
    move=> /inclP [H1 H3] /inclP [H2 H4];apply/inclP;split;last by SvD.fsetdec.
    by move=> x id Hin Hget;apply H2 => //;apply H1 => //;SvD.fsetdec.
  Qed.

  Lemma merge_incl_l r1 r2 : incl (merge r1 r2) r1.
  Proof.
    apply/inclP;split;first by move=> x idx Hin /mergeP;tauto.
    by have := @mergeP_mset r1 r2;SvD.fsetdec.
  Qed.

  Lemma merge_incl_r r1 r2 : incl (merge r1 r2) r2.
  Proof.
    apply/inclP;split;first by move=> x idx Hin /mergeP;tauto.
    by have := @mergeP_mset r1 r2;SvD.fsetdec.
  Qed.

  End M.

  Definition check_v xi1 xi2 (m:M.t) : cexec (M.t) :=
    let x1 := xi1.(v_var) in
    let x2 := xi2.(v_var) in
    if M.vsubtypeP x1 x2 is left h then
      match M.get m x1 with
      | None     =>
        if Sv.mem x1 (M.mset m)
        then cerror (Cerr_varalloc xi1 xi2 "variable already set") 
        else cok (M.set m x1 x2 h)
      | Some x2' =>
        if x2 == x2' then cok m
        else cerror (Cerr_varalloc xi1 xi2 "variable mismatch")
      end
    else cerror (Cerr_varalloc xi1 xi2 "type mismatch").
 

Section CHECKE.

Context (check_e_eval : pexpr -> pexpr -> M.t -> cexec M.t).
Fixpoint check_es_eval es1 es2 m : cexec M.t := 
  match es1, es2 with 
  | [::], [::] => ok m
  | e::es, e'::es' => 
    Let re := check_e_eval e e' m in
    Let res := check_es_eval es es' re in
    ok res
  | _, _ => cerror (Cerr_fold2 "case not possible") 
  end.

End CHECKE.

  Fixpoint check_e_eval (e1 e2:pexpr) (m:M.t) : cexec M.t :=
    let err _ := cerror (Cerr_neqexpr e1 e2 salloc) in
    match e1, e2 with
    | Pconst n1, Pconst n2 =>
      if n1 == n2 then cok m else err tt
    | Pbool  b1, Pbool  b2 =>
      if b1 == b2 then cok m else err tt
    | Parr_init n1, Parr_init n2 =>
      if n1 == n2 then cok m else err tt
    | Pvar   x1, Pvar   x2 => check_v x1 x2 m
    | Pglobal g1, Pglobal g2 =>
      if g1 == g2 then cok m else err tt
    | Pget w1 x1 e1, Pget w2 x2 e2 =>
      if w1 == w2 then check_v x1 x2 m >>= check_e_eval e1 e2 else err tt
    | Pload w1 x1 e1, Pload w2 x2 e2 =>
      if w1 == w2 then check_v x1 x2 m >>= check_e_eval e1 e2 else err tt
    | Papp1 o1 e1, Papp1 o2 e2 =>
      if o1 == o2 then check_e_eval e1 e2 m
      else cerror (Cerr_neqop1 o1 o2 salloc)
     | Papp2 o1 e11 e12, Papp2 o2 e21 e22 =>
      if o1 == o2 then check_e_eval e11 e21 m >>= check_e_eval e12 e22
      else cerror (Cerr_neqop2 o1 o2 salloc)
    | PappN o1 es1, PappN o2 es2 =>
      if o1 == o2
      then check_es_eval check_e_eval es1 es2 m 
      (*then fold2 (Cerr_fold2 "allocation: check_e (appN)") check_e_eval es1 es2 m*)
      else cerror (Cerr_neqopN o1 o2 salloc)
    | Pif t e e1 e2, Pif t' e' e1' e2' =>
      if t == t' then
        check_e_eval e e' m >>= check_e_eval e1 e1' >>= check_e_eval e2 e2'
      else err tt
    | _, _ => err tt
    end.

  Definition check_e (e1 e2 : pexpr) (m : M.t) : cexec (M.t * leak_e_tr) :=
    Let rs := check_e_eval e1 e2 m in
    cok (rs, LT_id).

  Definition check_es es1 es2 m : cexec (M.t * seq leak_e_tr) :=
   Let rs := check_es_eval check_e_eval es1 es2 m in 
   let lts :=  map (fun x => LT_id) es1 in
   cok (rs, lts).


  Definition check_var (x1 x2:var) m (h:M.vsubtype x1 x2): cexec (M.t) :=
    cok (M.set m x1 x2 h).

  Definition check_varc (xi1 xi2:var_i) m : cexec (M.t) :=
    let x1 := xi1.(v_var) in
    let x2 := xi2.(v_var) in
    if M.vsubtypeP x1 x2 is left h then check_var m h
    else cerror (Cerr_varalloc xi1 xi2 "type mismatch").

  Definition is_Pvar (e:option (stype * pexpr)) :=
    match e with
    | Some (ty, Pvar x) => Some (ty,x)
    | _ => None
    end.

  Lemma is_PvarP e ty x : is_Pvar e = Some (ty,x) -> e = Some (ty, Pvar x).
  Proof. by case: e => //= -[? []] //= v [<- <-]. Qed.

  Definition check_lval_eval (e2:option (stype * pexpr)) (x1 x2:lval) m : cexec M.t :=
    let err _ := cerror (Cerr_neqlval x1 x2 salloc) in
    match x1, x2 with
    | Lnone  _ t1, Lnone _ t2  =>
      if subtype t1 t2 then cok m else err tt
    | Lnone  _ t1, Lvar x      =>
      if subtype t1 x.(v_var).(vtype) then
        cok (M.remove m x.(v_var))
      else err tt
    | Lvar x1    , Lvar x2     =>
      match is_Pvar e2 with
      | Some (ty, x2') =>
        if M.vsubtypeP x1 x2 is left h then
          if (vtype x1 == ty) && (vtype x1 == vtype x2) && (x2.(v_var) == x2') 
          then cok (M.add m x1 x2 h)
          else check_var m h
        else cerror (Cerr_varalloc x1 x2 "type mismatch")
      | _               => check_varc x1 x2 m
      end
    | Lmem w1 x1 e1, Lmem w2 x2 e2  =>
      if w1 == w2 
      then check_v x1 x2 m >>= check_e_eval e1 e2 else err tt
    | Laset w1 x1 e1, Laset w2 x2 e2 =>
      if w1 == w2 
      then check_v x1 x2 m >>= check_e_eval e1 e2 >>= check_varc x1 x2
      else err tt
    | _          , _           => err tt
    end.

  Definition check_lval  (e2:option (stype * pexpr)) (x1 x2:lval) m : cexec (M.t * leak_e_tr) :=
    Let rs := check_lval_eval e2 x1 x2 m in
    cok (rs, LT_id).

  Definition eq_alloc (r:M.t) (vm1 vm2:vmap) :=
    [/\ vm_uincl vmap0 vm2,
        (forall x, ~Sv.In x (M.mset r) -> vm1.[x] = pundef_addr x.(vtype)) &
        (forall x x', M.get r x = Some x' ->
                      eval_uincl vm1.[x] vm2.[x'])].

  Lemma eq_alloc_empty: eq_alloc M.empty vmap0 vmap0.
  Proof. by split;rewrite /vm_uincl=> *;rewrite /vmap0 !Fv.get0. Qed.

  Lemma eq_alloc_incl r1 r2 vm vm':
    M.incl r2 r1 ->
    eq_alloc r1 vm vm' ->
    eq_alloc r2 vm vm'.
  Proof.
    move=> /M.inclP [Hi Hsub] [ Huincl epa eqa];split=>//.
    + by move=> x Hx;apply epa;SvD.fsetdec.
    move=> x x'; case: (Sv_memP x (M.mset r1)) => [ /Hi H /H /eqa // | /epa -> hget].
    have := Huincl x'.
    have [_ /(_ x') /= heq _ ]:= eq_alloc_empty.
    rewrite heq;last by rewrite SvD.F.empty_iff.
    apply: eval_uincl_trans; apply subtype_eval_uincl_pundef.
    by have []:= M.svalid hget.
  Qed.

  Lemma check_vP x1 x2 r re vm1 vm2 :
    check_v x1 x2 r = ok re ->
    eq_alloc r vm1 vm2 ->
    eq_alloc re vm1 vm2 /\
    (forall v1 : value,
       get_var vm1 x1 = ok v1 ->
       exists v2 : value, get_var vm2 x2 = ok v2 /\ value_uincl v1 v2).
  Proof.
    rewrite /check_v;case: M.vsubtypeP => // hsub.
    have husub : subtype (vundef_type (vtype x1)) (vtype x2).
    +  by apply (subtype_trans (subtype_vundef_type (vtype x1))).
    case Hget : M.get => [id | ].
    + case: eqP => //= ? [<-];subst id => Hea;split=>//.
      case: Hea => _ _ /(_ _ _ Hget) Hev v1 {Hget} Hget.
      case: x1 x2 hsub husub Hget Hev=> [[xt1 xn1] ii1] [[xt2 xn2] ii2] /= hsub husub.
      rewrite /get_var;apply: on_vuP => //= t -> <- /=.
      by case: (vm2.[_])%vmap => //= z' Hz';exists (pto_val z').
    case: ifPn => //= /Sv_memP Hnot [] <- [ Hvm0 Hset Huincl];split;first split=>//.
    + by move=> x;rewrite M.setP_mset => ?;apply Hset;SvD.fsetdec.
    + move=> x id;rewrite M.setP;case:eqP => [<- [<-]| Hne].
      + rewrite (Hset _ Hnot) /=.
        apply: (eval_uincl_trans (v2:= (pundef_addr (vtype x2)))).
        + by apply subtype_eval_uincl_pundef.
        by have := Hvm0 x2; rewrite Fv.get0.
      by case:ifP => // _;apply Huincl.
    move=> v1;rewrite /get_var (Hset _ Hnot) //=.
    case: x2 hsub husub (Hvm0 x2) => [[xt2 xn2] ?] /= hsub husub;rewrite Fv.get0 /= => heval.
    apply on_vuP => [ v heq| //] ?;subst v1.
    have : eval_uincl (pundef_addr (vtype x1)) vm2.[{| vtype := xt2; vname := xn2 |}].
    + by apply: eval_uincl_trans heval; apply subtype_eval_uincl_pundef.
    by rewrite heq; case: (vm2.[_]) => //= a ?; eexists;split;first by reflexivity.
  Qed.

Section Section.
Context {LO:LeakOp}.

  Section CHECK_EP.
    Context (gd: glob_decls) (vm2: vmap).

    Let P e1 : Prop :=
      ∀ e2 r re vm1, check_e_eval e1 e2 r = ok (re) →
      eq_alloc r vm1 vm2 →
      eq_alloc re vm1 vm2 ∧
      ∀ m v1 l1, sem_pexpr gd {| emem := m ; evm := vm1 |} e1 = ok (v1, l1) →
      exists v2, sem_pexpr gd {| emem := m ; evm := vm2 |} e2 = ok (v2, l1) /\
                 value_uincl v1 v2.

    Let Q es1 : Prop :=
      ∀ es2 r re vm1,
      check_es_eval check_e_eval es1 es2 r = ok re ->
      (*fold2 err (fun e1 e2 r1 => Let rs := check_e e1 e2 r1.1 in
                            ok (rs.1, rcons r1.2 rs.2)) es1 es2 (r, [::]) = ok (re, lte) ->*)
      (*fold2 err check_e es1 es2 r = ok re →*)
      eq_alloc r vm1 vm2 →
      eq_alloc re vm1 vm2 ∧
      ∀ m vs1, sem_pexprs gd {| emem := m ; evm := vm1 |} es1 = ok vs1 →
      exists vs2, sem_pexprs gd {| emem := m ; evm := vm2 |} es2 = ok vs2 
                      /\ List.Forall2 value_uincl (unzip1 vs1) (unzip1 vs2)
                      /\ (unzip2 vs1) = (unzip2 vs2).

    Lemma check_e_esP : (∀ e, P e) ∧ (∀ es, Q es).
    Proof.
      apply: pexprs_ind_pair; split; subst P Q => //=.
      - move=> [] r re vm1 Ht. move=> H. case: Ht=> <- /=.
        split. auto. move=> m' vs1 [] <- /=. exists [::].
        split. auto. split. rewrite /=. auto. auto.
        move=> vm0 //.
      - move=> e He es Hes [] // e' es' r re vm1. t_xrbindP.
        move=> r' He' re' Hes' <- Heq.
        move: (He e' r r' vm1). rewrite He' /=. move=> []. auto. auto. move=> Heq' Hse.
        move: (Hes es' r' re' vm1). rewrite Hes' /=. move=> []. auto. auto.
        move=> Heq'' Hse'. split=> //.
        move=> m vs1. t_xrbindP. move=> [v le] He'' vs Hes'' <-.
        move: (Hse m v le He''). move=> [] v' [] Hee Hv. move: (Hse' m vs Hes'').
        move=> [] vs' [] Hess [] Hvs Hvs' /=. rewrite Hee /=. rewrite Hess /=.
        exists ((v', le) :: vs'). split=> //.
        split=> //. rewrite /=. apply List.Forall2_cons. auto. auto. rewrite /=.
        by rewrite Hvs'.
      - rewrite /check_e. move=> z1 [] // z2 r re vm1 /=.
        t_xrbindP. case: ifPn. move=> /eqP <- [] <- Hvm1.
        split=> //. move=> m v1 l1 [] <- <-. by exists z1.
        move=> H //=.
      - move=> b1 [] // b2 r re vm1 /=. t_xrbindP.
        case: ifPn. move=> /eqP <- [] <- Hvm. split. auto.
        move=> vm2' v1 l1 [] <- <-.
        by exists b1. move=> /eqP H //=.
      - move=> n1 [] // n2 r re vm1 /=. t_xrbindP.
        case: ifPn. move=> /eqP <- [] <- Hvm. split. auto.
        move=> vm2' v1 l1 [] <- <- /=.
        by exists (Varr (WArray.empty n1)). move=> /eqP H //=.
      - move=> x1 [] // x2 r re vm1 /=. t_xrbindP.
        t_xrbindP. move=> /check_vP Hv Hvm.
        move: (Hv vm1 vm2 Hvm). move=> [] Hvm' Hv'. split. auto.
        move=> vm2' v1 l1. t_xrbindP. move=> v1' Hg <- <- /=.
        move: (Hv' v1' Hg). move=> [] v2 [] -> Hv'' /=. exists v2.
        by split.
      - move=> g1 [] // g2 r re vm1 /=. t_xrbindP.
        case: ifPn. move=> /eqP <- [] <- Hvm. split. auto. move=> vm2' v1 l1.
        t_xrbindP. move=> v2 Hg <- <- /=. rewrite Hg /=. exists v2. by split.
        move=> /eqP H //=.
      - move=> sz1 x1 e1 He1 [] // sz2 x2 e2 r re vm1 /=.
        case: eqP => // <-. t_xrbindP. move=> r' Hcv Hce Hvm.
        move: check_vP. move=> Hcv'. move: (Hcv' x1 x2 r r' vm1 vm2 Hcv Hvm).
        move=> [] Hvm' {Hcv'} Hcv'. move: (He1 e2 r' re vm1).
        rewrite Hce /=. move=> []. auto. auto. move=> Hvm1. move=> He.
        split. auto. move=> vm1' v1 l1.
        apply: on_arr_varP=> n t Heqt /Hcv' [v2 []].
        rewrite /on_arr_var; case: v2 => //= n' t' -> Ht.
        t_xrbindP. move=> [yv yl] He1' z Hv sz2' /WArray.uincl_get Ha <- <- /=.
        move: (He vm1' yv yl He1'). move=> [] yv' [] -> /= Hyv.
        move: value_uincl_int. move=> Hvv. move: (Hvv yv yv' z Hyv Hv).
        move=> {Hvv} [] Hyv1 Hyv2. rewrite -Hyv1 in Hyv2. rewrite -Hyv2 in Hv.
        rewrite Hv /=. move: (Ha n' t' Ht). move=> {Ha} -> /=. by exists (Vword sz2').
      - move=> sz1 x1 e1 He1 [] // sz2 x2 e2 r re vm1 /=.
        case: eqP => // ->. t_xrbindP. move=> r' Hcv Hce Hvm.
        move: check_vP. move=>Hcv'. move: (Hcv' x1 x2 r r' vm1 vm2 Hcv Hvm).
        move=> [] Hvm' Hg. move: (He1 e2 r' re vm1). rewrite Hce /=.
        move=> []. auto. auto. move=> Hvm'' Hce'.
        split. auto. move=> vm1' v1 l1. t_xrbindP.
        move=> yv v Hg'  /value_uincl_word Hp [yv' yl'] He yv''
               /value_uincl_word Hp' w Hr <- <- /=.
        move: (Hce' vm1' yv' yl' He). move=> [] v2 [] He2 Hv.
        move: (Hg v Hg'). move=> {Hg} [] v3 [] -> Hv' /=.
        move: (Hp v3 Hv'). move=> -> /=. rewrite He2 /=.
        move: (Hp' v2 Hv). move=> -> /=. rewrite Hr /=. by exists (Vword w).
      - move=> op1 e1 He1 [] // op2 e2 r re vm1 /=.
        case: eqP => // <-. move=> Hce Hvm1.
        move: (He1 e2 r re vm1 Hce Hvm1). move=> [] Hvm' He.
        split. auto. t_xrbindP. move=> vm1' v l [yv yl] he vo Ho les Hl <- <- /=.
        move: (He vm1' yv yl he). move=> {He} [] yv2 [] -> Hyv /=.
        move: vuincl_sem_sop1. move=> Ho'. move: (Ho' op1 yv yv2 vo Hyv Ho).
        move=> -> /=. exists vo. by have -> /= := leak_sop1_eq Hyv Hl.
      - move=> op1 e11 He11 e12 He12 [] // op2 e21 e22 r re vm1 /=.
        case: eqP => // <-. t_xrbindP. move=> r' He1 He2 Hvm1.
        move: (He11 e21 r r' vm1). rewrite He1. move=> []. auto. auto.
        move=> Hvm2 He1'.
        move: (He12 e22 r' re vm1). rewrite He2. move=> []. auto. auto.
        move=> Hvm2' He2'.
        split. auto. t_xrbindP. move=> vm1' v l [v1' l1'] he1 [v2' l2'] he2 /=.
        move: (He1' vm1' v1' l1' he1). move=> [] v2 [] -> Hv vo Ho' les Hl <- <- /=.
        move: (He2' vm1' v2' l2' he2). move=> [] v3 [] -> Hov /=.
        move: vuincl_sem_sop2. move=> Ho''.
        move: (Ho'' op1 v1' v2 v2' v3 vo Hv Hov Ho').
        move=> {Ho''} -> /=. exists vo. by have -> /= := leak_sop2_eq Hv Hov Hl.
      - move=> op1 es1 Hes1 [] // op2 es2 r re vm1.
        case: eqP => // <- {op2}. t_xrbindP. move=> ok_re Heq.
        move: (Hes1 es2 r re vm1).
        rewrite ok_re /=. move=> []. auto. auto. move=> Heq' Hes'. split=> //.
        t_xrbindP. move=> m v le vs Hes vo Ho les Hl <- Hle. rewrite /sem_pexprs in Hes'.
        move: (Hes' m vs Hes). move=> [] vs' [] -> [] Hv' Hl' /=.
        move: vuincl_sem_opN. move=> Ho'. move: (Ho' op1 (unzip1 vs) vo (unzip1 vs') Ho Hv').
        move=> [] vo' -> Hvo /=. exists vo'. split=> //. rewrite -Hle. rewrite -Hl'.
        by have -> /= := leak_opN_eq Hv' Hl.
      move=> t e He e11 He11 e12 He12 [] // t' e2 e21 e22 r re vm1 /=.
      case: eqP => // <-.
      t_xrbindP. move=> m m' Hce Hce1 Hce2 Hvm.
      move: (He e2 r m' vm1). rewrite Hce /=. move=> []. auto. auto.
      move=> {He} Hvm' He'.
      move: (He11 e21 m' m vm1). rewrite Hce1 /=. move=> []. auto. auto.
      move=> {He11} Hvm1' He1'.
      move: (He12 e22 m re vm1). rewrite Hce2 /=. move=> []. auto. auto.
      move=> {He12} Hvm2' He2'.
      split. auto. t_xrbindP.
      move=> vm1' v l [yv yl] he b /value_uincl_bool hb
             [yv' yl'] he1' [yv'' yl''] he2' tv
             /truncate_value_uincl ht tv' /truncate_value_uincl ht' <- <- /=.
      move: (He' vm1' yv yl he). move=> [] v1' [] -> Hv1 /= {He'}.
      move: (hb v1' Hv1). move=> [] _ -> /=. move: (He1' vm1' yv' yl' he1').
      move=> [] v2' [] -> Hv2 /= {He1'}. move: (He2' vm1' yv'' yl'' he2').
      move=> [] v3' [] -> Hv3 /= {He2'}. move: (ht v2' Hv2). move=> [] vt -> Hvt /=.
      move: (ht' v3' Hv3). move=> [] vt' -> Hvt' /=. case: (b). by exists vt. by exists vt'.
   Qed.

  End CHECK_EP.

  Definition check_eP' gd e1 e2 r re lte vm1 vm2 :=
    (check_e_esP gd vm2).1 e1 e2 r re lte vm1.

  Lemma check_eP : forall gd e1 e2 r re lte vm1 vm2 stk,
    check_e e1 e2 r = ok (re, lte) ->
    eq_alloc r vm1 vm2 ->
    eq_alloc re vm1 vm2 /\
    forall m v1 l1,  sem_pexpr gd (Estate m vm1) e1 = ok (v1, l1) ->
                     exists v2, sem_pexpr gd (Estate m vm2) e2 = ok (v2, leak_E stk lte l1) /\ value_uincl v1 v2.
    Proof.
    rewrite /check_e. move: check_eP'. move=> H. t_xrbindP. move=> gd e e2 r re lte vm1 vm2 stk re' He'. 
    move: (H gd e e2 r re' vm1 He'). move=> H'. move=> [] <- <- Hvm1. move: (H' vm2 Hvm1). move=> {H'} H'.
    apply H'.
    Qed.


  Lemma vm_uincl0_set vm x (v : exec (psem_t (vtype x))) :
    vm_uincl vmap0 vm ->
    ((exists v', v = ok v') \/ v = undef_error) ->
    vm_uincl vmap0 vm.[x <- apply_undef v].
  Proof.
    move=> Hvm0 H z; case (x =P z) => [<- | /eqP Hne].
    + rewrite Fv.setP_eq /vmap0 Fv.get0 /=.
      by case: H => [[v']|] ?;subst v => //=;apply eval_uincl_undef.
    by rewrite Fv.setP_neq.
  Qed.

  Lemma eq_alloc_set x1 (v1 :exec (psem_t (vtype x1))) r x2 (v2 :exec (psem_t (vtype x2)))
            vm1 vm2 (h:M.vsubtype x1 x2) :
    eq_alloc r vm1 vm2 ->
    eval_uincl v1 v2 ->
    ((exists v', v1 = ok v') \/ (v1 = undef_error /\ vtype x1 = sbool)) ->
    eq_alloc (M.set r x1 x2 h) vm1.[x1 <- apply_undef v1]
                               vm2.[x2 <- apply_undef v2].
  Proof.
    move=> [Hvm0 Hin Hget] Hu H1.
    have H2: (exists v', v2 = ok v') \/ (v2 = undef_error /\ vtype x2 = sbool).
    + elim H1 => [[v1' ?] | [? hx1]]; subst v1.
      + by move: Hu => /=; case: v2 => //; eauto.
      move: h;rewrite /M.vsubtype hx1 => /eqP ->.
      by case: v2 Hu => /= [ | ? <-]; eauto.
    split.
    + apply vm_uincl0_set => //;intuition.
    + move=> z;rewrite M.setP_mset => Hnin.
      by rewrite Fv.setP_neq;[apply Hin|apply /eqP];SvD.fsetdec.
    move=> x id;rewrite M.setP;case:eqP => [<-[<-] | /eqP Hne].
    + rewrite !Fv.setP_eq.
      case: H1 Hu => [ [v1' ?]| [? heq1]];subst v1;
      case: H2 => [ [v2' ?]| [? heq2]];subst v2 => //=; last by rewrite heq1 heq2.
      by move: h v2'; rewrite /M.vsubtype heq1 => /eqP <-.
    case: ifPn => //= /Sv_memP Hid Hgetx.
    rewrite !Fv.setP_neq //;first by apply Hget.
    move: Hgetx;rewrite M.Mv.mvalid => Hgetx.
    by apply/eqP => ?; subst id; apply: Hid.
  Qed.

  Lemma eq_alloc_add x1 (v1:exec (psem_t (vtype x1))) r x2  vm1 vm2 (h:M.vsubtype x1 x2) :
    eq_alloc r vm1 vm2 ->
    let v2 := vm2.[x2] in
    eval_uincl v1 v2 ->
    ((exists v', v1 = ok v') \/ (v1 = undef_error /\ vtype x1 = sbool)) ->
    eq_alloc (M.add r x1 x2 h) vm1.[x1 <- apply_undef v1]
                               vm2.[x2 <- apply_undef v2].
  Proof.
    move=> [Hvm0 Hin Hget] v2 /= Hu H1.
    have H2: (exists v', v2 = ok v') \/ (v2 = undef_error /\ vtype x2 = sbool).
    + elim H1 => [[v1' ?] | [? hx1]]; subst v1.
      + by move: Hu => /=; case: v2 => //; eauto.
      move: h;rewrite /M.vsubtype hx1 => /eqP ->.
      by case: v2 Hu => /= [ | ? <-]; eauto.
    split.
    + by apply vm_uincl0_set => //;intuition.
    + move=> z;rewrite M.addP_mset => Hnin.
      by rewrite Fv.setP_neq;[apply Hin|apply /eqP];SvD.fsetdec.
    move=> x id;rewrite M.addP;case:eqP => [<-[<-] | /eqP Hne].
    + rewrite !Fv.setP_eq.
      case: H1 Hu => [ [v1' ?]| [? heq1]];subst v1;
      case: H2 => [ [v2' ->]| [-> heq2]] => //=;last by rewrite heq1 heq2.
      by move: h v2'; rewrite /M.vsubtype heq1 => /eqP <-.
    move=> hx;rewrite Fv.setP_neq //.
    case: (x2 =P id) => [? | /eqP hne];last by rewrite Fv.setP_neq //;apply Hget.
    subst;rewrite Fv.setP_eq;have := Hget _ _ hx.
    move: H2;rewrite /v2 => -[ [v' ->]| [-> ?]] /=; case : vm1.[x] => //= -[] // _.
    by case: (vtype id).
  Qed.

  Lemma check_varP r1 r1' vm1 vm2 vm1' x1 x2 v1 v2 (h:M.vsubtype x1 x2):
    eq_alloc r1 vm1 vm2 ->
    @check_var x1 x2 r1 h = ok r1' ->
    set_var vm1 x1 v1 = ok vm1' ->
    value_uincl v1 v2 ->
    exists vm2' : vmap,
      set_var vm2 x2 v2 = ok vm2' /\ eq_alloc r1' vm1' vm2'.
  Proof.
    rewrite /check_var => Hea -[<-].
    apply: set_varP; rewrite /set_var.
    + move=> vx1 hvx1 <- hu.
      have [vx1' [hv2x1 hvx1']]:= pof_val_uincl hu hvx1.
      have [vx2 -> hsub /=] := subtype_pof_val_ok h hv2x1.
      eexists;split;first reflexivity.
      have hincl: eval_uincl (ok vx1) (ok vx2).
      + by apply: (eval_uincl_trans (v2:= ok vx1')).
      by apply (eq_alloc_set h Hea hincl); eauto.
    move=> v1' Hv1' <- Hu.
    case: x1 v1' h Hv1' (h) => t1 x1 /= /eqP ?;subst t1.
    case: x2 => t2 x2 h;rewrite /M.vsubtype => /to_bool_undef ? /=;subst v1.
    move=> h0; have /eqP ? := h0; subst t2; move: Hu => /eqP.
    move=> /type_of_val_bool [? | [b ?]]; subst v2 => /=;
      eexists; (split; first reflexivity).
    + have hincl : @eval_uincl sbool sbool undef_error undef_error by done.
      apply (eq_alloc_set h Hea hincl);eauto.
    have hincl : @eval_uincl sbool sbool undef_error (ok b) by done.
    apply (eq_alloc_set h Hea hincl);eauto.
  Qed.

  Lemma check_varcP r1 r1' vm1 vm2 vm1' x1 x2 v1 v2 :
    eq_alloc r1 vm1 vm2 ->
    check_varc x1 x2 r1 = ok r1' ->
    set_var vm1 x1 v1 = ok vm1' ->
    value_uincl v1 v2 ->
    exists vm2' : vmap,
      set_var vm2 x2 v2 = ok vm2' /\ eq_alloc r1' vm1' vm2'.
  Proof.
    by rewrite /check_varc; case: M.vsubtypeP => // h; apply check_varP.
  Qed.

  Lemma eq_alloc_rm r x s vm z :
    eval_uincl (pundef_addr (vtype x)) z ->
    eq_alloc r (evm s) vm ->
    eq_alloc (M.remove r x) (evm s) vm.[x <- z].
  Proof.
    move=> Hz [Hmap0 Hinit Halloc];split.
    + move=> y;case:(x =P y) => [<-|/eqP ne].
      + by rewrite Fv.setP_eq /vmap0 Fv.get0.
      by rewrite Fv.setP_neq.
    + by move=> y /=;apply: Hinit.
    move=> x0 id; rewrite M.removeP.
    case: M.get (Halloc x0) => [id' | ] //.
    move=> /(_ _ (refl_equal _));case:ifPn => //= Hne He [?];subst id'.
    rewrite Fv.setP_neq //;by apply: contra Hne => /eqP ->.
  Qed.

 Lemma check_lvalP gd r1 r1' lt' x1 x2 e2 s1 s1' le1' vm1 v1 v2 stk:
    check_lval e2 x1 x2 r1 = ok (r1', lt') ->
    eq_alloc r1 s1.(evm) vm1 ->
    value_uincl v1 v2 ->
    oapp (fun te2 =>
            Let vl := sem_pexpr gd (Estate s1.(emem) vm1) te2.2 in
            truncate_val te2.1 vl.1 = ok v2) true e2 ->
    write_lval gd x1 v1 s1 = ok (s1', le1') ->
    exists vm1',
      write_lval gd x2 v2 (Estate s1.(emem) vm1) = ok (Estate s1'.(emem) vm1', leak_E stk lt' le1') /\
      eq_alloc r1' s1'.(evm) vm1'.
  Proof.
    case: x1 x2 => /= [ii1 t1 | x1 | sz1 x1 p1 | sz1 x1 p1]
                      [ii2 t2 | x2 | sz2 x2 p2 | sz2 x2 p2] //=.
    (* Lnone case1 *)
    + rewrite /check_lval /=.
      case:ifP => //= hs [] <- <- Heq Hv h. t_xrbindP. move=> s2 H <- <-.
      have [-> [ [u hpof]| [hpof ?]]]:= write_noneP H; rewrite /write_none.
      + have [v1' ]:= subtype_pof_val_ok hs hpof.
        by move=> /(pof_val_uincl Hv) [v2' [-> ]] /= ??;eauto.
      subst t1;move/eqP: hs => ?;subst t2.
      have [->|[b] ->] /=:= pof_val_undef Hv hpof; eauto.
    (* Lnone case2 *)
    + rewrite /check_lval /=.
      case:ifP => //= hs [] <- <- Heqa Hu Happ. t_xrbindP. move=> s2 H <- <-.
      have [-> ]:= write_noneP H.
      rewrite /write_var /set_var => -[ [u]| ].
      + move=> /(subtype_pof_val_ok hs) [v3].
        move=> /(pof_val_uincl Hu) [z' [-> ?]] /= ?.
        eexists; split; eauto; apply eq_alloc_rm => //.
        by apply eval_uincl_undef.
      move=> [hpof ?];subst t1; case : x2 hs => -[tx2 x2] ii2 /= /eqP ?;subst tx2.
      have [->|[b] ->] /= := pof_val_undef Hu hpof; eexists;(split; first by eauto);
        apply eq_alloc_rm => //.
    (* Lvar case1 *)
    + rewrite /check_lval /=.
      rewrite /write_var => Hc Hvm1 Hv Happ. t_xrbindP.
      move=> s2 vm1' Hset <- <- <- /=.
      move: Hc; case: is_Pvar (@is_PvarP e2).
      + move=> [ty x] /(_ _ _ (refl_equal _)) ?; subst e2. rewrite /=.
        case: M.vsubtypeP=> // ht; case: ifPn. 
        move=> /andP[]/andP []/eqP ? /eqP heqt /eqP; subst ty.
        move=> hx [] <-.
        move: x1 x2 x heqt hx ht Hset Happ.
        move=> [[xt1 xn1] ii1] [[xt2 xn2] ii2] [x ii] /=.
        set x1 := {| vname := xn1 |}; set x2 := {| vname := xn2 |}.
        move=> hteq' hteq ht hset. t_xrbindP. move=> [v2' le'] vg Happ [] <- <- htr /=.
        apply: set_varP hset=> /=; rewrite /set_var.
        + move=> v1' Hv1 hh'; subst.
          apply: on_vuP Happ=> //.
          move=> v2'' hv2'' hhg; subst.
          have ?:= truncate_pto_val htr;subst v2.
          rewrite pof_val_pto_val /=;eexists;split;rewrite -h3 /=;first reflexivity.
          have /= := @eq_alloc_add x1 (ok v1') r1 x2 (evm s1) vm1 ht Hvm1.
          rewrite hv2'' /= /pval_uincl => H;apply H;last by eauto.
          by apply (value_uincl_pof_val Hv1 Hv).
        move=> /= hniw hv1 hh;subst; rewrite hniw /=.
        apply: on_vuP Happ => //.
        move=> v2'' heq hhg;subst;have ?:= truncate_pto_val htr;subst v2.
        rewrite pof_val_pto_val /=;eexists;split; rewrite -h3;first reflexivity.
        have /= := @eq_alloc_add x1 (pundef_addr xt2) r1 x2 (evm s1) vm1 ht Hvm1.
        rewrite heq /= apply_undef_pundef_addr=> H;apply H.
        + by apply eval_uincl_undef.
        by move /eqP: hniw => ->;right.
        move=> hh [] hc <-. move: check_varP. move=> hc'. rewrite /check_var in hc'.
        move: (hc' r1 r1' (evm s1) vm1 vm1' x1 x2 v1 v2 ht Hvm1).  move=> []. auto.
        rewrite hc /=. auto. auto. auto. move=> x0' [] -> /= Hvm1'. by exists x0'.
        move=> hh. t_xrbindP. move=> r2 hc [] <- <- /=. move: check_varcP. move=> hc'.
        move: (hc' r1 r2 (evm s1) vm1 vm1' x1 x2 v1 v2 Hvm1 hc Hset Hv). move=> [] vm2' [] -> /= Hvm2'.
        by exists vm2'.
    (* Lmem case *)
    + rewrite /check_lval /=.
      case: eqP => // -> /=. t_xrbindP. 
      move=> r2 r3 Hcv Hce [] <- <- Hvm1 Hv Happ wx vx.
      have [Hr2 H/H{H} [vx' [-> Hvx /=]]]:= check_vP Hcv Hvm1.
      move=> /(value_uincl_word Hvx) /= -> /=. move=> [ve le].
      case: (s1) Hvm1 Hr2 => sm1 svm1 /= Hvm1 Hr2.
      move: check_eP. move=> Hce'.
      rewrite /check_e in Hce'. move: (Hce' gd p1 p2 r3 r2 LT_id svm1 vm1 stk).
      rewrite Hce /=. move=> [] {Hce'}. auto. auto. 
      move=> Hr1' H/H{H} [] ve' [] -> Hve /= vp.
      move=> /(value_uincl_word Hve) /= -> /= w.
      move=> /(value_uincl_word Hv) /= -> /= sm1' -> /= <- /= <- /=.
      by exists vm1.
    (* Laset case *)
    rewrite /check_lval /=.
    case: eqP => // -> /=. t_xrbindP.
    move=> r2 r3 r4 Hcv Hce Hcva [] <- <- Hvm1 Hv Happ.
    apply: on_arr_varP=> n t Htx; rewrite /on_arr_var /=.
    move: check_vP. move=> Hcv'. move: (Hcv' x1 x2 r1 r4 (evm s1) vm1 Hcv Hvm1).
    move=> [] Hr3 H/H{H} [] vx2 [] -> /=.
    case: vx2 => //= n0 t2 Ht. t_xrbindP. move=> [ve le].
    case: (s1) Hvm1 Hr3 => sm1 svm1 /= Hvm1 Hr3.
    move: check_eP. move=> Hce'. rewrite /check_e in Hce'.
    move: (Hce' gd p1 p2 r4 r3 LT_id svm1 vm1 stk). rewrite Hce /=.
    move=> []. auto. auto. move=> Hr1' H/H{H} [] ve' [] -> Hve /= x0.
    move=> /(value_uincl_int Hve) [] h1 h2 /= w.
    move=> /(value_uincl_word Hv) -> /= a Ht1' vm2 Hvm2 <- <-. rewrite h2 /=.
    have h := WArray.uincl_set Ht Ht1'. move: h. move=> [] t2' [] -> Ht2' /=.
    have Hu: value_uincl (Varr a) (Varr t2') := Ht2'.
    have [vm2' [-> ?] /=]:= check_varcP Hr1' Hcva Hvm2 Hu.
    by exists vm2'.
  Qed.
End Section.

End CBAreg.

Module CheckAllocReg :=  MakeCheckAlloc CBAreg.

Lemma alloc_reg_funP_eq {LO:LeakOp} p fn fn' f f' m1 vargs vargs' vres vres' s1 s2 ltc lc: 
    CheckAllocReg.check_fundef (fn, f) (fn, f') = ok (fn', ltc)
  → mapM2 ErrType truncate_val (f_tyin f) vargs' = ok vargs
  → write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1
  → sem p s1 (f_body f) lc s2
  → mapM (λ x : var_i, get_var (evm s2) x) (f_res f) = ok vres
  → mapM2 ErrType truncate_val (f_tyout f) vres = ok vres'
  → ∃ (s1' : estate) (vm2 : vmap) (vres1 vres1' : seq value),
 [/\ mapM2 ErrType truncate_val (f_tyin f') vargs' = ok vargs,
     write_vars (f_params f') vargs {| emem := m1; evm := vmap0 |} = ok s1',
     sem p s1' (f_body f') lc {| emem := emem s2; evm := vm2 |},
     mapM (λ x : var_i, get_var vm2 x) (f_res f') = ok vres1
   & List.Forall2 value_uincl vres' vres1'
   ∧ mapM2 ErrType truncate_val (f_tyout f') vres1 = ok vres1'].
Proof.
  apply: (CheckAllocReg.alloc_funP_eq); last by exact 0%R.
  + by rewrite /CBAreg.check_e; t_xrbindP=> ???????? [<-].
  + by rewrite /CBAreg.check_lval; t_xrbindP => ?????????[<-].
Qed.

