(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Require Import psem compiler_util.
Require Export allocation.

Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Definition eq_alloc (r:M.t) (vm1 vm2:Vm.t) :=
    [/\ (forall x, ~Sv.In x (M.mset r) -> vm1.[x] = undef_addr x.(vtype)) &
        (forall x x', M.get r x = Some x' ->
                      value_uincl vm1.[x] vm2.[x'])].

Lemma eq_alloc_empty: eq_alloc M.empty Vm.init Vm.init.
Proof. by split => * //; rewrite Vm.initP. Qed.

Lemma eq_alloc_incl r1 r2 vm vm':
  M.incl r2 r1 ->
  eq_alloc r1 vm vm' ->
  eq_alloc r2 vm vm'.
Proof.
  move=> /M.inclP [Hi Hsub] [ epa eqa];split=>//.
  + by move=> x Hx;apply epa;SvD.fsetdec.
  move=> x x'; case: (Sv_memP x (M.mset r1)) => [ /Hi H /H /eqa // | /epa -> hget].
  apply subtype_value_uincl_undef.
  have [_ /compat_type_undef_t ->] := M.svalid hget; apply subtype_undef_get.
Qed.

Lemma check_vP wdb x1 x2 r re vm1 vm2 :
  check_v x1 x2 r = ok re ->
  eq_alloc r vm1 vm2 ->
  eq_alloc re vm1 vm2 /\
  (forall v1 : value,
     get_var wdb vm1 x1 = ok v1 ->
     exists v2 : value, get_var wdb vm2 x2 = ok v2 /\ value_uincl v1 v2).
Proof.
  rewrite /check_v;case: M.v_compat_typeP => // hsub.
  case Hget : M.get => [id | ].
  + t_xrbindP => /eqP ? <- Hea; subst id; split => //.
    case: Hea => _ /(_ _ _ Hget) Hev v1 {Hget}.
    rewrite /get_var; t_xrbindP => /(value_uincl_defined Hev) -> <- /=; eauto.
  t_xrbindP => /Sv_memP Hnot <- [ Hset Huincl]; split; first split => //.
  + by move=> x;rewrite M.setP_mset => ?;apply Hset;SvD.fsetdec.
  + move=> x id;rewrite M.setP;case:eqP => [<- [<-]| Hne].
    + rewrite (Hset _ Hnot) /=.
      by apply value_uincl_undef; rewrite (compat_type_undef_t hsub) (compat_type_undef_t (Vm.getP vm2 x2)).
    by case:ifP => // _;apply Huincl.
  move=> v1;rewrite /get_var (Hset _ Hnot) //=.
  t_xrbindP; case: wdb => /=.
  + move=> /is_defined_undef_addr [len heq] <-.
    move: hsub (Vm.getP vm2 x2); rewrite /M.v_compat_type heq.
    move => /compat_typeEl -> /compat_typeE /type_of_valI [a] -> /=.
    by exists (Varr a); split => //; apply: WArray.uincl_empty.
  move=> _ <-; eexists; split; eauto.
  apply value_uincl_undef.
  by rewrite (compat_type_undef_t hsub) (compat_type_undef_t (Vm.getP vm2 x2)).
Qed.

Lemma check_gvP wdb x1 x2 r re gd vm1 vm2 :
  check_gv x1 x2 r = ok re ->
  eq_alloc r vm1 vm2 ->
  eq_alloc re vm1 vm2 /\
  (forall v1 : value,
     get_gvar wdb gd vm1 x1 = ok v1 ->
     exists v2 : value, get_gvar wdb gd vm2 x2 = ok v2 /\ value_uincl v1 v2).
Proof.
  rewrite /check_gv /get_gvar /is_lvar; case: x1 x2 => x1 k1 [x2 k2] /=.
  t_xrbindP => /eqP ->; case:eqP => _; first by apply check_vP.
  t_xrbindP => /eqP -> <-; split; eauto.
Qed.

Lemma is_PvarP e ty x : is_Pvar e = Some (ty,x) -> e = Some (ty, Plvar x).
Proof. by case: e => //= -[? []] //= [] v [] // [<- <-]. Qed.

Section CHECK_EP.
  Context (wdb : bool) (gd : glob_decls) (vm2 : Vm.t).

  Let P e1 : Prop :=
    ∀ e2 r re vm1, check_e e1 e2 r = ok re →
    eq_alloc r vm1 vm2 →
    eq_alloc re vm1 vm2 ∧
    ∀ scs m v1,
      sem_pexpr wdb gd {| escs := scs; emem := m ; evm := vm1 |} e1 = ok v1 →
    ∃ v2, sem_pexpr wdb gd {| escs := scs; emem := m ; evm := vm2 |} e2 = ok v2 ∧
          value_uincl v1 v2.

  Let Q es1 : Prop :=
    ∀ es2 r re vm1 err,
    fold2 err check_e es1 es2 r = ok re →
    eq_alloc r vm1 vm2 →
    eq_alloc re vm1 vm2 ∧
    ∀ scs m vs1,
      sem_pexprs wdb gd {| escs := scs; emem := m ; evm := vm1 |} es1 = ok vs1 →
    ∃ vs2, sem_pexprs wdb gd {| escs := scs; emem := m ; evm := vm2 |} es2 = ok vs2 ∧
           List.Forall2 value_uincl vs1 vs2.

  Lemma check_e_esP : (∀ e, P e) ∧ (∀ es, Q es).
  Proof.
    apply: pexprs_ind_pair; split; subst P Q => /=.
    - case => // r _ vm1 _ [<-] h; split => // scs m _ [<-] /=; eauto.
    - move => e1 he1 es1 hes1 [] // e2 es2 r re vm1 err; t_xrbindP => r' ok_r' ok_re h.
      move: he1 => /(_ e2 r r' vm1 ok_r' h) [] h' he1.
      move: hes1 => /(_ es2 r' re vm1 err ok_re h') [] hre hes1.
      apply: (conj hre) => scs m vs1'; t_xrbindP => v1 ok_v1 vs1 ok_vs1 <- {vs1'} /=.
      move: he1 => /(_ _ _ _ ok_v1) [] v2 [] -> hv.
      move: hes1 => /(_ _ _ _ ok_vs1) [] vs2 [] -> hvs.
      eexists; split; first reflexivity. by constructor.
    - by move => z1 [] // z2 r re vm1; t_xrbindP => /eqP <- -> ?; split=> // ??? [] <-; exists z1.
    - by move => b1 [] // b2 r re vm1; t_xrbindP => /eqP <- -> ?; split=> // ??? [] <-; exists b1.
    - by move => n1 [] // n2 r re vm1; t_xrbindP => /eqP <- <- ?; split => //= ??? [<-]; eauto.
    - move => x1 [] // x2 r re vm1.
      by move=> /check_gvP Hv /(Hv wdb gd) [Hea H].
    - move => al1 aa1 sz1 x1 e1 He1 [] // al2 aa2 sz2 x2 e2 r re vm1.
      t_xrbindP => r' /andP[] /andP [/eqP ? /eqP ?] /eqP ? Hcv Hce Hea; subst al2 aa2 sz2.
      have [Hea' Hget]:= check_gvP wdb gd Hcv Hea.
      have [Hre Hse1]:= He1 _ _ _ _ Hce Hea';split => //= scs m v1.
      apply: on_arr_gvarP => n t Heqt /Hget [v2 []].
      rewrite /on_arr_var; case: v2 => //= n' t' -> /WArray.uincl_get Ht.
      t_xrbindP=> w ve /Hse1 [v2 [-> ]] /[swap] /to_intI -> /value_uinclE -> ? /= /Ht -> /= <-.
      by eauto.
    - move => aa1 sz1 len1 x1 e1 He1 [] // aa2 sz2 len2 x2 e2 r re vm1.
      t_xrbindP => r' /and3P [/eqP ? /eqP ? /eqP ?] Hcv Hce Hea; subst aa2 sz2 len2.
      have [Hea' Hget]:= check_gvP wdb gd Hcv Hea.
      have [Hre Hse1]:= He1 _ _ _ _ Hce Hea';split => //= scs m v1.
      apply: on_arr_gvarP => n t Heqt /Hget [v2 []].
      rewrite /on_arr_var; case: v2 => //= n' t' -> /WArray.uincl_get_sub Ht.
      t_xrbindP => w ve /Hse1 [v2 [-> ]] /[swap] /to_intI -> /value_uinclE -> ? /= /Ht [? -> ?] <- /=.
      by eauto.
    - move => al1 sz1 x1 e1 He1 [] // al2 sz2 x2 e2 r re vm1.
      t_xrbindP => r' /andP[] /eqP -> /eqP -> Hcv Hce Hea.
      have [Hea' Hget]:= check_vP wdb Hcv Hea.
      have [Hre Hse1]:= He1 _ _ _ _ Hce Hea';split => //= scs m v1.
      t_xrbindP => w1 ve1 /Hget [ve1' [->]] /[swap] /to_wordI [? [? [-> ]]]
        /word_uincl_truncate h /value_uinclE [? [? [-> /h{h} /= ->]]]
        > /Hse1{Hse1} [? [-> ]] /[swap] /to_wordI [? [? [-> ]]]
        /word_uincl_truncate h /value_uinclE [? [? [-> /h{h} /= ->]]] ? /= -> /= ->.
      by eauto.
    - move => op1 e1 He1 [] // op2 e2 r re vm1.
      t_xrbindP => /eqP <- H /(He1 _ _ _ _ H) [Hea Hse1];split=>//= scs m v1.
      t_xrbindP => v /Hse1 [v1'] [-> U1].
      by move=> /(vuincl_sem_sop1 U1);exists v1.
    - move => op1 e11 He11 e12 He12 [] // op2 e21 e22 r re vm1.
      t_xrbindP => r' /eqP <- Hs1 Hs2 Hea.
      have [Hea' Hse1]:= He11 _ _ _ _ Hs1 Hea.
      have [? Hse2]:= He12 _ _ _ _ Hs2 Hea'; split => //= scs m v.
      t_xrbindP => v1 /Hse1 [v1' [-> U1]] v2 /Hse2 [v2' [-> U2]].
      by move=> /(vuincl_sem_sop2 U1 U2);exists v.
    - move => op1 es1 Hes1 [] // op2 es2 r re vm1.
      t_xrbindP => /eqP <- ok_re hr.
      move: Hes1 => /(_ _ _ _ _ _  ok_re hr) [] hre h.
      split => //= scs m v1; t_xrbindP => vs1 ok_vs1 ok_v1.
      rewrite -/(sem_pexprs _ _ _).
      move: h => /(_ _ _ _ ok_vs1) [] vs2 [] -> hs /=.
      by have [] := vuincl_sem_opN ok_v1 hs; eauto.
    move => t e He e11 He11 e12 He12 [] // t' e2 e21 e22 r re vm1.
    t_xrbindP => r1 r' /eqP <- /He Hr' /He11 Hr1 /He12 Hr2 {He He11 He12}.
    move=> /Hr'{Hr'}[] /Hr1{Hr1}[] /Hr2{Hr2}[] Hre Hs2 Hs1 Hs;split=>// scs m v1.
    t_xrbindP=> b > /Hs [_] /= [->] /= /[swap] /to_boolI -> /value_uinclE ->.
    move=> ?? /Hs1 [?[-> /=]] /value_uincl_truncate H/H{H} [? -> ?].
    move=> ?? /Hs2 [?[-> /=]] /value_uincl_truncate H/H{H} [? -> ?] <- /=.
    by eexists;split;eauto;case: (b).
  Qed.

End CHECK_EP.

Definition check_eP wdb gd e1 e2 r re vm1 vm2 :=
  (check_e_esP wdb gd vm2).1 e1 e2 r re vm1.

Lemma eq_alloc_set x1 v1  r x2 v2 vm1 vm2 (h:M.v_compat_type x1 x2) :
  eq_alloc r vm1 vm2 ->
  value_uincl (vm_truncate_val (vtype x1) v1) (vm_truncate_val (vtype x2) v2) ->
  eq_alloc (M.set r x1 x2 h) vm1.[x1 <- v1] vm2.[x2 <- v2].
Proof.
  move=> [Hin Hget] Hu.
  split.
  + move=> z;rewrite M.setP_mset => Hnin.
    by rewrite Vm.setP_neq;[apply Hin|apply /eqP];SvD.fsetdec.
  move=> x id;rewrite M.setP;case:eqP => [<-[<-] | /eqP Hne].
  + by rewrite !Vm.setP_eq.
  case: ifPn => //= /Sv_memP Hid Hgetx.
  rewrite !Vm.setP_neq //;first by apply Hget.
  move: Hgetx;rewrite M.Mv.mvalid => Hgetx.
  by apply/eqP => ?; subst id; apply: Hid.
Qed.

Lemma eq_alloc_add x1 v1 r x2 vm1 vm2 (h:M.v_compat_type x1 x2) :
  eq_alloc r vm1 vm2 ->
  let v2 := vm2.[x2] in
  value_uincl (vm_truncate_val (vtype x1) v1) (vm_truncate_val (vtype x2) v2) ->
  eq_alloc (M.add r x1 x2 h) vm1.[x1 <- v1]
                             vm2.[x2 <- v2].
Proof.
  move=> [Hin Hget] v2 /= Hu.
  split.
  + move=> z; rewrite M.addP_mset => Hnin.
    by rewrite Vm.setP_neq; [apply Hin|apply /eqP]; SvD.fsetdec.
  move=> x id; rewrite M.addP; case:eqP => [<-[<-] | /eqP Hne].
  + by rewrite !Vm.setP_eq.
  move=> /Hget {} Hget; rewrite Vm.setP_neq //.
  rewrite Vm.setP; case: eqP; last by [].
  by subst v2 => ->; rewrite vm_truncate_val_get.
Qed.

Lemma check_varP wdb r1 r1' vm1 vm2 vm1' x1 x2 v1 v2 (h:M.v_compat_type x1 x2):
  eq_alloc r1 vm1 vm2 ->
  @check_var_aux _ x1 x2 r1 h = ok r1' ->
  set_var wdb vm1 x1 v1 = ok vm1' ->
  value_uincl v1 v2 ->
  exists2 vm2' : Vm.t,
    set_var wdb vm2 x2 v2 = ok vm2' & eq_alloc r1' vm1' vm2'.
Proof.
  rewrite /check_var => Hea -[<-].
  move=> /set_varP [hdb1 htr1 ->] hu.
  have [htr2 hu2 hdb2]:= compat_truncate_uincl h htr1 hu hdb1.
  by rewrite set_var_truncate //; eexists; eauto; apply eq_alloc_set.
Qed.

Lemma check_varcP wdb r1 r1' vm1 vm2 vm1' x1 x2 v1 v2 :
  eq_alloc r1 vm1 vm2 ->
  check_varc x1 x2 r1 = ok r1' ->
  set_var wdb vm1 x1 v1 = ok vm1' ->
  value_uincl v1 v2 ->
  exists2 vm2' : Vm.t,
    set_var wdb vm2 x2 v2 = ok vm2' & eq_alloc r1' vm1' vm2'.
Proof. by rewrite /check_varc; case: M.v_compat_typeP => // h; apply check_varP. Qed.

Lemma eq_alloc_rm r x s vm z :
  value_uincl (undef_addr (vtype x)) (vm_truncate_val (vtype x) z) ->
  eq_alloc r (evm s) vm ->
  eq_alloc (M.remove r x) (evm s) vm.[x <- z].
Proof.
  move=> Hz [Hinit Halloc];split.
  + by move=> y /=;apply: Hinit.
  move=> x0 id; rewrite M.removeP.
  case: M.get (Halloc x0) => [id' | ] //.
  move=> /(_ _ (refl_equal _));case:ifPn => //= Hne He [?];subst id'.
  rewrite Vm.setP_neq //;by apply: contra Hne => /eqP ->.
Qed.

Lemma check_lvalP wdb gd r1 r1' x1 x2 e2 s1 s1' vm1 v1 v2 :
  check_lval e2 x1 x2 r1 = ok r1' ->
  eq_alloc r1 s1.(evm) vm1 ->
  value_uincl v1 v2 ->
  oapp (fun te2 =>
      sem_pexpr wdb gd (with_vm s1 vm1) te2.2 >>= truncate_val te2.1 = ok v2) true e2 ->
  write_lval wdb gd x1 v1 s1 = ok s1' ->
  exists2 vm1',
    write_lval wdb gd x2 v2 (with_vm s1 vm1) = ok (with_vm s1' vm1') &
    eq_alloc r1' s1'.(evm) vm1'.
Proof.
  case: x1 x2 => /= [ii1 t1 | x1 | al1 sz1 x1 p1 | al1 aa1 sz1 x1 p1 | aa1 sz1 len1 x1 p1]
                    [ii2 t2 | x2 | al2 sz2 x2 p2 | al2 aa2 sz2 x2 p2 | aa2 sz2 len2 x2 p2] //=.
  + t_xrbindP => hs <- ? Hv _ H.
    have [ -> htr hdb]:= write_noneP H; rewrite /write_none.
    have [ -> hu' -> /=]:= compat_truncate_uincl hs htr Hv hdb; eauto.
  + t_xrbindP => hs <- Heqa Hu Happ H.
    have [-> htr hdb]:= write_noneP H; rewrite /write_var /set_var.
    have [-> hu' -> /=]:= compat_truncate_uincl hs htr Hu hdb.
    rewrite with_vm_idem; eexists; eauto.
    apply eq_alloc_rm => //=.
    by apply/value_uincl_undef; rewrite -(compat_type_undef_t (vm_truncate_val_compat v2 _)).
  + rewrite /write_var=> Hc Hvm1 Hv Happ; t_xrbindP => vm1' Hset <- /=.
    move: Hc;case: is_Pvar (@is_PvarP e2); last first.
    + by move=> ? hc;have [vm2' -> /= ?]:= check_varcP Hvm1 hc Hset Hv;eexists; rewrite ?with_vm_idem;eauto.
    move=> [ty x] /(_ _ _ (refl_equal _)) ?;subst e2.
    case: M.v_compat_typeP => // ht;case:ifPn; last first.
    + move=> ? hc;have [vm2' -> /= ?]:= check_varP Hvm1 hc Hset Hv.
      by eexists; rewrite ?with_vm_idem; eauto.
    move=> /and3P[] /eqP ? /eqP heqt /eqP; subst ty.
    move: x1 x2 x heqt ht Hset Happ=> [x1 ii1] [ x2 ii2] [x ii] /=; rewrite /get_gvar /= /get_var.
    t_xrbindP => hteq ht hset v2' _ ? htr ? ?; subst v2' x r1' => /=.
    have := truncate_val_subtype_eq htr; rewrite hteq => /(_ (getP_subtype _ _)) ?; subst v2.
    move/set_varP: hset => [hdb htr1 ->]; rewrite /set_var.
    have [-> hu' -> /=] := compat_truncate_uincl ht htr1 Hv hdb.
    exists vm1.[x2 <- vm1.[x2]] => //.
    apply: eq_alloc_add ht Hvm1 hu'.

  + t_xrbindP => r2 /andP[] /eqP -> /eqP -> Hcv Hce Hvm1 Hv Happ wx vx.
    have [Hr2 H/H{H} [vx' [-> ]]]:= check_vP wdb Hcv Hvm1.
    move=> /of_value_uincl_te h/(h (sword _) _){h} /= -> >.
    case: (s1) Hvm1 Hr2 => scs1 sm1 svm1 /= Hvm1 Hr2.
    have [Hr1' H/H{H} [ve' [-> ]]]:= check_eP wdb gd Hce Hr2.
    by move=> /of_value_uincl_te h/(h (sword _) _){h} /= -> ?
      /(@of_value_uincl_te (sword _) _ _ _ Hv) /= -> ? /= -> <-; eexists.
  + t_xrbindP => r2 r3 /andP [] /andP[] /eqP -> /eqP -> /eqP -> Hcv Hce Hcva Hvm1 Hv Happ.
    apply: on_arr_varP => n t Htx;rewrite /on_arr_var /=.
    have [Hr3 H/H{H} [vx2 [->]]]:= check_vP wdb Hcv Hvm1.
    case: vx2 => //= n0 t2 Ht.
    t_xrbindP => we ve.
    case: (s1) Hvm1 Hr3 => scs1 sm1 svm1 /= Hvm1 Hr3.
    have [Hr1' H/H{H} [ve' [-> ]]]:= check_eP wdb gd Hce Hr3.
    move=> /of_value_uincl_te h/(h sint _){h} /= -> ?
      /(@of_value_uincl_te (sword _) _ _ _ Hv) /= -> ?
      /(WArray.uincl_set Ht) [? [/= -> Ht2']].
    have: value_uincl (Varr _) (Varr _) := Ht2'.
    by rewrite /write_var; t_xrbindP=> /(check_varcP Hr1' Hcva) h ?
      /h{h} [vm2' /= -> ?] <-; eexists.
  t_xrbindP=> r2 r3 /and3P[]/eqP -> /eqP -> /eqP -> Hcv Hce Hcva Hvm1 Hv Happ.
  apply: on_arr_varP => n t Htx;rewrite /on_arr_var /=.
  have [Hr3 H/H{H} [vx2 [->]]]:= check_vP wdb Hcv Hvm1.
  case: vx2 => //= n0 t2 Ht.
  t_xrbindP => we ve.
  case: (s1) Hvm1 Hr3 => scs1 sm1 svm1 /= Hvm1 Hr3.
  have [Hr1' H/H{H} [ve' [-> ]]]:= check_eP wdb gd Hce Hr3.
    move=> /of_value_uincl_te h/(h sint _){h} /= -> ?
      /(@of_value_uincl_te (sarr _) _ _ _ Hv) [? /= -> ]
      /(WArray.uincl_set_sub Ht) h ? /h{h} [? /= -> Ht2'].
  have: value_uincl (Varr _) (Varr _) := Ht2'.
  by rewrite /write_var; t_xrbindP=> /(check_varcP Hr1' Hcva) h ?
    /h{h} [vm2' /= -> ?] <-; eexists.
Qed.

Section PROG.

Context
  {pT: progT}
  {sCP : semCallParams}.

Variable init_alloc : extra_fun_t -> extra_prog_t -> extra_prog_t -> cexec M.t.

Hypothesis init_allocP :
  forall (ef: extra_fun_t) (ep1 ep2: extra_prog_t) ev s1 scs m r,
    init_alloc ef ep1 ep2 = ok r ->
    init_state ef ep1 ev (Estate scs m Vm.init) = ok s1 ->
    exists vm2,
      init_state ef ep2 ev (Estate scs m Vm.init) = ok (with_vm s1 vm2) /\
      eq_alloc r s1.(evm) vm2.

Variable (check_f_extra: M.t → extra_fun_t → extra_fun_t → seq var_i → seq var_i → cexec M.t).

Hypothesis check_f_extraP :
  ∀ r e1 e2 p1 p2 r',
    check_f_extra r e1 e2 p1 p2 = ok r' →
    [/\
       check_vars p1 p2 r = ok r',
       ∀ ep ev s s', init_state e1 ep ev s = ok s' → init_state e2 ep ev s = ok s' &
       ∀ m, finalize e1 m = finalize e2 m
    ].

Local Notation check_fundef := (check_fundef init_alloc check_f_extra).
Local Notation check_prog := (check_prog init_alloc check_f_extra).

Section PROOF.

  Variable p1 p2:prog.
  Variable ev : extra_val_t.

  Local Notation gd := (p_globs p1).
  Local Notation ep1 := (p_extra p1).
  Local Notation ep2 := (p_extra p2).

  Hypothesis Hcheck: check_prog ep1 p1.(p_funcs) ep2 p2.(p_funcs) = ok tt.
  Hypothesis eq_globs : p_globs p1 = p_globs p2.

  Lemma all_checked : forall fn fd1,
    get_fundef (p_funcs p1) fn = Some fd1 ->
    exists fd2, get_fundef (p_funcs p2) fn = Some fd2 /\ 
                check_fundef ep1 ep2 (fn,fd1) (fn,fd2) tt = ok tt.
  Proof.
    move: Hcheck; rewrite /check_prog;clear Hcheck eq_globs.
    move: (p_funcs p1) (p_funcs p2). 
    elim => [ | [fn1' fd1'] pf1 Hrec] [ | [fn2 fd2] pf2] //.
    apply: rbindP => -[] Hc /Hrec {Hrec} Hrec.
    have ? : fn1' = fn2.
    + by move: Hc;rewrite /check_fundef; t_xrbindP => /and3P[]/eqP.
    subst=> fn fd1;rewrite !get_fundef_cons.
    by case:ifPn => [/eqP -> [] <-| _ /Hrec //]; exists fd2.
  Qed.

  Let Pi_r s1 (i1:instr_r) s2:=
    forall r1 i2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_i i1 i2 r1 = ok r2 ->
    exists2 vm2, eq_alloc r2 (evm s2) vm2 &
      sem_i p2 ev (with_vm s1 vm1) i2 (with_vm s2 vm2).

  Let Pi s1 (i1:instr) s2:=
    forall r1 i2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_I i1 i2 r1 = ok r2 ->
    exists2 vm2, eq_alloc r2 (evm s2) vm2 &
      sem_I p2 ev (with_vm s1 vm1) i2 (with_vm s2 vm2).

  Let Pc s1 (c1:cmd) s2:=
    forall r1 c2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_cmd c1 c2 r1 = ok r2 ->
    exists2 vm2, eq_alloc r2 (evm s2) vm2 &
      sem p2 ev (with_vm s1 vm1) c2 (with_vm s2 vm2).

  Let Pfor (i1:var_i) vs s1 c1 s2 :=
    forall i2 r1 r1' c2 r2 vm1, eq_alloc r1 (evm s1) vm1 ->
    check_var i1 i2 r1 = ok r1' ->
    check_cmd c1 c2 r1' = ok r2 -> M.incl r1 r2 ->
    exists2 vm2, eq_alloc r1 (evm s2) vm2 &
      sem_for p2 ev i2 vs (with_vm s1 vm1) c2 (with_vm s2 vm2).

  Let Pfun scs m fn vargs1 scs' m' vres :=
    forall vargs2, List.Forall2 value_uincl vargs1 vargs2 ->
    exists2 vres',
       sem_call p2 ev scs m fn vargs2 scs' m' vres' &
       List.Forall2 value_uincl vres vres'.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof. move=> s r1 [ | ??] //= r2 vm1 ? [] <-;exists vm1 =>//;constructor. Qed.

  Local Lemma Hcons : sem_Ind_cons p1 ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc r1 [ | i2 c2] //= r2 vm1 /Hi Hvm1.
    t_xrbindP => r3 /Hvm1 [vm2 /Hc Hvm2 ?] /Hvm2 [vm3 ??].
    exists vm3 =>//;econstructor;eauto.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p1 ev Pi_r Pi.
  Proof.
    move=> ii i s1 s2 _ Hi  r1 [? i2] r2 vm1 /Hi Hvm /= /add_iinfoP /Hvm [vm2 ??].
    by exists vm2 => //;constructor.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn p1 Pi_r.
  Proof.
    move => s1 s2 x tag ty e v v'.
    case: s1 => scs1 sm1 svm1 He Htr Hw r1 [] //= x2 tag2 ty2 e2 r2 vm1 Hvm1.
    rewrite /check_i; t_xrbindP => r1' /eqP <- /check_eP -/(_ true (p_globs p1) _ _ Hvm1)
      [Hr1'] /(_ _ _ _ He) [v2 [He2 Hu2]] Hcx.
    have [v2' Htr' Hu2']:= value_uincl_truncate Hu2 Htr.
    have  /(_ _ Hr1') [|vm2 Hwv Hvm2]:= check_lvalP Hcx _ Hu2' _ Hw.
    + by rewrite /= He2 /= Htr'.
    by exists vm2 =>//;econstructor;rewrite -?eq_globs;eauto.
  Qed.

  Lemma check_esP wdb e1 e2 r re s vm:
    check_es e1 e2 r = ok re ->
    eq_alloc r s.(evm) vm ->
    eq_alloc re s.(evm) vm /\
    forall v1,  sem_pexprs wdb gd s e1 = ok v1 ->
    exists v2, sem_pexprs wdb (p_globs p2) (with_vm s vm) e2 = ok v2 /\
               List.Forall2 value_uincl v1 v2.
  Proof.
    case: s => scs mem vm1.
    rewrite -eq_globs => h1 h2; case (check_e_esP wdb gd vm) => _ /(_ _ _ _ _ _ _ h1 h2) /= [h3 h4].
    split => // v1; apply h4.
  Qed.

  Lemma check_lvalsP wdb gd xs1 xs2 vs1 vs2 r1 r2 s1 s2 vm1 :
    check_lvals xs1 xs2 r1 = ok r2 ->
    eq_alloc r1 s1.(evm) vm1 ->
    List.Forall2 value_uincl vs1 vs2 ->
    write_lvals wdb gd s1 xs1 vs1 = ok s2 ->
    exists2 vm2,
      write_lvals wdb gd (with_vm s1 vm1) xs2 vs2 = ok (with_vm s2 vm2) &
      eq_alloc r2 s2.(evm) vm2.
  Proof.
    elim: xs1 xs2 vs1 vs2 r1 r2 s1 s2 vm1 => [ | x1 xs1 Hrec] [ | x2 xs2] //=
      vs1 vs2 r1 r2 s1 s2 vm1.
    + by move=> [<-] Hvm1 [] //= [<-];exists vm1.
    t_xrbindP => r3 Hx Hcxs Hvm1 [] //= {vs1 vs2} v1 v2 vs1 vs2 Hv Hvs.
    t_xrbindP => s3 Hw Hws.
    have [//| vm3 ->/= Hvm3] := check_lvalP (e2:= None) Hx Hvm1 Hv _ Hw.
    apply: Hrec Hcxs Hvm3 Hvs Hws.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p1 Pi_r.
  Proof.
    move => s1 s2 t o xs es.
    rewrite /sem_sopn; t_xrbindP => v ves He Ho Hw r1 [] //= xs2 t' o2 es2 r2 vm1 Hvm1.
    rewrite /check_i; t_xrbindP => r1' /eqP <- /check_esP -/(_ true _ _ Hvm1) [Hr1'] /(_ _ He) [v2 [He2 Hu2]].
    have [v' Ho' Hv Hcxs]:= vuincl_exec_opn Hu2 Ho.
    have /(_ _ Hr1') [vm2 Hwv Hvm2]:= check_lvalsP Hcxs _ Hv Hw.
    by exists vm2 =>//; constructor; rewrite /sem_sopn He2 /= Ho' -eq_globs.
  Qed.

  Local Lemma Hsyscall : sem_Ind_syscall p1 Pi_r.
  Proof.
    move => s1 scs m s2 o xs es ves vs hes hsys hw r1 [] //= xs2 o2 es2 r2 vm1 Hvm1.
    rewrite /check_i; t_xrbindP => r1'/eqP <- /check_esP -/(_ true _ _ Hvm1) [Hr1'] /(_ _ hes) [v2 [He2 Hu2]] Hcxs.
    have  [vs' Ho' Hv] := exec_syscallP hsys Hu2.
    have /(_ _ Hr1') [vm2 Hwv Hvm2]:= check_lvalsP Hcxs _ Hv hw.
    by exists vm2 => //; econstructor; eauto; rewrite -eq_globs.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2.
    case: s1 => scs1 sm1 svm1 Hve _ Hc1 r1 [] //= e' c1' c2' r2 vm1 Hvm1.
    rewrite /check_i -/check_I.
    t_xrbindP => r1' /check_eP -/(_ true gd _ _ Hvm1) [] Hr1'.
    move=> /(_ _ _ _ Hve) [ve' [Hve' /value_uinclE ?]];subst ve'.
    move => r3 Hr3 r4 Hr4 <-.
    have [vm2 Hvm2 Hsem]:= Hc1 _ _ _ _ Hr1' Hr3;exists vm2.
    + by eapply eq_alloc_incl;eauto;apply M.merge_incl_l.
    by apply Eif_true => //;rewrite -eq_globs Hve'.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2.
    case: s1 => scs1 sm1 svm1 Hve _ Hc1 r1 [] //= e' c1' c2' r2 vm1 Hvm1.
    rewrite /check_i -/check_I.
    t_xrbindP => r1' /check_eP -/(_ true gd _ _ Hvm1) [] Hr1'.
    move=> /(_ _ _ _ Hve) [ve' [Hve' /value_uinclE ?]];subst ve'.
    move => r3 Hr3 r4 Hr4 <-.
    have [vm2 Hvm2 Hsem]:= Hc1 _ _ _ _ Hr1' Hr4;exists vm2.
    + by eapply eq_alloc_incl;eauto;apply M.merge_incl_r.
    by apply Eif_false => //;rewrite -eq_globs Hve'.
  Qed.

  Local Lemma loop2P check_c n r1 r2:
    loop2 check_c n r1 = ok r2 ->
      exists r2' r3,
      [/\ check_c r2' = ok (r2, r3), M.incl r2' r1 & M.incl r2' r3].
  Proof.
    elim: n r1 r2 => //= n Hrec r1 r2.
    apply: rbindP => -[r2_1 r2_2] Hc;case:ifPn => [? [] <- | _ /Hrec].
    + exists r1, r2_2;split=>//;apply M.incl_refl.
    move=> [r2' [r3 [H1 H2 H3]]];exists r2', r3;split=>//.
    apply: (M.incl_trans H2); apply M.merge_incl_l.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 s3 s4 a c e c'.
    case: s2 => scs2 sm2 svm2 _ Hc Hse _ Hc' _ Hw r1 [] //= a2 c2 e2 c2' r2 vm1 Hvm1.
    rewrite /check_i -/check_I.
    apply: rbindP => r /loop2P [r2' [r3 [H Hir1 Hir3]]] [?];subst r.
    have Hvmr2' := eq_alloc_incl Hir1 Hvm1.
    move: H; t_xrbindP => r0 Cc2; move /Hc: (Hvmr2') (Cc2) => H /H {H} [vm2 Hvm2 /= Hc2] re Hre.
    have /= [Hrevm2 /(_ _ _ _ Hse) [vb' [Hse2 /value_uinclE ?]]]:= check_eP true gd Hre Hvm2.
    subst vb' => r' Cc2' ??;subst r2 r3.
    move /Hc': (Hrevm2) (Cc2')=> H /H {H} [vm3 Hvm3 /= Hc2'].
    have /Hw {Hw} Hw:= eq_alloc_incl Hir3 Hvm3.
    have : check_i (Cwhile a c e c') (Cwhile a2 c2 e2 c2') r2' = ok re.
    + by rewrite /check_i -/check_I Loop.nbP /= Cc2 /= Hre /= Cc2' /= Hir3 /=.
    move=> /Hw [vm4 Hvm4 Hsw];exists vm4 => //.
    by apply: Ewhile_true Hsw;eauto;rewrite -eq_globs Hse2.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 a c e c'.
    case: s2 => scs2 sm2 svm2 _ Hc Hse r1 [] //= a2 c2 e2 c2' r2 vm1 Hvm1.
    rewrite /check_i -/check_I.
    t_xrbindP => r /loop2P [r2' [r3 [H Hir1 Hir3]]] ?;subst r.
    have Hvmr2' := eq_alloc_incl Hir1 Hvm1.
    move: H; t_xrbindP=> r0 Cc2; move /Hc: (Hvmr2') (Cc2) => H /H {H} [vm2 Hvm2 /= Hc2] re Hre.
    have /= [Hrevm2 /(_ _ _ _ Hse) [vb' [Hse2 /value_uinclE ?]]]:= check_eP true gd Hre Hvm2.
    subst vb' => r' Cc2' ??;subst r2 r3; exists vm2 => //.
    by apply: Ewhile_false;rewrite // -eq_globs Hse2.
  Qed.

  Local Lemma loopP check_c n r1 r2:
    loop check_c n r1 = ok r2 ->
      exists r2',
      [/\ check_c r2 = ok r2', M.incl r2 r1 & M.incl r2 r2'].
  Proof.
    elim: n r1 r2 => //= n Hrec r1 r2.
    apply: rbindP => r2' Hc;case:ifPn => [? [] <- | _ /Hrec].
    + exists r2';split=>//;apply M.incl_refl.
    move=> [r2'' [H1 H2 H3]];exists r2'';split=>//.
    apply: (M.incl_trans H2); apply M.merge_incl_l.
  Qed.

  Local Lemma Hfor : sem_Ind_for p1 ev Pi_r Pfor.
  Proof.
    move => s1 s2 i d lo hi c vlo vhi.
    case: s1 => scs1 sm1 svm1 Hlo Hhi Hc Hfor r1 [] //= i2 [[d2 lo2] hi2] c2 r2 vm1 Hvm1.
    rewrite /check_i -/check_I.
    case: eqP => //= ?;subst d2.
    t_xrbindP => r1' r1'' /check_eP -/(_ true gd _ _ Hvm1) [Hr1'' Heqlo].
    have [vlo'' [Hlo2 /value_uinclE Hvlo']] := Heqlo _ _ _ Hlo.
    subst vlo'' => /check_eP -/(_ true gd _ _ Hr1'') [Hr1' Heqhi].
    have [vhi'' [Hhi2 /value_uinclE Hhi']] := Heqhi _ _ _ Hhi.
    subst vhi'' => /loopP [r2'] []; t_xrbindP=> r2'' Hcv Hcc Hr2r1 Hr2r2.
    have := Hfor _ _ _ _ _ _ (eq_alloc_incl Hr2r1 Hr1') Hcv Hcc Hr2r2.
    move=> [vm2 Hvm2 Hsem2];exists vm2 => //.
    econstructor; rewrite -?eq_globs ?Hlo2 ?Hhi2 /= ;eauto.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof. by move=> s i c i2 r1 r1' c2 r2 vm1 Ha ???;exists vm1 => //;constructor. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p1 ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hwi _ Hc _ Hfor i2 r1 r1' c2 r2 vm2 Heq Hr1' Hcc Hincl.
    have [//|vm3 Hwi2 Hvm3] := check_lvalP (gd := gd) Hr1' Heq (value_uincl_refl _) _ Hwi.
    have [vm4 Hvm4 Hsc] := Hc _ _ _ _ Hvm3 Hcc.
    have [vm5 Hvm5 Hsf] := Hfor _ _ _ _ _ _ (eq_alloc_incl Hincl Hvm4) Hr1' Hcc Hincl.
    by exists vm5 => //; econstructor; eauto.
  Qed.

  Local Lemma Hcall : sem_Ind_call p1 ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 xs fn args vargs vs Hes Hsc Hfun Hw r1
      [] //= xs2 fn2 args2 r2 vm1 Hr1.
    rewrite /check_i -/check_I; t_xrbindP => r1' /eqP ? Hca Hcxs; subst fn2.
    have [Hr1' /(_ _ Hes) [vargs2 [Hargs2 Hvargs]]] := check_esP (~~direct_call) Hca Hr1.
    have [v' Hs2 Hvs]:= Hfun _ Hvargs.
    have /(_ _ Hr1') [vm2 Hw2 Hr2]:= check_lvalsP Hcxs _ Hvs Hw.
    by exists vm2 =>//; econstructor;eauto;rewrite -?eq_globs.
  Qed.

  Section REFL.

    Hypothesis eq_prog : p1 = p2.

    Local Lemma Hproc_eq scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres':
      get_fundef (p_funcs p1) fn = Some f ->
      mapM2 ErrType dc_truncate_val f.(f_tyin) vargs' = ok vargs ->
      init_state f.(f_extra) (p_extra p1) ev (Estate scs1 m1 Vm.init) = ok s0 ->
      write_vars (~~direct_call) (f_params f) vargs s0 = ok s1 ->
      sem p1 ev s1 (f_body f) s2 ->
      Pc s1 (f_body f) s2 ->
      get_var_is (~~ direct_call) s2.(evm) (f_res f) = ok vres ->
      mapM2 ErrType dc_truncate_val f.(f_tyout) vres = ok vres' ->
      scs2 = s2.(escs) ->
      m2 = finalize f.(f_extra) s2.(emem) ->
      Pfun scs1 m1 fn vargs' scs2 m2 vres'.
    Proof.
      move=> Hget Hca Hi Hw Hsem _ Hres Hcr hscs Hfi vargs2 Hvargs2; rewrite -eq_prog.
      have h : sem_call p1 ev scs1 m1 fn vargs' scs2 m2 vres' by econstructor;eauto.
      have [?[]]:= sem_call_uincl Hvargs2 h; eauto.
    Qed.

    Lemma alloc_funP_eq_aux fn f f' scs1 m1 scs2 m2 vargs vargs' vres s0 s1 s2 vres':
      check_fundef ep1 ep2 (fn, f) (fn, f') tt = ok tt ->
      mapM2 ErrType dc_truncate_val f.(f_tyin) vargs' = ok vargs ->
      init_state f.(f_extra) (p_extra p1) ev (Estate scs1 m1 Vm.init) = ok s0 ->
      write_vars (~~direct_call) (f_params f) vargs s0 = ok s1 ->
      sem p1 ev s1 (f_body f) s2 ->
      get_var_is (~~ direct_call) (evm s2) (f_res f) = ok vres ->
      mapM2 ErrType dc_truncate_val f.(f_tyout) vres = ok vres' ->
      scs2 = s2.(escs) ->
      m2 = finalize f.(f_extra) s2.(emem) ->
      exists vm0' vm1' vm2' vres1 vres1',
       [ /\ mapM2 ErrType dc_truncate_val f'.(f_tyin) vargs' = ok vargs,
            init_state f'.(f_extra) (p_extra p2) ev (Estate scs1 m1 Vm.init) = ok (with_vm s0 vm0') /\
            write_vars (~~direct_call) (f_params f') vargs (with_vm s0 vm0') = ok (with_vm s1 vm1'),
            sem p2 ev (with_vm s1 vm1') (f_body f') (with_vm s2 vm2'),
            [ /\ get_var_is (~~ direct_call) (evm (with_vm s2 vm2')) (f_res f') = ok vres1,
                 List.Forall2 value_uincl vres' vres1' &
                mapM2 ErrType dc_truncate_val f'.(f_tyout) vres1 = ok vres1'] &
            scs2 = s2.(escs) /\ m2 = finalize f'.(f_extra) s2.(emem) ].
    Proof.
      rewrite /check_fundef eq_refl => /=.
      t_xrbindP => /andP[]/eqP htyin /eqP htyout r0 Hcinit r1 /check_f_extraP[] Hcparams hinit hfinalize r2 Hcc r3 Hcres _ Hca.
      move=> /(init_allocP Hcinit) [vm0 [Hi0 Hvm0]].
      rewrite (write_vars_lvals (~~direct_call) gd)=> /(check_lvalsP Hcparams).
      move=> /(_ vargs _ Hvm0) [ | vm3 /= Hw2 Hvm3].
      + by apply: List_Forall2_refl.
      move=> /(sem_Ind Hskip Hcons HmkI Hassgn Hopn Hsyscall Hif_true Hif_false
                Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc_eq) Hc.
      have [vm4 /= Hvm4 Hsc2 Hres Hcr]:= Hc _ _ _ _ Hvm3 Hcc.
      have := check_esP (~~direct_call) Hcres Hvm4.
      move=> [Hr3];rewrite sem_pexprs_get_var => /(_ _ Hres) [vres1' /= []].
      rewrite sem_pexprs_get_var => hmap huincl ??.
      have [vres2' ??]:= mapM2_dc_truncate_val Hcr huincl.
      do 5 eexists;split;eauto.
      + by rewrite -htyin.
      + split; first by eauto.
        by rewrite (write_vars_lvals _ gd).
      + by rewrite -htyout;split;eauto.
      by rewrite -hfinalize.
    Qed.

  End REFL.

  Local Lemma Hproc : sem_Ind_proc p1 ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hget Hca Hi Hw _ Hc Hres Hcr Hscs Hfi.
    have [fd2 [Hget2 /=]]:= all_checked Hget.
    t_xrbindP => /and3P [] _ /eqP htyin /eqP htyout r0 Hcinit r1 /check_f_extraP[] Hcparams hinit hfinalize r2 Hcc r3 Hcres _.
    move=> vargs2 Hvargs2.
    have [vm0 [Hi0 Hvm0]]:= init_allocP Hcinit Hi.
    have [vs2 htr hall2]:= mapM2_dc_truncate_val Hca Hvargs2.
    move: Hw;rewrite (write_vars_lvals _ gd)=> /(check_lvalsP Hcparams).
    move=> /(_ _ _ Hvm0 hall2) [vm3 /= Hw2 Hvm3].
    have [vm4 /= Hvm4 Hsc2]:= Hc _ _ _ _ Hvm3 Hcc.
    have := check_esP (~~direct_call) Hcres Hvm4.
    move=> [Hr3];rewrite sem_pexprs_get_var => /(_ _ Hres) [vres1' /= []].
    rewrite sem_pexprs_get_var => H1 H2.
    have [vs3 ??]:= mapM2_dc_truncate_val Hcr H2.
    econstructor;eauto.
    econstructor;eauto.
    + by rewrite -htyin; eauto.
    + by rewrite (write_vars_lvals (~~direct_call) gd).
    + by rewrite -htyout.
    by rewrite -hfinalize.
  Qed.

  Lemma alloc_callP_aux f scs mem scs' mem' va vr:
    sem_call p1 ev scs mem f va scs' mem' vr ->
    exists vr', sem_call p2 ev scs mem f va scs' mem' vr' /\ List.Forall2 value_uincl vr vr'.
  Proof.
    move=> h.
    have [|]:=
      (sem_call_Ind
          Hskip
          Hcons
          HmkI
          Hassgn
          Hopn
          Hsyscall
          Hif_true
          Hif_false
          Hwhile_true
          Hwhile_false
          Hfor
          Hfor_nil
          Hfor_cons
          Hcall
          Hproc
          h va); eauto.
    by apply List_Forall2_refl.
  Qed.

End PROOF.

Lemma alloc_callP ev gd ep1 p1 ep2 p2 (H: check_prog ep1 p1 ep2 p2 = ok tt) f scs mem scs' mem' va vr:
    sem_call {|p_globs := gd; p_funcs := p1; p_extra := ep1; |} ev scs mem f va scs' mem' vr ->
    exists vr', 
     sem_call {|p_globs := gd; p_funcs := p2; p_extra := ep2; |} ev scs mem f va scs' mem' vr' /\
                List.Forall2 value_uincl vr vr'.
Proof.
  by apply alloc_callP_aux.
Qed.

Lemma alloc_funP_eq p ev fn f f' scs1 m1 scs2 m2 vargs vargs' vres vres' s0 s1 s2:
  check_fundef (p_extra p) (p_extra p) (fn, f) (fn, f') tt = ok tt ->
  mapM2 ErrType dc_truncate_val f.(f_tyin) vargs' = ok vargs ->
  init_state (f_extra f) (p_extra p) ev (Estate scs1 m1 Vm.init) = ok s0 ->
  write_vars (~~direct_call) (f_params f) vargs s0 = ok s1 ->
  sem p ev s1 (f_body f) s2 ->
  get_var_is (~~ direct_call) (evm s2) (f_res f) = ok vres ->
  mapM2 ErrType dc_truncate_val f.(f_tyout) vres = ok vres' ->
  scs2 = s2.(escs) ->
  m2 = finalize f.(f_extra) s2.(emem) ->
  exists vm0' vm1' vm2' vres1 vres1',
       [ /\ mapM2 ErrType dc_truncate_val f'.(f_tyin) vargs' = ok vargs,
            init_state f'.(f_extra) (p_extra p) ev (Estate scs1 m1 Vm.init) = ok (with_vm s0 vm0') /\
            write_vars (~~direct_call) (f_params f') vargs (with_vm s0 vm0') = ok (with_vm s1 vm1'),
            sem p ev (with_vm s1 vm1') (f_body f') (with_vm s2 vm2'),
            [ /\ get_var_is (~~ direct_call) (evm (with_vm s2 vm2')) (f_res f') = ok vres1,
                 List.Forall2 value_uincl vres' vres1' &
                mapM2 ErrType dc_truncate_val f'.(f_tyout) vres1 = ok vres1'] &
            scs2 = s2.(escs) /\ m2 = finalize f'.(f_extra) s2.(emem) ].
  Proof. by apply alloc_funP_eq_aux. Qed.

End PROG.

Section UPROG.

#[local]
Existing Instance progUnit.

Lemma init_alloc_uprogP :
  forall (ef: extra_fun_t) (ep1 ep2: extra_prog_t) ev s1 scs m r,
    init_alloc_uprog ef ep1 ep2 = ok r ->
    init_state ef ep1 ev (Estate scs m Vm.init) = ok s1 ->
    exists vm2,
      init_state ef ep2 ev (Estate scs m Vm.init) = ok (with_vm s1 vm2) /\
      eq_alloc r s1.(evm) vm2.
Proof.
  by move=> /= ??? _ ???? [<-] [<-]; exists Vm.init; split => //=; apply eq_alloc_empty.
Qed.

Lemma alloc_call_uprogP ev gd ep1 p1 ep2 p2
  (H: check_prog init_alloc_uprog check_f_extra_u ep1 p1 ep2 p2 = ok tt) f scs mem scs' mem' va vr:
    sem_call {|p_globs := gd; p_funcs := p1; p_extra := ep1; |} ev scs mem f va scs' mem' vr ->
    exists vr', 
     sem_call {|p_globs := gd; p_funcs := p2; p_extra := ep2; |} ev scs mem f va scs' mem' vr' /\
                List.Forall2 value_uincl vr vr'.
Proof.
  apply: (alloc_callP init_alloc_uprogP _ H).
  by rewrite /check_f_extra_u; t_xrbindP => r e _ a1 a2 r' /eqP <-.
Qed.

Lemma alloc_fun_uprogP_eq p ev fn f f' scs1 m1 scs2 m2 vargs vargs' vres vres' s0 s1 s2:
  check_fundef init_alloc_uprog check_f_extra_u (p_extra p) (p_extra p) (fn, f) (fn, f') tt = ok tt ->
  mapM2 ErrType dc_truncate_val f.(f_tyin) vargs' = ok vargs ->
  init_state (f_extra f) (p_extra p) ev (Estate scs1 m1 Vm.init) = ok s0 ->
  write_vars (~~direct_call) (f_params f) vargs s0 = ok s1 ->
  sem p ev s1 (f_body f) s2 ->
  get_var_is (~~ direct_call) (evm s2) (f_res f) = ok vres ->
  mapM2 ErrType dc_truncate_val f.(f_tyout) vres = ok vres' ->
  scs2 = s2.(escs) ->
  m2 = finalize f.(f_extra) s2.(emem) ->
  exists vm0' vm1' vm2' vres1 vres1',
       [ /\ mapM2 ErrType dc_truncate_val f'.(f_tyin) vargs' = ok vargs,
            init_state f'.(f_extra) (p_extra p) ev (Estate scs1 m1 Vm.init) = ok (with_vm s0 vm0') /\
            write_vars (~~direct_call) (f_params f') vargs (with_vm s0 vm0') = ok (with_vm s1 vm1'),
            sem p ev (with_vm s1 vm1') (f_body f') (with_vm s2 vm2'),
            [ /\ get_var_is (~~ direct_call) (evm (with_vm s2 vm2')) (f_res f') = ok vres1,
                 List.Forall2 value_uincl vres' vres1' &
                mapM2 ErrType dc_truncate_val f'.(f_tyout) vres1 = ok vres1'] &
            scs2 = s2.(escs) /\ m2 = finalize f'.(f_extra) s2.(emem) ].
Proof. by apply (alloc_funP_eq_aux init_alloc_uprogP). Qed.

End UPROG.

Section SPROG.

#[local]
Existing Instance progStack.

Lemma check_fundef_meta ep1 ep2 ffd1 ffd2 u u' :
  check_fundef init_alloc_sprog check_f_extra_s ep1 ep2 ffd1 ffd2 u = ok u' →
  let fd1 := ffd1.2 in
  let fd2 := ffd2.2 in
  [/\
     sf_align fd1.(f_extra) = sf_align fd2.(f_extra),
     sf_stk_max fd1.(f_extra) = sf_stk_max fd2.(f_extra),
     sf_return_address fd1.(f_extra) = sf_return_address fd2.(f_extra) &
     sf_align_args fd1.(f_extra) = sf_align_args fd2.(f_extra)
  ].
Proof.
  case: ffd1 ffd2 => f1 fd1 [] f2 fd2.
  rewrite /check_fundef; t_xrbindP => _ r _ r'.
  rewrite /check_f_extra_s; t_xrbindP => /and4P[] /eqP -> _ _.
  case/and4P => _ /eqP -> _.
  case/and4P => _ _ /eqP -> /eqP ->.
  done.
Qed.

Lemma init_alloc_sprogP :
  forall (ef: extra_fun_t) (ep1 ep2: extra_prog_t) ev s1 scs m r,
    init_alloc_sprog ef ep1 ep2 = ok r ->
    init_state ef ep1 ev (Estate scs m Vm.init) = ok s1 ->
    exists vm2,
      init_state ef ep2 ev (Estate scs m Vm.init) = ok (with_vm s1 vm2) /\
      eq_alloc r s1.(evm) vm2.
Proof.
  rewrite /init_alloc_sprog /init_state /= /init_stk_state /check_vars.
  t_xrbindP => ef ep1 ep2 ev s1 scs m r hc m' ha; rewrite (@write_vars_lvals _ _ _ _ _ [::]) => hw.
  have [vm2 ]:= check_lvalsP (s1 := (Estate scs m' Vm.init)) hc eq_alloc_empty
                         (List_Forall2_refl _ (@value_uincl_refl)) hw.
  rewrite ha -write_vars_lvals => ??.
  by exists vm2.
Qed.

Lemma alloc_call_sprogP ev gd ep1 p1 ep2 p2
  (H: check_prog init_alloc_sprog check_f_extra_s ep1 p1 ep2 p2 = ok tt) f scs mem scs' mem' va vr:
    sem_call {|p_globs := gd; p_funcs := p1; p_extra := ep1; |} ev scs mem f va scs' mem' vr ->
    exists vr', 
     sem_call {|p_globs := gd; p_funcs := p2; p_extra := ep2; |} ev scs mem f va scs' mem' vr' /\
                List.Forall2 value_uincl vr vr'.
Proof.
  apply: (alloc_callP init_alloc_sprogP _ H).
  rewrite /check_f_extra_s; t_xrbindP => r e1 e2 a1 a2 r' c1 c2.
  split; last by []; first by case: ifP c2.
  rewrite /= /init_stk_state => a b c d.
  case/and4P: c1 => /eqP -> /eqP -> /eqP ->.
  by case/and4P => /eqP ->.
Qed.

End SPROG.

End WITH_PARAMS.
