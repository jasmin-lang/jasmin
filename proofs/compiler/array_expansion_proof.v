(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From mathcomp Require Import word_ssrZ.
Require Import psem array_expansion compiler_util ZArith.
Import Utf8 Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Record wf_ai (m : t) (x:var) ai := {
  x_nin : ~ Sv.In x m.(svars);
  len_pos : (0 < ai.(ai_len))%Z;
  len_def : ai_len ai = Z.of_nat (size (ai_elems ai));
  x_ty    : vtype x = sarr (Z.to_pos (arr_size ai.(ai_ty) (Z.to_pos ai.(ai_len))));
  xi_nin  : forall xi, xi \in ai_elems ai -> ~ Sv.In xi m.(svars);
  xi_ty   : forall xi, xi \in ai_elems ai -> xi.(vtype) = sword ai.(ai_ty);
  el_uni  : uniq (ai_elems ai);
  xi_disj : forall x' ai' xi, x <> x' -> Mvar.get m.(sarrs) x' = Some ai' ->
               ~(xi \in ai_elems ai /\ xi \in ai_elems ai')
}.

Definition wf_t (m : t) :=
  forall x ai, Mvar.get m.(sarrs) x = Some ai -> wf_ai m x ai.

Definition eval_array ws v i :=
  if v is Varr _ t
  then ok (rdflt undef_w (rmap (@Vword _) (WArray.get Aligned AAscale ws t i)))
  else type_error.

Definition eq_alloc_vm {wsw : WithSubWord} (m : t) vm1 vm2 :=
  vm1 =[m.(svars)] vm2 /\
  forall x ai xi,
    Mvar.get m.(sarrs) x = Some ai ->
    xi \in ai.(ai_elems) ->
    eval_array ai.(ai_ty) vm1.[x] (zindex xi ai.(ai_elems)) = ok vm2.[xi].

Definition expand_v expd v :=
  match expd with
  | Some (ws, len) => mapM (eval_array ws v) (ziota 0 len)
  | None => ok [:: v]
  end.

Definition expand_vs := mapM2 ErrType expand_v.

(* ---------------------------------------------------------------------- *)

Lemma eval_arrayP ws v i w : eval_array ws v i = ok w ->
  is_sarr (type_of_val v) /\ (w = undef_w \/ exists ww, w = @Vword ws ww).
Proof.
  by case: v => //= > [<-]; split=> //; case: WArray.get; auto; right; eexists.
Qed.

Lemma wf_mem dfl m x ax i :
  wf_ai m x ax ->
  [&& 0 <=? i & i <? ax.(ai_len)]%Z ->
  znth dfl ax.(ai_elems) i \in ax.(ai_elems).
Proof. move=> hai; rewrite hai.(len_def); apply mem_znth. Qed.

Lemma wf_index dfl m x ax i:
  wf_ai m x ax ->
  (0 <=? i)%Z && (i <? ax.(ai_len))%Z ->
  zindex (znth dfl (ai_elems ax) i) (ai_elems ax) = i.
Proof.
  move=> hai; rewrite /zindex hai.(len_def) => /andP[] /ZleP ? /ZltP ?.
  rewrite znthE // index_uniq.
  + by apply Z2Nat.id.
  + by apply/ZNltP;rewrite Z2Nat.id.
  apply hai.(el_uni).
Qed.

Lemma zindex_bound m x ai y:
  wf_ai m x ai ->
  let k := zindex y (ai_elems ai) in
  ((0 <=? k)%Z && (k <? ai_len ai)%Z) = (y \in ai_elems ai).
Proof.
  move=> hva /=; rewrite -index_mem.
  apply Bool.eq_iff_eq_true; split.
  + by move=> /andP [] _ /ZltP ?; apply/ZNltP; rewrite -/(zindex y (ai_elems ai)) -hva.(len_def).
  by move=> /ZNltP; rewrite (len_def hva) => h; apply /andP; split; [apply/ZleP/Zle_0_nat | apply/ZltP].
Qed.

Lemma wf_take_drop dfl m x ai i len :
  wf_ai m x ai ->
  (0 <= i)%Z -> (i + len <= ai_len ai)%Z -> (0 <= len)%Z ->
  take (Z.to_nat len) (drop (Z.to_nat i) (ai_elems ai)) =
  map (fun j => znth dfl (ai_elems ai) (i + j)) (ziota 0 len).
Proof.
  move=> vai h0i hilen h0len.
  have heq : size (take (Z.to_nat len) (drop (Z.to_nat i) (ai_elems ai))) = Z.to_nat len.
  + rewrite size_takel // size_drop; apply/ZNleP.
    rewrite Nat2Z.n2zB.
    + by rewrite -vai.(len_def) !Z2Nat.id // -subZE; lia.
    by apply/ZNleP; rewrite -vai.(len_def) !Z2Nat.id //; lia.
  apply (eq_from_nth (x0:= dfl)).
  + by rewrite size_map size_ziota.
  move=> j; rewrite heq => hj.
  rewrite nth_take // nth_drop (nth_map 0%Z) ?size_ziota // nth_ziota // /= znthE; last by lia.
  rewrite Z2Nat.inj_add // ?Nat2Z.id //; apply Zle_0_nat.
Qed.

Lemma wf_ai_elems dfl m x ai :
  wf_ai m x ai ->
  ai_elems ai = map (fun j => znth dfl (ai_elems ai) j) (ziota 0 ai.(ai_len)).
Proof.
  move=> vai.
  have /= := @wf_take_drop dfl m x ai 0 ai.(ai_len) vai (Z.le_refl _) (Z.le_refl _).
  rewrite vai.(len_def) => /(_ (Zle_0_nat _)) <-.
  by rewrite drop0 Nat2Z.id take_size.
Qed.

Lemma expand_vP n a ws l :
  mapM (eval_array ws (@Varr n a)) l =
    ok (map (fun i => rdflt undef_w (rmap (@Vword _) (WArray.get Aligned AAscale ws a i)))  l).
Proof. by elim: l => // *; simpl map; rewrite -mapM_cons. Qed.


Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  (fi : funname -> ufundef -> expand_info)
  (entries : seq funname)
  (p1 p2 : uprog).

#[local] Existing Instance direct_c.

Definition eq_alloc (m : t) (s1 s2 : estate) :=
  [/\ eq_alloc_vm m s1.(evm) s2.(evm),
      s1.(escs) = s2.(escs) &  s1.(emem) = s2.(emem)].

Local Notation gd := (p_globs p1).

Section Expr.

Context (m : t) (valid : wf_t m).

Section WDB.

Context (wdb : bool).

Lemma check_var_get s1 s2 x : 
  Sv.mem x (svars m) ->
  eq_alloc m s1 s2 ->
  get_var wdb (evm s1) x = get_var wdb (evm s2) x.
Proof. by move=> /Sv_memP hin -[] [] heq _ _; rewrite /get_var /= heq. Qed.

Lemma check_var_gets s1 s2 xs : 
  all (fun (x:var_i) => Sv.mem x (svars m)) xs ->
  eq_alloc m s1 s2 ->
  get_var_is wdb (evm s1) xs = get_var_is wdb (evm s2) xs.
Proof. 
  move=> hall heqa; elim: xs hall => //= x xs hrec /andP [].
  by move=> /(check_var_get) -/(_ _ _ heqa) -> /hrec ->.
Qed.

Lemma check_gvar_get s1 s2 x :
  check_gvar m x ->
  eq_alloc m s1 s2 ->
  get_gvar wdb gd s1.(evm) x = get_gvar wdb gd s2.(evm) x.
Proof. rewrite /get_gvar /check_gvar; case: is_lvar => //=; apply check_var_get. Qed.

Lemma eq_alloc_mem s1 s2 : eq_alloc m s1 s2 -> emem s1 = emem s2.
Proof. by case. Qed.

Lemma eq_alloc_scs s1 s2 : eq_alloc m s1 s2 -> escs s1 = escs s2.
Proof. by case. Qed.

Section EXPR.

Context (s1 s2 : estate) (h : eq_alloc m s1 s2).

Let P e1 :=
  forall e2, expand_e m e1 = ok e2 ->
  forall v, sem_pexpr wdb gd s1 e1 = ok v ->
            sem_pexpr wdb gd s2 e2 = ok v.

Let Q es1 :=
  forall es2, expand_es m es1 = ok es2 ->
  forall v, sem_pexprs wdb gd s1 es1 = ok v ->
            sem_pexprs wdb gd s2 es2 = ok v.


Lemma expand_eP_and : (forall e, P e) /\ (forall es, Q es).
Proof.
  apply: pexprs_ind_pair; subst P Q; split => //=; t_xrbindP.
  + by move=> > <- > <-.
  + by move=> > he > hes > hex > hexs <- > /(he _ hex) /= -> > /(hes _ hexs) /= -> <-.
  + by move=> z _ <- _ <-.
  + by move=> b _ <- _ <-.
  + by move=> n _ <- _ <-.
  + by move=> > /(check_gvar_get) -/(_ _ _ h) -> <-.
  + move=> al aa sz x e hrec e2.
    case: ifP => [/check_gvar_get /(_ h)|/norP/proj1/negbNE hlv].
    + t_xrbindP=> -> e1 /hrec he <- v /=.
      apply: on_arr_gvarP => n t hty ->.
      by t_xrbindP=> i vi /he -> /= -> /= w -> <-.
    case hgetx : Mvar.get => [ax|//]; case: is_constP => // i.
    t_xrbindP=> /eqP <- /eqP -> /eqP -> hbound <- v; have hai := valid hgetx.
    apply: on_arr_gvarP => n t /eqP hty.
    rewrite /get_gvar hlv{hlv} => /get_varP [ hx1 _ _] /=.
    t_xrbindP=> ? hw <-.
    case: h=> -[_] /(_ _ _ _ hgetx (wf_mem (v_var (gv x)) hai hbound)).
    by rewrite -hx1 /= (wf_index _ hai hbound) /get_gvar /get_var hw /= => -[<-] /=; rewrite orbT.
  + move=> aa sz len x e hrec e2 he e1 /hrec hrec1 <- /=.
    rewrite (check_gvar_get he h) => v.
    apply on_arr_gvarP => n t hty -> /=.
    by t_xrbindP => i vi /hrec1 -> /= -> t' /= -> <-.
  + move=> al sz x e hrec e2 hin e1 /hrec hrec1 <- /=.
    move=> v p vp; rewrite (check_var_get hin h) => -> /= -> /= i vi /hrec1 -> /= -> /=.
    by rewrite (eq_alloc_mem h) => ? -> <-.
  + by move=> o e1 hrec e2 e1' /hrec he1 <- /= ?? /he1 -> /= ->.
  + by move=> o e1 hrec1 e2 hrec2 e' e1' /hrec1 he1 e2' /hrec2 he2 <- /= ?? /he1 -> /= ? /he2 -> /=.
  + by move=> op es hrec e' es' hes' <- ?? /(hrec _ hes') /=; rewrite /sem_pexprs => -> /= ->.
  move=> t b hrecb e1 hrec1 e2 hrec2 e' b' /hrecb hb e1' /hrec1 he1 e2'  /hrec2 he2 <- /=.
  by move=> ??? /hb -> /= -> /= ?? /he1 -> /= -> ?? /he2 -> /= -> /= <-.
Qed.

Lemma expand_eP e : P e.
Proof. by case: expand_eP_and. Qed.

Lemma expand_esP e : Q e.
Proof. by case: expand_eP_and. Qed.

End EXPR.

Lemma eq_alloc_write_var s1 s2 (x: var_i) v s1':
   eq_alloc m s1 s2 ->
   Sv.mem x (svars m) ->
   write_var wdb x v s1 = ok s1' ->
   ∃ s2' : estate, write_var wdb x v s2 = ok s2' ∧ eq_alloc m s1' s2'.
Proof.
  move=> h; case: (h) => -[heq ha] hscs hmem /=.
  move=> /Sv_memP hin hw.
  have [vm2 hw2 heq2]:= write_var_eq_on hw heq.
  exists (with_vm s1' vm2); split.
  + have -> // : s2 = with_vm s1 (evm s2) by case: (s2) hscs hmem => ??? /= <- <-.
  split => //; split; first by apply: eq_onI heq2; SvD.fsetdec.
  move=> x' ai xi hai hxi.
  have vai := valid hai; move: vai.(x_nin) (vai.(xi_nin) hxi) => hnx' hnxi.
  rewrite -(vrvP_var hw); last by SvD.fsetdec.
  rewrite -(vrvP_var hw2); last by SvD.fsetdec.
  by apply ha.
Qed.

Lemma expand_lvP (s1 s2 : estate) : 
  eq_alloc m s1 s2 ->
  forall x1 x2, expand_lv m x1 = ok x2 ->
  forall v s1',
     write_lval wdb gd x1 v s1 = ok s1' ->
     exists s2', write_lval wdb gd x2 v s2 = ok s2' /\ eq_alloc m s1' s2'.
Proof.
  move=> h; case: (h) => -[heq ha] hscs hmem [] /=.
  + move=> ii ty _ [<-] /= ?? /dup [] /write_noneP [-> _ _] hn.
    by exists s2; split => //; apply: uincl_write_none hn.
  + by move=> x; t_xrbindP => _ ? <- /= v1 s1'; apply eq_alloc_write_var.
  + move=> al ws x e x2; t_xrbindP => hin e' he <- v s1' vx p /=.
    rewrite (check_var_get hin h) => -> /= -> /= pe ve.
    move=> /(expand_eP h he) -> /= -> /= ? -> /= mem.
    by rewrite -hmem => -> /= <-; exists (with_mem s2 mem).
  + move=> al aa ws x e x2.
    case: ifPn => [hin | hnin].
    + t_xrbindP => e' he <- v s1' /=.
      apply on_arr_varP => n t hty.
      rewrite (check_var_get hin h) => -> /=.
      t_xrbindP => i vi /(expand_eP h he) -> /= -> /= ? -> /= t' -> hw.
      by apply (eq_alloc_write_var h hin hw).
    case hai: Mvar.get => [ai | //].
    case: is_constP => // i ; t_xrbindP => /eqP <- /eqP -> /eqP -> hbound <- v s1'.
    apply on_arr_varP => n t hty hget /=.
    t_xrbindP => w hvw t' ht' /dup[] hw1 /write_varP [? _ htrv]; subst s1'.
    have vai := valid hai; have hin := wf_mem (v_var x) vai hbound.
    move: (vai.(xi_ty) hin) (vai.(xi_nin) hin) => htyi ?.
    have [htri htrvi hdb hdv]:= to_word_vm_truncate_val wdb htyi hvw.
    set xi := znth (v_var x) (ai_elems ai) i.
    have hw2 := write_var_truncate (x:= {| v_var := xi; v_info := v_info x |}) hdb htri s2.
    eexists; split; first eauto.
    split => //; split.
    + apply: (eq_onT (vm2:= evm s1)).
      + apply eq_onS; apply: (disjoint_eq_on (wdb := wdb) (gd := gd) (r := x) (v := Varr t')) => //.
        by rewrite vrv_var; move/Sv_memP : hnin => hnin; apply/Sv.is_empty_spec; SvD.fsetdec.
      apply: (eq_onT heq).
      apply:
        (disjoint_eq_on
           (wdb := wdb)
           (gd := gd)
           (r := Lvar (VarI xi x.(v_info)))
           (v := v)) => //.
      rewrite vrv_var /= /xi; apply/Sv.is_empty_spec; SvD.fsetdec.
    move=> x' ai' xi' hx' hxi'.
    rewrite /eval_array/on_arr_var /=.
    have [htri' htrvi' hdb' hdv']:= to_word_vm_truncate_val true htyi hvw.
    rewrite Vm.setP //; case: eqP => hxx'.
    + subst x'; move: hx'; rewrite hai => -[?]; subst ai'.
      rewrite hty /= eqxx.
      rewrite (WArray.setP _ ht').
      rewrite Vm.setP; case: (xi =P xi') => hxixi'.
      + by subst xi'; rewrite (wf_index _ vai hbound) eqxx htrvi'.
      case: eqP => ?.
      + by subst i; elim hxixi'; rewrite /xi znth_index.
      have := ha _ _ _ hai hxi'; rewrite /eval_array.
      by move/get_varP: hget => [<-].
    rewrite Vm.setP_neq; first by apply: ha hx' hxi'.
    have /(_ xi) hn := vai.(xi_disj) hxx' hx'.
    by apply /eqP => ?; subst xi'; apply hn.
  move=> aa ws len x e x2; t_xrbindP => hin e' he <- /= v s1'.
  apply on_arr_varP => n t hty.
  rewrite (check_var_get hin h) => -> /=.
  t_xrbindP => i vi /(expand_eP h he) -> /= -> /= ? -> /= t' -> /= hw.
  by apply (eq_alloc_write_var h hin hw).
Qed.

Lemma expand_lvsP (s1 s2 : estate) : 
  eq_alloc m s1 s2 ->
  forall x1 x2, expand_lvs m x1 = ok x2 ->
  forall vs s1',
     write_lvals wdb gd s1 x1 vs = ok s1' ->
     exists s2', write_lvals wdb gd s2 x2 vs = ok s2' /\ eq_alloc m s1' s2'.
Proof.
  move=> heqa x1 x2 hex; elim: x1 x2 hex s1 s2 heqa => /=.
  + by move=> ? [<-] s1 s2 ? [ | //] ? [<-]; exists s2.
  move=> x1 xs1 hrec ?; t_xrbindP => x2 hx xs2 hxs <- s1 s2 heqa [//|v vs] s1'.
  t_xrbindP => s1'' /(expand_lvP heqa hx) [s2'' [hw heqa']] /(hrec _ hxs _ _ heqa') [s2' [??]].
  by exists s2'; split => //=; rewrite hw.
Qed.

End WDB.

Opaque ziota.

Lemma expand_paramsP (s1 s2 : estate) e expdin :
  eq_alloc m s1 s2 ->
  forall es1 es2 vs, mapM2 e (expand_param m) expdin es1 = ok es2 ->
    sem_pexprs false gd s1 es1 = ok vs ->
    exists2 vs', expand_vs expdin vs = ok vs' &
      sem_pexprs false gd s2 (flatten es2) = ok (flatten vs').
Proof.
  move=> h ?? + H; elim: {H}(mapM2_Forall3 H) => [?[<-]|]; first by eexists.
  move=> [] /=; last first.
  + by t_xrbindP => > /(expand_eP h) {}h <- ?
      hrec > /h{h} /= -> ? /hrec{hrec}[? + ->] <- /= => ->; eexists.
  move=> [ws len] [] //=.
  + move=> g c >.
    t_xrbindP=> a1 /o2rP hga /and3P[/eqP? /eqP ? hloc] + _; subst.
    rewrite /get_gvar /=hloc{hloc} /get_var /=.
    move=> + hrec _ _ [<-] z0 /hrec{hrec}+ <- => + [? ->] /= => <-.
    have vai := (valid hga); case: h => -[_ /(_ _ _ _ hga){hga}hgai _ _].
    have := Vm.getP (evm s1) (gv g); rewrite vai.(x_ty) /compat_val /=.
    move => /compat_typeE /type_of_valI [x2 /dup[] hg ->].
    rewrite /sem_pexprs mapM_cat -/(sem_pexprs _ _ _ (flatten _)) => -> /=.
    rewrite expand_vP /=; eexists; eauto.
    rewrite mapM_map /comp /= /get_gvar /get_var /= mapM_ok /=; do 2!f_equal.
    rewrite (wf_ai_elems (v_var (gv g)) vai).
    rewrite -map_comp; apply eq_in_map => i; rewrite in_ziota /comp /= => hbound.
    move/hgai: (wf_mem (v_var (gv g)) vai hbound); rewrite hg /= => -[<-].
    by rewrite (wf_index _ vai hbound).

  move=> aa ws' len' g ei es >.
  t_xrbindP=> /eqP ?; subst aa.
  case: is_constP => // i _ /o2rP [<-].
  move=> a /o2rP hga.
  move=> /and4P [] /eqP ? /eqP ? /eqP ? hloc ? _ hrec vs z; subst ws ws' len es => /=.
  have vai := valid hga.

(*  have [hninx [hlen hxty] hlena haxi huni hother]:= valid hga. *)
  apply: on_arr_gvarP; rewrite vai.(x_ty) => len1 t [?]; subst len1.
  rewrite /get_gvar hloc => /get_varP [hgx _ _]; t_xrbindP => st hst ?; subst z.
  move=> ? /hrec[? hex +] <-; rewrite /sem_pexprs mapM_cat hex /= => -> /=.
  rewrite expand_vP /=; eexists; eauto.
  rewrite mapM_map /comp /= /get_gvar /get_var /= mapM_ok /=; do 2!f_equal.
  have := WArray.get_sub_bound hst.
  rewrite /arr_size /=.
  move: t st hgx hst.
  set wsaty := (X in (X * len')%positive).
  set wsaty' := (X in (X * _)%positive).
  have -> : wsaty' = wsaty by done.
  have -> : Zpos (wsaty * len') = (wsize_size (ai_ty a) * Zpos len')%Z by done.
  have -> : Zpos (wsaty * Z.to_pos (ai_len a))%positive = (wsize_size (ai_ty a) * ai_len a)%Z.
  + by have ? := vai.(len_pos); rewrite Pos2Z.inj_mul Z2Pos.id.
  move=> {wsaty'} t st hgx hst hi.
  have ? := wsize_size_pos (ai_ty a).
  rewrite -Z2Nat.inj_pos (wf_take_drop (v_var (gv g)) vai) //. 2,3: by nia.
  rewrite -map_comp; apply eq_in_map => j; rewrite in_ziota /comp /= => /andP [] /ZleP ? /ZltP ?.
  have hbound : (0 <=? i + j)%Z && (i + j <? ai_len a)%Z.
  + by apply /andP; split; [apply/ZleP|apply/ZltP] => //; nia.
  case: h => -[_ /(_ _ _ _ hga){hga}hgai _ _].
  move/hgai: (wf_mem (v_var (gv g)) vai hbound); rewrite -hgx /= => -[<-].
  by rewrite (wf_index _ vai hbound) (WArray.get_sub_get hst).
Qed.

Lemma wf_write_get s (x:var_i) ai (a : WArray.array (Z.to_pos (arr_size (ai_ty ai) (Z.to_pos (ai_len ai))))) i len :
  wf_ai m x ai ->
  (0 <= i)%Z -> (i + len <= ai_len ai)%Z -> (0 <= len)%Z ->
  exists2 vm,
    write_lvals false gd s [seq Lvar {| v_var := znth (v_var x) (ai_elems ai) x0; v_info := v_info x |} | x0 <- ziota i len]
      [seq rdflt undef_w (rmap (Vword (s:=ai_ty ai)) (WArray.get Aligned AAscale (ai_ty ai) a i)) | i <- ziota i len] = ok (with_vm s vm) &
    forall y,
      vm.[y] =
        let j := zindex y (ai_elems ai) in
        if j \in ziota i len then
           rdflt undef_w (rmap (Vword (s:=ai_ty ai)) (WArray.get Aligned AAscale (ai_ty ai) a j))
        else (evm s).[y].
Proof.
  move => hva h0i hilen h0l.
  have : uniq (ziota i len).
  + rewrite ziotaE map_inj_uniq ?iota_uniq //.
    by move=> j1 j2 h; apply Nat2Z.inj; lia.
  elim/ziota_ind: (ziota _ _) s => /= [ | k l hk hrec] s.
  + by move=> _; exists (evm s) => //; rewrite with_vm_same.
  move=> /andP [] hkl huni.
  rewrite /write_var /set_var /DB /=.
  have hk1 : (0 <=? k)%Z && (k <? ai_len ai)%Z.
  + by apply/andP; split; [apply/ZleP|apply/ZltP]; lia.
  have hin := wf_mem (v_var x) hva hk1.
  rewrite (xi_ty hva hin).
  have -> /= : (truncatable false (sword (ai_ty ai)) (rdflt undef_w (rmap (Vword (s:=ai_ty ai)) (WArray.get Aligned AAscale (ai_ty ai) a k)))).
  + by case: WArray.get => //=.
  set s1 := with_vm _ _.
  case: (hrec s1 huni) => vm -> hvm; exists vm => // y; rewrite in_cons.
  case: eqP => [he | hne] /=.
  + move: (hk1); rewrite -he (zindex_bound y hva) => hyin.
    rewrite hvm {1}he (negbTE hkl) /s1 /= -he znth_index // Vm.setP_eq.
    rewrite (xi_ty hva hyin); case: WArray.get => /= ?.
    + by rewrite cmp_le_refl orbT.
    by apply (to_word_undef (s:=U8)).
  rewrite hvm; case: ifPn => // _.
  by rewrite /s1 /= Vm.setP_neq //; apply /eqP => ?; subst y; apply/hne/(wf_index _ hva hk1).
Qed.

Opaque Z.mul.
Lemma expand_returnP (s1 s2 : estate) expdout :
  eq_alloc m s1 s2 ->
  forall x1 xs2, expand_return m expdout x1 = ok xs2 ->
  forall v vs' s1',
    write_lval false gd x1 v s1 = ok s1' ->
    expand_v expdout v = ok vs' ->
    exists2 s2', write_lvals false gd s2 xs2 vs' = ok s2' &
      eq_alloc m s1' s2'.
Proof.
  move=> heqa.
  case: expdout => /=; last first.
  + t_xrbindP => > /expand_lvP hlv <- > hw <- /=.
    by have [? [-> ?] /=]:= hlv _ _ _ heqa _ _ hw; eauto.
  move=> [a len] [] //.
  + move=> > [<-] v1 vs ? /write_noneP [->] _ _ hm; exists s2 => //.
    rewrite -(size_ziota 0) -map_const_nseq.
    elim/ziota_ind: (ziota _ _) vs hm; first by move=> ? [<-].
    move=> /= > ? hrec; t_xrbindP => > /eval_arrayP [? h] ?/hrec{}hrec <-.
    rewrite /write_none /= /truncatable.
    by case: h => [-> | [? ->]] /=; rewrite ?wsize_le_U8.
  + move=> x xs2.
    t_xrbindP=> ai /o2rP hga; have hva:= valid hga.
    move=> /andP[/eqP? /eqP?] hmap va vs' s1'; subst.
    move=> /write_varP [-> _]. rewrite hva.(x_ty) => /vm_truncate_valEl [] a -> _.
    rewrite expand_vP => -[?]; subst vs'.
    rewrite (wf_ai_elems (v_var x) hva) -map_comp /comp.
    have [vm2 -> hvm2 ]:= wf_write_get s2 a hva (Z.le_refl _) (Z.le_refl _) (Z.lt_le_incl _ _ (len_pos hva)).
    eexists; eauto.
    case heqa => heqv ??; split => //; split => /=.
    + move=> y hin; rewrite hvm2 /= Vm.setP_neq; last by apply/eqP=> ?; subst y; apply (x_nin hva hin).
      case: ifP; last by move=> _; apply heqv.
      rewrite in_ziota /= (zindex_bound y hva).
      by move=> /(xi_nin hva); elim.
    move=> y ai' xi; rewrite hvm2 /= Vm.setP; case: eqP => [? | hne]; last first.
    + move=> hga' hin'.
      case: ifP; last by move=> _; apply heqv.
      rewrite in_ziota /= (zindex_bound _ hva) => ?.
      have /(_ xi):= xi_disj hva hne hga'; elim => //.
    subst y; rewrite hga => -[<-] hin.
    by rewrite in_ziota (zindex_bound _ hva) hin (x_ty hva) vm_truncate_val_eq.
  move => aa ws' len' x e xs2; t_xrbindP => /eqP ?; subst aa.
  case: is_constP => // i _ /o2rP [<-] ai /o2rP hga; have hva:= valid hga.
  move=> /and3P []/eqP ? /eqP ? /eqP ? <- va vs' s1'; subst a ws' len.
  have /= := Vm.getP (evm s1) x; rewrite hva.(x_ty) => /compat_valEl [a heqx]; rewrite heqx.
  t_xrbindP => sa /to_arrI -> ra hra /write_varP [] -> _ _.
  rewrite expand_vP => -[?]; subst vs'.
  have := WArray.set_sub_bound hra.
  have [ltws lt0len]:= (wsize_size_pos (ai_ty ai), len_pos hva).
  rewrite /arr_size /mk_scale {1}(Z2Pos.id _ lt0len) Z2Pos.id; last by nia.
  move=> hb; have [{hb} h0i hilen'] : (0 <= i /\ i + len' <= ai_len ai)%Z by nia.
  have -> := wf_take_drop (v_var x) hva h0i hilen' (Zle_0_pos _).
  rewrite -map_comp /comp.
  have [vm2 ] := wf_write_get s2 ra hva h0i hilen' (Zle_0_pos _).
  rewrite {1 2}(ziota_shift i len') -!map_comp /comp.
  have -> :
   [seq rdflt undef_w (rmap (Vword (s:=ai_ty ai)) (WArray.get Aligned AAscale (ai_ty ai) ra (i + x0))) | x0 <- ziota 0 len'] =
   [seq rdflt undef_w (rmap (Vword (s:=ai_ty ai)) (WArray.get Aligned AAscale (ai_ty ai) sa i0)) | i0 <- ziota 0 len'].
  + apply eq_in_map => j; rewrite in_ziota => /andP [] /ZleP ? /ZltP ?.
    rewrite (WArray.set_sub_get hra).
    have -> : (i <=? i + j)%Z && (i + j <? i + len')%Z; last by do 3!f_equal; ring.
    by apply/andP; split; [apply/ZleP|apply/ZltP]; nia.
  move=> -> hvm2; eexists; eauto.
  have hybound: forall y,
        (i <=? zindex y (ai_elems ai))%Z && (zindex y (ai_elems ai) <? i + len')%Z ->
        (y \in ai_elems ai).
  + move=> y => /andP [/ZleP ? /ZltP ?]; rewrite -(zindex_bound y hva).
    by apply/andP; split; [apply/ZleP|apply/ZltP]; nia.
  case heqa => heqv ??; split => //; split => /=.
  + move=> y hin; rewrite hvm2 /= Vm.setP_neq; last by apply/eqP=> ?; subst y; apply (x_nin hva hin).
    case: ifP; last by move=> _; apply heqv.
    by rewrite in_ziota /= => /hybound /(xi_nin hva); elim.
  move=> y ai' xi; rewrite hvm2 /= Vm.setP; case: eqP => [? | hne]; last first.
  + move=> hga' hin'.
    case: ifP; last by move=> _; apply heqv.
    rewrite in_ziota /= => /hybound ?.
    have /(_ xi):= xi_disj hva hne hga'; elim => //.
  subst y; rewrite hga => -[<-] hin.
  rewrite in_ziota (x_ty hva); case: ifP => //=; rewrite eqxx //.
  move: (hin); rewrite -(zindex_bound _ hva) => /andP [] /ZleP ? /ZltP ? hn.
  rewrite /= (WArray.set_sub_get hra).
  by rewrite hn; have [_ /(_ _ _ _ hga hin)]:= heqv; rewrite heqx.
Qed.

Lemma expand_returnsP (s1 s2 : estate) e expdout :
  eq_alloc m s1 s2 ->
  forall xs1 xs2, mapM2 e (expand_return m) expdout xs1 = ok xs2 ->
  forall vs vs' s1',
    write_lvals false gd s1 xs1 vs = ok s1' ->
    expand_vs expdout vs = ok vs' ->
    exists2 s2', write_lvals false gd s2 (flatten xs2) (flatten vs') = ok s2' &
      eq_alloc m s1' s2'.
Proof.
  move=> + > H; elim: {H}(mapM2_Forall3 H) s1 s2.
  + by move=> ??? [] // ?? [<-] [<-]; eexists.
  move=> a b c la lb lc hexp _ hrec s1 s2 heqa [] // v1 vs vs' s1' /=.
  t_xrbindP => s1'' hw hws vs2 hexpv vs2' hexpvs <- /=.
  have [s2'' hw2 heqa'']:= expand_returnP heqa hexp hw hexpv.
  have [s2' hws2 heqa'] := hrec _ _ heqa'' _ _ _ hws hexpvs.
  exists s2' => //; apply: cat_fold2 hw2 hws2.
Qed.

End Expr.

Hypothesis Hcomp : expand_prog fi entries p1 = ok p2.

Local Notation ev := tt.

Section Step1.

Context step1
  (Hstep1 : map_cfprog_name (expand_fsig fi entries) (p_funcs p1) = ok step1).

Definition fsigs :=
  foldr (fun x y => Mf.set y x.1 x.2.2) (Mf.empty _) step1.

Lemma eq_globs : p_globs p2 = gd.
Proof. by move: Hcomp; rewrite /expand_prog; t_xrbindP=> z ??? <-. Qed.

Lemma all_checked fn fd1 :
  get_fundef (p_funcs p1) fn = Some fd1 ->
  exists fd2 fd2' m g, [/\ get_fundef (p_funcs p2) fn = Some fd2,
    Mf.get fsigs fn = Some g,
    expand_fsig fi entries fn fd1 = ok (fd2', m, g) &
    expand_fbody fsigs fn (fd2', m) = ok fd2].
Proof.
  move=> /(get_map_cfprog_name_gen Hstep1)[[[fd2' m'] fex'] hex' hfd'].
  move: Hcomp; rewrite /expand_prog Hstep1 /=.
  t_xrbindP=> pf2 hpf2 ?; subst.
  have [f' /= hf' hgf'] := get_map_cfprog_name_gen hpf2 hfd'.
  eexists _, _, _, _; split; eauto.
  rewrite /fsigs.
  elim: step1 hfd' => //= -[] > hrec /=.
  by case: ifP => [+[?]|+/hrec]; rewrite eq_sym Mf.setP => ->; subst.
Qed.

Let Pi_r s1 (i1:instr_r) s2:=
  forall ii m ii' i2 s1',
    wf_t m -> eq_alloc m s1 s1' ->
    expand_i fsigs m (MkI ii i1) = ok (MkI ii' i2) ->
  exists2 s2', eq_alloc m s2 s2' & sem_i p2 ev s1' i2 s2'.

Let Pi s1 (i1:instr) s2:=
  forall m i2 s1',
    wf_t m -> eq_alloc m s1 s1' ->
    expand_i fsigs m i1 = ok i2 ->
  exists2 s2', eq_alloc m s2 s2' & sem_I p2 ev s1' i2 s2'.

Let Pc s1 (c1:cmd) s2 :=
  forall m c2 s1',
    wf_t m -> eq_alloc m s1 s1' ->
    mapM (expand_i fsigs m) c1 = ok c2 ->
  exists2 s2', eq_alloc m s2 s2' & sem p2 ev s1' c2 s2'.

Let Pfor (i1:var_i) vs s1 c1 s2 :=
  forall m c2 s1',
    wf_t m -> eq_alloc m s1 s1' -> Sv.mem i1 m.(svars) ->
    mapM (expand_i fsigs m) c1 = ok c2 ->
  exists2 s2', eq_alloc m s2 s2' & sem_for p2 ev i1 vs s1' c2 s2'.

Let Pfun scs m fn vargs scs' m' vres :=
  forall expdin expdout, Mf.get fsigs fn = Some (expdin, expdout) ->
  forall vargs', expand_vs expdin vargs = ok vargs' ->
  exists2 vres', expand_vs expdout vres = ok vres' &
    sem_call p2 ev scs m fn (flatten vargs') scs' m' (flatten vres').

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move=> s1 m c2 s1' hwf heqa /= [<-]; exists s1' => //; constructor.
Qed.

Local Lemma Hcons : sem_Ind_cons p1 ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ Hi _ Hc m c2 s1' hwf heqa1 /=.
  t_xrbindP => i' /Hi -/(_ _ hwf heqa1) [s2' heqa2 hsemi].
  move=> c' /Hc -/(_ _ hwf heqa2) [s3' heqa3 hsemc] <-; exists s3' => //.
  econstructor; eauto.
Qed.

Local Lemma HmkI : sem_Ind_mkI p1 ev Pi_r Pi.
Proof.
  move=> ii i s1 s2 _ Hi m [ii' i2] s1' hwf heqa /Hi -/(_ _ hwf heqa) [s2' heqa' hsemi].
  exists s2' => //; constructor.
Qed.

Local Lemma Hassgn : sem_Ind_assgn p1 Pi_r.
Proof.
  move => s1 s2 x tag ty e v v' hse htr hw ii m ii' i2 s1' hwf heqa /=.
  t_xrbindP => x' hx e' he _ <-.
  have ? := expand_eP hwf heqa he hse.
  have [s2' [hw' heqa']] := expand_lvP hwf heqa hx hw.
  exists s2' => //; econstructor; rewrite ?eq_globs; eauto.
Qed.

Local Lemma Hopn : sem_Ind_opn p1 Pi_r.
Proof.
  move => s1 s2 t o xs es; rewrite /sem_sopn; t_xrbindP => vs ves hse ho hws.
  move=> ii m ii' e2 s1' hwf heqa /=; t_xrbindP => xs' hxs es' hes _ <-.
  have := expand_esP hwf heqa hes hse.
  have := expand_lvsP hwf heqa hxs hws.
  rewrite -eq_globs => -[s2' [hws' ?]] hse'; exists s2' => //.
  by constructor; rewrite /sem_sopn hse' /= ho.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p1 Pi_r.
Proof.
  move => s1 scs2 m2 s2 o xs es vs ves hse ho hws.
  move=> ii m ii' e2 s1' hwf heqa /=; t_xrbindP => xs' hxs es' hes _ <-.
  have := expand_esP hwf heqa hes hse.
  have heqa': eq_alloc m (with_scs (with_mem s1 m2) scs2) (with_scs (with_mem s1' m2) scs2) by case: heqa.
  have := expand_lvsP hwf heqa' hxs hws.
  rewrite -eq_globs => -[s2' [hws' ?]] hse'; exists s2' => //.
  by econstructor; eauto; rewrite -(eq_alloc_mem heqa) -(eq_alloc_scs heqa).
Qed.

Local Lemma Hif_true : sem_Ind_if_true p1 ev Pc Pi_r.
Proof.
  move => s1 s2 e c1 c2 hse hs hrec ii m ii' ? s1' hwf  heqa /=.
  t_xrbindP => e' he c1' hc1 c2' hc2 _ <-.
  have := expand_eP hwf heqa he hse; rewrite -eq_globs => hse'.
  have [s2' ??] := hrec _ _ _ hwf heqa hc1.
  by exists s2' => //; apply Eif_true.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p1 ev Pc Pi_r.
Proof.
  move => s1 s2 e c1 c2 hse hs hrec ii m ii' ? s1' hwf  heqa /=.
  t_xrbindP => e' he c1' hc1 c2' hc2 _ <-.
  have := expand_eP hwf heqa he hse; rewrite -eq_globs => hse'.
  have [s2' ??] := hrec _ _ _ hwf heqa hc2.
  by exists s2' => //; apply Eif_false.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p1 ev Pc Pi_r.
Proof.
  move => s1 s2 s3 s4 a c1 e c2 _ hrec1 hse _ hrec2 _ hrecw ii m ii' ? s1' hwf heqa /=.
  t_xrbindP => e' he c1' hc1 c2' hc2 hii <-.
  have [sc1 heqa1 hs1]:= hrec1 _ _ _ hwf heqa hc1.
  have := expand_eP hwf heqa1 he hse; rewrite -eq_globs => hse'.
  have [sc2 heqa2 hs2]:= hrec2 _ _ _ hwf heqa1 hc2.
  have [| s2' ? hsw]:= hrecw ii m ii' (Cwhile a c1' e' c2') _ hwf heqa2.
  + by rewrite /= he hc1 hc2 hii.
  exists s2' => //; apply: Ewhile_true hsw; eauto.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p1 ev Pc Pi_r.
Proof.
  move => s1 s2 a c e c' _ hrec1 hse ii m ii' ? s1' hwf heqa /=.
  t_xrbindP => e' he c1' hc1 c2' hc2 hii <-.
  have [s2' heqa1 hs1]:= hrec1 _ _ _ hwf heqa hc1.
  have := expand_eP hwf heqa1 he hse; rewrite -eq_globs => hse'.
  exists s2' => //; apply: Ewhile_false; eauto.
Qed.

Local Lemma Hfor : sem_Ind_for p1 ev Pi_r Pfor.
Proof.
  move => s1 s2 i d lo hi c vlo vhi hslo hshi _ hfor ii m ii' ? s1' hwf heqa /=.
  t_xrbindP => hin lo' hlo hi' hhi c' hc ? <-.
  have := expand_eP hwf heqa hlo hslo.
  have := expand_eP hwf heqa hhi hshi; rewrite -eq_globs => hshi' hslo'.
  have [s2' ??]:= hfor _ _ _ hwf heqa hin hc.
  exists s2' => //; econstructor; eauto.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof.
  move=> s i c i2 c' s1' hwf heqa _; exists s1' => //; constructor.
Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p1 ev Pc Pfor.
Proof.
  move=> s1 s1w s2 s3 i w ws c Hwi _ Hc _ Hfor m c' s1' hwf heqa hin hc.
  have [s1w' [? heqa1']]:= eq_alloc_write_var hwf heqa hin Hwi.
  have [s2' heqa2 ?]:= Hc _ _ _ hwf heqa1' hc.
  have [s3' ??]:= Hfor _ _ _ hwf heqa2 hin hc.
  exists s3' => //; econstructor; eauto.
Qed.

Local Lemma Hcall : sem_Ind_call p1 ev Pi_r Pfun.
Proof.
  move=> s1 scs2 m2 s2 xs fn args vargs vs Hes Hsc Hfun Hw ii1 m ii2 i2 s1' hwf heqa /=.
  case hgfn: Mf.get => [[ei eo]|//].
  t_xrbindP=> xs' sxs' hxs <- es' ses' hes <- _.
  have [? heva]:= expand_paramsP hwf heqa hes Hes.
  have heqa': eq_alloc m (with_scs (with_mem s1 m2) scs2) (with_scs (with_mem s1' m2) scs2) by case: heqa.
  case: {Hfun}(Hfun ei eo hgfn _ heva) => ? hevr.
  have [s2' ]:= expand_returnsP hwf heqa' hxs Hw hevr.
  rewrite -eq_globs => ???? <-; exists s2' => //; econstructor; eauto.
  by case: heqa => _ <- <-.
Qed.

Lemma wf_init_map ffi m finf : init_map ffi = ok (m, finf) -> wf_t m.
Proof.
  rewrite /init_map; t_xrbindP.
  set svars_ := sv_of_list _ _.
  pose wf_st := 
    fun (svm: Sv.t * Mvar.t array_info) =>
      [/\ wf_t {| svars := svars_; sarrs := svm.2 |}, 
          Sv.Subset svars_ svm.1 &
          (forall  x ai xi,
             Mvar.get svm.2 x = Some ai ->
             xi \in (ai_elems ai) ->
             Sv.In xi svm.1)].
  suff : forall l svm svm', wf_st svm -> foldM init_array_info svm l = ok svm' -> wf_st svm'.
  + move=> h svm' /h []; first by split => //=.
    by move=> ? _ _ <-.
  elim => /= [ ??? [<-] // | vi vis hrec svm svm' hwf].
  t_xrbindP => svm1 heq; apply: hrec.
  move: heq; rewrite /init_array_info.
  case: svm hwf => sv1 m1 hwf; t_xrbindP => /Sv_memP hin [sv2 len].
  set ty := sword _; t_xrbindP.
  set elems := [seq _ | id <- vi_n vi] => hfold.
  have :
    [/\ Sv.Equal sv2 (Sv.union (sv_of_list id elems) sv1),
        disjoint sv1 (sv_of_list (fun x => x) elems),
        uniq elems &
        len = (0 + Z.of_nat (size elems))%Z].
  + elim: elems sv1 {hwf hin} 0%Z hfold => /= [ | x elems hrec] sv1 z; t_xrbindP.
    + move => <- <-; split => //; last by rewrite Z.add_0_r.
      by rewrite /sv_of_list /=; apply/disjointP; SvD.fsetdec.
    move=> _ /Sv_memP hnin <- /hrec [heq /disjointP hdis huni ->]; split => //.
    + by rewrite sv_of_list_cons heq; SvD.fsetdec.
    + apply/disjointP => y ?; rewrite sv_of_list_cons.
      by have := hdis y; SvD.fsetdec.
    + apply /andP; split => //; apply /negP => hin.
      by apply (hdis x); [SvD.fsetdec | apply /sv_of_listP/map_f].
    have /= -> := Nat2Z.inj_succ (size elems); ring.
  move=> [heq /disjointP hdis huni hlen] /andP [] /ZltP h0len /eqP hty <-.
  case: hwf => /= hwf hincl hget.
  split => /=.
  + move=> x ai /=; rewrite Mvar.setP; case: eqP.
    + move=> ? [<-]; subst x.
      constructor => //=.
      + by have := hdis (vi_v vi); SvD.fsetdec.
      + by move=> xi; rewrite -(map_id elems) => /sv_of_listP; have := hdis xi; SvD.fsetdec.
      + by move=> xi /mapP [id ? ->].
      move=> x' ai' xi /eqP ?. rewrite Mvar.setP_neq // => /hget -/(_ xi) h [].
      by rewrite -(map_id elems) => /sv_of_listP -/hdis h1 /h.
    move=> hne /dup[] /hget h1 /hwf [/= ??????? xi_disj]; constructor => //=.
    move=> x' ai' xi hxx'; rewrite Mvar.setP; case: eqP => [? | hne']; last by apply xi_disj.
    by move=> [<-] [] /= /h1 /hdis h2; rewrite -(map_id elems) => /sv_of_listP.
  + by SvD.fsetdec.
  move=> x ai xi; rewrite Mvar.setP; case: eqP => [? | _].
  + by move=> [<-] /=; rewrite -(map_id elems) => /sv_of_listP; SvD.fsetdec.
  move=> h1 h2; have := hget _ _ _ h1 h2; SvD.fsetdec.
Qed.

Lemma eq_alloc_empty m scs mem :
  wf_t m ->
  eq_alloc m {| escs := scs; emem := mem; evm := Vm.init |} {| escs := scs; emem := mem; evm := Vm.init |}.
Proof.
  move=> hwf; split => //; split => //=.
  move=> x ai xi /hwf hva hin.
  rewrite !Vm.initP (x_ty hva) (xi_ty hva hin) /=.
  case heq : WArray.get => [w | /=]; last first.
  + by rewrite /undef_v (undef_x_vundef (_ _)).
  have []:= WArray.get_bound heq; rewrite /mk_scale => ???.
  have h : ((0 <= Z0 < wsize_size (ai_ty ai)))%Z.
  + by move=> /=; have := wsize_size_pos (ai_ty ai); lia.
  have [_ /(_ Z0 h)] := read_read8 heq.
  by rewrite WArray.get0 //= WArray.addE; have := wsize_size_pos (ai_ty ai); lia.
Qed.

Lemma mapM2_dc_truncate_id tys vs vs':
  mapM2 ErrType dc_truncate_val tys vs' = ok vs -> vs' = vs.
Proof.
  by rewrite /dc_truncate_val /=; move=> h; have := mapM2_Forall3 h; elim => // _ > [->] _ ->.
Qed.

Lemma expend_tyv_expand_return m b s tys (xs : list var_i) ins:
  mapM2 E.length_mismatch (expand_tyv m b s) tys xs = ok ins ->
  mapM2 E.length_mismatch (expand_return m) [seq i.2 | i <- ins] [seq Lvar i | i <- xs] =
    ok [seq map Lvar x.1.2 | x <- ins].
Proof.
  move=> hxs; have := mapM2_Forall3 hxs; elim => //= {tys hxs xs ins}.
  move=> ty x [[tysx xsx] o] tys xs cs0 hexty _ hrec; move: hexty.
  rewrite {1}/expand_tyv {2}/expand_return /=.
  case heq : Mvar.get => [ai | ]; t_xrbindP.
  + by move=> _ ???; subst tysx xsx o; rewrite /= !eqxx hrec /= map_comp.
  by move=> hin ???; subst tysx xsx o; rewrite hin /= hrec.
Qed.

Lemma expend_tyv_expand_param m b s tys (xs : list var_i) ins:
  mapM2 E.length_mismatch (expand_tyv m b s) tys xs = ok ins ->
  mapM2 E.length_mismatch (expand_param m) [seq i.2 | i <- ins] [seq Pvar (mk_lvar i) | i <- xs] =
    ok [seq map (fun y => Pvar (mk_lvar y)) x.1.2 | x <- ins].
Proof.
  move=> hxs; have := mapM2_Forall3 hxs; elim => //= {tys hxs xs ins}.
  move=> ty x [[tysx xsx] o] tys xs cs0 hexty _ hrec; move: hexty.
  rewrite {1}/expand_tyv {2}/expand_param /=.
  case heq : Mvar.get => [ai | ]; t_xrbindP.
  + by move=> _ ???; subst tysx xsx o; rewrite /= !eqxx /= hrec /= -!map_comp.
  by move=> hin ???; subst tysx xsx o; rewrite /check_gvar /=hin /= hrec.
Qed.

Local Lemma Hproc : sem_Ind_proc p1 ev Pc Pfun.
Proof.
  move=> scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hget Hca [?] Hw _ Hc Hres Hcr ??; subst s0 scs2 m2.
  have [fd1 [fd2 [m [inout [Hget2 hsigs /=]]]] {Hget}]:= all_checked Hget.
  rewrite /expand_fsig; t_xrbindP => -[mt finf].
  case: f Hca Hw Hc Hres Hcr => /=.
  move=> finfo ftyin fparams fbody ftyout fres fextra.
  set fd := {| f_info := finfo |} => Hca Hw Hc Hres Hcr hinit.
  t_xrbindP => ins hparams outs hres <- ??; subst mt inout.
  t_xrbindP => c hc ?; subst fd1.
  move=> expdin expdout; rewrite hsigs => -[??] vargs1 hexvs; subst expdin expdout.
  set (sempty := {| escs := scs1; emem := m1; evm := Vm.init |}).
  have hwf := wf_init_map hinit.
  have heqae : eq_alloc m sempty sempty by apply eq_alloc_empty.
  rewrite (write_vars_lvals false gd) in Hw.
  have [??]:= (mapM2_dc_truncate_id Hca, mapM2_dc_truncate_id Hcr); subst vargs' vres'.
  have [s1']:= expand_returnsP hwf heqae (expend_tyv_expand_return hparams) Hw hexvs.
  rewrite map_comp -map_flatten -(write_vars_lvals false gd) => hw heqa1.
  have [s2' heqa2 hsem]:= Hc _ _ _ hwf heqa1 hc.
  rewrite -(sem_pexprs_get_var false gd) in Hres.
  have [vs' hex]:= expand_paramsP hwf heqa2 (expend_tyv_expand_param hres) Hres.
  rewrite map_comp -map_flatten sem_pexprs_get_var => hwr.
  exists vs' => //.
  econstructor; eauto => //=.
  + elim: (mapM2_Forall3 hparams) vargs vargs1 {Hw Hca hw} hexvs.
    + by move=> [] //= ? [<-].
    move=> ty x [[tysx xsx] o] tys xs cs0 hexty _ hrec [] //= v vs ?.
    t_xrbindP => ? hexp ? hexps <- /=; apply: cat_mapM2 (hrec _ _ hexps).
    move: hexty hexp; rewrite /expand_tyv /expand_v.
    case heq: Mvar.get => [ai | ]; t_xrbindP.
    + move=> _ ???; subst tysx xsx o.
      have hva := hwf _ _ heq.
      rewrite (wf_ai_elems (v_var x) hva) -map_comp /comp.
      by move=> /mapM_Forall2; elim => //= > _ _ ->.
    by move=> hin <- _ <- [<-].
  + elim: (mapM2_Forall3 hres) vres vs' {hwr Hcr Hres} hex.
    + by move=> [] //= ? [<-].
    move=> ty x [[tysx xsx] o] tys xs cs0 hexty _ hrec [] //= v vs ?.
    t_xrbindP => ? hexp ? hexps <- /=; apply: cat_mapM2 (hrec _ _ hexps).
    move: hexty hexp; rewrite /expand_tyv /expand_v.
    case heq: Mvar.get => [ai | ]; t_xrbindP.
    + move=> _ ???; subst tysx xsx o.
      have hva := hwf _ _ heq.
      rewrite (wf_ai_elems (v_var x) hva) -map_comp /comp.
      by move=> /mapM_Forall2; elim => //= > _ _ ->.
    by move=> hin <- _ <- [<-].
  + by case: heqa2.
  by case: heqa2.
Qed.

Lemma expand_callP_aux f scs mem scs' mem' va vr:
  sem_call p1 ev scs mem f va scs' mem' vr ->
  Pfun scs mem f va scs' mem' vr.
Proof.
  exact: (sem_call_Ind Hskip Hcons HmkI Hassgn Hopn Hsyscall
          Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
Qed.

End Step1.

Lemma expand_callP f scs mem scs' mem' va vr:
  sem_call p1 ev scs mem f va scs' mem' vr ->
  f \in entries ->
  sem_call p2 ev scs mem f va scs' mem' vr.
Proof.
  apply: (rbindP _ Hcomp) => s1 /[dup]Hs1/expand_callP_aux h _ /[dup]+/h{h}.
  move=> [???? {}f fd {}va va' ??? {}vr vr' hgf htri _ _ _ _ htro _ _] h b.
  suff /h{h}h : Mf.get (fsigs s1) f =
    Some (map (fun=> None) (f_tyin fd), map (fun=> None) (f_tyout fd)).
  + have /h{h}[?] :
     expand_vs (map (fun=> None) (f_tyin fd)) va' = ok [seq [:: x] | x <- va'].
    + by elim: (f_tyin fd) va' va htri {h} => [[]|> hrec []]//=; t_xrbindP=> > /hrec ->.
    have : expand_vs (map (fun=> None) (f_tyout fd)) vr' = ok [seq [:: x] | x <- vr'].
    + by elim: (f_tyout fd) vr vr' htro => [[]//?[<-]//|> hrec [] //=>]; t_xrbindP => ? /hrec + <- => ->.
    by move=> -> [<-]; rewrite 2!flatten_seq1.
  move: Hs1 fd hgf {h htri htro}; rewrite {}/fsigs; elim: (p_funcs p1) s1
    => [> [<-]|[?[? fti fp ? fto fr]]> hrec] //=.
  t_xrbindP=> > +?? /hrec{hrec}h ?; subst=> /=.
  case: eqP; last by move=> /nesym /eqP?; rewrite Mf.setP_neq //.
  move=> <- + ? [] <- /=.
  rewrite Mf.setP_eq /expand_fsig b /=; t_xrbindP=> -[??] _; t_xrbindP=> ? hz ? hz1 <- /=.
  do 2 f_equal.
  + move: (mapM2_Forall3 hz); elim => //= > + _ ->.
    by rewrite /expand_tyv; case: Mvar.get => //; t_xrbindP => _ <-.
  move: (mapM2_Forall3 hz1); elim => //= > + _ ->.
  by rewrite /expand_tyv; case: Mvar.get => //; t_xrbindP => _ <-.
Qed.

End WITH_PARAMS.
