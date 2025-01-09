(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg eqtype.
From mathcomp Require Import word_ssrZ.
Require Import psem array_expansion array_expansion_cl compiler_util ZArith.
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
  xi_in   : forall xi, xi \in ai_elems ai -> Sv.In xi m.(selem);
  xi_ty   : forall xi, xi \in ai_elems ai -> xi.(vtype) = sword ai.(ai_ty);
  el_uni  : uniq (ai_elems ai);
  xi_disj : forall x' ai' xi, x <> x' -> Mvar.get m.(sarrs) x' = Some ai' ->
               ~(xi \in ai_elems ai /\ xi \in ai_elems ai')
}.

Definition wf_t (m : t) :=
  forall x ai, Mvar.get m.(sarrs) x = Some ai -> wf_ai m x ai.

Section Tabstract.
Context {tabstract : Tabstract}.
Context (fresh_var_ident: v_kind → string → stype → Ident.ident).

Definition dfl_w ws := Vword (wrepr ws 0).

Definition eval_array (ws:wsize) v i :=
  if v is Varr _ t
  then ok (rdflt (dfl_w ws) (rmap (@Vword _ _) (WArray.get Aligned AAscale ws t i)))
  else type_error.

Definition eq_alloc_vm_restr {wsw : WithSubWord} (X:Sv.t) (m : t) vm1 vm2 :=
  vm1 =[m.(svars)] vm2 /\
  forall x ai xi,
    Sv.In x X ->
    Mvar.get m.(sarrs) x = Some ai ->
    xi \in ai.(ai_elems) ->
    eval_array ai.(ai_ty) vm1.[x] (zindex xi ai.(ai_elems)) = ok vm2.[xi].

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
  is_sarr (type_of_val v) /\ exists ww, w = @Vword _ ws ww.
Proof.
  case: v => //= > h; split=> //.
  by case: WArray.get h => //= ww [<-]; eexists.
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
  mapM (eval_array ws (@Varr _ n a)) l =
    ok (map (fun i => rdflt (dfl_w ws) (rmap (@Vword _ _) (WArray.get Aligned AAscale ws a i))) l).
Proof. by elim: l => // *; simpl map; rewrite -mapM_cons. Qed.

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {absp : Prabstract}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  (fi : funname -> ufundef -> expand_info)
  (entries : seq funname)
  (p1 p2 : uprog).

#[local] Existing Instance direct_c.

Definition eq_alloc (m : t) (s1 s2 : estate) :=
  [/\ eq_alloc_vm m s1.(evm) s2.(evm),
      s1.(escs) = s2.(escs), s1.(emem) = s2.(emem) & s1.(eassert) = s2.(eassert)].

Definition eq_alloc_restr (X:Sv.t) (m : t) (s1 s2 : estate) :=
  [/\ eq_alloc_vm_restr X m s1.(evm) s2.(evm),
      s1.(escs) = s2.(escs), s1.(emem) = s2.(emem) & s1.(eassert) = s2.(eassert)].

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

Lemma eq_alloc_restr_write_var X s1 s2 (x: var_i) v s1':
   eq_alloc_restr X m s1 s2 ->
   Sv.mem x (svars m) ->
   write_var wdb x v s1 = ok s1' ->
   ∃ s2' : estate, write_var wdb x v s2 = ok s2' ∧ eq_alloc_restr (Sv.add x X) m s1' s2'.
Proof.
  move=> h; case: (h) => -[heq ha] hscs hmem hassert /=.
  move=> /Sv_memP hin hw.
  have [vm2 hw2 heq2]:= write_var_eq_on hw heq.
  exists (with_vm s1' vm2); split.
  + have -> // : s2 = with_vm s1 (evm s2) by case: (s2) hscs hmem hassert => ???? /= <- <- <-.
  split => //; split; first by apply: eq_onI heq2; SvD.fsetdec.
  move=> x' ai xi hP hai hxi.
  have vai := valid hai; move: vai.(x_nin) (vai.(xi_nin) hxi) => hnx' hnxi.
  rewrite -(vrvP_var hw); last by SvD.fsetdec.
  rewrite -(vrvP_var hw2); last by SvD.fsetdec.
  apply ha => //.
  case: (v_var x =P x'); last by SvD.fsetdec.
  by move=> ?; subst x'; elim: hnx'.
Qed.

Lemma eq_alloc_write_var s1 s2 (x: var_i) v s1':
   eq_alloc m s1 s2 ->
   Sv.mem x (svars m) ->
   write_var wdb x v s1 = ok s1' ->
   ∃ s2' : estate, write_var wdb x v s2 = ok s2' ∧ eq_alloc m s1' s2'.
Proof.
  move=> h; case: (h) => -[heq ha] hscs hmem hassert /=.
  move=> /Sv_memP hin hw.
  have [vm2 hw2 heq2]:= write_var_eq_on hw heq.
  exists (with_vm s1' vm2); split.
  + have -> // : s2 = with_vm s1 (evm s2) by case: (s2) hscs hmem hassert => ???? /= <- <- <-.
  split => //; split; first by apply: eq_onI heq2; SvD.fsetdec.
  move=> x' ai xi hai hxi.
  have vai := valid hai; move: vai.(x_nin) (vai.(xi_nin) hxi) => hnx' hnxi.
  rewrite -(vrvP_var hw); last by SvD.fsetdec.
  rewrite -(vrvP_var hw2); last by SvD.fsetdec.
  by apply ha.
Qed.

Let P e1 :=
  forall (s1 s2 : estate) (h : eq_alloc m s1 s2),
  forall e2, expand_e m e1 = ok e2 ->
  forall v, sem_pexpr wdb gd s1 e1 = ok v ->
            sem_pexpr wdb gd s2 e2 = ok v.

Let Q es1 :=
  forall (s1 s2 : estate) (h : eq_alloc m s1 s2),
  forall es2, expand_es m es1 = ok es2 ->
  forall v, sem_pexprs wdb gd s1 es1 = ok v ->
            sem_pexprs wdb gd s2 es2 = ok v.

Lemma expand_eP_and : (forall e, P e) /\ (forall es, Q es).
Proof.
  apply: pexprs_ind_pair; subst P Q; split => //=; t_xrbindP.
  + by move=> > ? > <- > <-.
  + by move=> > he > hes > h > hex > hexs <- > /(he _ _ h _ hex) /= -> > /(hes _ _ h _ hexs) /= -> <-.
  1-3: by move=> > _ _ <- _ <-.
  + by move=> > h > /(check_gvar_get) -/(_ _ _ h) -> <-.
  + move=> al aa sz x e hrec > h e2.
    case: ifP => [/check_gvar_get /(_ h)|/norP/proj1/negbNE hlv].
    + t_xrbindP=> -> e1 /(hrec _ _ h) he <- v /=.
      apply: on_arr_gvarP => n t hty ->.
      by t_xrbindP=> i vi /he -> /= -> /= w -> <-.
    case hgetx : Mvar.get => [ax|//]; case: is_constP => // i.
    t_xrbindP=> /eqP <- /eqP -> /eqP -> hbound <- v; have hai := valid hgetx.
    apply: on_arr_gvarP => n t /eqP hty.
    rewrite /get_gvar hlv{hlv} => /get_varP [ hx1 _ _] /=.
    t_xrbindP=> ? hw <-.
    case: h=> -[_] /(_ _ _ _ hgetx (wf_mem (v_var (gv x)) hai hbound)).
    by rewrite -hx1 /= (wf_index _ hai hbound) /get_gvar /get_var hw /= => -[<-] /=; rewrite orbT.
  + move=> aa sz len x e hrec > h e2 he e1 /(hrec _ _ h) hrec1 <- /=.
    rewrite (check_gvar_get he h) => v.
    apply on_arr_gvarP => n t hty -> /=.
    by t_xrbindP => i vi /hrec1 -> /= -> t' /= -> <-.
  + move=> al sz x e hrec > h e2 hin e1 /(hrec _ _ h) hrec1 <- /=.
    move=> v p vp; rewrite (check_var_get hin h) => -> /= -> /= i vi /hrec1 -> /= -> /=.
    by rewrite (eq_alloc_mem h) => ? -> <-.
  + by move=> o e1 hrec > h e2 e1' /(hrec _ _ h) he1 <- /= ?? /he1 -> /= ->.
  + by move=> o e1 hrec1 e2 hrec2 > h e' e1' /(hrec1 _ _ h) he1 e2' /(hrec2 _ _ h) he2 <- /= ?? /he1 -> /= ? /he2 -> /=.
  + by move=> op es hrec > h e' es' hes' <- ?? /(hrec _ _ h _ hes') /=; rewrite /sem_pexprs => -> /= ->.
  + move=> t b hrecb e1 hrec1 e2 hrec2 > h e' b' /(hrecb _ _ h) hb e1' /(hrec1 _ _ h) he1 e2' /(hrec2 _ _ h) he2 <- /=.
    by move=> ??? /hb -> /= -> /= ?? /he1 -> /= -> ?? /he2 -> /= -> /= <-.
  move=> > hi > hb > hs > hl > h > hin > /(hi _ _ h) hei > /hb heb > /(hs _ _ h) hes > /(hl _ _ h) hel <- /=.
  move=> > /hes -> /= -> > /hel -> /= -> /= v /hei -> /=.
  elim: ziota v => //= j js hrec v; t_xrbindP.
  move=> > /(eq_alloc_write_var h hin) [s2' [-> /= h']] > /(heb _ _ h') -> /= -> /=; apply hrec.
Qed.

Context (s1 s2 : estate) (h : eq_alloc m s1 s2).

Lemma expand_eP e1 e2 :
  expand_e m e1 = ok e2 ->
  forall v, sem_pexpr wdb gd s1 e1 = ok v ->
            sem_pexpr wdb gd s2 e2 = ok v.
Proof. apply: (proj1 expand_eP_and) h e2. Qed.

Lemma expand_esP es1 es2 :
  expand_es m es1 = ok es2 ->
  forall v, sem_pexprs wdb gd s1 es1 = ok v ->
            sem_pexprs wdb gd s2 es2 = ok v.
Proof. apply: (proj2 expand_eP_and) h es2. Qed.

End EXPR.

Lemma expand_lvP (s1 s2 : estate) :
  eq_alloc m s1 s2 ->
  forall x1 x2, expand_lv m x1 = ok x2 ->
  forall v s1',
     write_lval wdb gd x1 v s1 = ok s1' ->
     exists s2', write_lval wdb gd x2 v s2 = ok s2' /\ eq_alloc m s1' s2'.
Proof.
  move=> h; case: (h) => -[heq ha] hscs hmem heassert [] /=.
  + move=> ii ty _ [<-] /= ?? /[dup] /write_noneP [-> _ _] hn.
    exists s2; split => //; first by apply: uincl_write_none hn.
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
    t_xrbindP => w hvw t' ht' /[dup] hw1 /write_varP [? _ htrv]; subst s1'.
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

Lemma eval_array_is_def  ws t i v:
  eval_array ws t i = ok v ->
  is_defined v.
Proof.
  rewrite /eval_array; case: t => // len t [<-].
  by case: (WArray.get Aligned AAscale ws t i).
Qed.

Opaque ziota.
Lemma expand_paramsP (s1 s2 : estate) e expdin :
  eq_alloc m s1 s2 ->
  forall es1 es2 vs, mapM2 e (expand_param m) expdin es1 = ok es2 ->
    sem_pexprs wdb gd s1 es1 = ok vs ->
    exists2 vs', expand_vs expdin vs = ok vs' &
      sem_pexprs wdb gd s2 (flatten es2) = ok (flatten vs').
Proof.
  move=> h ?? + H; elim: {H}(mapM2_Forall3 H) => [?[<-]|]; first by eexists.
  move=> [] /=; last first.
  + by t_xrbindP => > /(expand_eP h) {}h <- ?
      hrec > /h{h} /= -> ? /hrec{hrec}[? + ->] <- /= => ->; eexists.
  move=> [ws len] [] //=.
  + move=> g c >.
    t_xrbindP=> a1 /o2rP hga /and3P[/eqP? /eqP ? hloc] + _; subst.
    rewrite /get_gvar /=hloc{hloc} /get_var /=; t_xrbindP.
    move=> + hrec _ _ hwdb <- z0 /hrec{hrec}+ <- => + [? ->] /= => <-.
    have vai := (valid hga); case: h => -[_ /(_ _ _ _ hga){hga}hgai _ _ _].
    have := Vm.getP (evm s1) (gv g); rewrite vai.(x_ty) /compat_val /=.
    move => /compat_typeE /type_of_valI [x2 /[dup] hg ->].
    rewrite /sem_pexprs mapM_cat -/(sem_pexprs _ _ _ (flatten _)) => -> /=.
    rewrite expand_vP /=; eexists; eauto.
    rewrite mapM_map /comp /= /get_gvar /get_var /=.
    have -> :
      mapM (λ x : var, assert (~~ wdb || is_defined (evm s2).[x]) ErrAddrUndef >> ok (evm s2).[x]) (ai_elems a1) =
      mapM (λ x : var, ok (evm s2).[x]) (ai_elems a1).
    + by apply mapM_ext => x /InP/hgai/eval_array_is_def ->; rewrite orbT.
    rewrite mapM_ok /=; do 2!f_equal.
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
  apply: on_arr_gvarP; rewrite vai.(x_ty) => len1 t [?]; subst len1.
  rewrite /get_gvar hloc => /get_varP [hgx _ _]; t_xrbindP => st hst ?; subst z.
  move=> ? /hrec[? hex +] <-; rewrite /sem_pexprs mapM_cat hex /= => -> /=.
  rewrite expand_vP /=; eexists; eauto.
  rewrite mapM_map /comp /= /get_gvar /get_var /=.
  have -> : mapM (λ x : var, assert (~~ wdb || is_defined (evm s2).[x]) ErrAddrUndef >> ok (evm s2).[x])
            (take (Pos.to_nat len') (drop (Z.to_nat i) (ai_elems a))) =
         mapM (λ x : var, ok (evm s2).[x]) (take (Pos.to_nat len') (drop (Z.to_nat i) (ai_elems a))).
  + case: h => -[_ /(_ _ _ _ hga){hga}hgai _ _ _].
    by apply mapM_ext => x /InP /mem_take /mem_drop/hgai/eval_array_is_def ->; rewrite orbT.
  rewrite mapM_ok /=; do 2!f_equal.
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
    write_lvals wdb gd s [seq Lvar {| v_var := znth (v_var x) (ai_elems ai) x0; v_info := v_info x |} | x0 <- ziota i len]
      [seq rdflt (dfl_w (ai_ty ai)) (rmap (Vword (s:=ai_ty ai)) (WArray.get Aligned AAscale (ai_ty ai) a i)) | i <- ziota i len] = ok (with_vm s vm) &
    forall y,
      vm.[y] =
        let j := zindex y (ai_elems ai) in
        if j \in ziota i len then
           rdflt (dfl_w (ai_ty ai)) (rmap (Vword (s:=ai_ty ai)) (WArray.get Aligned AAscale (ai_ty ai) a j))
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
  have -> /= : (truncatable wdb (sword (ai_ty ai)) (rdflt (dfl_w (ai_ty ai)) (rmap (Vword (s:=ai_ty ai)) (WArray.get Aligned AAscale (ai_ty ai) a k)))).
  + by case: WArray.get => //=; rewrite cmp_le_refl !orbT.
  have -> :
    is_defined (rdflt (dfl_w (ai_ty ai)) (rmap (Vword (s:=ai_ty ai)) (WArray.get Aligned AAscale (ai_ty ai) a k))).
  + by case: (WArray.get Aligned AAscale (ai_ty ai) a k).
  rewrite orbT /=.
  set s1 := with_vm _ _.
  case: (hrec s1 huni) => vm -> hvm; exists vm => // y; rewrite in_cons.
  case: eqP => [he | hne] /=.
  + move: (hk1); rewrite -he (zindex_bound y hva) => hyin.
    rewrite hvm {1}he (negbTE hkl) /s1 /= -he znth_index // Vm.setP_eq.
    by rewrite (xi_ty hva hyin); case: WArray.get => /= ?; rewrite cmp_le_refl orbT.
  rewrite hvm; case: ifPn => // _.
  by rewrite /s1 /= Vm.setP_neq //; apply /eqP => ?; subst y; apply/hne/(wf_index _ hva hk1).
Qed.

Opaque Z.mul.

Lemma expand_returnP_restr X (s1 s2 : estate) expdout :
  eq_alloc_restr X m s1 s2 ->
  forall x1 xs2, expand_return m expdout (Lvar x1) = ok xs2 ->
  forall v vs' s1',
    write_var wdb x1 v s1 = ok s1' ->
    expand_v expdout v = ok vs' ->
    exists2 s2', write_lvals wdb gd s2 xs2 vs' = ok s2' &
      eq_alloc_restr (Sv.add x1 X) m s1' s2'.
Proof.
  move=> heqa.
  case: expdout => /=; last first.
  + t_xrbindP => > hmem <- <- > hw <-.
    have [s2' [h ?] /= ]:= eq_alloc_restr_write_var heqa hmem hw.
    by exists s2' => //; rewrite h.
  move=> [a len] x xs2.
  t_xrbindP=> ai /o2rP hga; have hva:= valid hga.
  move=> /andP[/eqP? /eqP?] hmap va vs' s1'; subst.
  move=> /write_varP [-> _]; rewrite hva.(x_ty) => /vm_truncate_valEl [] a -> _.
  rewrite expand_vP => -[?]; subst vs'.
  rewrite (wf_ai_elems (v_var x) hva) -map_comp /comp.
  have [vm2 -> hvm2 ]:= wf_write_get s2 a hva (Z.le_refl _) (Z.le_refl _) (Z.lt_le_incl _ _ (len_pos hva)).
  eexists; eauto.
  case heqa => heqv ??; split => //; split => /=.
  + move=> y hin; rewrite hvm2 /= Vm.setP_neq; last by apply/eqP=> ?; subst y; apply (x_nin hva hin).
    case: ifP; last by move=> _; apply heqv.
    rewrite in_ziota /= (zindex_bound y hva).
    by move=> /(xi_nin hva); elim.
  move=> y ai' xi hor; rewrite hvm2 /= Vm.setP; case: eqP => [? | hne]; last first.
  + move=> hga' hin'.
    case: ifP.
    + rewrite in_ziota /= (zindex_bound _ hva) => ?.
      by have /(_ xi):= xi_disj hva hne hga'; elim.
    by move=> _; apply heqv; move/SvD.F.add_iff : hor => [?|//]; elim hne.
  subst y; rewrite hga => -[<-] hin.
  by rewrite in_ziota (zindex_bound _ hva) hin (x_ty hva) vm_truncate_val_eq.
Qed.

Lemma expand_returnsP_restr X (s1 s2 : estate) e expdout :
  eq_alloc_restr X m s1 s2 ->
  forall xs1 xs2, mapM2 e (expand_return m) expdout (map Lvar xs1) = ok xs2 ->
  forall vs vs' s1',
    write_vars wdb xs1 vs s1 = ok s1' ->
    expand_vs expdout vs = ok vs' ->
    exists2 s2', write_lvals wdb gd s2 (flatten xs2) (flatten vs') = ok s2' &
      eq_alloc_restr (Sv.union X (sv_of_list v_var xs1)) m s1' s2'.
Proof.
  move=> heqa xs1 xs2 h.
  elim: expdout xs1 xs2 h X s1 s2 heqa => [ | ex exs hrec] [ | x1 xs1] //=.
  + move=> _ [<-] X s1 s2 heqa [] // _ _ [<-] [<-] /=; exists s2 => //.
    rewrite /sv_of_list /=; case: heqa => -[] ? h ???; split => //; split => //.
    by move=> ??? hin; apply h; SvD.fsetdec.
  t_xrbindP => ? x1' hexp xs1' hmap <- X s1 s2 heqa [] //.
  t_xrbindP => > hw hws ? hexpv ? hexpvs <-.
  have [s2'' hw2 heqa''] := expand_returnP_restr heqa hexp hw hexpv.
  have [s2' hws2 heqa'] := hrec _ _ hmap _ _ _ heqa'' _ _ _ hws hexpvs.
  exists s2'; first by apply: cat_fold2 hw2 hws2.
  case: heqa' => -[] ? ha ???; split => //; split => //.
  move=> ???; rewrite sv_of_list_cons => hin; apply ha; SvD.fsetdec.
Qed.

Lemma expand_returnP (s1 s2 : estate) expdout :
  eq_alloc m s1 s2 ->
  forall x1 xs2, expand_return m expdout x1 = ok xs2 ->
  forall v vs' s1',
    write_lval wdb gd x1 v s1 = ok s1' ->
    expand_v expdout v = ok vs' ->
    exists2 s2', write_lvals wdb gd s2 xs2 vs' = ok s2' &
      eq_alloc m s1' s2'.
Proof.
  move=> heqa.
  case: expdout => /=; last first.
  + t_xrbindP => > /expand_lvP hlv <- > hw <- /=.
    by have [? [h ?] /=] := hlv _ _ heqa _ _ hw; rewrite h /=; eauto.
  move=> [a len] [] //.
  + move=> > [<-] v1 vs ? /write_noneP [->] _ _ hm; exists s2 => //.
    rewrite -(size_ziota 0) -map_const_nseq.
    elim/ziota_ind: (ziota _ _) vs hm; first by move=> ? [<-].
    move=> /= > ? hrec; t_xrbindP => > /eval_arrayP [? h] ?/hrec{}hrec <-.
    rewrite /write_none /= /truncatable.
    by case: h => ? -> /=; rewrite cmp_le_refl /DB !orbT /=.
  + move=> x xs2.
    t_xrbindP=> ai /o2rP hga; have hva:= valid hga.
    move=> /andP[/eqP? /eqP?] hmap va vs' s1'; subst.
    move=> /write_varP [-> _]; rewrite hva.(x_ty) => /vm_truncate_valEl [] a -> _.
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
      by have /(_ xi):= xi_disj hva hne hga'; elim.
    subst y; rewrite hga => -[<-] hin.
    by rewrite in_ziota (zindex_bound _ hva) hin (x_ty hva) vm_truncate_val_eq.
  move => aa ws' len' x e xs2; t_xrbindP => /eqP ?; subst aa.
  case: is_constP => // i _ /o2rP [<-] ai /o2rP hga; have hva:= valid hga.
  move=> /and3P []/eqP ? /eqP ? /eqP ? <- va vs' s1'; subst a ws' len.
  have /= := Vm.getP (evm s1) x; rewrite hva.(x_ty) => /compat_valEl [a heqx].
  rewrite /get_var heqx /= orbT /=.
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
   [seq rdflt (dfl_w (ai_ty ai)) (rmap (Vword (s:=ai_ty ai)) (WArray.get Aligned AAscale (ai_ty ai) ra (i + x0))) | x0 <- ziota 0 len'] =
   [seq rdflt (dfl_w (ai_ty ai)) (rmap (Vword (s:=ai_ty ai)) (WArray.get Aligned AAscale (ai_ty ai) sa i0)) | i0 <- ziota 0 len'].
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
  rewrite /= (WArray.set_sub_get hra) hn.
  by have [? /(_ _ _ _ hga hin)]:= heqv; rewrite heqx.
Qed.

Lemma expand_returnsP (s1 s2 : estate) e expdout :
  eq_alloc m s1 s2 ->
  forall xs1 xs2, mapM2 e (expand_return m) expdout xs1 = ok xs2 ->
  forall vs vs' s1',
    write_lvals wdb gd s1 xs1 vs = ok s1' ->
    expand_vs expdout vs = ok vs' ->
    exists2 s2', write_lvals wdb gd s2 (flatten xs2) (flatten vs') = ok s2' &
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

End WDB.
End Expr.

Hypothesis Hcomp : expand_prog fresh_var_ident fi entries p1 = ok p2.

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
    expand_fbody fresh_var_ident fsigs fn (fd2', m) = ok fd2].
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
  forall ii m c2 s1',
    wf_t m -> eq_alloc m s1 s1' ->
    expand_i fresh_var_ident fsigs m (MkI ii i1) = ok c2 ->
  exists2 s2', eq_alloc m s2 s2' & sem p2 ev s1' c2 s2'.

Let Pi s1 (i1:instr) s2:=
  forall m c2 s1',
    wf_t m -> eq_alloc m s1 s1' ->
    expand_i fresh_var_ident fsigs m i1 = ok c2 ->
  exists2 s2', eq_alloc m s2 s2' & sem p2 ev s1' c2 s2'.

Let Pc s1 (c1:cmd) s2 :=
  forall m c2 s1',
    wf_t m -> eq_alloc m s1 s1' ->
    mapM (expand_i fresh_var_ident fsigs m) c1 = ok c2 ->
  exists2 s2', eq_alloc m s2 s2' & sem p2 ev s1' (flatten c2) s2'.

Let Pfor (i1:var_i) vs s1 c1 s2 :=
  forall m c2 s1',
    wf_t m -> eq_alloc m s1 s1' -> Sv.mem i1 m.(svars) ->
    mapM (expand_i fresh_var_ident fsigs m) c1 = ok c2 ->
  exists2 s2', eq_alloc m s2 s2' & sem_for p2 ev i1 vs s1' (flatten c2) s2'.

Let Pfun scs m fn vargs scs' m' vres tr :=
  forall expdin expdout, Mf.get fsigs fn = Some (expdin, expdout) ->
  forall vargs', expand_vs expdin vargs = ok vargs' ->
  exists2 vres', expand_vs expdout vres = ok vres' &
    sem_call p2 ev scs m fn (flatten vargs') scs' m' (flatten vres') tr.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move=> s1 m c2 s1' hwf heqa /= [<-]; exists s1' => //; constructor.
Qed.

Local Lemma Hcons : sem_Ind_cons p1 ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ Hi _ Hc m c2 s1' hwf heqa1 /=.
  t_xrbindP => i' /Hi -/(_ _ hwf heqa1) [s2' heqa2 hsemi].
  move=> c' /Hc -/(_ _ hwf heqa2) [s3' heqa3 hsemc] <-; exists s3' => //=.
  apply: sem_app hsemi hsemc.
Qed.

Local Lemma HmkI : sem_Ind_mkI p1 ev Pi_r Pi.
Proof.
  by move=> ii i s1 s2 _ Hi m c2 s1' hwf heqa /Hi -/(_ _ hwf heqa) [s2' heqa' hsemi]; exists s2'.
Qed.

Lemma is_array_move_lvalP m x ws vi vs:
  is_array_move_lval m x = Some (ws, vi, vs) ->
  exists (x0:var_i) ai,
    [/\ Mvar.get (sarrs m) x0 = Some ai
      , ws = ai_ty ai
      & (x = Lvar x0 /\ vs = ai_elems ai) \/
        (exists len i,
          x = Lasub AAscale (ai_ty ai) len x0 (Pconst i) /\
          vs = take (Pos.to_nat len) (drop (Z.to_nat i) (ai_elems ai)))].
Proof.
  case: x => //= [x0 | aa ws' len x0 e]; case heq: Mvar.get => [ai | ] //.
  + by move=> [<- _ <-]; exists x0, ai; split; auto.
  case: is_constP => // i; case: andP => // -[/eqP ? /eqP ?] [???]; subst.
  exists x0, ai; split => //; eauto.
Qed.

Lemma is_array_move_rvalP m x ws vi vs:
  is_array_move_rval m x = Some (ws, vi, vs) ->
  exists (x0:var_i) ai,
    [/\ Mvar.get (sarrs m) x0 = Some ai
      , ws = ai_ty ai
      & (x = Pvar (mk_lvar x0) /\ vs = ai_elems ai) \/
        (exists len i,
          x = Psub AAscale (ai_ty ai) len (mk_lvar x0) (Pconst i) /\
          vs = take (Pos.to_nat len) (drop (Z.to_nat i) (ai_elems ai)))].
Proof.
  case: x => //= [[x0 []] | aa ws' len [x0 []] e] //=; case heq: Mvar.get => [ai | ] //.
  + by move=> [<- _ <-]; exists x0, ai; split; auto.
  case: is_constP => // i; case: andP => // -[/eqP ? /eqP ?] [???]; subst.
  exists x0, ai; split => //; eauto.
Qed.

Lemma is_array_moveP m x e ws vi1 t1 vi2 t2 :
  is_array_move m x e = Some (ws, vi1, t1, vi2, t2) ->
  exists (x1 x2:var_i) ai1 ai2,
   [/\ Mvar.get (sarrs m) x1 = Some ai1
     , Mvar.get (sarrs m) x2 = Some ai2
     , ws = ai_ty ai1 /\ ai_ty ai1 = ai_ty ai2
     , size t1 = size t2
     , 0 < size t2
     , (x = Lvar x1 /\ t1 = ai_elems ai1) \/
        (exists len i,
          x = Lasub AAscale ws len x1 (Pconst i) /\
          t1 = take (Pos.to_nat len) (drop (Z.to_nat i) (ai_elems ai1)))
     & (e = Pvar (mk_lvar x2) /\ t2 = ai_elems ai2) \/
       (exists len i,
          e = Psub AAscale ws len (mk_lvar x2) (Pconst i) /\
          t2 = take (Pos.to_nat len) (drop (Z.to_nat i) (ai_elems ai2)))].
Proof.
  rewrite /is_array_move.
  case h1 : is_array_move_lval => [[[ws1 vi3] t3] | //].
  case h2 : is_array_move_rval => [[[ws2 vi4] t4] | //].
  case: and3P=> // -[/eqP ? /eqP hsz ?] [?????]; subst ws1 ws2 vi3 vi4 t3 t4.
  have [x1 [ai1 [? hws ?]]] := is_array_move_lvalP h1.
  have [x2 [ai2 [? hws' ?]]] := is_array_move_rvalP h2; subst ws.
  by exists x1, x2, ai1, ai2; split => //; rewrite hws'.
Qed.

Lemma check_freshP selem selem' svar xs : check_fresh selem svar xs = ok selem' ->
  uniq xs /\
  forall x, x \in xs -> ~Sv.In x selem /\ ~Sv.In x svar.
Proof.
  elim: xs selem => //= y xs hrec selem; t_xrbindP.
  move=> z /andP [/Sv_memP ? /Sv_memP ? <-] /hrec [hu hnin]; split.
  + by apply/andP;split => //;apply/negP => /hnin; SvD.fsetdec.
  move=> x; rewrite in_cons => /orP [ /eqP -> //| /hnin]; SvD.fsetdec.
Qed.

Lemma index_take (T:eqType) x i (s : seq T) :
  x \in take i s ->
  seq.index x (take i s) = seq.index x s.
Proof.
  by move=> h; rewrite -{2} (cat_take_drop i s) index_cat h.
Qed.

Lemma zindex_cons (T : eqType) (t: seq T) x y :
  zindex x (y :: t) = (if y == x then 0 else zindex x t + 1)%Z.
Proof. rewrite /zindex /=; case: eqP => //;lia. Qed.

Lemma znth_cons (T : eqType) dfl (t: seq T) x i :
  (0 <= i)%Z ->
  znth dfl (x :: t) i = if i == 0%Z then x else znth dfl t (i-1)%Z.
Proof.
  move=> hi; rewrite znthE //; case: eqP => [-> // | ?].
  rewrite znthE /=; last by lia.
  by have <- : (Z.to_nat (i-1)).+1 = Z.to_nat i by lia.
Qed.

Lemma znth_cons1 (T : eqType) dfl (t: seq T) x i :
  (0 <= i)%Z ->
  znth dfl (x :: t) (i + 1) = znth dfl t i.
Proof.
  move=> ?; rewrite znth_cons; last lia.
  case: eqP; first lia.
  by have -> : (i + 1 - 1)%Z = i by ring.
Qed.

Lemma Forall2_zindex (T : eqType) (P : T -> T -> Prop) t1 t2 :
  List.Forall2 P t1 t2 ->
  uniq t1 -> uniq t2 ->
  forall x, x \in t1 ->
   [/\ P x (znth x t2 (zindex x t1))
     , zindex (znth x t2 (zindex x t1)) t2 = zindex x t1
     & znth x t2 (zindex x t1) \in t2].
Proof.
  elim => {t1 t2} // x1 x2 t1 t2 hP hall hrec.
  rewrite !cons_uniq => /andP[] hn1 hu1 /andP[] hn2 hu2 x.
  rewrite zindex_cons in_cons eq_sym; case: eqP.
  + by move=> <- _ /=; rewrite zindex_cons in_cons eqxx.
  move=> hne hin; have [h1 h2 h3] := hrec hu1 hu2 _ hin.
  rewrite /= in hin; rewrite znth_cons1; last by apply Zle_0_nat.
  split => //.
  + rewrite zindex_cons h2; case: eqP => //.
    move=> h; have : x2 \in t2.
    + rewrite h znthE; last by apply Zle_0_nat.
      by apply mem_nth; rewrite -(Forall2_size hall) /zindex Nat2Z.id index_mem.
    by move=> hh; rewrite hh in hn2.
  by rewrite in_cons h3 orbT.
Qed.

Lemma zindex_drop (T : eqType) i x (t : seq T) :
  (i <= zindex x t)%Z ->
  x \in t ->
  x \in drop (Z.to_nat i) t.
Proof.
  rewrite -{-3}(cat_take_drop (Z.to_nat i) t) !mem_cat /zindex !index_cat.
  case: ifP => // hnin.
  move=> h2 _.
  have := index_mem x (take (Z.to_nat i) t).
  rewrite hnin size_take => /ZNltP; case: ZNltP; lia.
Qed.

Lemma zindex_take (T : eqType) i x (t : seq T) :
  (zindex x t < i)%Z ->
  x \in t ->
  x \in take (Z.to_nat i) t.
Proof.
  rewrite -!index_mem size_take => h1 /ZNltP.
  rewrite -/(zindex x t) => h2.
  have ? : (zindex x (take (Z.to_nat i) t) <= zindex x t)%Z.
  + rewrite -{2}(cat_take_drop (Z.to_nat i) t) /zindex index_cat.
    case: ifP; first lia.
    have /ZNleP := index_size x (take (Z.to_nat i) t).
    rewrite Nat2Z.n2zD => h3 _.
    apply: Z.le_trans; last first.
    + apply/Zplus_le_compat_l/Zle_0_nat.
    lia.
  apply/ZNltP; rewrite -/(zindex x (take (Z.to_nat i) t)).
  case: ZNltP; lia.
Qed.

Lemma zindex_take_drop (T : eqType) i p x (t : seq T) :
  (0 <= i)%Z -> (0 <= p)%Z ->
  (i <= zindex x t)%Z ->
  (zindex x t < i + p)%Z ->
  x \in t ->
  x \in take (Z.to_nat p) (drop (Z.to_nat i) t).
Proof.
  move=> h0i h0p h1 h2 hin.
  apply: zindex_take; last by apply zindex_drop.
  move: h2.
  rewrite -{1}(cat_take_drop (Z.to_nat i) t) {1}/zindex.
  rewrite index_cat size_take.
  have -> : Z.to_nat i < size t.
  + apply/ZNltP; move: hin; rewrite -(index_mem x t) => /ZNltP.
    rewrite -/(zindex x t); lia.
  case: ifP; last first.
  + rewrite Nat2Z.n2zD -/(zindex x (drop (Z.to_nat i) t)) => _.
    rewrite /GRing.add/=; lia.
  have ?: (i < Z.of_nat (size t))%Z.
  + move: hin; rewrite -index_mem => /ZNltP; rewrite -/(zindex x t); lia.
  move=> hin1 _; move: h1.
  rewrite -(cat_take_drop (Z.to_nat i) t) /zindex index_cat hin1.
  move: hin1; rewrite -index_mem => /ZNltP.
  rewrite size_take.
  have -> : (Z.to_nat i < size t); last by lia.
  by apply/ZNltP; lia.
Qed.

Lemma zindex_sub_uniq (T : eqType) i p x (t : seq T) :
  uniq t ->
  let t1 := take p (drop i t) in
  (zindex x t1 < Z.of_nat (size t1))%Z ->
  zindex x t1 = (zindex x t - Z.of_nat i)%Z.
Proof.
  move=> + t1 hlt.
  have hin : x \in t1.
  + by rewrite -index_mem; apply/ZNltP.
  have -> : t = take i t ++ (t1 ++ drop p (drop i t)).
  + by rewrite !cat_take_drop.
  rewrite /zindex !index_cat cat_uniq hin => /and3P [_ /negP hnin _].
  case: ifP.
  + by move=> hin';elim: hnin; apply/hasP;exists x => //; rewrite mem_cat hin.
  rewrite size_take.
  case: ZNltP.
  + rewrite Nat2Z.n2zD /GRing.add /= => _ _; ring.
  by move=> /ZNltP h; move: hin; rewrite /t1 drop_oversize // leqNgt.
Qed.

Opaque wsize_size.
Lemma eval_array_sub ws len1 len2 i j
   (t t' : WArray.array (Z.to_pos (arr_size ws len1)))
     (ts : WArray.array (Z.to_pos (arr_size ws len2))) :
  WArray.set_sub AAscale t i ts = ok t' ->
  eval_array ws (Varr t') j =
    if ((i <=? j) && (j <? i + len2))%Z then eval_array ws (Varr ts) (j - i)
    else eval_array ws (Varr t) j.
Proof. by move=> hsub; rewrite /eval_array /= (WArray.set_sub_get hsub); case: ifP. Qed.

Local Lemma Hassgn : sem_Ind_assgn p1 Pi_r.
Proof.
  move => s1 s2 x tag ty e v v' hse htr hw ii m c2 s1' hwf heqa /=.
  case heq : is_array_move => [ [[[[ws vi1] t1] vi2] t2] | ]; first last.
  + t_xrbindP => x' hx e' he <-.
    have ? := expand_eP hwf heqa he hse.
    have [s2' [hw' heqa']] := expand_lvP hwf heqa hx hw.
    exists s2' => //; apply sem_seq_ir; econstructor; rewrite ?eq_globs; eauto.
  t_xrbindP; set vs := [seq _ | v <- t2] => selem' /check_freshP [huniq hnin] <-.
  set loads := map2 _ vs t2.
  set stores := map2 _ t1 vs.
  have [xd [xs [aid [ais [hgetd hgets [? heqs] hsz /ltP hsz2 hx he]]]]] := is_array_moveP heq.
  subst ws => {heq}.
  case: heqa => -[hvm hget hscs hmem hass].
  have sub_t2: forall x, x \in t2 -> x \in ai_elems ais.
  + by case: he => [ [_ -> //] | [len [i [_ ->]]]] y /mem_take /mem_drop.
  have ht2 :
    List.Forall (fun x => vtype x = sword (ai_ty ais) /\
      exists (w : word (ai_ty ais)), (evm s1').[x] = Vword w) t2.
  + apply/List.Forall_forall => y /InP /sub_t2 hin.
    rewrite (xi_ty (hwf _ _ hgets)) //; split => //.
    by have [_ ]:= eval_arrayP (hget _ _ _ hgets hin).
  have [vm [hseml heqe hall1]] :
    exists vm,
     [/\ sem p2 ev s1' loads (with_vm s1' vm)
       , evm s1' =[\ sv_of_list id vs] vm
       & List.Forall2 (fun v t => vm.[v] = (evm s1').[t]) vs t2].
  + subst loads vs => {stores hscs hmem hass hget hvm hsz he hsz2}.
    elim: t2 s1' huniq hnin ht2 sub_t2 => [ | x2 t2 hrec] /=.
    + by move=> s1' _ _ _; exists (evm s1'); split => //; rewrite with_vm_same; constructor.
    set v2 := {| vtype := _; vname := _ |}.
    move=> s1' /andP[] hv2 huniq hnin /List.Forall_cons_iff [[hty [w hx2]] hall] helems.
    set i := (MkI ii _).
    have hs1: sem_I p2 ev s1' i (with_vm s1' (evm s1').[v2 <- (evm s1').[x2]]).
    + constructor; econstructor.
      + rewrite /= /get_gvar /= /get_var hx2; reflexivity.
      + rewrite /truncate_val /= heqs truncate_word_u; reflexivity.
      by rewrite hx2; move: (w); rewrite -heqs => w'; apply: write_var_eq_type.
    have hv2t2 : v2 \notin t2.
    + apply/negP => hin.
      have := hnin v2; rewrite in_cons eqxx => /(_ erefl).
      have /(_ v2 (helems _ _)) := xi_in (hwf _ _ hgets).
      by rewrite in_cons hin orbT => /(_ erefl); SvD.fsetdec.
    have [|||]:= hrec (with_vm s1' (evm s1').[v2 <- (evm s1').[x2]]) huniq => {hrec} //.
    + by move=> ? hin; apply hnin; rewrite in_cons hin orbT.
    + apply/List.Forall_forall => y hin.
      move/List.Forall_forall: hall => /(_ _ hin).
      rewrite Vm.setP_neq //.
      apply/eqP => ?; subst y; by move/InP: hv2t2; apply.
    + by move=> y hy;apply helems; rewrite in_cons hy orbT.
    rewrite evm_with_vm => vm [hs2 heqe hall2].
    exists vm; split.
    + by apply: Eseq hs1 hs2.
    + rewrite sv_of_list_cons => h hy; rewrite -heqe; last by SvD.fsetdec.
      rewrite Vm.setP_neq //; apply /eqP; SvD.fsetdec.
    constructor.
    + rewrite -heqe.
      + by rewrite Vm.setP_eq hx2 /= heqs cmp_le_refl orbT.
      by apply/sv_of_listP; rewrite map_id.
    move=> {huniq hall helems hs2 heqe hnin hv2}.
    elim: t2 hall2 hv2t2 => /=.
    + by move=> _ _; constructor.
    move=> y t2 hrec /List.Forall2_cons_iff [] hvm hall.
    rewrite notin_cons => /andP[] /eqP hne hv2; constructor.
    + by rewrite hvm; rewrite Vm.setP_neq //; apply/eqP.
    by apply hrec.
  have sub_t1: forall x, x \in t1 -> x \in ai_elems aid.
  + by case: hx => [ [_ -> //] | [len [i [_ ->]]]] y /mem_take /mem_drop.
  have ht1 :
    List.Forall (fun x => vtype x = sword (ai_ty ais)) t1.
  + apply/List.Forall_forall => y /InP /sub_t1 hin.
    by rewrite (xi_ty (hwf _ _ hgetd)) // heqs.
  have huniqt1 : uniq t1.
  + have := el_uni (hwf _ _ hgetd).
    case: hx => [[_ ->] //| [? [? [_ -> ]]] ?].
    by apply/take_uniq/drop_uniq.
  have huniqt2 : uniq t2.
  + have := el_uni (hwf _ _ hgets).
    case: he => [[_ ->] //| [? [? [_ -> ]]] ?].
    by apply/take_uniq/drop_uniq.
  have [vm' [hsems heqe' hall2]] :
    exists vm',
      [/\ sem p2 ev (with_vm s1' vm) stores (with_vm s1' vm')
        , vm =[\sv_of_list id t1] vm'
        &  List.Forall2 (fun t1 t2 => vm'.[t1] = (evm s1').[t2]) t1 t2].
  + move: huniqt1; have : forall x, x \in t1 -> x \notin vs.
    + move=> y /sub_t1 hyt1; apply /negP=> /hnin hyvs.
      have := xi_in (hwf _ _ hgetd).
      by move=> /(_ _ hyt1); SvD.fsetdec.
    subst stores vs => {loads hseml hx he heqe huniq sub_t2 huniqt2 hsz2}.
    elim: t1 t2 vm hsz sub_t1 ht1 hnin hall1 ht2.
    + by move=> [] //= vm; exists vm; split => //; constructor.
    move=> x1 t1 hrec [] //= x2 t2 vm [hsz] sub_t1 /List.Forall_cons_iff [] tyx1 ht1 hnin.
    move=> /List.Forall2_cons_iff [] hx2 hall2 /List.Forall_cons_iff [] [] tyx2 [w2 hw2] ht2.
    move=> ht1vs /andP[] hx1t1 huniq.
    set i := MkI _ _.
    have hsemi : sem_I p2 ev (with_vm s1' vm) i (with_vm s1' (vm.[x1 <- (evm s1').[x2]])).
    + econstructor; econstructor.
      + by rewrite /= /get_gvar /= /get_var hx2 hw2 /=; eauto.
      + by rewrite /truncate_val /= heqs truncate_word_u /=; eauto.
      rewrite /=; apply write_varP; constructor => //.
      + by rewrite with_vm_idem /= hw2.
      by apply: subtype_truncatable; rewrite /= tyx1.
    case: (hrec t2 vm.[x1 <- (evm s1').[x2]]) => // {hrec}.
    + by move=> z hz; apply sub_t1; rewrite in_cons hz orbT.
    + by move=> z hz; apply hnin; rewrite in_cons hz orbT.
    + have := ht1vs x1 (mem_head _ _).
      rewrite notin_cons => /andP [] _.
      elim: (t2) hall2 => // x2' t2' hrec' /List.Forall2_cons_iff [hx2' hall2].
      rewrite /= notin_cons => /andP [] hx1 hnin'; constructor.
      + by rewrite Vm.setP_neq.
      by apply hrec'.
    + by move=> z hz; have := ht1vs z; rewrite in_cons hz orbT notin_cons => /(_ erefl) /andP [].
    move=> vm' [hsem2 heqe hall2'].
    exists vm'; split.
    + by apply: Eseq hsemi hsem2.
    + move=> z; rewrite sv_of_list_cons => hz.
      rewrite -heqe; last by SvD.fsetdec.
      by rewrite Vm.setP_neq //; apply/eqP; SvD.fsetdec.
    constructor => //; rewrite -heqe.
    + by rewrite Vm.setP_eq hw2 tyx1 /= cmp_le_refl orbT.
    move=> /sv_of_listP; rewrite map_id => h.
    by move: hx1t1; rewrite h.
  exists (with_vm s1' vm'); last by apply: sem_app hseml hsems.
  have xsty := x_ty (hwf _ _ hgets).
  have xdty := x_ty (hwf _ _ hgetd).
  have [[t ?] hint2] :
    (exists (t : WArray.array (Z.to_pos (arr_size (ai_ty ais) (Pos.of_nat (size t2))))), v' = Varr t) /\
    forall xi,
    xi \in t2 ->
    eval_array ais.(ai_ty) v' (zindex xi t2) = ok (evm s1').[xi].
  + case: he => [ [? ?] | [len [i [??]]] ]; subst t2 e.
    + move: hse => /= /get_varP /=; rewrite xsty /= => -[? _ /compat_valEl] [t hv]; subst v.
      move: htr; rewrite hv => /truncate_valE [??]; subst ty v'; split.
      + move: (t); rewrite (len_def (hwf _ _ hgets)).
        have -> : Z.to_pos (Z.of_nat (size (ai_elems ais))) = Pos.of_nat (size (ai_elems ais)).
        + by lia.
        by move=> t0; exists t0.
      by move=> xi; rewrite -hv; apply: (hget _ _ _ hgets).
    move: hse; apply: on_arr_varP; rewrite /= xsty => len1 t [?]; subst len1.
    move=> /get_varP [ht _ _]; t_xrbindP => t' hget_sub ?; subst v.
    move: htr => /truncate_valE [??]; subst ty v'.
    have [] := WArray.get_sub_bound hget_sub.
    rewrite /arr_size /mk_scale.
    move => h1 h2; have h3 := wsize_size_pos (ai_ty aid); have h4 := len_def (hwf _ _ hgets).
    rewrite -heqs in h2.
    split.
    + rewrite -heqs;
      have -> : Pos.of_nat (size (take (Pos.to_nat len) (drop (Z.to_nat i) (ai_elems ais)))) =
                len; last by eauto.
      rewrite size_take size_drop.
      case: ZNltP; first by rewrite Pos2Nat.id.
      rewrite /subn /subn_rec /=; nia.
    move=> xi hin.
    have h : xi \in (ai_elems ais).
    + by apply/mem_drop/mem_take/hin.
    have {h} <- := hget _ _ xi hgets h.
    rewrite /eval_array -ht; do 3!f_equal.
    move: t ht hget_sub; rewrite -heqs => t ht hget_sub.
    rewrite (WArray.get_sub_get hget_sub); last first.
    + rewrite /zindex; split; first by apply Zle_0_nat.
      rewrite -(Z2Nat.id (Zpos len)) //; apply/inj_lt/ltP => /=.
      by rewrite index_take //; apply index_ltn.
    rewrite /zindex.
    have := el_uni (hwf _ _ hgets).
    have {-2}<-:= cat_take_drop (Z.to_nat i) (ai_elems ais).
    rewrite index_cat cat_uniq => /and3P [_ /negP hhas _].
    have hin' : xi \in drop (Z.to_nat i) (ai_elems ais).
    + by apply: mem_take hin.
    case: ifPn => hin1.
    + by elim: hhas; apply/hasP; exists xi.
    rewrite index_take // Nat2Z.n2zD size_take /GRing.add /=; do 2!f_equal.
    case: ifPn.
    + move=> _; rewrite Z2Nat.id //; nia.
    move=> /ZNltP; rewrite Z2Nat.id; last nia.
    rewrite -(len_def (hwf _ _ hgets)); nia.
  subst v'; case: hx.
  + move=> [??]; subst x t1; move: hw => /write_varP [-> _ _].
    split => //; split => /=.
    + move=> z hz; rewrite Vm.setP_neq; last first.
      + by apply/eqP => ?; subst z; apply (x_nin (hwf _ _ hgetd)).
      rewrite hvm // heqe; last first.
      + by move=> /sv_of_listP; rewrite map_id => /hnin [_]; apply.
      apply heqe' => /sv_of_listP; rewrite map_id => /sub_t1 h.
      by have /(_ _ h) := xi_nin (hwf _ _ hgetd); apply.
    move=> x ai xi; rewrite Vm.setP; case: eqP => heqx.
    + subst x; rewrite hgetd => -[?] hxi; subst ai.
      rewrite vm_truncate_val_eq; last first.
      + have h := len_pos (hwf _ _ hgetd); rewrite /= xdty -hsz heqs /arr_size; f_equal.
        have ? /= := (len_def (hwf _ _ hgetd)); nia.
      have [h1 h2 h3]:= Forall2_zindex hall2 huniqt1 huniqt2 hxi.
      by rewrite h1 -h2 heqs znth_index // hint2.
    move=> hgx hxin; rewrite hget //.
    rewrite heqe; last first.
    + move=> /sv_of_listP; rewrite map_id => /hnin [+ _]; apply.
      by apply (xi_in (hwf _ _ hgx)).
    rewrite heqe' // => /sv_of_listP; rewrite map_id => h.
    by have /(_ xi) := xi_disj (hwf _ _ hgetd) heqx hgx; apply.
  move=> [len [i [??]]]; subst x t1.
  move: hw => /=; rewrite heqs.
  apply: on_arr_varP => n txd.
  rewrite xdty => -[?] hgetxd; subst n; t_xrbindP => t' ht'.
  have ? : len = Pos.of_nat (size t2).
  + have := WArray.cast_len ht'; rewrite /arr_size /=.
    have ? := wsize_size_pos (ai_ty ais); nia.
  subst len; move: ht'; rewrite WArray.castK => -[?]; subst t'.
  move=> t' hsub /write_varP [? _ _]; subst s2.
  split => //; split => /=.
  + move=> z hz; rewrite Vm.setP_neq; last first.
    + by apply/eqP => ?; subst z; apply (x_nin (hwf _ _ hgetd)).
    rewrite hvm // heqe; last first.
    + by move=> /sv_of_listP; rewrite map_id => /hnin [_]; apply.
    apply heqe' => /sv_of_listP; rewrite map_id => /sub_t1 h.
    by have /(_ _ h) := xi_nin (hwf _ _ hgetd); apply.
  move=> x ai xi; rewrite Vm.setP; case: eqP => heqx.
  + subst x; rewrite hgetd => -[?] hxi; subst ai.
    rewrite vm_truncate_val_eq; last by rewrite xdty.
    move: t t' htr hint2 txd hgetxd hsub; rewrite heqs => t t' htr hint2 txd hgetxd hsub.
    rewrite (eval_array_sub _ hsub).
    have := WArray.set_sub_bound hsub; rewrite /mk_scale => h_1.
    have h_2 := wsize_size_pos (ai_ty ais).
    case: ifPn.
    + move=> /andP [] /ZleP hii /ZltP hit2.
      have /(_ xi) [|]:= Forall2_zindex hall2 huniqt1 huniqt2.
      + have -> : Pos.to_nat (Pos.of_nat (size t2)) = Z.to_nat (Z.of_nat (size t2)) by lia.
        apply: zindex_take_drop => //; lia.
      set t1 := take _ (drop _ _) => -> h1 h2.
      have -> : (zindex xi (ai_elems aid) - i)%Z = zindex xi t1.
      + rewrite zindex_sub_uniq //; first by lia.
        + by apply: (el_uni (hwf _ _ hgetd)).
        by rewrite -/t1 -h1 hsz;apply/ZNltP; rewrite index_mem.
      by rewrite -h1 hint2 // znth_index.
    move=> /nandP hle.
    have := hget _ _ _ hgetd hxi.
    move: hgetxd; rewrite /get_var heqs; t_xrbindP => hdef <- ->; f_equal.
    rewrite heqe ?heqe' //; last first.
    + move=> /sv_of_listP; rewrite map_id => /hnin [+ _]; apply.
      by apply (xi_in (hwf _ _ hgetd)).
    move=> /sv_of_listP; rewrite map_id -index_mem => /ZNltP.
    set t1 := take _ (drop _ _) => h.
    have := zindex_sub_uniq (el_uni (hwf _ _ hgetd)) h; rewrite -/t1 => heq.
    case: hle => [/ZleP | /ZltP].
    + by have : (0 <= zindex xi t1)%Z; first rewrite /zindex; lia.
    apply.
    move: h; rewrite -/(zindex xi t1) heq hsz.
    have -> : Z.of_nat (Z.to_nat i) = i by lia.
    have -> : Z.of_nat (size t2) = Pos.of_nat (size t2) by lia.
    lia.
  move=> hgx hxin; rewrite hget //.
  rewrite heqe; last first.
  + move=> /sv_of_listP; rewrite map_id => /hnin [+ _]; apply.
    by apply (xi_in (hwf _ _ hgx)).
  rewrite heqe' // => /sv_of_listP; rewrite map_id.
  move=> /mem_take/mem_drop => h.
  by have /(_ xi) := xi_disj (hwf _ _ hgetd) heqx hgx; apply.
Qed.

Local Lemma Hopn : sem_Ind_opn p1 Pi_r.
Proof.
  move => s1 s2 t o xs es; rewrite /sem_sopn; t_xrbindP => vs ves hse ho hws.
  move=> ii m c s1' hwf heqa /=; t_xrbindP => xs' hxs es' hes <-.
  have := expand_esP hwf heqa hes hse.
  have := expand_lvsP hwf heqa hxs hws.
  rewrite -eq_globs => -[s2' [hws' ?]] hse'; exists s2' => //.
  by apply sem_seq_ir; constructor; rewrite /sem_sopn hse' /= ho.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p1 Pi_r.
Proof.
  move => s1 scs2 m2 s2 o xs es vs ves hse ho hws.
  move=> ii m c s1' hwf heqa /=; t_xrbindP => xs' hxs es' hes <-.
  have := expand_esP hwf heqa hes hse.
  have heqa': eq_alloc m (with_scs (with_mem s1 m2) scs2) (with_scs (with_mem s1' m2) scs2) by case: heqa.
  have := expand_lvsP hwf heqa' hxs hws.
  rewrite -eq_globs => -[s2' [hws' ?]] hse'; exists s2' => //.
  by apply sem_seq_ir; econstructor; eauto; rewrite -(eq_alloc_mem heqa) -(eq_alloc_scs heqa).
Qed.

Local Lemma Hassert : sem_Ind_assert p1 Pi_r.
Proof.
  move => s t p e b he ? m c2 s1' hwf heqa /=; t_xrbindP => e' he' <-.
  have := expand_eP hwf heqa he' he;rewrite -eq_globs => hse'.
  exists (add_contract s1' (t,b)) => //; subst.
  + by case: heqa => ??? h; split => //=; rewrite h.
  by apply/sem_seq_ir/Eassert.
Qed.

Local Lemma Hif_true : sem_Ind_if_true p1 ev Pc Pi_r.
Proof.
  move => s1 s2 e c1 c2 hse hs hrec ii m c s1' hwf heqa /=.
  t_xrbindP => e' he c1' hc1 c2' hc2 <-.
  have := expand_eP hwf heqa he hse; rewrite -eq_globs => hse'.
  have [s2' ??] := hrec _ _ _ hwf heqa hc1.
  by exists s2' => //; apply/sem_seq_ir/Eif_true.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p1 ev Pc Pi_r.
Proof.
  move => s1 s2 e c1 c2 hse hs hrec ii m c s1' hwf heqa /=.
  t_xrbindP => e' he c1' hc1 c2' hc2 <-.
  have := expand_eP hwf heqa he hse; rewrite -eq_globs => hse'.
  have [s2' ??] := hrec _ _ _ hwf heqa hc2.
  by exists s2' => //; apply/sem_seq_ir/Eif_false.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p1 ev Pc Pi_r.
Proof.
  move => s1 s2 s3 s4 a c1 e c2 _ hrec1 hse _ hrec2 _ hrecw ii m c s1' hwf heqa /=.
  t_xrbindP => e' he c1' hc1 c2' hc2 <-.
  have [sc1 heqa1 hs1]:= hrec1 _ _ _ hwf heqa hc1.
  have := expand_eP hwf heqa1 he hse; rewrite -eq_globs => hse'.
  have [sc2 heqa2 hs2]:= hrec2 _ _ _ hwf heqa1 hc2.
  have [| s2' ?] := hrecw ii m [::MkI ii (Cwhile a (flatten c1') e' (flatten c2'))] _ hwf heqa2.
  + by rewrite /= he hc1 hc2.
  move=> /sem_seq1_iff/sem_IE hsw.
  exists s2' => //; apply/sem_seq_ir;apply:Ewhile_true hsw; eauto.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p1 ev Pc Pi_r.
Proof.
  move => s1 s2 a c e c' _ hrec1 hse ii m ? s1' hwf heqa /=.
  t_xrbindP => e' he c1' hc1 c2' hc2 <-.
  have [s2' heqa1 hs1]:= hrec1 _ _ _ hwf heqa hc1.
  have := expand_eP hwf heqa1 he hse; rewrite -eq_globs => hse'.
  exists s2' => //; apply/sem_seq_ir/Ewhile_false; eauto.
Qed.

Local Lemma Hfor : sem_Ind_for p1 ev Pi_r Pfor.
Proof.
  move => s1 s2 i d lo hi c vlo vhi hslo hshi _ hfor ii m c2 s1' hwf heqa /=.
  t_xrbindP => hin lo' hlo hi' hhi c' hc <-.
  have := expand_eP hwf heqa hlo hslo.
  have := expand_eP hwf heqa hhi hshi; rewrite -eq_globs => hshi' hslo'.
  have [s2' ??]:= hfor _ _ _ hwf heqa hin hc.
  exists s2' => //; apply sem_seq_ir; econstructor; eauto.
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

Lemma wf_init_map ffi m finf : init_map ffi = ok (m, finf) -> wf_t m.
Proof.
  rewrite /init_map; t_xrbindP.
  set svars_ := sv_of_list _ _.
  pose wf_st :=
    fun (svm: Sv.t * Mvar.t array_info) =>
      [/\ wf_t {| svars := svars_; sarrs := svm.2; selem := svm.1|} &
          (forall  x ai xi,
             Mvar.get svm.2 x = Some ai ->
             xi \in (ai_elems ai) ->
             Sv.In xi svm.1)].
  suff : forall l svm svm', wf_st svm -> foldM (init_array_info svars_) svm l = ok svm' -> wf_st svm'.
  + move=> h svm' /h []; first by split => //=.
    by move=> ? _ <-.
  elim => /= [ ??? [<-] // | vi vis hrec svm svm' hwf].
  t_xrbindP => svm1 heq; apply: hrec.
  move: heq; rewrite /init_array_info.
  case: svm hwf => sv1 m1 hwf; t_xrbindP => /andP [] /Sv_memP hnin1 /Sv_memP hnin2 [sv2 len].
  set ty := sword _; t_xrbindP.
  set elems := [seq _ | id <- vi_n vi] => hfold.
  have :
    [/\ Sv.Equal sv2 (Sv.union (sv_of_list id elems) sv1),
        disjoint sv1 (sv_of_list id elems),
        disjoint svars_ (sv_of_list id elems),
        uniq elems &
        len = (0 + Z.of_nat (size elems))%Z].
  + elim: elems sv1 {hwf hnin1 hnin2} 0%Z hfold => /= [ | x elems hrec] sv1 z; t_xrbindP.
    + move => <- <-; split => //; last (by rewrite Z.add_0_r);
       by rewrite /sv_of_list /=; apply/disjointP; SvD.fsetdec.
    move=> _ /andP[] /Sv_memP hnin1 /Sv_memP hnin_ <- /hrec.
    move=> [heq /disjointP hdisj1 /disjointP hdisj_ huni ->]; split => //.
    + by rewrite sv_of_list_cons heq; SvD.fsetdec.
    + apply/disjointP => y ?; rewrite sv_of_list_cons.
      by have := hdisj1 y; SvD.fsetdec.
    + apply/disjointP => y ?; rewrite sv_of_list_cons.
      by have := hdisj_ y; SvD.fsetdec.
    + apply /andP; split => //; apply /negP => hin.
      by apply (hdisj1 x); [SvD.fsetdec | apply /sv_of_listP/map_f].
    have /= -> := Nat2Z.inj_succ (size elems); ring.
  move=> [heq /disjointP hdisj1 /disjointP hdisj_ huni hlen] /andP [] /ZltP h0len /eqP hty <-.
  case: hwf => /= hwf hget.
  split => /=.
  + move=> x ai /=; rewrite Mvar.setP; case: eqP.
    + move=> ? [<-]; subst x.
      constructor => //=.
      + by move=> xi hxi /hdisj_/sv_of_listP; rewrite map_id hxi.
      + by move=> xi; rewrite -(map_id elems) => /sv_of_listP; have := hdisj1 xi; SvD.fsetdec.
      + by move=> xi /mapP [id ? ->].
      move=> x' ai' xi /eqP ?; rewrite Mvar.setP_neq // => /hget -/(_ xi) h [].
      by rewrite -(map_id elems) => /sv_of_listP -/hdisj1 h1 /h.
    move=> hne /[dup] /hget h1 /hwf [/= ????? hnin ?? xi_disj]; constructor => //=.
    + by move=> ? /hnin; SvD.fsetdec.
    move=> x' ai' xi hxx'; rewrite Mvar.setP; case: eqP => [? | hne']; last by apply xi_disj.
    by move=> [<-] [] /= /h1 /hdisj1 h2; rewrite -(map_id elems) => /sv_of_listP.
  move=> x ai xi; rewrite Mvar.setP; case: eqP => [? | _].
  + by move=> [<-] /=; rewrite -(map_id elems) => /sv_of_listP; SvD.fsetdec.
  move=> h1 h2; have := hget _ _ _ h1 h2; SvD.fsetdec.
Qed.

Lemma eq_alloc_empty m scs mem tr :
  wf_t m ->
  eq_alloc_restr Sv.empty m
    {| escs := scs; emem := mem; evm := Vm.init; eassert := tr |}
    {| escs := scs; emem := mem; evm := Vm.init; eassert := tr |}.
Proof.
  move=> hwf; split => //; split => //=.
  move=> ??? hin; SvD.fsetdec.
Qed.

Lemma mapM2_dc_truncate_id tys vs vs':
  mapM2 ErrType dc_truncate_val tys vs' = ok vs -> vs' = vs.
Proof.
  by rewrite /dc_truncate_val /= => h; have := mapM2_Forall3 h; elim => // _ > [->] _ ->.
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

Local Lemma expand_vs_flatten
  S m (ins : seq (seq stype * seq var_i * option (wsize * Z))) fn ftyin fparams vargs vargs1 :
  wf_t m ->
  mapM2 E.length_mismatch (expand_tyv m (fn \notin entries) S) ftyin fparams = ok ins ->
  expand_vs [seq i.2 | i <- ins] vargs = ok vargs1 ->
  mapM2 ErrType dc_truncate_val (flatten [seq x.1.1 | x <- ins]) (flatten vargs1) = ok (flatten vargs1).
Proof.
  move=> hwf hparams.
  elim: (mapM2_Forall3 hparams) vargs vargs1.
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
Qed.

Lemma mapM_ext_ok (eT aT bT : Type) (f1 f2 : aT → result eT bT) (l : seq aT) bs :
  (forall a b , f1 a = ok b -> f2 a = ok b) ->
  mapM f1 l = ok bs -> mapM f2 l = ok bs.
Proof.
  move=> h; elim: l bs => //= a l hrec bs.
  by t_xrbindP => > /h -> /= > /hrec -> <-.
Qed.

Lemma wf_restr_map X m : wf_t m -> wf_t (restr_map X m).
Proof.
  move=> hwf x ai; rewrite /restr_map /=.
  rewrite Mvar.filter_mapP; case heq: Mvar.get => [ ai' | ] //=.
  case: ifP => // _ [<-]; have [???????? h]:= hwf _ _ heq; split => //=.
  move=> x' > hne; rewrite Mvar.filter_mapP.
  case heq': Mvar.get => [ai'' | ] //=; case: ifP => //.
  move=> _ [<-]; apply: h hne heq'.
Qed.

Lemma eq_alloc_restr_map X m s1 s2 :
  eq_alloc_restr X m s1 s2 ->
  eq_alloc (restr_map X m) s1 s2.
Proof.
  move=> [] [] ? h ???; split => //; split => // x ai xi.
  rewrite Mvar.filter_mapP; case heq: Mvar.get => [ai' | ] //=; case: ifP => //.
  move=> /Sv_memP hin [?]; subst ai'; apply: h hin heq.
Qed.

Instance eq_alloc_restr_morph :
  Proper (Sv.Equal ==> eq ==> eq ==> eq ==> iff) eq_alloc_restr.
Proof.
  move=> X1 X2 hX ?? -> ?? -> ?? ->; split => -[] [] ? h ???; split => //; split => //;
  move=> ??? hin; apply h; SvD.fsetdec.
Qed.

Local Lemma sem_pre_ok scs m1 fn ei eo vargs vargs1 v :
  Mf.get fsigs fn = Some (ei, eo) ->
  expand_vs ei vargs = ok vargs1 ->
  sem_pre p1 scs m1 fn vargs = ok v ->
  sem_pre p2 scs m1 fn (flatten vargs1) = ok v.
Proof.
  rewrite /sem_pre => hsig hexp.
  case Hget: get_fundef => [f | //].
  have [fd1 [fd2 [m [inout [-> hsigs /=]]]] {Hget}]:= all_checked Hget.
  rewrite /expand_fsig; t_xrbindP => -[m' finf].
  case: f => /= finfo fci ftyin fparams fbody ftyout fres fextra.
  set fd := {| f_info := finfo |} => hinit.
  t_xrbindP => insf hparams outsf hres ci' hci <- ??; subst m inout.
  t_xrbindP => c' _ <- /=.
  move: hci; rewrite /expand_ci; case: (fci); last by move=> [<-] [<-].
  move=> ci; t_xrbindP => z h1 /eqP heq1 /eqP heq2 z1 h2 /eqP heq3 /eqP heq4 pr' hpr' po' hpo' <-.
  move: hsigs; rewrite hsig /= => -[??]; subst ei eo.
  move=> vargs' Hca s1 Hw hpr.
  set (sempty := {| escs := scs; emem := m1; evm := Vm.init; eassert := [::] |}).
  have hwf := wf_init_map hinit.
  have heqae : eq_alloc_restr Sv.empty m' sempty sempty by apply eq_alloc_empty.
  have ?:= mapM2_dc_truncate_id Hca; subst vargs'.
  have := expand_returnsP_restr hwf heqae (expend_tyv_expand_return h1) Hw.
  rewrite -heq2 => /(_ _ hexp) [s1'].
  have -> := expand_vs_flatten hwf hparams hexp.
  rewrite map_comp -map_flatten -(write_vars_lvals false gd) /= => -> /= heqa1.
  pose X := sv_of_list v_var (f_iparams ci).
  have {}hwf := @wf_restr_map X _ hwf.
  rewrite Sv_union_empty in heqa1.
  have {}heqa1 := eq_alloc_restr_map heqa1.
  elim : (f_pre ci) (pr') v hpr' hpr => /=.
  + by move=> _ _ [<-] [<-].
  move=> a l hrec ? ? ; t_xrbindP.
  move=> > hexe <- > hpr' <- > hse hbool > hpr <- /=.
  have := expand_eP hwf heqa1 hexe hse.
  by rewrite -eq_globs => -> /=; rewrite hbool /= (hrec _ _ hpr' hpr).
Qed.

Local Lemma sem_post_ok scs m1 fn ei eo vargs vargs1 vres vres1 v :
  Mf.get fsigs fn = Some (ei, eo) ->
  expand_vs ei vargs = ok vargs1 ->
  expand_vs eo vres = ok vres1 ->
  sem_post p1 scs m1 fn vargs vres = ok v ->
  sem_post p2 scs m1 fn (flatten vargs1) (flatten vres1) = ok v.
Proof.
  rewrite /sem_post => hsig hexpa hexpr.
  case Hget: get_fundef => [f | //].
  have [fd1 [fd2 [m [inout [-> hsigs /=]]]] {Hget}]:= all_checked Hget.
  rewrite /expand_fsig; t_xrbindP => -[m' finf].
  case: f => /= finfo fci ftyin fparams fbody ftyout fres fextra.
  set fd := {| f_info := finfo |} => hinit.
  t_xrbindP => insf hparams outsf hres ci' hci <- ??. subst m inout.
  t_xrbindP => c' _ <- /=.
  move: hci; rewrite /expand_ci; case: (fci); last by move=> [<-] [<-].
  move=> ci; t_xrbindP => iins hiparams /eqP heqins1 /eqP heqins2 ires hires /eqP heqres1 /eqP heqres2.
  move=> pr' hpr' po' hpo' <-.
  move: hsigs; rewrite hsig /= => -[??]; subst ei eo.
  move=> vargs' Hca s1 Hw1 s2 Hw2 hpo.
  set (sempty := {| escs := scs; emem := m1; evm := Vm.init; eassert := [::] |}).
  have hwf := wf_init_map hinit.
  have heqae : eq_alloc_restr Sv.empty m' sempty sempty by apply eq_alloc_empty.
  have ?:= mapM2_dc_truncate_id Hca; subst vargs'.
  rewrite heqins2 in hexpa.
  have [s1'] := expand_returnsP_restr hwf heqae (expend_tyv_expand_return hiparams) Hw1 hexpa.
  rewrite heqins1.
  have -> := expand_vs_flatten hwf hiparams hexpa.
  rewrite map_comp -map_flatten -(write_vars_lvals false gd) /= => -> /= heqa1.
  have := expand_returnsP_restr hwf heqa1 (expend_tyv_expand_return hires) Hw2.
  rewrite -heqres2 => /(_ _ hexpr) [?].
  rewrite map_comp -map_flatten -(write_vars_lvals false gd) /= => -> /= heqa2.
  rewrite Sv_union_empty in heqa2.
  pose X := Sv.union (sv_of_list v_var (f_iparams ci)) (sv_of_list v_var (f_ires ci)).
  have {}hwf := @wf_restr_map X _ hwf.
  have {}heqa2 := eq_alloc_restr_map heqa2.
  elim : (f_post ci) (po') v hpo' hpo => /=.
  + by move=> _ _ [<-] [<-].
  move=> a l hrec ? ? ; t_xrbindP.
  move=> > hexe <- > hpo' <- > hse hbool > hpo <- /=.
  have := expand_eP hwf heqa2 hexe hse.
  by rewrite -eq_globs => -> /=; rewrite hbool /= (hrec _ _ hpo' hpo).
Qed.

Local Lemma Hcall : sem_Ind_call p1 ev Pi_r Pfun.
Proof.
  move=> s1 scs2 m2 s2 s3 xs fn args vargs vs vpr vpo tr Hes hpr Hsc Hfun Hw hpo -> ii m c2 s1' hwf heqa /=.
  case hgfn: Mf.get => [[ei eo]|//].
  t_xrbindP=> xs' sxs' hxs <- es' ses' hes <- <-.
  have [? heva]:= expand_paramsP hwf heqa hes Hes.
  have heqa': eq_alloc m (with_scs (with_mem s1 m2) scs2) (with_scs (with_mem s1' m2) scs2) by case: heqa.
  case: {Hfun}(Hfun ei eo hgfn _ heva) => ? hevr.
  have [s2' ]:= expand_returnsP hwf heqa' hxs Hw hevr.
  rewrite -eq_globs => ? heqa2 ??.
  exists (add_assumes (add_contracts (add_asserts s2' vpr) tr) vpo) => //.
  + by case: heqa2 => ??? h; split => //=; rewrite h.
  apply sem_seq_ir.
  econstructor; eauto => //.
  + by case: heqa => ? <- <- ?;apply: (sem_pre_ok hgfn) hpr.
  + by case: heqa => _ <- <-.
  by apply: (sem_post_ok hgfn) hpo.
Qed.

Definition ai_beq (ai1 ai2 : array_info) :=
  [&& ai_ty ai1 == ai_ty ai2, ai_len ai1 == ai_len ai2 & ai_elems ai1 == ai_elems ai2].

Lemma ai_eq_axiom : Equality.axiom ai_beq.
Proof.
  move=> [ty1 len1 el1] [ty2 len2 el2]; apply (equivP and3P); split => /=.
  + by move=> [/eqP -> /eqP -> /eqP ->].
  by move=> [] -> -> ->.
Qed.

HB.instance Definition _ := hasDecEq.Build array_info ai_eq_axiom.

Lemma fold_init_arrayP m P (XS: seq (var * array_info)) X c:
  wf_t m ->
  (forall x ai, (x, ai) \in XS -> Mvar.get m.(sarrs) x = Some ai) ->
  (forall x ai, Mvar.get m.(sarrs) x = Some ai -> (x, ai) \in XS \/ Sv.In x X) ->
  (forall s, exists vm,
     [/\ sem p2 ev s c (with_vm s vm)
       , (forall x ai xi,
            ~Sv.In x P -> Sv.In x X ->
            Mvar.get m.(sarrs) x = Some ai ->
            xi \in ai.(ai_elems) ->
            vm.[xi] = dfl_w (ai_ty ai))
       & (forall xi, (evm s).[xi] = vm.[xi] \/
            exists x ai, [/\ ~Sv.In x P, Sv.In x X, Mvar.get m.(sarrs) x = Some ai & xi \in ai.(ai_elems)])]) ->
  forall s, exists vm,
   [/\ sem p2 ev s (foldl (λ c (kv : var * array_info), init_array P kv.1 kv.2 c) c XS) (with_vm s vm)
     , (forall x ai xi,
          ~Sv.In x P ->
          Mvar.get m.(sarrs) x = Some ai ->
          xi \in ai.(ai_elems) ->
          vm.[xi] = dfl_w (ai_ty ai))
      & (forall xi, (evm s).[xi] = vm.[xi] \/
           exists x ai, [/\ ~Sv.In x P, Mvar.get m.(sarrs) x = Some ai & xi \in ai.(ai_elems)])].
Proof.
  move=> hwf.
  elim: XS X c => [ | [x ai] XS hrec] X c /= hai hX hs s.
  + have [vm [hsem hget hor]] := hs s; exists vm; split => //.
    + move=> x ai xi hP hin; apply: hget (hin) => //.
      by case: (hX _ _ hin).
    move=> xi; case: (hor xi); auto.
    by move=> [x [ai [h1 h2 h3 h4]]]; right; exists x, ai; split.
  apply: (hrec (Sv.add x X) (init_array P x ai c) _ _ _ s) => {hrec}.
  + by move=> x' ai' hin; apply hai; rewrite in_cons hin orbT.
  + by move=> x' ai' /hX; rewrite in_cons => -[ /orP [ /eqP [-> ->]| ? ]| ?];
        [|by left|]; right; SvD.fsetdec.
  move=> {}s.
  rewrite /init_array; case: Sv_memP => hxP.
  + have [vm [h1 h2 h3]]:= hs s; exists vm; split => //.
    + by move=> x' ai' xi hnin hin; apply (h2 x' ai' xi hnin); SvD.fsetdec.
    move=> xi; case: (h3 xi) => h; [by left | right].
    by case h => x' [ai' [????]]; exists x', ai'; split => //; SvD.fsetdec.
  have : exists vm1,
    [/\ sem p2 ev s
          ([seq MkI dummy_instr_info
                  (Cassgn {| v_var := x0; v_info := dummy_var_info |} AT_none (sword (ai_ty ai))
                     (wconst (wrepr (ai_ty ai) 0)))
              | x0 <- ai_elems ai]) (with_vm s vm1)
       & forall x,
          vm1.[x] = if x \in ai_elems ai then dfl_w (ai_ty ai) else (evm s).[x]].
  + have := hai x ai; rewrite in_cons eqxx /= => /(_ erefl) /hwf hwfai.
    elim: (ai_elems ai) s (xi_ty hwfai) => [ | xi xis hrec] s /=.
    + by move=> _; exists (evm s); rewrite with_vm_same; split => //; constructor.
    set i := (MkI _ _) => hty.
    have h1 : sem_I p2 ev s i (with_vm s (Vm.set (evm s) xi (dfl_w (ai_ty ai)))).
    + constructor; apply: Eassgn => /=.
      + rewrite /sem_sop1 /= wrepr_unsigned; reflexivity.
      + rewrite /truncate_val /= truncate_word_u /=; reflexivity.
      apply/write_varP; split => //=.
      by rewrite hty ?in_cons ?eqxx // cmp_le_refl orbT.
    have [|vm [h2 hvm]]:= hrec (with_vm s (evm s).[xi <- dfl_w (ai_ty ai)]).
    + by move=> ? h; apply hty; rewrite in_cons h orbT.
    exists vm; split.
    + by apply: Eseq h1 h2.
    move=> y; rewrite hvm in_cons Vm.setP eq_sym.
    case: eqP => [ ? | hne] //=.
    by rewrite hty ?in_cons ?eqxx // cmp_le_refl orbT; case: ifP.
  move=> [vm1 [hsem1 hvm1]].
  have [vm [hsem2 hdfl hvm]]:= hs (with_vm s vm1).
  have := hai x ai; rewrite in_cons eqxx => /(_ erefl) hgetx.
  exists vm; split.
  + by apply: sem_app hsem1 hsem2.
  + move=> x' ai' xi hnP.
    case: (x =P x');
     last by move=> hne hin hget; apply (hdfl x') => //; SvD.fsetdec.
    move=> ? _; subst x' => hget hxi.
    rewrite hgetx in hget; case: hget => ?; subst ai'.
    case: (hvm xi) => /=.
    + by move=> <-; rewrite hvm1 hxi.
    move=> [x' [ai' [hnP' hxX' hget' hxi']]].
    have := (hdfl _ _ _ hnP' hxX' hget' hxi').
    case (x =P x').
    + by move=> ?; subst x'; rewrite hgetx in hget'; case: hget' => <-.
    by move=> hne; have /(_ xi) := xi_disj (hwf _ _ hgetx) hne hget'; case.
  move=> xi; case (hvm xi).
  + move=> <- /=; rewrite hvm1; case: ifP; last by left.
    by move=> ?; right; exists x, ai; split => //; SvD.fsetdec.
  by move=> [x' [ai' [????]]]; right; exists x', ai'; split => //; SvD.fsetdec.
Qed.

Local Lemma Hproc : sem_Ind_proc p1 ev Pc Pfun.
Proof.
  move=> scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' vpr vpo tr Hget Hca [?] Hw hpr _ Hc Hres Hcr ?? hpo ?; subst s0 scs2 m2 tr.
  have [fd1 [fd2 [m [inout [Hget2 hsigs /=]]]] {Hget}]:= all_checked Hget.
  rewrite /expand_fsig; t_xrbindP => -[mt finf].
  case: f Hca Hw Hc Hres Hcr hpo => /=.
  move=> finfo fci ftyin fparams fbody ftyout fres fextra.
  set fd := {| f_info := finfo |} => Hca Hw Hc Hres Hcr hpo hinit.
  t_xrbindP => ins hparams outs hres ci hci <- ??; subst m inout.
  t_xrbindP => c hc ?; subst fd1.
  move=> expdin expdout; rewrite hsigs => -[??] vargs1 hexvs; subst expdin expdout.
  set (sempty := {| escs := scs1; emem := m1; evm := Vm.init; eassert := [::] |}).
  have hwf := wf_init_map hinit.
  have heqae : eq_alloc_restr Sv.empty mt sempty sempty by apply eq_alloc_empty.
  have [??]:= (mapM2_dc_truncate_id Hca, mapM2_dc_truncate_id Hcr); subst vargs' vres'.
  have [s1']:= expand_returnsP_restr hwf heqae (expend_tyv_expand_return hparams) Hw hexvs.
  rewrite map_comp -map_flatten -(write_vars_lvals false gd) Sv_union_empty => hw heqa1.
  have heqa1' : eq_alloc_restr (sv_of_list v_var fparams) mt (add_assumes s1 vpr) (add_assumes s1' vpr).
  + by case: heqa1 => ??? h; split => //=; rewrite h.
  set P := sv_of_list v_var fparams.
  have [] := @fold_init_arrayP mt P (Mvar.elements (sarrs mt)) Sv.empty [::] hwf _ _ _ (add_assumes s1' vpr).
  + by move=> ?? /Mvar.elementsP.
  + by move=> ?? h; left; apply/Mvar.elementsP.
  + move=> s; exists (evm s); rewrite with_vm_same; split.
    + by constructor.
    + by move=> x ai xi ??; SvD.fsetdec.
    by move=> xi; left.
  move=> vm; rewrite -Mvar.foldP => -[hsem hvm0 hvm].
  have heqa: eq_alloc mt (add_assumes s1 vpr) (with_vm (add_assumes s1' vpr) vm).
  + case heqa1' => -[/= h1 h2] ???; split => //; split => /=.
    + move=> xi hxi; rewrite h1 //.
      case: (hvm xi) => //= -[x [ai [hxP hget hxiin]]].
      by have [] := xi_nin (hwf _ _ hget) hxiin.
    move=> x ai xi hget hxi.
    case: (Sv_memP x (sv_of_list v_var fparams)) => hin.
    + rewrite (h2 _ _ _ hin hget hxi).
      case: (hvm xi) => /= [-> // | [x' [ai' [hnin hget' hai']]]].
      case: (x =P x') => heq.
      + by subst x'; elim hnin.
      by have /(_ xi) [] := xi_disj (hwf _ _ hget) heq hget'.
    rewrite /eval_array.
    rewrite (write_vars_lvals _ gd) in Hw.
    have /= <- := vrvsP Hw; last first.
    + move=> hin'; apply hin.
      elim: (fparams) hin' => //=.
      move=> y ys hrec; rewrite vrvs_cons sv_of_list_cons => /Sv.union_spec.
      by rewrite vrv_var => -[|/hrec]; SvD.fsetdec.
    rewrite Vm.initP (x_ty (hwf _ _ hget)) /=.
    rewrite /WArray.get readE.
    rewrite (hvm0 _ _ _ hin hget hxi).
    have : (ziota 0 (wsize_size (ai_ty ai))) <> [::].
    + move=> heq; have : size (ziota 0 (wsize_size (ai_ty ai))) = 0 by rewrite heq.
      by rewrite size_ziota; case (ai_ty ai).
    by case: ziota => // i i_s _ /=; rewrite WArray.get_empty; case: ifP => /=; case: is_align.
  have [s2' heqa2 hsemc] := Hc _ _ _ hwf heqa hc.
  rewrite -(sem_pexprs_get_var false gd) in Hres.
  have [vs' hex]:= expand_paramsP hwf heqa2 (expend_tyv_expand_param hres) Hres.
  rewrite map_comp -map_flatten sem_pexprs_get_var => hwr.
  exists vs' => //.
  econstructor; eauto => //=.
  + by apply: expand_vs_flatten hwf hparams hexvs.
  + by apply: (sem_pre_ok hsigs) hpr.
  + by apply: sem_app hsem hsemc.
  + by apply: expand_vs_flatten hwf hres hex.
  + by case heqa2. + by case heqa2.
  + by apply: (sem_post_ok hsigs) hpo.
  by case heqa2 => ??? ->.
Qed.

Lemma expand_callP_aux f scs mem scs' mem' va vr tr :
  sem_call p1 ev scs mem f va scs' mem' vr tr ->
  Pfun scs mem f va scs' mem' vr tr.
Proof.
  exact: (sem_call_Ind Hskip Hcons HmkI Hassgn Hopn Hsyscall Hassert
          Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
Qed.

End Step1.

Lemma expand_callP f scs mem scs' mem' va vr tr :
  sem_call p1 ev scs mem f va scs' mem' vr tr ->
  exists expdin expdout,
   ∀ (vargs' : seq (seq value)), expand_vs expdin va = ok vargs' ->
  exists2 vres' : seq (seq value),
     expand_vs expdout vr = ok vres' &
     sem_call p2 ev scs mem f (flatten vargs') scs' mem' (flatten vres') tr.
Proof.
  apply: (rbindP _ Hcomp) => s1 /[dup]Hs1/expand_callP_aux h _ /[dup]+/h{h}.
  move=> [???? {}f fd {}va va' ??? {}vr vr' vpr vpo tr' hgf htri _ _ _ _ _ htro _ _ _ _] h.
  suff : exists expdin expdout, Mf.get (fsigs s1) f = Some (expdin, expdout).
  + move=> [expdin [expdout hget1]].
    exists expdin, expdout.
    by apply h.
  move: Hs1 fd hgf {h htri htro}; rewrite {}/fsigs; elim: (p_funcs p1) s1
    => [> [<-]|[? [? ? fti fp ? fto fr]]> hrec] //=.
  t_xrbindP => ?? [? [expdin expdout]] + ?? /hrec{hrec}h ?; subst=> /=.
  case: eqP; last by move=> /nesym /eqP?; rewrite Mf.setP_neq //.
  move=> <- + fd' [] ? /=; subst fd'.
  rewrite Mf.setP_eq => _; eauto.
Qed.

End WITH_PARAMS.

End Tabstract.
