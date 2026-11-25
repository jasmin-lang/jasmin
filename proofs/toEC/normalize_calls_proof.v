From ITree Require Import ITree ITreeFacts.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import compiler_util psem psem_facts.
Require Import normalize_calls.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Section SYNTAX.

Context (fresh_var_ident : v_kind -> instr_info -> PrimInt63.int -> string -> atype -> Ident.ident).
Context (arrays_by_size : bool).

(* An auxiliary variable and a destination that fits hold values of the same
   type as the output. *)
Lemma aux_type_eval ty : eval_atype (aux_type arrays_by_size ty) = eval_atype ty.
Proof.
  rewrite /aux_type; case: arrays_by_size ty => // -[] //= ws len.
  by rewrite (arr_sizeE U8) Z.mul_1_l.
Qed.

Lemma fits_eval ty ty' : fits arrays_by_size ty ty' -> eval_atype ty = eval_atype ty'.
Proof. by rewrite /fits; case: arrays_by_size => [/convertible_eval_atype | /eqP ->]. Qed.

Section FUNDEF.

Context (fii : instr_info) (X : Sv.t).

Lemma fresh_auxP ii acc ty acc' x :
  fresh_aux fresh_var_ident arrays_by_size fii X ii acc ty = ok (acc', x) ->
  [/\ vtype x = aux_type arrays_by_size ty, ~ Sv.In x X, ~ Sv.In x acc & acc' = Sv.add x acc].
Proof.
  rewrite /fresh_aux; set y := {| vtype := _; vname := _ |}.
  t_xrbindP => /Sv_memP hx <- <-.
  rewrite /=; split => //; clearbody y; SvD.fsetdec.
Qed.

Lemma flag_destP lv ty x :
  flag_dest lv ty = Some x -> [/\ lv = Lvar x, vtype x = abool & ty = abool].
Proof.
  case: lv => //= y; case: andP => // -[/eqP h1 /eqP h2] [<-]; done.
Qed.

Lemma flag_varsP x lvs touts :
  Sv.In x (flag_vars lvs touts) -> Sv.In x (vrvs lvs) /\ vtype x = abool.
Proof.
  elim: lvs touts => [|lv lvs ih] [|ty touts] /=; try SvD.fsetdec.
  rewrite vrvs_cons; case h: flag_dest => [y|] /=.
  2: by move=> /ih [] ??; split => //; SvD.fsetdec.
  case: (flag_destP h) => -> hy _ /SvD.F.add_iff [<- | /ih [] ??].
  all: by split => //; rewrite vrv_var; SvD.fsetdec.
Qed.

Context {asm_op : Type} {asmop : asmOp asm_op}.

(* The new destinations write flags of the original ones, or variables that
   are fresh. *)
Lemma nc_dests_vrvs ii tg acc lvs touts acc' xs c :
  nc_dests fresh_var_ident arrays_by_size fii X ii tg acc lvs touts = ok (acc', xs, c) ->
  Sv.Subset acc acc' /\
  forall y, Sv.In y (vrvs xs) ->
    Sv.In y (flag_vars lvs touts) \/ (~ Sv.In y X /\ ~ Sv.In y acc).
Proof.
  elim: lvs touts acc acc' xs c => [|lv lvs ih] [|ty touts] acc acc' xs c /=.
  1-3: by move=> [<- <- _]; split => // y; rewrite /vrvs /=; SvD.fsetdec.
  case h: flag_dest => [x|].
  + t_xrbindP => -[[acc2 xs2] c2] /ih /= [hs hy] [<- <- _].
    split => // y; case: (flag_destP h) => -> _ _; rewrite vrvs_cons vrv_var => hin.
    case: (SvP.MP.Dec.F.union_1 hin) => [/SvD.F.singleton_1 -> | /hy [? | ?]];
      [left | left | right]; SvD.fsetdec.
  t_xrbindP => -[acc1 a] /fresh_auxP [_ ha1 ha2 ->].
  t_xrbindP => -[[acc2 xs2] c2] /ih /= [hs hy] [<- <- _].
  split; first SvD.fsetdec.
  move=> y; rewrite vrvs_cons vrv_var => hin.
  case: (SvP.MP.Dec.F.union_1 hin) => [/SvD.F.singleton_1 <- | /hy]; first by right.
  by case=> [? | ?]; [left | right]; SvD.fsetdec.
Qed.

Lemma nc_dests_lvars ii tg acc lvs touts acc' xs c :
  nc_dests fresh_var_ident arrays_by_size fii X ii tg acc lvs touts = ok (acc', xs, c) ->
  exists ys, mapM get_lvar xs = ok ys.
Proof.
  elim: lvs touts acc acc' xs c => [|lv lvs ih] [|ty touts] acc acc' xs c /=.
  1-3: by move=> [_ <- _]; exists [::].
  case h: flag_dest => [x|].
  + case: (flag_destP h) => ? _ _; subst lv.
    t_xrbindP => -[[acc2 xs2] c2] /ih [ys hys] [_ <- _].
    by exists (v_var x :: ys); rewrite /= hys.
  t_xrbindP => -[acc1 a] _; t_xrbindP => -[[acc2 xs2] c2] /ih [ys hys] [_ <- _].
  by exists (v_var a :: ys); rewrite /= hys.
Qed.

End FUNDEF.

End SYNTAX.

Section PROOF.

#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {wa : WithAssert}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Lemma write_var_rel (x y : var_i) v (t s t' : estate) :
  vtype x = vtype y ->
  write_var (wdb := true) x v t = ok t' ->
  exists2 s', write_var (wdb := true) y v s = ok s' &
    [/\ escs t' = escs t /\ emem t' = emem t, escs s' = escs s /\ emem s' = emem s,
        (evm t').[x] = (evm s').[y],
        evm s' = (evm s).[y <- v]
      & type_of_val v <> cbool -> vtype x <> abool].
Proof.
  move=> hty; rewrite /write_var /set_var; t_xrbindP.
  move=> _ hdb htr <- <-; rewrite hdb -hty htr /=; eexists; first reflexivity.
  split => //=.
  + by rewrite !Vm.setP_eq hty.
  by move=> hv hx; apply hv; move: htr; rewrite hx => /truncatable_bool.
Qed.

Lemma truncate_val_of_val ty v w :
  truncate_val ty v = ok w -> of_val ty w = of_val ty v.
Proof. by rewrite /truncate_val; t_xrbindP => x hx <-; rewrite of_val_to_val hx. Qed.

(* A variable that is not a flag receives the same value from [v] and from
   its truncation. *)
Lemma truncate_val_set ty v w :
  truncate_val ty v = ok w -> type_of_val v <> cbool ->
  [/\ DB (wdb := true) v, truncatable (wdb := true) ty v
    & vm_truncate_val ty v = vm_truncate_val ty w].
Proof.
  move=> htr hv; case: ty htr => [||len|ws] /truncate_val_typeE.
  + by move=> [b ? _]; subst v.
  + by move=> [i -> ->].
  + by move=> [a -> ->]; split => //; apply truncatable_arr.
  move=> [w0 [ws' [w' [htw -> ->]]]].
  have [-> -> -> _] := to_word_vm_truncate_val true erefl (htw : to_word ws (Vword w') = ok w0).
  by rewrite vm_truncate_val_eq.
Qed.

(* A copy, which writes the truncation of [v] to the type of the destination,
   writes the destination as the original instruction does. A destination
   that is not a flag receives a value that is not a boolean. *)
Lemma copy_writeP gd lv v w (t s t' : estate) :
  escs t = escs s -> emem t = emem s ->
  type_of_val v <> cbool ->
  (forall z, Sv.In z (read_rv lv) -> (evm t).[z] = (evm s).[z]) ->
  truncate_val (eval_atype (ty_lval lv)) v = ok w ->
  write_lval (wdb := true) gd lv w t = ok t' ->
  exists2 s', write_lval (wdb := true) gd lv v s = ok s' &
    [/\ escs t' = escs s', emem t' = emem s'
      & forall y, Sv.In y (vrv lv) -> vtype y <> abool /\ (evm t').[y] = (evm s').[y]].
Proof using sip wa.
  move=> hscs hmem hv hr htr.
  have hre : forall e, Sv.Subset (read_e e) (read_rv lv) ->
    sem_pexpr (wdb := true) gd t e = sem_pexpr (wdb := true) gd s e.
  + by move=> e hsub; apply: eq_on_sem_pexpr => // z hz; apply hr; SvD.fsetdec.
  case: lv hr hre htr => /=.
  + move=> _ ty _ _ /truncate_val_set /(_ hv) [hdb htr _]; rewrite /write_none hdb htr /=.
    t_xrbindP => _ _ <-; exists s => //; split => // y; SvD.fsetdec.
  + move=> x _ _ /truncate_val_set /(_ hv) [hdb htr hvw] /write_varP [-> _ _].
    have hx : vtype x <> abool.
    + by move=> hx; apply hv; move: htr; rewrite hx => /truncatable_bool.
    rewrite write_var_truncate //; eexists; first reflexivity.
    split => //= y /SvD.F.add_iff [<- | ]; last SvD.fsetdec.
    by split => //; rewrite !Vm.setP_eq hvw.
  + move=> al ws _ e _ hre /truncate_val_of_val /= ->.
    rewrite hre // hmem; t_xrbindP => pe ve -> /= -> /= w1 -> /= m -> <- /=.
    by eexists; first reflexivity; split => // y; rewrite /vrv /=; SvD.fsetdec.
  (* An array cell and a sub-array are written alike. *)
  all: move=> ??? x e hr hre /truncate_val_of_val /= heq.
  all: apply: on_arr_varP => n a htyx hget.
  all: have hx : Sv.In x (read_e_rec (Sv.add x Sv.empty) e) by rewrite read_eE; SvD.fsetdec.
  all: have hget' : get_var (wdb := true) (evm s) x = ok (Varr a)
         by move: hget; rewrite /get_var (hr x hx).
  all: have he : Sv.Subset (read_e e) (read_e_rec (Sv.add x Sv.empty) e)
         by rewrite read_eE; SvD.fsetdec.
  all: rewrite hget' /= heq; t_xrbindP => i vi hvi hi w1 hw a' ha' hwr.
  all: rewrite (hre _ he) in hvi; rewrite hvi /= hi /= hw /= ha' /=.
  all: case: (write_var_rel s erefl hwr) => s' -> [[h1 h2] [h3 h4] hx' _ hb].
  all: eexists; first reflexivity.
  all: split; [by rewrite h1 h3 | by rewrite h2 h4 | ].
  all: move=> y /SvD.F.add_iff [<- | ]; last SvD.fsetdec.
  all: by split => //; apply hb.
Qed.

Context (fresh_var_ident : v_kind -> instr_info -> PrimInt63.int -> string -> atype -> Ident.ident).
Context (arrays_by_size : bool).
Context (p' : prog) (ev : extra_val_t).

(* The invariant of the copies: [U] is the target state before the copy of
   the first destination of [lvs], [S] the source state before writing it,
   [TF] the target state after the instruction. A flag that a remaining
   position writes holds its final value already. *)
Definition nc_inv (X : Sv.t) (lvs : lvals) (touts : seq atype) (TF U S : estate) :=
  [/\ escs U = escs S /\ emem U = emem S,
      (forall z, Sv.In z X -> ~ Sv.In z (flag_vars lvs touts) ->
         (evm U).[z] = (evm S).[z]),
      (forall a, ~ Sv.In a X -> (evm U).[a] = (evm TF).[a])
    & (forall z, Sv.In z (flag_vars lvs touts) -> (evm U).[z] = (evm TF).[z])].

Lemma nc_destsP fii ii X tg (TF : estate) lvs touts acc acc' xs c vs (W U S U' : estate) :
  nc_dests fresh_var_ident arrays_by_size fii X ii tg acc lvs touts = ok (acc', xs, c) ->
  Sv.Subset (vars_lvals lvs) X ->
  flags_ok lvs touts ->
  List.map type_of_val vs = map eval_atype touts ->
  dests_match arrays_by_size lvs touts ->
  write_lvals (wdb := true) (p_globs p') W xs vs = ok TF ->
  esem p' ev c U = ok U' ->
  nc_inv X lvs touts TF U S ->
  exists2 S', write_lvals (wdb := true) (p_globs p') S lvs vs = ok S' & st_eq_on X U' S'.
Proof.
  elim: lvs touts acc acc' xs c vs W U S =>
    [|lv lvs ih] [|ty touts] acc acc' xs c vs W U S /=.
  2,3: by move=> _ _ _ _ hf; exfalso; apply: notF hf.
  + move=> [_ <- <-] _ _; case: vs => [|//] _ _ _ [<-] [[h1 h2] h3 _ _]; exists S => //.
    by split => // z hz; apply: h3 hz _; SvD.fsetdec.
  move=> hnc hsub /andP [hok hoks]; case: vs => [|v vs] //= [htv htys] /andP [hm hms] hW hc.
  move=> [[h1 h2] h3 h4 h5].
  have [hlv hsub'] : Sv.Subset (Sv.union (read_rv lv) (vrv lv)) X /\ Sv.Subset (vars_lvals lvs) X.
  + by move: hsub; rewrite /vars_lvals read_rvs_cons vrvs_cons; split; SvD.fsetdec.
  have hflX : forall y, Sv.In y (flag_vars lvs touts) -> Sv.In y X.
  + by move=> y /flag_varsP [hy _]; move: hsub'; rewrite /vars_lvals; SvD.fsetdec.
  move: hnc hok h3 h5; case hf: flag_dest => [x|] /= hnc hok h3 h5; rewrite hf in h3 h5.
  + case: (flag_destP hf) => ? _ ?; subst lv ty.
    have hxX : Sv.In x X by move: hlv; rewrite vrv_var; SvD.fsetdec.
    move: hnc; t_xrbindP => -[[acc2 xs2] c2] hnc [_ ? ?]; subst xs c.
    move: hW => /=; t_xrbindP => W1 hW1 hW'.
    have [S1 hS1 [_ [hS1a hS1b] hraw hvmS1 _]] := write_var_rel (y := x) S erefl hW1.
    rewrite hS1 /=.
    have [_ hvrs] := nc_dests_vrvs hnc.
    have hxl : ~ Sv.In x (flag_vars lvs touts) by move/Sv_memP: hok.
    have hxTF : (evm W1).[x] = (evm TF).[x].
    + by apply: (vrvsP hW') => /hvrs [ | []].
    apply: (ih touts _ _ _ _ vs W1 U S1 hnc hsub' hoks htys hms hW' hc).
    split.
    + by rewrite hS1a hS1b.
    + move=> z hz hzl; case: (v_var x =P z) => [<- | hne].
      + by rewrite h5 -?hraw ?hxTF //; SvD.fsetdec.
      rewrite hvmS1 Vm.setP_neq; last by apply/eqP.
      by apply h3 => //; SvD.fsetdec.
    + done.
    by move=> z hz; apply h5; SvD.fsetdec.
  move: hnc; t_xrbindP => -[acc1 a] /fresh_auxP [hta haX _ ->].
  t_xrbindP => -[[acc2 xs2] c2] hnc [_ ? ?]; subst xs c.
  move: hW => /=; t_xrbindP => W1 hW1 hW'.
  have [_ hvrs] := nc_dests_vrvs hnc.
  have haTF : (evm W1).[a] = (evm TF).[a].
  + by apply: (vrvsP hW') => /hvrs [/hflX // | [_ /=]]; SvD.fsetdec.
  have [[vi [ty' ?]] | [hnn {}hc]] : (exists vi ty', lv = Lnone vi ty') \/
    ((forall vi ty', lv <> Lnone vi ty') /\
     esem p' ev (MkI ii (Cassgn lv tg (ty_lval lv) (Plvar a)) :: c2) U = ok U').
  + by case: (lv) hc; eauto; right.
  + subst lv; move: hm => /fits_eval hm.
    move: hW1 => /=; rewrite /write_var /set_var; t_xrbindP => vm1 hdb htr _ _.
    rewrite /= /write_none hm -(aux_type_eval arrays_by_size ty) -hta htr hdb /=.
    by apply: (ih touts _ _ _ _ vs W1 U S hnc hsub' hoks htys hms hW' hc); split.
  move: hc => /=; t_xrbindP => U1 hU1 hc.
  move: hU1; rewrite /sem_assgn; t_xrbindP => w0 hw0 w htr hwr.
  move: hW1 => /=; rewrite /write_var /set_var; t_xrbindP => vm1 _ _ ? ?; subst vm1 W1.
  have hUa : (evm U).[a] = v.
  + by rewrite (h4 _ haX) -haTF /= Vm.setP_eq vm_truncate_val_eq // hta aux_type_eval.
  move: hw0 => /=; rewrite /get_gvar /= /get_var hUa; t_xrbindP => _ ?; subst w0.
  (* the copy of a destination that is not a flag does not receive a boolean *)
  have hvb : type_of_val v <> cbool.
  + move=> hb; move: (truncate_val_subctype htr); rewrite hb => /subctypeE.
    have hty : ty = abool by move: htv; rewrite hb; case: (ty).
    case: (lv) hnn hf => //= [?? h | x _]; first by case: (h _ _ erefl).
    by rewrite hty eqxx andbT; case: (vtype x).
  have hrd : forall z, Sv.In z (read_rv lv) -> (evm U).[z] = (evm S).[z].
  + by move=> z hz; apply: h3; [SvD.fsetdec | apply: (disjointP _ _ hok) hz].
  have [S1 hS1 [hsc hme hy]] := copy_writeP h1 h2 hvb hrd htr hwr.
  rewrite hS1 /=.
  apply: (ih touts _ _ _ _ vs _ U1 S1 hnc hsub' hoks htys hms hW' hc).
  have hU1 := vrvP hwr; have hS1' := vrvP hS1.
  split => //.
  + move=> z hz hzl; case: (Sv_memP z (vrv lv)) => hzv; first by case: (hy _ hzv).
    by rewrite -hU1 // -hS1' //; apply h3.
  + by move=> b hb; rewrite -hU1 ?h4 //; SvD.fsetdec.
  move=> z hz; rewrite -hU1 ?h5 // => /hy [] hzb _; apply: hzb; exact: (flag_varsP hz).2.
Qed.

Lemma nc_inv_init fii ii X tg lvs touts acc acc' xs c vs (W S TF : estate) :
  nc_dests fresh_var_ident arrays_by_size fii X ii tg acc lvs touts = ok (acc', xs, c) ->
  st_eq_on X W S ->
  write_lvals (wdb := true) (p_globs p') W xs vs = ok TF ->
  nc_inv X lvs touts TF TF S.
Proof using wa.
  move=> hnc [hsc hme hX] hW.
  have [_ hvrs] := nc_dests_vrvs hnc.
  have [ys hys] := nc_dests_lvars hnc.
  have hsc' := write_lvals_escs hW; have hme' := write_lvals_emem hys hW.
  split => //; first by rewrite hsc' hme'.
  move=> z hz hzl; rewrite -(vrvsP hW); first by apply hX.
  by move=> /hvrs [ | []].
Qed.

Context (p : prog).
Hypothesis Hp : normalize_calls_prog fresh_var_ident arrays_by_size p = ok p'.

Lemma normalize_calls_fd_inv f f' :
  normalize_calls_fd fresh_var_ident arrays_by_size p f = ok f' ->
  [/\ f_info f = f_info f', f_contract f = f_contract f', f_tyin f = f_tyin f',
      f_params f = f_params f', f_tyout f = f_tyout f', f_res f = f_res f'
    & f_extra f = f_extra f'].
Proof. by rewrite /normalize_calls_fd; t_xrbindP => ?? <-. Qed.

Lemma normalize_calls_prog_inv :
  [/\ map_cfprog (normalize_calls_fd fresh_var_ident arrays_by_size p) (p_funcs p) = ok (p_funcs p'),
      p_globs p' = p_globs p
    & p_extra p' = p_extra p].
Proof using Hp. by apply: rbindP Hp => ?? [<-]. Qed.

Lemma eq_globs : p_globs p' = p_globs p.
Proof using Hp. by case: normalize_calls_prog_inv. Qed.

Lemma normalize_calls_get_fundef fn :
  if get_fundef (p_funcs p) fn is Some fd then
    exists2 fd', normalize_calls_fd fresh_var_ident arrays_by_size p fd = ok fd'
               & get_fundef (p_funcs p') fn = Some fd'
  else get_fundef (p_funcs p') fn = None.
Proof using Hp.
  apply: get_map_cfprog_name_gen_aux.
  by case: normalize_calls_prog_inv => H _ _; exact H.
Qed.

Lemma normalize_calls_sem_pre fn fs :
  sem_pre p' fn fs = ok tt -> sem_pre p fn fs = ok tt.
Proof using Hp.
  rewrite /sem_pre eq_globs.
  move: (normalize_calls_get_fundef fn).
  case: get_fundef => [fd [fd' H1 ->]| -> //].
  by case: (normalize_calls_fd_inv H1) => _ -> ->.
Qed.

Lemma normalize_calls_sem_post fn vs fr :
  sem_post p' fn vs fr = ok tt -> sem_post p fn vs fr = ok tt.
Proof using Hp.
  rewrite /sem_post eq_globs.
  move: (normalize_calls_get_fundef fn).
  case: get_fundef => [fd [fd' H1 ->]| -> //].
  by case: (normalize_calls_fd_inv H1) => _ -> ->.
Qed.

(* The results of a call have the types of the outputs of the callee. *)
Definition results_typed (fn : funname) (fr : fstate) :=
  forall fd, get_fundef (p_funcs p) fn = Some fd ->
    List.map type_of_val (fvals fr) = map eval_atype (f_tyout fd).

Definition nc_spec : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 => fn1 = fn2 /\ fs1 = fs2
   ; rpostF_ := fun fn1 fn2 fs1 fs2 fr1 fr2 => fr1 = fr2 /\ results_typed fn2 fr2 |}.

#[local] Lemma checker_st_eq_onP' : Checker_eq p' p checker_st_eq_on.
Proof using Hp. by apply checker_st_eq_onP; rewrite eq_globs. Qed.
#[local] Lemma checker_a_st_eq_onP' : Checker_a_eq p' p checker_a_st_eq_on.
Proof using Hp. by apply checker_a_st_eq_onP; rewrite eq_globs. Qed.

#[local] Hint Resolve checker_st_eq_onP' checker_a_st_eq_onP' : core.

(* The rewriting of the destinations of an instruction: [W] and [S] are the
   states in which its outputs are written. *)
Lemma normalize_destsP fii ii X tg lvs touts xs post vs (W S TF U' : estate) :
  normalize_dests fresh_var_ident arrays_by_size fii X ii tg lvs touts = ok (xs, post) ->
  Sv.Subset (vars_lvals lvs) X ->
  List.map type_of_val vs = map eval_atype touts ->
  st_eq_on X W S ->
  write_lvals (wdb := true) (p_globs p) W xs vs = ok TF ->
  esem p' ev post TF = ok U' ->
  exists2 S', write_lvals (wdb := true) (p_globs p) S lvs vs = ok S' & st_eq_on X U' S'.
Proof using Hp.
  move=> hnd hsub htys hWS hW hpost.
  move: hnd; rewrite /normalize_dests; case: ifP => hneed.
  + t_xrbindP => hok; t_xrbindP => -[[acc2 xs2] post2] hnc [? ?]; subst xs2 post2.
    rewrite -eq_globs in hW *.
    apply: (nc_destsP hnc hsub hok htys _ hW hpost (nc_inv_init hnc hWS hW)).
    by case/andP: hneed.
  move=> [? ?]; subst xs post; move: hpost => [?]; subst U'.
  case: hWS => hW1 hW2 hWS.
  have [|vm2 hS' heq] := write_lvals_eq_on _ hW hWS.
  + by move: hsub; rewrite /vars_lvals; SvD.fsetdec.
  have hWS' : with_vm W (evm S) = S.
  + by move: hW1 hW2; clear; case: W S => ??? [???] /= <- <-.
  rewrite hWS' in hS'.
  exists (with_vm TF vm2) => //; split => //=.
  by apply: eq_onI heq; SvD.fsetdec.
Qed.

Lemma nc_dests_basic fii ii X tg acc lvs touts acc' xs c :
  nc_dests fresh_var_ident arrays_by_size fii X ii tg acc lvs touts = ok (acc', xs, c) -> all basic_i c.
Proof.
  elim: lvs touts acc acc' xs c => [|lv lvs ih] [|ty touts] acc acc' xs c /=.
  1-3: by move=> [_ _ <-].
  case: flag_dest => [x|].
  + by t_xrbindP => -[[acc2 xs2] c2] /ih hb [_ _ <-].
  t_xrbindP => -[acc1 a] _; t_xrbindP => -[[acc2 xs2] c2] /ih hb [_ _ <-].
  by case: (lv).
Qed.

Lemma normalize_dests_basic fii ii X tg lvs touts xs post :
  normalize_dests fresh_var_ident arrays_by_size fii X ii tg lvs touts = ok (xs, post) ->
  all basic_i post.
Proof.
  rewrite /normalize_dests; case: ifP => _; last by move=> [_ <-].
  by t_xrbindP => _; t_xrbindP => -[[acc2 xs2] post2] /nc_dests_basic hb [_ <-].
Qed.

Context {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Lemma nc_call X ii xs1 xs2 f es c1 (Q : rel_c) :
  all basic_i c1 ->
  Sv.Subset (read_es es) X ->
  (forall fr t s t', st_eq_on X t s -> results_typed f fr ->
     (Let t1 := upd_estate (wdb := true) (p_globs p') xs1 fr t in esem p' ev c1 t1) = ok t' ->
     exists2 s', upd_estate (wdb := true) (p_globs p) xs2 fr s = ok s' & Q t' s') ->
  wequiv_rec p' p ev ev nc_spec (st_eq_on X)
    (MkI ii (Ccall xs1 f es) :: c1) [:: MkI ii (Ccall xs2 f es)] Q.
Proof using Hp.
  move=> hb hes hpost' t s hRts.
  have [h1 h2 h3] := hRts.
  rewrite /isem_cmd_ /= bind_ret_r.
  rewrite bind_bind /isem_pexprs eq_globs.
  have hes' : evm t =[read_es es] evm s by apply: eq_onI h3.
  rewrite (eq_on_sem_pexprs (s := t) (s' := s) _ _ h2 hes').
  case: sem_pexprs => [vs | e].
  2: rewrite /iresult bind_throw; apply xrutt.xrutt_CutL => //.
  2: by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite !bind_ret_l bind_bind /isem_pre.
  have hfs : mk_fstate vs t = mk_fstate vs s by rewrite /mk_fstate h1 h2.
  rewrite hfs.
  case hpre: (sem_pre p' f (mk_fstate vs s)) => [[] | e].
  2: rewrite /iresult bind_throw; apply xrutt.xrutt_CutL => //.
  2: by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite (normalize_calls_sem_pre hpre) !bind_ret_l bind_bind.
  apply xrutt_facts.xrutt_bind with (rpostF (eS := nc_spec) f f (mk_fstate vs s) (mk_fstate vs s)).
  + by apply (wequiv_fun_rec (p1 := p') (p2 := p) (ev1 := ev) (ev2 := ev)).
  move=> fr _ [<- htyped] /=; rewrite /isem_post.
  case hpost: (sem_post p' f vs fr) => [[] | e].
  2: rewrite bind_bind /iresult bind_throw; apply xrutt.xrutt_CutL => //.
  2: by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite (normalize_calls_sem_post hpost) !bind_ret_l.
  have hpo := hpost' fr t s; rewrite eq_globs in hpo.
  case hup: upd_estate => [t1 | e].
  2: rewrite /iresult bind_throw; apply xrutt.xrutt_CutL => //.
  2: by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite bind_ret_l -/(isem_cmd_ p' ev c1 t1).
  rewrite hup /= in hpo.
  rewrite (esem_basicP _ _ _ hb); case hc1: esem => [t' | e] /=.
  + by have [s' -> hQ] := hpo t' hRts htyped hc1; apply xrutt.xrutt_Ret.
  apply xrutt.xrutt_CutL => //.
  by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
Qed.

Let Pi (i : instr) :=
  forall fii X c', Sv.Subset (vars_I i) X ->
  normalize_calls_i fresh_var_ident arrays_by_size p fii X i = ok c' ->
  wequiv_rec p' p ev ev nc_spec (st_eq_on X) c' [:: i] (st_eq_on X).

Let Pi_r (ir : instr_r) := forall ii, Pi (MkI ii ir).

Let Pc (c : cmd) :=
  forall fii X c', Sv.Subset (vars_c c) X ->
  normalize_calls_c (normalize_calls_i fresh_var_ident arrays_by_size p fii X) c = ok c' ->
  wequiv_rec p' p ev ev nc_spec (st_eq_on X) c' c (st_eq_on X).

Lemma normalize_calls_body : forall c, Pc c.
Proof using Hp.
  apply (cmd_rect (Pr := Pi_r) (Pi := Pi)).
  + done.
  + by move=> fii X c' _ [<-]; apply wequiv_nil.
  + move=> i c Hi Hc fii X c' hsub /=.
    t_xrbindP => ci hci cc hcc <-.
    rewrite vars_c_cons in hsub.
    rewrite -cat1s; apply wequiv_cat with (st_eq_on X).
    + by apply: (Hi _ _ _ _ hci); SvD.fsetdec.
    by apply: (Hc _ _ _ _ hcc); SvD.fsetdec.
  { move=> x tg ty e ii fii X c' hsub [<-].
    rewrite vars_I_assgn /vars_lval in hsub.
    apply wequiv_assgn_rel_eq with checker_st_eq_on X => //.
    all: by split; try done; rewrite /read_es /read_rvs /=; SvD.fsetdec. }
  { move=> xs tg o es ii fii X c' hsub /=.
    rewrite vars_I_opn in hsub.
    case: ifP => _; last first.
    + move=> [<-]; apply wequiv_opn_rel_eq with checker_st_eq_on X => //.
      + by split => //; SvD.fsetdec.
      by split; move: hsub; rewrite /vars_lvals; SvD.fsetdec.
    rewrite /normalize_dests_i; t_xrbindP => -[xs' post] hnd [<-].
    have hsubl : Sv.Subset (vars_lvals xs) X by SvD.fsetdec.
    apply wequiv_basic_esem; first by rewrite /= (normalize_dests_basic hnd).
    move=> t s U' hts; have [h1 h2 h3] := hts.
    rewrite esem_cons /= /sem_sopn; t_xrbindP => TF vs ves hves hvs hW hpost.
    have hves' : sem_pexprs (wdb := true) (p_globs p) s es = ok ves.
    + rewrite -eq_globs -hves; symmetry; apply: eq_on_sem_pexprs => //.
      by apply: eq_onI h3; SvD.fsetdec.
    rewrite eq_globs in hW.
    have [S' hS' heq] := normalize_destsP hnd hsubl (sopn_toutP hvs) hts hW hpost.
    by exists S' => //; rewrite hves' /= hvs /= hS'. }
  { move=> xs o es ii fii X c' hsub /=.
    rewrite /normalize_dests_i; t_xrbindP => -[xs' post] hnd [<-].
    rewrite vars_I_syscall in hsub.
    have hsubl : Sv.Subset (vars_lvals xs) X by SvD.fsetdec.
    apply wequiv_basic_esem; first by rewrite /= (normalize_dests_basic hnd).
    move=> t s U' hts; have [h1 h2 h3] := hts.
    rewrite esem_cons /= /sem_syscall; t_xrbindP => TF ves hves fs hfs hW hpost.
    have hves' : sem_pexprs (wdb := true) (p_globs p) s es = ok ves.
    + rewrite -eq_globs -hves; symmetry; apply: eq_on_sem_pexprs => //.
      by apply: eq_onI h3; SvD.fsetdec.
    have hfs' : mk_fstate ves t = mk_fstate ves s by rewrite /mk_fstate h1 h2.
    have [_ htys] := syscall_u_toutP hfs.
    move: hW; rewrite /upd_estate eq_globs => hW.
    have [S' hS' heq] := normalize_destsP hnd hsubl htys
      (W := with_scs (with_mem t (fmem fs)) (fscs fs))
      (S := with_scs (with_mem s (fmem fs)) (fscs fs)) (And3 erefl erefl h3) hW hpost.
    by exists S' => //; rewrite hves' /= -hfs' hfs /= /upd_estate hS'. }
  { move=> a ii fii X c' hsub [<-].
    rewrite vars_I_assert in hsub.
    eapply wequiv_assert_rel_eq with checker_a_st_eq_on => //.
    by split; try done; SvD.fsetdec. }
  { move=> e c1 c2 Hc1 Hc2 ii fii X c' hsub /=.
    t_xrbindP => c1' hc1 c2' hc2 <-.
    rewrite vars_I_if in hsub.
    apply wequiv_if_rel_eq with checker_st_eq_on X X X => //.
    + by split; try done; SvD.fsetdec.
    + by apply: (Hc1 _ _ _ _ hc1); SvD.fsetdec.
    by apply: (Hc2 _ _ _ _ hc2); SvD.fsetdec. }
  { move=> v dir lo hi c Hc ii fii X c' hsub /=.
    t_xrbindP => c1' hc <-.
    rewrite vars_I_for in hsub.
    apply wequiv_for_rel_eq with checker_st_eq_on X X => //.
    + by split => //; rewrite /read_es /= read_eE; SvD.fsetdec.
    + by split; try done; SvD.fsetdec.
    by apply: (Hc _ _ _ _ hc); SvD.fsetdec. }
  { move=> a c e info c' Hc Hc' ii fii X c'' hsub /=.
    t_xrbindP => c1' hc c2' hc' <-.
    rewrite vars_I_while in hsub.
    apply wequiv_while_rel_eq with checker_st_eq_on X => //.
    + by split; try done; SvD.fsetdec.
    + by apply: (Hc _ _ _ _ hc); SvD.fsetdec.
    by apply: (Hc' _ _ _ _ hc'); SvD.fsetdec. }
  move=> xs f es ii fii X c' hsub /=.
  rewrite /normalize_dests_i; t_xrbindP => fd /o2rP hfd -[xs' post] hnd [<-].
  rewrite vars_I_call in hsub.
  have hsubl : Sv.Subset (vars_lvals xs) X by SvD.fsetdec.
  apply (nc_call (X := X)); first by apply: normalize_dests_basic hnd.
  + by SvD.fsetdec.
  move=> fr t s U' [h1 h2 h3] htyped; t_xrbindP => TF hW hpost.
  move: hW; rewrite /upd_estate eq_globs => hW.
  have [S' hS' heq] := normalize_destsP hnd hsubl (htyped _ hfd)
    (W := with_scs (with_mem t (fmem fr)) (fscs fr))
    (S := with_scs (with_mem s (fmem fr)) (fscs fr)) (And3 erefl erefl h3) hW hpost.
  by exists S'.
Qed.

Lemma normalize_calls_finalize fn fd fd' fs :
  get_fundef (p_funcs p) fn = Some fd ->
  normalize_calls_fd fresh_var_ident arrays_by_size p fd = ok fd' ->
  wrequiv (st_eq_on (vars_fd fd)) (finalize_funcall fd') (finalize_funcall fd)
    (rpostF (eS := nc_spec) fn fn fs fs).
Proof using spp.
  move=> hget hfd; rewrite /finalize_funcall.
  case: (normalize_calls_fd_inv hfd) => _ _ _ _ <- <- <- t s fr [h1 h2 h3].
  t_xrbindP => vs hvs vs' htr <-.
  move: hvs; rewrite -(sem_pexprs_get_var _ [::]) => hvs.
  rewrite (eq_on_sem_pexprs (~~ direct_call) [::] h2 (eq_onI _ h3)) in hvs.
  2: by rewrite vars_l_read_es /vars_fd; SvD.fsetdec.
  rewrite sem_pexprs_get_var in hvs.
  rewrite hvs /= htr /= h1 h2; eexists; first reflexivity.
  split => // fd0; rewrite hget => -[<-].
  exact: mapM2_truncate_val_has_type htr.
Qed.

Lemma normalize_calls_nc fn :
  wiequiv_f p' p ev ev (rpreF (eS := nc_spec)) fn fn (rpostF (eS := nc_spec)).
Proof using Hp.
  apply wequiv_fun_ind_wa => {}fn fn' fsi fs [<- <-] fd' H.
  move: (normalize_calls_get_fundef fn); case hget: get_fundef => [fd|]; last by rewrite H.
  move=> [fd'_ Hfd Hfn]; move: Hfn; rewrite H => -[?]; subst fd'_.
  exists fd; first done.
  move=> Hsem; split; first by apply: normalize_calls_sem_pre.
  move=> si hinit; exists si.
  + move: hinit; rewrite /initialize_funcall.
    case: (normalize_calls_fd_inv Hfd) => _ _ <- <- _ _ <-.
    by case: normalize_calls_prog_inv => _ _ ->.
  exists (st_eq_on (vars_fd fd)), (st_eq_on (vars_fd fd)); split.
  + done.
  + move: Hfd; rewrite /normalize_calls_fd; t_xrbindP => c hc <-.
    by apply: normalize_calls_body hc; rewrite /vars_fd; SvD.fsetdec.
  + exact: normalize_calls_finalize hget Hfd.
  by move=> fr1 fr2 [-> _]; apply normalize_calls_sem_post.
Qed.

Lemma normalize_calls_l fn :
  wiequiv_f p' p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using Hp.
  move=> fs1 fs2 hpre; have := normalize_calls_nc hpre.
  apply xrutt_facts.xrutt_weaken => //.
  by move=> > [].
Qed.

End PROOF.
