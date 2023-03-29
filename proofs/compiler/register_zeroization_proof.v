From mathcomp Require Import
  all_ssreflect
  all_algebra.
Require Import Relations.
Require Import ZArith.
Require Psatz.

Require Import
  compiler_util
  linear
  linear_sem
  linear_util
  one_varmap
  psem
  word.
Require Import
  arch_decl
  arch_extra.
Require Import register_zeroization.
Import one_varmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: Move and import in linearization_proof. *)
Section MOVE.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

(* asmgenproof*)
Lemma get_var_eq_except vm1 vm2 x X :
   ~Sv.In x X ->
   vm1 = vm2 [\X] ->
   get_var vm1 x = get_var vm2 x.
Proof. by rewrite /get_var => hnin -> //. Qed.

End MOVE.

Lemma sv_of_list_cat_union X (xs ys : seq X) f :
  Sv.Equal
    (sv_of_list f (xs ++ ys))
    (Sv.union (sv_of_list f xs) (sv_of_list f ys)).
Proof.
  apply: SvP.MP.subset_antisym => x hx.

  - apply/Sv.union_spec.
    move: hx => /sv_of_listP.
    rewrite map_cat mem_cat.
    move=> /orP [] /sv_of_listP ?; by econstructor.

  apply/sv_of_listP.
  rewrite map_cat mem_cat.
  apply/orP.
  move: hx => /Sv.union_spec [] /sv_of_listP hx; by econstructor.
Qed.

Definition is_prefix {X} (xs ys : seq X) : Prop :=
  exists zs, ys = xs ++ zs.

Lemma onth_prefix {X} (xs ys : seq X) n x :
  oseq.onth xs n = Some x
  -> is_prefix xs ys
  -> oseq.onth ys n = Some x.
Proof.
  move=> hnth [tail htail].
  elim: xs ys n hnth htail => //= x0 xs hi ys n.
  case: n.
  - move=> [?]; subst x0. by move=> ->.
  move=> n hnth -> /=.
  by apply: (hi _ _ hnth).
Qed.

Section LPROG_EXTEND.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}
  (lp lp' : lprog).

Definition lprog_extend lp lp' :=
  forall fn lfd,
    get_fundef (lp_funcs lp) fn = Some lfd
    -> exists2 lfd',
         get_fundef (lp_funcs lp') fn = Some lfd'
         & is_prefix (lfd_body lfd) (lfd_body lfd').

Context (hextend : lprog_extend lp lp').

Lemma lprog_extend_get_fundef fn lfd :
  get_fundef (lp_funcs lp) fn = Some lfd
  -> exists lfd',
       get_fundef (lp_funcs lp') fn = Some lfd'.
Proof. move=> h. have [lfd' hlfd' _] := hextend h. by exists lfd'. Qed.

Lemma lprog_extend_find_instr ls i :
  find_instr lp ls = Some i
  -> find_instr lp' ls = Some i.
Proof.
  rewrite /find_instr.
  case hlfd: get_fundef => [lfd | //] hget.
  have [lfd' hlfd'] := lprog_extend_get_fundef hlfd.
  rewrite hlfd'.
  have [lfd'' hlfd'' hpre] := hextend hlfd.
  move: hlfd''.
  rewrite hlfd'.
  move=> [?]; subst lfd''.
  by rewrite (onth_prefix hget hpre).
Qed.

Definition lprog_extend_eval_instr i ls ls' :
  eval_instr lp i ls = ok ls'
  -> eval_instr lp' i ls = ok ls'.
Proof.
  move: i => [ii i].
  case: i => //.
Admitted.

Lemma lprog_extend_lsem1 ls ls' :
  lsem1 lp ls ls'
  -> lsem1 lp' ls ls'.
Proof.
  rewrite /lsem1 /step /find_instr.
  case hlfd: get_fundef => [lfd | //].
  have [lfd' hlfd'] := lprog_extend_get_fundef hlfd.
  rewrite hlfd'.

  case hpc: oseq.onth => [i | //].
  have -> : oseq.onth (lfd_body lfd') (lpc ls) = Some i.
  - have : find_instr lp' ls = Some i.
    + apply: lprog_extend_find_instr. rewrite /find_instr. by rewrite hlfd.
    rewrite /find_instr.
    case h0: get_fundef => [lfd0 | //].
    move: h0.
    rewrite hlfd'.
    by move=> [->].

  exact: lprog_extend_eval_instr.
Qed.

Lemma lprog_extend_lsem ls ls' :
  lsem lp ls ls'
  -> lsem lp' ls ls'.
Proof.
  move: ls'.
  apply: clos_refl_trans_ind_left; first exact: rt_refl.
  move=> ls0 ls1 hsem hsem' hstep.
  apply: (lsem_step_end hsem').
  apply: lprog_extend_lsem1.
  exact: hstep.
Qed.

End LPROG_EXTEND.

Section ZEROIZATION.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}
  (zeroized : var -> option value).

Definition zeroized_on (vm : vmap) (x : var) : Prop :=
  match get_var vm x, zeroized x with
  | Ok v, Some v' => v = v'
  | _, _ => False
  end.

Definition zeroized_on_vars (vm vm' : vmap) (xs : seq var) : Prop :=
  vm' = vm [\ sv_of_list id xs ]
  /\ forall x, x \in xs -> zeroized_on vm' x.

Lemma zeroized_on_varsT xs ys vm0 vm1 vm2 :
  zeroized_on_vars vm0 vm1 xs
  -> zeroized_on_vars vm1 vm2 ys
  -> zeroized_on_vars vm0 vm2 (xs ++ ys).
Proof.
  move=> [hvm0 hzero0] [hvm1 hzero1].
  split=> y hy.

  - move: hy => /sv_of_listP.
    rewrite map_cat mem_cat negb_or.
    move=> /andP [hxs hys].
    rewrite (vmap_eq_exceptTI hvm1 hvm0); first done.
    move=> /Sv.union_spec.
    move=> [] /sv_of_listP; by apply/negP.

  case hys: (y \in ys); first exact: (hzero1 _ hys).
  move: hy.
  rewrite mem_cat.
  move=> /orP [hxs|]; last by rewrite hys.
  rewrite /zeroized_on.

  rewrite (get_var_eq_except _ hvm1); first exact: (hzero0 _ hxs).
  apply/sv_of_listP.
  rewrite map_id.
  by apply/negPf.
Qed.

End ZEROIZATION.

Section H_REGISTER_ZEROIZATION_PARAMS.

Context
  {reg regx xreg rflag cond : Type}
  {arch : arch_decl reg regx xreg rflag cond}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}
  (rzparams : register_zeroization_params).

Definition flags_of_rzm (rzm : rzmode) : seq var :=
  if rzm_flags rzm then map to_var rflags else [::].

Definition registers_of_rzm (rzm : rzmode) : seq var :=
  if rzm_registers rzm then map to_var registers else [::].

Definition xregisters_of_rzm (rzm : rzmode) : seq var :=
 if rzm_xregisters rzm then map to_var xregisters else [::].

Definition vars_of_rzm (rzm : rzmode) : seq var :=
  let xs := registers_of_rzm rzm ++ xregisters_of_rzm rzm ++ flags_of_rzm rzm in
  seq_diff xs (Sv.elements one_varmap.callee_saved).

Record h_register_zeroization_params :=
  {
    h_rz_zeroized : var -> option value;

    h_rz_cmd_args :
      forall lp scs vm m fn rzm xs err_flags err_register P Q args,
        rz_cmd_args rzparams rzm xs err_flags err_register = ok args
        -> (forall x, x \in xs -> ~~ is_sbool (vtype x))
        -> let: lcmd := map (li_of_lopn_args dummy_instr_info) args in
           is_linear_of lp fn (P ++ lcmd ++ Q)
           -> exists2 vm',
                let: ls :=
                  {|
                    lscs := scs;
                    lvm := vm;
                    lmem := m;
                    lfn := fn;
                    lpc := size P;
                  |}
                in
                let: ls' :=
                  {|
                    lscs := scs;
                    lvm := vm';
                    lmem := m;
                    lfn := fn;
                    lpc := size P + size lcmd;
                  |}
                in
                lsem lp ls ls'
                & let: vars := seq_diff (vars_of_rzm rzm) xs in
                  zeroized_on_vars h_rz_zeroized vm vm' vars;
  }.

End H_REGISTER_ZEROIZATION_PARAMS.

Section WITH_PARAMS.

Context
  {reg regx xreg rflag cond : Type}
  {arch : arch_decl reg regx xreg rflag cond}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}
  (rzm_of_fn : funname -> rzmode)
  (rzparams : register_zeroization_params)
  (hrzparams : h_register_zeroization_params rzparams).

Notation register_zeroization_lfd :=
  (register_zeroization_lfd rzm_of_fn rzparams).
Notation register_zeroization_lprog :=
  (register_zeroization_lprog rzm_of_fn rzparams).
Notation zeroized_on := (zeroized_on (h_rz_zeroized hrzparams)).
Notation zeroized_on_vars := (zeroized_on_vars (h_rz_zeroized hrzparams)).

Lemma register_zeroization_lprog_get_fundef lp lp' fn lfd :
  register_zeroization_lprog lp = ok lp'
  -> get_fundef (lp_funcs lp) fn = Some lfd
  -> exists2 lfd',
       register_zeroization_lfd fn lfd = ok lfd'
       & get_fundef (lp_funcs lp') fn = Some lfd'.
Proof.
  rewrite /register_zeroization_lprog.
  t_xrbindP=> fs hmap <- hget.
  exact: (get_map_cfprog_name_gen hmap hget).
Qed.

Lemma lprog_extend_register_zeroization lp lp' :
  register_zeroization_lprog lp = ok lp'
  -> lprog_extend lp lp'.
Proof.
  move=> h fn lfd hlfd.

  have [lfd' h' hlfd'] := register_zeroization_lprog_get_fundef h hlfd.
  clear h hlfd.

  exists lfd'; first exact: hlfd'.
  move: h'.
  rewrite /register_zeroization_lfd /=.
  case: lfd_export; last first.
  - move=> [<-]. exists [::]. by rewrite cats0.

  t_xrbindP=> ?? <-.
  by eexists.
Qed.

Lemma register_zeroization_lprogP lp lp' fn lfd scs m vm scs' m' vm' :
  let: ls :=
    {|
      lscs := scs;
      lmem := m;
      lvm := vm;
      lfn := fn;
      lpc := 0;
    |}
  in
  let: ls' :=
    {|
      lscs := scs';
      lmem := m';
      lvm := vm';
      lfn := fn;
      lpc := size (lfd_body lfd);
    |}
  in
  register_zeroization_lprog lp = ok lp'
  -> get_fundef (lp_funcs lp) fn = Some lfd
  -> lfd_export lfd
  -> lsem lp ls ls'
  -> exists lfd',
      [/\ get_fundef (lp_funcs lp') fn = Some lfd'
        , register_zeroization_lfd fn lfd = ok lfd'
        & exists2 vm'',
            let: ls'' :=
              {|
                lscs := scs';
                lmem := m';
                lvm := vm'';
                lfn := fn;
                lpc := size (lfd_body lfd');
              |}
            in
            lsem lp' ls ls''
            & let: vars :=
                seq_diff (vars_of_rzm (rzm_of_fn fn)) (map v_var (lfd_res lfd))
              in
              zeroized_on_vars vm' vm'' vars
      ].
Proof.
  set ls := {| lpc := 0; |}.
  set ls' := {| lpc := size _; |}.
  set vars := map _ _.
  move=> h hlfd hexport hsem.

  have hextend := lprog_extend_register_zeroization h.
  have [lfd' h' hlfd'] := register_zeroization_lprog_get_fundef h hlfd.
  clear h hlfd.

  rewrite h'.
  move: h'.
  rewrite /register_zeroization_lfd.
  rewrite hexport /=.
  t_xrbindP=> rzcmd hrzcmd ?; subst lfd'.
  move: hrzcmd.
  rewrite /rz_cmd.
  t_xrbindP=> hres args hrzcmd ?; subst rzcmd.
  set rzcmd := map _ args.

  move: hres => /allP hres.

  have hbody :
    is_linear_of lp' fn (lfd_body lfd ++ rzcmd ++ [::]).
  - rewrite cats0. rewrite /is_linear_of. eexists; first exact: hlfd'. done.

  have /= [vm0 hsem0 [hvm0 hz0]] :=
    h_rz_cmd_args hrzparams scs' vm' m' hrzcmd hres hbody.
  clear hrzcmd hres hbody.

  eexists; split;
    first exact hlfd';
    first done.

  eexists; last first.

  - split; first exact: hvm0. exact: hz0.

  apply: lsem_trans.
  - apply: (lprog_extend_lsem hextend). exact: hsem.
  rewrite /= size_cat.
  exact: hsem0.
Qed.

Lemma register_zeroization_lprog_invariants lp lp' :
  register_zeroization_lprog lp = ok lp'
  -> [/\ lp_rip lp = lp_rip lp'
       , lp_rsp lp = lp_rsp lp'
       & lp_globs lp = lp_globs lp'
     ].
Proof.
  rewrite /register_zeroization_lprog.
  by t_xrbindP=> ? _ <-.
Qed.

Lemma register_zeroization_lfd_invariants fn lfd lfd' :
  register_zeroization_lfd fn lfd = ok lfd'
  -> [/\ lfd_tyin lfd' = lfd_tyin lfd
       , lfd_arg lfd' = lfd_arg lfd
       , lfd_tyout lfd' = lfd_tyout lfd
       , lfd_res lfd' = lfd_res lfd
       , lfd_export lfd' = lfd_export lfd
       , lfd_callee_saved lfd' = lfd_callee_saved lfd
       & lfd_total_stack lfd' = lfd_total_stack lfd
     ].
Proof.
  rewrite /register_zeroization_lfd.
  case h: lfd_export; last by move=> [<-].
  by t_xrbindP=> ?? <-.
Qed.

Lemma seq_diff_sv xs ys :
  let: to_sv := sv_of_list id in
  Sv.Equal (to_sv (seq_diff xs ys)) (Sv.diff (to_sv xs) (to_sv ys)).
Proof.
  apply: SvP.MP.subset_antisym => x hx.
  - apply/Sv.diff_spec.
    move: hx => /sv_of_listP.
    rewrite /seq_diff.
    rewrite map_id mem_filter.
    move=> /andP [hys hxs].
    split;
      apply/sv_of_listP;
      by rewrite map_id.

  move: hx => /Sv.diff_spec [].
  move=> /sv_of_listP hxs /sv_of_listP hys.
  apply/sv_of_listP.
  rewrite /seq_diff.
  move: hxs hys.
  rewrite !map_id mem_filter.
  by move=> -> ->.
Qed.

Lemma Sv_subset_diff_diff xs xs' ys ys' :
  Sv.Subset xs ys
  -> Sv.Subset ys' xs'
  -> Sv.Subset (Sv.diff xs xs') (Sv.diff ys ys').
Proof.
  move=> h h'.
  move=> x /Sv.diff_spec [hxs hxs'].
  apply/Sv.diff_spec.
  split; first exact: (h _ hxs).
  clear h hxs.
  by move=> /h'.
Qed.

Lemma register_zeroization_correct lp lp' scs m fn vm scs' m' vm' lfd vres :
  register_zeroization_lprog lp = ok lp'
  -> lsem_exportcall lp scs m fn vm scs' m' vm'
  -> get_fundef (lp_funcs lp) fn = Some lfd
  -> mapM (fun x => get_var vm' (v_var x)) (lfd_res lfd) = ok vres
  -> exists2 vm'',
       lsem_exportcall lp' scs m fn vm scs' m' vm''
       & mapM (fun x => get_var vm'' (v_var x)) (lfd_res lfd) = ok vres.
Proof.
  move=> h [lfd' hlfd' hexport hsem hvm'] hlfd hvres.

  move: hlfd'.
  rewrite hlfd.
  move=> [?]; subst lfd'.

  have [lfd' [hlfd' h' [vm'' hsem' [hvm'' hclear]]]] :=
    register_zeroization_lprogP h hlfd hexport hsem.
  clear h hlfd hsem.

  have [_ _ _ _ hexport' _ _] := register_zeroization_lfd_invariants h'.

  rewrite hexport {hexport} in hexport'.

  exists vm''; first last.

  - clear - hvres hvm''.
    rewrite -hvres {hvres}.
    move: hvm''.
    move: (vars_of_rzm _) => vom.
    elim: (lfd_res lfd) => //= x xs hind hvm''.

    rewrite (get_var_eq_except _ hvm''); first last.
    + apply/sv_of_listP.
      rewrite /seq_diff.
      rewrite map_id mem_filter.
      rewrite negb_and Bool.negb_involutive.
      by rewrite mem_head.

    rewrite hind {hind}; first done.
    + apply: (vmap_eq_exceptI _ hvm'').
      rewrite !seq_diff_sv.
      apply: Sv_subset_diff_diff; first done.
      move=> y /sv_of_listP hxs.
      apply/sv_of_listP.
      move: hxs.
      rewrite !map_id in_cons.
      move=> ->.
      exact: orbT.

  clear h' hvres.

  eexists;
    first exact hlfd';
    first exact: hexport';
    first exact: hsem'.

  clear hlfd' hexport' hsem' hclear.
  move=> x hx.
  rewrite hvm''; first exact: hvm'.
  rewrite seq_diff_sv.
  move=> /Sv.diff_spec [].
  rewrite /vars_of_rzm.
  rewrite seq_diff_sv.
  move=> /Sv.diff_spec [_ h _].
  apply: h.
  by rewrite sv_of_list_elements.
Qed.

End WITH_PARAMS.
