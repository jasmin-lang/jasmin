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

Definition zeroized_on_vars (vm vm' : vmap) (xs : Sv.t) : Prop :=
  vm' = vm [\ xs ]
  /\ forall x, Sv.mem x xs -> zeroized_on vm' x.

#[export]
Instance zov_Sv_equal vm0 vm1 :
  Proper (Sv.Equal ==> iff) (zeroized_on_vars vm0 vm1).
Proof.
  move=> xs ys h.
  rewrite /zeroized_on_vars.
  rewrite {1}h.
  split=> -[hvm hz].
  all: split; first done.
  all: move=> x hx.
  all: apply: hz.
  - by rewrite h.
  by rewrite -h.
Qed.

Lemma zeroized_on_varsT xs ys vm0 vm1 vm2 :
  zeroized_on_vars vm0 vm1 xs
  -> zeroized_on_vars vm1 vm2 ys
  -> zeroized_on_vars vm0 vm2 (Sv.union xs ys).
Proof.
  move=> [hvm0 hzero0] [hvm1 hzero1].
  split=> y hy.

  - move: hy => /Sv.union_spec /Decidable.not_or.
    move=> [hxs hys].
    rewrite (vmap_eq_exceptTI hvm1 hvm0); first done.
    move=> /Sv.union_spec.
    by move=> [].

  case hys: (Sv.mem y ys); first exact: (hzero1 _ hys).
  move: hy.
  move=> /Sv_memP /Sv.union_spec [hxs|];
    last by move: hys => /negbT /Sv_memP.

  rewrite /zeroized_on.
  rewrite (get_var_eq_except _ hvm1).
  - move: hxs => /Sv_memP. exact: hzero0.
  apply/Sv_memP.
  by rewrite hys.
Qed.

End ZEROIZATION.

Section H_REGISTER_ZEROIZATION_PARAMS.

Context
  {reg regx xreg rflag cond : Type}
  {arch : arch_decl reg regx xreg rflag cond}
  {atoI : arch_toIdent}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}
  (rzparams : register_zeroization_params).

Definition flags_of_rzm (rzm : rzmode) : Sv.t :=
  if rzm_flags rzm then sv_of_list to_var rflags else Sv.empty.

Definition registers_of_rzm (rzm : rzmode) : Sv.t :=
  if rzm_registers rzm then sv_of_list to_var registers else Sv.empty.

Definition xregisters_of_rzm (rzm : rzmode) : Sv.t :=
 if rzm_xregisters rzm then sv_of_list to_var xregisters else Sv.empty.

Definition vars_of_rzm (rzm : rzmode) : Sv.t :=
  let xs :=
    Sv.union
      (registers_of_rzm rzm)
      (Sv.union (xregisters_of_rzm rzm) (flags_of_rzm rzm))
  in
  Sv.diff xs one_varmap.callee_saved.

Definition h_rz_cmd_args_spec
  (rz_cmd_args :
    rzmode
    -> seq var
    -> pp_error_loc
    -> (var -> pp_error_loc)
    -> cexec (seq lopn_args))
  (zeroized : var -> option value) :
  Prop :=
  forall lp scs vm m fn rzm xs err_flags err_register P Q args,
    rz_cmd_args rzm xs err_flags err_register = ok args
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
            & let: vars := Sv.diff (vars_of_rzm rzm) (sv_of_list id xs) in
              zeroized_on_vars zeroized vm vm' vars.

Record h_register_zeroization_params :=
  {
    h_rz_zeroized : var -> option value;
    h_rz_cmd_args : h_rz_cmd_args_spec (rz_cmd_args rzparams) h_rz_zeroized;
  }.

End H_REGISTER_ZEROIZATION_PARAMS.

Section WITH_PARAMS.

Context
  {reg regx xreg rflag cond : Type}
  {arch : arch_decl reg regx xreg rflag cond}
  {atoI : arch_toIdent}
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
                Sv.diff
                  (vars_of_rzm (rzm_of_fn fn))
                  (sv_of_list v_var (lfd_res lfd))
              in
              zeroized_on_vars vm' vm'' vars
      ].
Proof.
  set ls := {| lpc := 0; |}.
  set ls' := {| lpc := size _; |}.
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
  rewrite sv_of_list_id_map in hvm0.
  clear hrzcmd hres hbody.

  eexists; split;
    first exact hlfd';
    first done.

  eexists; last first.

  - split; first exact: hvm0.
    move=> x.
    have := hz0 x.
    by rewrite sv_of_list_id_map.

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
    + move=> /Sv.diff_spec [_ hxs].
      move: hxs => /sv_of_listP.
      by rewrite mem_head.

    rewrite hind {hind}; first done.
    + apply: (vmap_eq_exceptI _ hvm'').
      apply: Sv_subset_diff_diff; first done.
      move=> y /sv_of_listP hy.
      apply/sv_of_listP.
      by rewrite in_cons hy orbT.

  clear h' hvres.

  eexists;
    first exact hlfd';
    first exact: hexport';
    first exact: hsem'.

  clear hlfd' hexport' hsem' hclear.
  move=> x hx.
  rewrite hvm''; first exact: hvm'.

  clear - hx.
  rewrite /vars_of_rzm.
  move=> /Sv.diff_spec [].
  by move=> /Sv.diff_spec [].
Qed.

End WITH_PARAMS.
