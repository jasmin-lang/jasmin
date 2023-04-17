From mathcomp Require Import
  all_ssreflect
  all_algebra.

Require Import
  linear
  linear_sem
  one_varmap
  psem
  utils
  var.
Require Import
  compiler_util
  register_zeroization
  register_zeroization_utils
  register_zeroization_proof.
Require Import
  arch_decl
  arch_extra
  sem_params_of_arch_extra.
Require asm_gen_proof.

Import one_varmap.

Section RZP_UTILS.

Context
  {reg regx xreg rflag cond asm_op extra_op syscall_state : Type}
  {scsem : syscall_sem syscall_state}
  {asme : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  (zeroize_var : (var -> pp_error_loc) -> var -> cexec lopn_args)
  (zeroize_flags : pp_error_loc -> option var -> cexec (seq lopn_args))
  (zeroized : var -> option value).

Notation zeroized_on := (zeroized_on zeroized).
Notation zeroized_on_vars := (zeroized_on_vars zeroized).

Definition invariant (xs : seq var) (s s' : estate) : Prop :=
  [/\ escs s = escs s'
    , emem s = emem s'
    & zeroized_on_vars (evm s) (evm s') (sv_of_list id xs)
  ].

Lemma invariant_cat xs ys s0 s1 s2 :
  invariant xs s0 s1
  -> invariant ys s1 s2
  -> invariant (xs ++ ys) s0 s2.
Proof.
  move=> [?? h0] [?? h1].
  split; first congruence; first congruence.
  clear - h0 h1.
  rewrite sv_of_list_cat.
  exact: (zeroized_on_varsT h0 h1).
Qed.

Definition zeroize_flags_spec :=
  forall lp scs vm m err_flags fn ii xname P Q args,
    let: x := {| vname := xname; vtype := sword reg_size; |} in
    zeroize_flags err_flags (Some x) = ok args
    -> zeroized_on vm x
    -> let: lcmd := map (li_of_lopn_args ii) args in
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
            & zeroized_on_vars vm vm' (sv_of_list to_var rflags).

(* All lemmas are generalized to code rather than a single instruction. *)
Notation zeroize_var_cmd err :=
  (fun x => Let args := zeroize_var err x in ok [:: args ])
  (only parsing).

Context
  (zeroize_varP :
     forall err_register x,
       get_lopn_invariant (zeroize_var_cmd err_register) invariant x)
  (zeroize_flagsP : zeroize_flags_spec)
  (zeroize_flags_errorP :
    forall err_flags, zeroize_flags err_flags None = Error err_flags).

Lemma zeroize_varsP err_register xs :
  map_get_lopn_invariant (zeroize_var_cmd err_register) invariant xs.
Proof.
  apply: map_get_lopn_invariantP;
    first done.

  - clear.
    move=> xs ys s0 s1 s2 [hscs0 hm0 hzero0] [hscs1 hm1 hzero1].
    split;
      first (by rewrite hscs0);
      first by rewrite hm0.
    rewrite sv_of_list_cat.
    exact: (zeroized_on_varsT hzero0 hzero1).

  move=> x _.
  exact: zeroize_varP.
Qed.

Lemma naive_rz_cmd_argsP :
  h_rz_cmd_args_spec (naive_rz_cmd_args zeroize_var zeroize_flags) zeroized.
Proof.
  move=> lp scs vm m fn rzm xs err_flags err_register P Q args h hxs hbody.

  move: h.
  rewrite /= /naive_rz_cmd_args.
  set ignore := Sv.union callee_saved (sv_of_list id xs).
  set vregs := map to_var registers.
  set vxregs := map to_var xregisters.
  set zregs : seq var := if rzm_registers _ then _ else _.
  set zxregs : seq var := if rzm_xregisters _ then _ else _.
  t_xrbindP=> rzregisters hrzregisters rzflags hrzflags ?; subst args.

  (* Zeroize registers. *)
  rewrite map_cat -!catA in hbody.
  move: hrzregisters => /mapM_singleton hrzregisters.
  rewrite -(conc_map_singleton _ rzregisters) in hbody.
  have [scs0 [vm0 [m0 [hsem0 [hscs0 hm0 hzero0]]]]] :=
    zeroize_varsP _ _ _ scs vm m _ _ _ _ _ hrzregisters hbody.
  rewrite conc_map_singleton in hsem0.
  move: hscs0 hm0 => /= ? ?; subst scs0 m0.
  clear hrzregisters.

  (* Zeroize flags. *)
  move: hrzflags.
  case hrzmf: rzm_flags; first last.

  - move=> [?]; subst rzflags.
    rewrite !cats0.
    exists vm0; first exact: hsem0.
    move: hzero0.
    rewrite /vars_of_rzm /registers_of_rzm /xregisters_of_rzm /flags_of_rzm.
    rewrite hrzmf.
    subst vregs vxregs zregs zxregs.
    change [::] with (filter (fun x => ~~ Sv.mem x ignore) [::]).
    rewrite -2!(fun_if (filter _)).
    rewrite -filter_cat.
    rewrite sv_of_list_filter.
    rewrite sv_of_list_cat.
    rewrite 2!(fun_if (sv_of_list _)).
    rewrite Sv_diff_diff Sv_union_empty_r.
    case: rzm_registers;
      case: rzm_xregisters;
      by rewrite ?sv_of_list_id_map.

  move=> hrzflags.

  (* [rzm_registers rzm] must be true. *)
  subst zregs.
  move: hrzflags hzero0.
  case hrzmr: rzm_registers; last by rewrite zeroize_flags_errorP.
  move=> hrzflags hzero0.

  (* [zregs] must be non-empty. *)
  remember (filter (fun x => ~~ Sv.mem x ignore) vregs) as zregs eqn:hzregs.
  move: hzregs hrzflags hzero0.
  case: zregs => [| x zregs]; first by rewrite zeroize_flags_errorP.
  move=> hzregs hrzflags hzero0.

  have hvtype : vtype x = sword reg_size.
  - have := mem_head x zregs.
    rewrite hzregs mem_filter.
    move=> /andP [] _.
    by move=> /in_map [? _ ->].

  have hx : zeroized_on vm0 x.
  - move: hzero0 => [_ h]. apply: h. by rewrite sv_of_listE mem_head.

  move: hrzflags hx.
  rewrite (var_surj x) hvtype /=.
  move=> hrzflags hx.

  rewrite catA in hbody.

  have [vm1 hsem1 hzero1] :=
    zeroize_flagsP _ scs _ m _ _ _ _ _ _ _ hrzflags hx hbody.
  rewrite conc_map_singleton in hsem1.

  (* Put everything together. *)
  exists vm1.
  - apply: (lsem_trans hsem0). move: hsem1. by rewrite map_cat !size_cat addnA.

  have -> :
    Sv.Equal
      (Sv.diff (vars_of_rzm rzm) (sv_of_list id xs))
      (Sv.union
         (sv_of_list id (x :: zregs ++ zxregs))
         (sv_of_list to_var rflags)).
  - rewrite /vars_of_rzm /registers_of_rzm /xregisters_of_rzm /flags_of_rzm.
    rewrite hrzmf hrzmr.
    rewrite -[_ :: _ ++ _]/((_ :: _) ++ _).
    rewrite sv_of_list_cat.
    set sregs := sv_of_list to_var registers.
    set sxregs := if rzm_xregisters _ then _ else _.
    set sflags := sv_of_list to_var rflags.

    (* Registers. *)
    have -> :
      Sv.Equal
        (sv_of_list id (x :: zregs))
        (Sv.diff sregs ignore).
    + rewrite hzregs.
      subst vregs.
      rewrite sv_of_list_filter.
      by rewrite sv_of_list_id_map.

    (* Extra registers. *)
    have -> :
      Sv.Equal
        (sv_of_list id zxregs)
        (Sv.diff sxregs ignore).
    + subst zxregs sxregs.
      case: rzm_xregisters; last done.
      rewrite sv_of_list_filter.
      by rewrite sv_of_list_id_map.

    (* Flags. *)
    have {2}-> :
      Sv.Equal
        sflags
        (Sv.diff sflags ignore).
    + symmetry.
      apply: disjoint_diff.
      subst ignore sflags.
      apply/disjointP.
      move=> vf h hf.
      move: hf => /sv_of_listP /in_map [f hf ?]; subst vf.
      move: h => /Sv.union_spec []; first last.
      * move=> /sv_of_listP. rewrite map_id. by move=> /hxs.

      move=> /Sv_elemsP.
      rewrite -/(to_var f).
      rewrite -(Bool.negb_involutive (_ \in _)).
      by rewrite asm_gen_proof.flags_notin_callee_saved.

    rewrite Sv_diff_diff.
    rewrite -/ignore.
    rewrite -2!Sv_union_diff_diff.
    by rewrite -SvP.MP.union_assoc.

  exact: (zeroized_on_varsT hzero0 hzero1).
Qed.

End RZP_UTILS.
