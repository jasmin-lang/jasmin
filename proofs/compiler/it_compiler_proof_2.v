Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From mathcomp Require Import fintype finfun ssralg.
From ITree Require Import
  Basics
  ITree
  ITreeFacts
.

Require Import
  arch_params_proof
  compiler
  compiler_util
  psem
  psem_facts
  relational_logic
  sem_one_varmap
.
Require Import
  stack_zeroization_proof
  stack_alloc_proof_2
  tunneling_proof
  tunneling_proof_2
  linearization_proof
  merge_varmaps_proof
  psem_of_sem_proof
.

Require Import xrutt_facts.
Require Import
  compiler_proof
  it_compiler_proof
.

Require Import
  arch_decl
  arch_extra
  arch_sem
  asm_gen_proof
  sem_params_of_arch_extra
.

Section IT.

Context
  {reg regx xreg rflag cond asm_op extra_op syscall_state : Type}
  {sc_sem : syscall.syscall_sem syscall_state}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}
  {lowering_options : Type}
  (aparams : architecture_params lowering_options)
  (haparams : h_architecture_params aparams)
  (cparams : compiler_params lowering_options)
  (print_uprogP : forall s p, cparams.(print_uprog) s p = p)
  (print_sprogP : forall s p, cparams.(print_sprog) s p = p)
  (print_linearP : forall s p, cparams.(print_linear) s p = p)
.

Notation E := (ErrEvent +' RndEvent syscall_state) (only parsing).
Notation E0 := (RndEvent syscall_state) (only parsing).

#[local] Existing Instance wE.
#[local] Existing Instance HandlerContract.
#[local] Existing Instance RndE00.
#[local] Existing Instance RndE0Refl.
#[local] Existing Instance HandlerContract_trans.

Section FULL.

Context
  (entries : seq funname)
  (up : uprog (asmop := _asmop))
  (xp : asm_prog)
.

Definition zeroized_u fn args argt ms mt mt' :=
  cparams.(stack_zero_info) fn <> None ->
  forall p,
    Forall3
      (disjoint_from_writable_param (ep := ep_of_asm_e) p)
      (get_wptrs up fn)
      args argt ->
    zeroized_p ms mt mt' p.

Definition wf_args_x rip fn ms mi args argt :=
  let n := Z.of_nat (size (asm_globs xp)) in
  let ws := get_wptrs up fn in
  let al := get_asm_align_args xp fn in
  wf_args n rip ms mi ws al args argt.

Let pre fn xfd s t :=
  let: args := s.(fvals) in
  let: ms := s.(fmem) in
  let: rm := t.(asm_reg) in
  let: argt := get_typed_reg_values t xfd.(asm_fd_arg) in
  let: mt := t.(asm_mem) in
  exists mi : @mem _pd,
    [/\ mem_agreement_with_ghost ms mt t.(asm_rip) xp.(asm_globs) mi
      , enough_stack_space xp fn (top_stack ms) mt
      , t.(asm_scs) = s.(fscs)
      , rm ad_rsp = top_stack ms
      , wf_args_x t.(asm_rip) fn ms mi args argt
      & Forall3 (value_uincl_or_in_mem mt) (get_wptrs up fn) args argt
    ].

(* TODO why [t'.(asm_rip)] and not from [t]? *)

Let post fn xfd s t s' t' :=
  let: args := s.(fvals) in
  let: ms := s.(fmem) in
  let: argt := get_typed_reg_values t xfd.(asm_fd_arg) in
  let: mt := t.(asm_mem) in
  let: ress := s'.(fvals) in
  let: ms' := s'.(fmem) in
  let: rest := get_typed_reg_values t' xfd.(asm_fd_res) in
  let: mt' := t'.(asm_mem) in
  let: n := get_nb_wptr up fn in
  [/\ mem_agreement ms' mt' t'.(asm_rip) xp.(asm_globs)
    , t'.(asm_scs) = s'.(fscs)
    , zeroized_u fn args argt ms mt mt'
    , List.Forall2 (value_in_mem mt') (take n ress) (take n argt)
    & values_uincl (drop n ress) rest
  ].

Lemma it_compile_prog_to_asmP {fn} :
  compile_prog_to_asm aparams cparams entries up = ok xp ->
  fn \in entries ->
  exists xfd,
    [/\ get_fundef xp.(asm_funcs) fn = Some xfd
      , xfd.(asm_fd_export)
      & wkequiv_io
          (pre fn xfd)
          (isem_unit up fn)
          (iasmsem_exportcall xp fn)
          (post fn xfd)
   ].
Proof.
rewrite /compile_prog_to_asm; t_xrbindP => sp ok_sp ok_xp ok_fn.
(* Extract xfd independently of rip; print_linearP is needed by the lemma. *)
have [sfd [xfd [get_sfd get_xfd xfd_export align_args_eq]]] :=
  compiler_back_end_to_asm_get_fundef print_linearP ok_xp ok_fn.
exists xfd; split => //.
(* Unfold wkequiv_io: fix a source state fs and asm state xm,
   destructure the FULL precondition. *)
move=> fs xm hpre.
case: hpre => mi [hmga hesp hscs_eq hrsp_eq hwfa hfuim].
(* Specialise FE and BE at rip := asm_rip xm (input-dependent).
   FE: haparams explicit; entries/up/sp/fn inferred from ok_sp/ok_fn
.
   BE: all section vars explicit; rip := asm_rip xm. *)
have FE := it_compiler_front_endP haparams print_uprogP print_sprogP ok_sp ok_fn.
have [xfd2 [get_xfd2 _ BE]] :=
  it_compiler_back_end_to_asmP haparams print_linearP (asm_rip xm) ok_xp ok_fn.
have heq_xfd : xfd2 = xfd by move: get_xfd2; rewrite get_xfd => [[->]].
subst xfd2.

(* ======================================================================= *)
(* STEP 1: construct the intermediate sp-level fstate [fs_sp] that bridges *)
(*         the uincl_or_in_mem precondition (FULL.pre) with the            *)
(*         eq_or_in_mem precondition expected by FE.                       *)
(*                                                                         *)
(*   va2   := map3 (fun o v v' => if o is Some _ then v' else v)           *)
(*                  (get_wptrs up fn) (fvals fs) argt                      *)
(*   fs_sp := {| fscs := fscs fs; fmem := mi; fvals := va2 |}              *)
(*                                                                         *)
(*   Mirrors the [va2] trick in compiler_proof.v:683                       *)
(*   [compiler_front_endP_uincl]. Key outputs:                             *)
(*     - Forall3 (value_eq_or_in_mem mi) wptrs (fvals fs) va2              *)
(*     - values_uincl va2 argt                                             *)
(*     - Forall3 (fun o v v' => o <> None -> v = v') wptrs (fvals fs) va2  *)
(*       (needed later for [ptr_eq_mem_unchanged_params]).                 *)
(* ======================================================================= *)
have [fs_sp [hsp_mem hsp_scs hsp_eqinmem hsp_uincl hsp_ptr_eq]] :
  exists fs_sp : @fstate extended_op _ ep_of_asm_e sip_of_asm_e,
    [/\ fmem fs_sp = mi
      , fscs fs_sp = fscs fs
      , Forall3 (value_eq_or_in_mem mi) (get_wptrs up fn) (fvals fs) (fvals fs_sp)
      , values_uincl (fvals fs_sp) (get_typed_reg_values xm (asm_fd_arg xfd))
      & Forall3 (fun o v v' => isSome o -> v = v')
                (get_wptrs up fn) (fvals fs_sp)
                (get_typed_reg_values xm (asm_fd_arg xfd))
    ].
- (* Transfer hfuim from mt = asm_mem xm to mi *)
  have [hsize1 hsize2] := Forall3_size hfuim.
  have hfuim_mi :
    Forall3 (value_uincl_or_in_mem mi) (get_wptrs up fn) (fvals fs)
      (get_typed_reg_values xm (asm_fd_arg xfd)).
  + apply: (nth_Forall3 None (Vbool true) (Vbool true) hsize1 hsize2) => i hi.
    have := Forall3_nth hfuim None (Vbool true) (Vbool true) hi.
    case ok_writable: (nth None (get_wptrs up fn) i) => [writable|//].
    move=> [pr [ok_pr hread]]; rewrite ok_pr.
    exists pr; split; first by reflexivity.
    move=> off w /[dup] /get_val_byte_bound hoff /hread ok_w.
    move: (hwfa i); rewrite /wf_arg ok_writable ok_pr.
    move=> [_ [[<-] hargp]].
    rewrite -ok_w; apply (match_mem_read_incl_mem hmga.(ma_match_mem)).
    apply hargp.(wap_valid).
    by apply (between_byte hargp.(wap_no_overflow) (zbetween_refl _ _) hoff).
  (* Construct fs_sp with va2 = map3 (ptr → argt, non-ptr → src) *)
  exists {| fscs := fscs fs; fmem := mi
          ; fvals := map3 (fun o v v' => if o is Some _ then v' else v)
                          (get_wptrs up fn) (fvals fs)
                          (get_typed_reg_values xm (asm_fd_arg xfd)) |}.
  split => /=.
  + reflexivity.
  + reflexivity.
  + elim: hfuim_mi => /=.
    - by constructor.
    - move=> wptr v v' wptrs' vs argt' h _ ih.
      constructor; last exact: ih.
      by case: wptr h.
  + elim: hfuim_mi => /=.
    - by constructor.
    - move=> wptr v v' wptrs' vs argt' h _ ih.
      constructor; last exact: ih.
      case: wptr h => [writable h | h] /=.
      * exact: value_uincl_refl.
      * exact: h.
  + (* hsp_ptr_eq: at pointer positions, fvals fs_sp = argt *)
    elim: hfuim_mi => /=.
    - by constructor.
    - move=> wptr v v' wptrs' vs argt' _ _ ih.
      constructor; last exact: ih.
      by case: wptr.

(* ======================================================================= *)
(* STEP 2: apply FE at (asm_rip xm, tt) to obtain an xrutt refinement      *)
(*         [isem_unit up fn fs] ~ [isem_stack sp (asm_rip xm) fn fs_sp].   *)
(*                                                                         *)
(*   Discharging FE's precondition [rpreF fn fn fs fs_sp] requires:        *)
(*     - alloc_ok sp fn (fmem fs_sp)                                       *)
(*         <- enough_stack_space_alloc_ok ok_xp ok_fn _ hesp,              *)
(*            with the stack-range premise from hmga.(ma_stack_range).    *)
(*     - wf_args_s fn (fmem fs) (fmem fs_sp) (fvals fs) (fvals fs_sp)      *)
(*         <- hwfa rewritten via [compiler_back_end_to_asm_meta] for       *)
(*            [size_glob sp] and via sfd/xfd alignment identity for        *)
(*            [get_align_args sp fn].                                      *)
(*     - Forall3 (value_eq_or_in_mem (fmem fs_sp))                         *)
(*              (get_wptrs up fn) (fvals fs) (fvals fs_sp)                 *)
(*         <- STEP 1 output.                                               *)
(*     - it_extend_mem (fmem fs) (fmem fs_sp)                              *)
(*         <- hmga.(ma_extend_mem) with sp_globs rewritten via meta.       *)
(*     - fscs fs = fscs fs_sp                                              *)
(*         <- STEP 1 output (hscs_sp, reversed).                           *)
(* ======================================================================= *)
(* Prove FE's precondition [rpreF fn fn fs fs_sp], then feed it through
   [FE _ tt] to obtain the xrutt refinement [h_fe]. *)
have/(FE _ tt) h_fe :
  rpreF (eS := FrontEndEquiv up sp (asm_rip xm)) fn fn fs fs_sp.
- split.
  - reflexivity. (* fn = fn *)
  - (* alloc_ok sp fn (fmem fs_sp) *)
    have h4 : enough_stack_space xp fn (top_stack mi) (asm_mem xm).
    + by rewrite -(ss_top_stack hmga.(ma_stack_stable)).
    have halloc :=
      enough_stack_space_alloc_ok print_linearP ok_xp ok_fn hmga.(ma_stack_range) h4.
    by rewrite hsp_mem.
  - (* wf_args_s fn (fmem fs) (fmem fs_sp) (fvals fs) (fvals fs_sp) *)
    rewrite /wf_args_s hsp_mem /size_glob.
    rewrite -(compiler_back_end_to_asm_meta print_linearP ok_xp).
    rewrite /get_align_args get_sfd /= align_args_eq.
    move=> i; move: (hwfa i); rewrite /wf_args_x /get_asm_align_args get_xfd /= /wf_arg.
    case hptr: (nth None (get_wptrs up fn) i) => [writable|//].
    move=> [p [hargt_p hargptr]].
    have hi := nth_not_default hptr ltac:(discriminate).
    have hfssp_i : nth (Vbool true) (fvals fs_sp) i =
                   nth (Vbool true) (get_typed_reg_values xm (asm_fd_arg xfd)) i.
    + have := Forall3_nth hsp_ptr_eq None (Vbool true) (Vbool true) hi.
      by rewrite hptr /= => /(_ isT).
    exists p; split; first by rewrite hfssp_i.
    case: hargptr => halign hover hvalid hfresh hwng hdisj.
    split => //.
    move=> hw j vaj pj neq_ij hsome_j hvaj hfssp_j.
    move: hsome_j; case hptr_j: (nth None (get_wptrs up fn) j) => [writablej|//] _.
    have hj := nth_not_default hptr_j ltac:(discriminate).
    have hfssp_j_eq : nth (Vbool true) (fvals fs_sp) j =
                      nth (Vbool true) (get_typed_reg_values xm (asm_fd_arg xfd)) j.
    + have := Forall3_nth hsp_ptr_eq None (Vbool true) (Vbool true) hj.
      by rewrite hptr_j /= => /(_ isT).
    apply: (hdisj hw _ _ _ neq_ij _ hvaj _).
    + by rewrite hptr_j.
    + by rewrite -hfssp_j_eq; exact: hfssp_j.
  - by rewrite hsp_mem; exact: hsp_eqinmem. (* Forall3 (value_eq_or_in_mem (fmem fs_sp)) ... *)
  - have this := hmga.(ma_extend_mem).
    rewrite (compiler_back_end_to_asm_meta print_linearP ok_xp) -hsp_mem
      in this.
    exact: this.
  by rewrite hsp_scs. (* fscs fs = fscs fs_sp  <- STEP 1 hsp_scs. *)

(* ======================================================================= *)
(* STEP 3: apply BE at (fs_sp, xm) to obtain an xrutt refinement           *)
(*         [isem_stack sp (asm_rip xm) fn fs_sp] ~                         *)
(*         [iasmsem_exportcall xp fn xm].                                  *)
(*                                                                         *)
(*   Discharging BE's precondition requires:                               *)
(*     - asm_reg xm ad_rsp = top_stack (fmem fs_sp)                        *)
(*         <- hrsp_eq (= top_stack (fmem fs)) +                            *)
(*            ss_top_stack hmga.(ma_stack_stable).                         *)
(*     - asm_rip xm = asm_rip xm                      <- erefl.            *)
(*     - values_uincl (fvals fs_sp) argt              <- STEP 1 output.    *)
(*     - match_mem (fmem fs_sp) (asm_mem xm)          <- hmga.(ma_match_mem). *)
(*     - fscs fs_sp = asm_scs xm                      <- STEP 1 + hscs_eq. *)
(*     - allocatable_stack (fmem fs_sp) (asm_fd_total_stack xfd)           *)
(*         <- hesp + ma_stack_range (mirrors compiler_proof.v:1297-1299). *)
(* ======================================================================= *)
(* Prove BE's precondition [back_end_to_asm_pre (asm_rip xm) xfd fs_sp xm],
   then feed it through [BE] to obtain the xrutt refinement [h_be]. *)
have /BE h_be : back_end_to_asm_pre (asm_rip xm) xfd fs_sp xm.
- split.
  - by rewrite hsp_mem -(ss_top_stack hmga.(ma_stack_stable)).
  - reflexivity. (* asm_rip xm = asm_rip xm *)
  - exact: hsp_uincl. (* values_uincl (fvals fs_sp) argt — STEP 1 output *)
  - rewrite hsp_mem; exact: hmga.(ma_match_mem).
  - by rewrite hsp_scs hscs_eq.
  (* allocatable_stack (fmem fs_sp) (asm_fd_total_stack xfd)
     mirrors compiler_proof.v:1297-1299 *)
  rewrite /allocatable_stack hsp_mem.
  have hrange := hmga.(ma_stack_range).
  have hstk /= := hesp xfd get_xfd.
  rewrite (ss_top_stack hmga.(ma_stack_stable)) in hstk.
  split; first by apply: hstk.1.
  apply: Z.le_trans; first exact: hstk.2.
  apply Z.sub_le_mono_l; exact: hrange.

(* ======================================================================= *)
(* STEP 4: chain [h_fe] and [h_be] via transitivity of xrutt               *)
(*         (proofs/itrees/xrutt_facts.v:910), then weaken the composed     *)
(*         post to [FULL.post].                                            *)
(* ======================================================================= *)
apply: xrutt_weaken_v1;
  last apply: (xrutt_trans _ h_fe h_be).
- (* EE1 impl: errcutoff (is_error wE) ⊆ errcutoff (is_error wE). *)
  done.
- (* EE2 impl: nocutoff ⊆ nocutoff. *)
  done.
- (* REv impl: EPreRel ⊆ prcompose EPreRel EPreRel (via EventRels_trans). *)
  move=> T1 T3 e1 e3 [T2 e2]; rewrite /EPreRel.
  case: (mfun1 e1) (mfun1 e2) (mfun1 e3) => [err1|e0_1] /=
    [err2|e0_2] //= [err3|e0_3] //.
  case: e0_1 e0_2 e0_3 => [scs1 n1] [scs2 n2] [scs3 n3] /=.
  by move=> [-> ->] [-> ->].
- (* RAns rev impl: pocompose EPreRel EPreRel EPostRel EPostRel ⊆ EPostRel.*)
  move=> T1 T2 e1 t1 e2 t2 hpost T3 e3 hpre13 hpre32.
  rewrite /EPreRel /EPostRel in hpost hpre13 hpre32 *.
  case: e1 t1 hpost hpre13 => [[]|e0_1] t1 //.
  move=> /= hpost hpre13.
  case: e3 hpre13 hpre32 => [err3|e0_3] //= hpre13 hpre32.
  case: e2 hpost hpre32 => [err2|e0_2] //= hpost hpre32.
  exact: (ERpost_trans hpre13 hpre32 hpost).
- (* RR impl: reduce [rcompose rpostF back_end_to_asm_post] to [post].
     Destructure the intermediate fs_sp' and the two posts:
     - h_fe_post : [/\ Forall2 value_in_mem (take n ress) (take n argt),
                     values_uincl (drop n ress) (fvals fs_sp'),
                     it_extend_mem (fmem fs') (fmem fs_sp'),
                     mem_unchanged_params ..., fscs fs' = fscs fs_sp' ]
     - h_be_post : [/\ values_uincl (fvals fs_sp')
                         (get_typed_reg_values xm' ...),
                     match_mem (fmem fs_sp') (asm_mem xm'),
                     fscs fs_sp' = asm_scs xm',
                     zeroized_s fn (fmem fs_sp) (asm_mem xm) (asm_mem xm') ] *)
  move=> fs' xm' [] fs_sp' h_fe_post h_be_post.
  split.
  + (* (1) mem_agreement (fmem fs') (asm_mem xm') (asm_rip xm') (asm_globs xp)
            <- combine hmga.(ma_extend_mem) transported across FE-post's
               it_extend_mem, BE-post's match_mem, and stack_stable
               transitivity (mirrors compiler_proof.v:1303-1315). *)
    admit.
  + by have [_ _ <- _] := h_be_post; have [_ _ _ _ <-] := h_fe_post.
  + (* (3) zeroized_u fn (fvals fs) argt (fmem fs) (asm_mem xm) (asm_mem xm')
     PLAN:
       After [move=> hszs pr hdisj hnvalid], we have:
         hnvalid : ~~ validw (fmem fs) pr
         hdisj   : Forall3 (disjoint_from_writable_param pr)
                     (get_wptrs up fn) (fvals fs) argt
       Destructure:
         have [hfe1 hfe2 hfe3 hfe4 hfe5 hfe6 hfe7] := h_fe_post.
         have [hbe1 hbe2 hbe3 hbe4 hbe5 hbe6] := h_be_post.
       (hfe fields for rpostF, hbe fields for back_end_to_asm_post)
       Do [case: (@idP (validw mi Aligned pr U8))].

       INVALID CASE (~~ validw mi pr = ~~ validw (fmem fs_sp) pr by hsp_mem):
         hbe4 : zeroized_s fn (fmem fs_sp) (asm_mem xm) (asm_mem xm')
         zeroized_p (fmem fs_sp) ms mt mt' p = ~~ validw (fmem fs_sp) p →
                       read mt' p = read mt p ∨ read mt' p = ok 0%R
         Choose [right], rewrite [<- hsp_mem] in hnvalid to get
           ~~ validw mi pr → same as ~~ validw (fmem fs_sp) pr
         Apply: exact/(hbe4 hszs pr)/(negbTE (negbNE _))
         Or more concretely: apply (hbe4 hszs pr); rewrite hsp_mem; exact hninvalid.

       VALID CASE (hvalid : validw mi pr):
         Available hypotheses after destructuring:
           hfe3 : it_extend_mem sp (asm_rip xm) (fmem fs') (fmem fs_sp')
                = extend_mem (fmem fs') (fmem fs_sp') (asm_rip xm) (sp_globs (p_extra sp))
           hfe4 : mem_unchanged_params (fmem fs) mi (fmem fs_sp')
                    (get_wptrs up fn) (fvals fs) (fvals fs_sp)
           hfe7 : stack_stable (fmem fs_sp) (fmem fs_sp')
           hbe2 : match_mem (fmem fs_sp') (asm_mem xm')
           hbe4 : zeroized_s cparams fn (fmem fs_sp) (asm_mem xm) (asm_mem xm')
           hbe6 : stack_stable (asm_mem xm) (asm_mem xm')
           hmga : mem_agreement_with_ghost (fmem fs) (asm_mem xm) (asm_rip xm)
                    (asm_globs xp) mi
             .ma_extend_mem : extend_mem (fmem fs) mi (asm_rip xm) (asm_globs xp)
             .ma_match_mem  : match_mem mi (asm_mem xm)
             .ma_stack_stable : stack_stable (fmem fs) mi

         Step 1 - convert hdisj to use fvals fs_sp instead of argt:
           disjoint_from_writable_param p wptr v1 v2 depends on v2 only when
           wptr = Some true. For those positions, hsp_ptr_eq gives
           fvals fs_sp = argt. So [Forall3_impl] + case on wptr gives:
             hdisj_sp : Forall3 (disjoint_from_writable_param pr)
                          (get_wptrs up fn) (fvals fs) (fvals fs_sp)

         Step 2 - from hfe4 (mem_unchanged_params):
           [hfe4 hvalid hnvalid hdisj_sp : read mi pr = read (fmem fs_sp') pr]
           (here mi = fmem fs_sp by hsp_mem; valid in mi, not valid in fmem fs)

         Step 3 - from hmga.(ma_match_mem) : match_mem mi (asm_mem xm):
           [match_mem_read_incl_mem hmga.(ma_match_mem) hvalid :
              read mi pr = read (asm_mem xm) pr]
           (match_mem_read_incl_mem : match_mem m m' → validw m p →
              read m Aligned p U8 = read m' Aligned p U8)
           Proof: uses read_incl_mem + stack_region_is_free to discharge the
             non-stack-region condition. Since validw mi pr holds,
             stack_region_is_free gives ~~ (stack_limit mi ≤ pr < top_stack mi).

         Step 4 - need read (asm_mem xm') pr = read (fmem fs_sp') pr via hbe2.
           This is the STUCK POINT. Two options, both need more investigation:

           Option A: prove validw (fmem fs_sp') pr from validw mi pr.
             - stack_region_is_free shows pr is NOT in stack region of mi.
             - Confirmed: NO stack_stable_validw lemma exists in the library.
               Search (stack_stable _ _ -> forall _, validw...) = no results.
               Search (stack_stable _ _ -> validw _ = _) = no results.
             - hfe3 : extend_mem (fmem fs') (fmem fs_sp') rip data, so
               em_valid hfe3 : validw (fmem fs') pr || between rip data pr
                             → validw (fmem fs_sp') pr
               But how to get validw (fmem fs') pr or between rip data pr?
             - em_valid is ONE-DIRECTIONAL only (confirmed from Print extend_mem).
               No em_validE (biconditional) lemma found.
             - KEY INSIGHT TO EXPLORE: from hmga.ma_extend_mem and validw mi pr
               and ~~ validw (fmem fs) pr, it follows semantically that pr must
               be a global data address (between rip (asm_globs xp) pr), because
               extend_mem (fmem fs) mi rip (asm_globs xp) is constructed by
               alloc_glob which adds EXACTLY the global range. If there is a
               converse of em_valid, i.e.:
                 validw mi pr → validw (fmem fs) pr || between rip globs pr
               (which would be provable from the implementation), then with
               ~~ validw (fmem fs) pr we'd get between rip (asm_globs xp) pr.
               Then since sp_globs (p_extra sp) = asm_globs xp (global data
               is preserved across compilation), em_valid hfe3 would give
               validw (fmem fs_sp') pr.
               ACTION: search for the converse em_valid lemma, or look at
               how extend_mem is constructed in the memory model (alloc_glob).

           Option B: prove read (fmem fs_sp') pr = ok v.
             - read (fmem fs_sp') pr = read mi pr (from Step 2 symm)
             - So need read mi pr = ok v (i.e., read succeeds on valid address).
             - Search (validw _ _ _ _ -> read _ _ _ _ = ok _) = no results.
               Search (validw _ _ _ _ -> read _ _ _ _ = _) shows only
               {ass,fss}_read_old8 and match_mem_read_incl_mem (same memory,
               different direction) — no forward validw→read=ok lemma.
             - readV : read = ok → validw (WRONG direction; confirmed).
             - POSSIBLE APPROACH: use mm_read_ok which needs read = ok v as
               hypothesis. mm_read_ok : match_mem_gen sp m m' →
                 read m al a s = ok v → read m' al a s = ok v.
               But we need read (fmem fs_sp') pr = ok v first, which needs
               the same forward direction.

           NEXT STEPS (in priority order):
           1. Search for an inverse em_valid lemma:
                Search (extend_mem _ _ _ _ -> validw _ _ _ _ ->
                        validw _ _ _ _ || between _ _ _ _).
              Or look at alloc_glob definition in
                proofs/lang/memory_model.v or similar.
           2. Check if sp_globs (p_extra sp) = asm_globs xp is provable
              from ok_sp / ok_xp.
           3. If no converse exists, look at match_mem_gen.read_incl_mem
              and try to use the structure differently:
              read_incl_mem hbe2 : ~ (stack_limit (fmem fs_sp') ≤ pr <
                top_stack (fmem fs_sp')) → validw (fmem fs_sp') pr →
                read (fmem fs_sp') pr = read (asm_mem xm') pr.
              The first condition follows from stack_region_is_free applied
              to (fmem fs_sp') IF we already know validw (fmem fs_sp') pr.
              This is circular, but read_incl_stk might help for stack
              addresses.
         Combine (once Step 4 is resolved): choose [left];
           read (asm_mem xm') pr = read (fmem fs_sp') pr  (Step 4)
                                 = read mi pr              (Step 2 symm)
                                 = read (asm_mem xm) pr.   (Step 3) *)
    admit.
  + (* (4) List.Forall2 (value_in_mem (asm_mem xm'))
                        (take n (fvals fs')) (take n argt)
            <- Forall2_impl + mm_read_ok from BE post's match_mem. *)
    case: h_fe_post => hfe1 hfe2 hfe3 hfe4 hfe5.
    case: h_be_post => hbe1 hbe2 hbe3 hbe4.
    have [hsz1 hsz2] := Forall3_size hsp_ptr_eq.
    have heq_take : take (get_nb_wptr up fn) (fvals fs_sp) =
                    take (get_nb_wptr up fn)
                         (get_typed_reg_values xm (asm_fd_arg xfd)).
    { apply: (@eq_from_nth _ (Vbool true)).
      - by rewrite !size_take -hsz1 hsz2.
      - move=> i; rewrite size_take ltn_min => /andP [hlt_n hlt_wptr].
        rewrite -hsz1 in hlt_wptr.
        rewrite nth_take // nth_take //.
        apply: (Forall3_nth hsp_ptr_eq None (Vbool true) (Vbool true)
                            hlt_wptr).
        have hbf := before_find None hlt_n.
        by case: (nth None (get_wptrs up fn) i) hbf. }
    rewrite -heq_take.
    apply: Forall2_impl hfe1 => v1 v2 [pr [-> hread]].
    exists pr; split; first by reflexivity.
    move=> off w /hread; exact: mm_read_ok hbe2.
  (* (5) values_uincl (drop n (fvals fs'))
                      (get_typed_reg_values xm' (asm_fd_res xfd))
          <- values_uincl_trans on FE post's drop-n uincl and BE post's
             values_uincl. *)
  admit.
(* CND (from xrutt_trans): for e1 ~ e2 under [prcompose EPreRel EPreRel],
   if e2 is a cut event (errcutoff), then e1 is a cut event. *)
by move=> T1 T2 [?|n1] [?|n2].
Admitted.

End FULL.

End IT.
