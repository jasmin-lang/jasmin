From mathcomp Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import word_ssrZ.

Require Import
  psem
  shift_kind.
Require Import
  arch_utils
  sem_params_of_arch_extra.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ignore_has_shift mn sf ic hs hs' :
  mn \notin has_shift_mnemonics
  -> let opts :=
       {| set_flags := sf; is_conditional := ic; has_shift := hs; |}
     in
     let opts' :=
       {| set_flags := sf; is_conditional := ic; has_shift := hs'; |}
     in
     mn_desc opts mn = mn_desc opts' mn.
Proof. by case: mn. Qed.

(* TODO_ARM: It seems like we need to characterize conditional execution,
   but the variable number of arguments makes it very cumbersome.
   This gets multiplied if they set flags or have shifts. *)

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {atoI : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {pT : progT}
  {sCP : semCallParams}.

Definition truncate_args
  (op : sopn) (vargs : seq value) : exec (seq value) :=
  mapM2 ErrType truncate_val (sopn_tout op) vargs.

Lemma exec_sopn_conditional mn sf osk b vargs vprev vres0 vres1 :
  let opts :=
    {| set_flags := sf; is_conditional := false; has_shift := osk; |}
  in
  let op := Oarm (ARM_op mn opts) in
  truncate_args op vprev = ok vres1
  -> exec_sopn op vargs = ok vres0
  -> exec_sopn
       (Oarm (ARM_op mn (set_is_conditional opts)))
       (vargs ++ Vbool b :: vprev)
       = ok (if b then vres0 else vres1).
Proof.
  all: case: sf.
  all: case: osk => [sk|].
  all: case: mn => [||||||||||||||||??|??|?|||||||||||||||||||||||||||||||||].
  all: rewrite /truncate_args /truncate_val.

  (* Destruct [vprev]. *)
  all:
    do 6? (
      case: vprev => [| ? vprev ] //=;
      t_xrbindP=> //;
      repeat
        match goal with
        | [ |- forall (_ : value), forall _, _ ] => move=> ? ? ? ? ?
        | [ |- ([::] = _) -> _ ] => move=> ?
        | [ |- (_ :: _ = _) -> _ ] => move=> ?
        end
    ).

  all: try move=> <-.
  all: subst.

  (* Destruct [vargs]. *)
  all: rewrite /exec_sopn /=.
  all: case: vargs => [| ? vargs ] //; t_xrbindP => // v.
  all:
    do 6? (
      case: vargs => [| ? vargs ] //;
      t_xrbindP => //;
      match goal with
      | [ |- forall _, ((_ = ok _) -> _) ] => move=> ? ?
      end
    ).
  all: move=> hsemop ?; subst vres0.
  all: rewrite /=.
  all:
    repeat (
      match goal with
      | [ h : _ = ok _ |- _ ] => rewrite h {h} /=
      end
    ).

  (* Introduce and rewrite all semantic checks. *)
  all: move: hsemop.
  all: cbn.
  all:
    try match goal with
    | [ |- ?f _ = ok _ -> _ ] => rewrite /f
    end.
  all: t_xrbindP=> *; subst v; t_eq_rewrites.

  all: by case: b.
Qed.

(* TODO_ARM: Is this the best way of expressing the [write_val] condition? *)
Lemma sem_i_conditional
  {dc : DirectCall} (p : prog)
  ev s0 s1 mn sf osk lvs tag args c prev vargs b vprev vprev' vres :
  let opts :=
    {| set_flags := sf; is_conditional := false; has_shift := osk; |}
  in
  let aop := Oarm (ARM_op mn opts) in
  sem_pexprs true (p_globs p) s0 args = ok vargs
  -> sem_pexpr true (p_globs p) s0 c = ok (Vbool b)
  -> sem_pexprs true (p_globs p) s0 prev = ok vprev
  -> truncate_args aop vprev = ok vprev'
  -> exec_sopn aop vargs = ok vres
  -> (if b
      then write_lvals true (p_globs p) s0 lvs vres = ok s1
      else write_lvals true (p_globs p) s0 lvs vprev' = ok s1)
  -> let aop' := Oarm (ARM_op mn (set_is_conditional opts)) in
     let ir := Copn lvs tag aop' (args ++ c :: prev) in
     sem_i p ev s0 ir s1.
Proof.
  move=> opts aop hsemargs hsemc hsemprev htruncprev hexec hwrite.

  apply: Eopn.
  rewrite /sem_sopn /=.
  rewrite /sem_pexprs mapM_cat /= -2![mapM _ _]/(sem_pexprs _ _ _ _).
  rewrite hsemargs hsemc hsemprev {hsemargs hsemc hsemprev} /=.

  case: b hwrite => hwrite.
  all: rewrite (exec_sopn_conditional _ htruncprev hexec) {htruncprev hexec} /=.
  all: exact: hwrite.
Qed.

End WITH_PARAMS.
