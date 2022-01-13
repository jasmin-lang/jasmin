From mathcomp Require Import all_ssreflect all_algebra.
Require Import expr linearization.
Require Import arm_decl arm_instr_decl arm_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Linear parameters specific to ARM M4. *)
(* Read the definition in linearization.v for more information. *)

Definition opts :=
  {| args_size      := reg_size
  ;  set_flags      := false
  ;  is_conditional := false
  ;  has_shift      := None
  |}.

Definition arm_allocate_stack_frame (rspi : var_i) (sz : Z) :=
  let rspg := Gvar rspi Slocal in
  ([:: Lvar rspi ], Oarm (ADDI opts), [:: Pvar rspg; Pconst sz ]).

Definition arm_free_stack_frame (rspi : var_i) (sz : Z) :=
  let rspg := Gvar rspi Slocal in
  ([:: Lvar rspi ], Oarm (ADDI opts), [:: Pvar rspg; Pconst (-sz) ]).

Definition arm_ensure_rsp_alignment (rspi : var_i) (al : wsize) :=
  let p0 := Pvar (Gvar rspi Slocal) in
  let p1 := Pconst (- wsize_size al) in
  ([:: Lvar rspi ], Oarm (ANDI opts), [:: p0; p1 ]).

Definition arm_lassign (x : lval) (ws : wsize) (e : pexpr) :=
  let opts :=
    {| args_size      := ws
    ;  set_flags      := false
    ;  is_conditional := false
    ;  has_shift      := None
    |} in
  ([:: x ], Oarm (MOV opts), [:: e ]).

Definition arm_linearization_params : linearization_params :=
  {|
    lip_tmp                  := "r0"%string;
    lip_allocate_stack_frame := arm_allocate_stack_frame;
    lip_free_stack_frame     := arm_free_stack_frame;
    lip_ensure_rsp_alignment := arm_ensure_rsp_alignment;
    lip_lassign              := arm_lassign;
  |}.
