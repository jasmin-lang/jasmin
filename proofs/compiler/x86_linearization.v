From mathcomp Require Import all_ssreflect all_algebra.
Require Import expr linearization.
Require Import x86_decl x86_instr_decl x86_extra x86_linear_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Linear parameters specific to x86. *)
(* Read the definition in linear.v for more information. *)

Definition x86_allocate_stack_frame (rspi: var_i) (sz: Z) :=
  let rspg := Gvar rspi Slocal in
  let p := Papp2 (Oadd (Op_w Uptr)) (Pvar rspg) (cast_const sz) in
  ([:: Lvar rspi ], Ox86 (LEA Uptr), [:: p ]).

Definition x86_free_stack_frame (rspi: var_i) (sz: Z) :=
  let rspg := Gvar rspi Slocal in
  let p := Papp2 (Osub (Op_w Uptr)) (Pvar rspg) (cast_const sz) in
  ([:: Lvar rspi ], Ox86 (LEA Uptr), [:: p ]).

Definition x86_ensure_rsp_alignment (rspi: var_i) (al: wsize) :=
  let to_lvar x := Lvar (VarI (to_var x) xH) in
  let eflags := List.map to_lvar [:: OF ; CF ; SF ; PF ; ZF ] in
  let p0 := Pvar (Gvar rspi Slocal) in
  let p1 := Papp1 (Oword_of_int Uptr) (Pconst (- wsize_size al)) in
  (eflags ++ [:: Lvar rspi ], Ox86 (AND Uptr), [:: p0; p1 ]).

Definition x86_lassign (x: lval) (ws: wsize) (e: pexpr) :=
  let op := if (ws <= U64)%CMP
            then MOV ws
            else VMOVDQU ws
  in ([:: x ], Ox86 op, [:: e ]).

Definition x86_linearization_params : linearization_params :=
  {|
    lp_tmp                  := "RAX"%string;
    lp_allocate_stack_frame := x86_allocate_stack_frame;
    lp_free_stack_frame     := x86_free_stack_frame;
    lp_ensure_rsp_alignment := x86_ensure_rsp_alignment;
    lp_lassign              := x86_lassign;
  |}.
