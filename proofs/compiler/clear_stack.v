From mathcomp Require Import
  all_ssreflect
  all_algebra.
Require Import ZArith.

Require Import
  compiler_util
  expr
  label
  linear
  sopn
  utils
  word
  wsize.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CLEAR_STACK.

(* Architecture-specific parameters. *)

Context
  {pd : PointerData}
  (asm_op : Type)
  (asmop : asmOp asm_op)
  (max_ws : wsize)
  (set0 : sopn)
  (instr_addf : var_i -> var_i -> seq lval * sopn)
  (rsp r off vlr zf : gvar).

Context
  (lower_cmd : cmd -> cmd)
  (linearize_cmd : cmd -> lcmd).


Definition clear_stack_loop : cmd :=
  let ri := gv r in
  let offi := gv off in
  let vlri := gv vlr in
  let zfi := gv zf in

  (* r = rsp; *)
  let i0 := Cassgn (Lvar ri) AT_none (sword Uptr) (Pvar rsp) in

  (* ymm = #set0_256(); *)
  let i1 := Copn [:: Lvar vlri ] AT_none set0 [::] in

  let al_const :=
    Papp1 (Oword_of_int Uptr) (Pconst (wsize_size max_ws))
  in

  let aligned_r :=
    Papp2 (Oland Uptr) (Pvar r) (Papp1 (Oneg (Op_w Uptr)) al_const)
  in

  (* r &= -32; *)
  let i2 := Cassgn (Lvar ri) AT_none (sword Uptr) aligned_r in

  let c :=
    Papp1 (Oword_of_int Uptr) (wsize_size max_ws)
  in

  (* off = -max_size; *)
  let i3 :=
    Cassgn (Lvar offi) AT_none (sword Uptr) (Papp1 (Oneg (Op_w Uptr)) c)
  in

  (* (u256)[r + off] = ymm; *)
  let i4a :=
    Cassgn (Lmem U256 ri (Pvar off)) AT_none (sword max_ws) (Pvar vlr)
  in

  let '(lvs, add_sopn) := instr_addf zfi offi in

  (* ?{zf}, off = #ADD(off, 32); *)
  let i4b :=
    Copn lvs AT_none add_sopn [:: Pvar off; Pconst 32 ]
  in

  let i4 :=
    Cwhile NoAlign (map (MkI xH) [:: i4a; i4b ]) (Papp1 Onot (Pvar zf)) [::]
  in

  map (MkI xH) [:: i0; i1; i2; i3; i4 ].

Definition fd_clear_stack (lfd : lfundef) : lfundef :=
  let c := linearize_cmd (lower_cmd clear_stack_loop) in
  {|
    lfd_info := lfd_info lfd;
    lfd_align := lfd_align lfd;
    lfd_tyin := lfd_tyin lfd;
    lfd_arg := lfd_arg lfd;
    lfd_tyout := lfd_tyout lfd;
    lfd_total_stack := lfd_total_stack lfd;
    lfd_res := lfd_res lfd;
    lfd_export := lfd_export lfd;
    lfd_callee_saved := lfd_callee_saved lfd;
    lfd_body := lfd_body lfd ++ c;
  |}.

Definition prog_clear_stack (lp : lprog) : lprog :=
  map_lprog fd_clear_stack lp.

End CLEAR_STACK.
