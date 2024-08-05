Require Import
  expr
  fexpr
  label
  linear
  stack_zero_strategy
  arch_decl
  arch_extra
  x86_decl
  x86_extra
  x86_instr_decl.
Require Import compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section STACK_ZEROIZATION.

Context {atoI : arch_toIdent}.

Let vflags := map (fun f => mk_var_i (to_var f)) [:: OF; CF; SF; PF; ZF ].
Let flags_lexprs := map LLvar vflags.

Section RSP.

Context (rspn : Ident.ident).
Let rspi := vid rspn.

Let vlocal {t T} {_ : ToString t T} {_ : ToIdent T} (x : T) : gvar :=
  mk_lvar (mk_var_i (to_var x)).
(* TODO: the gvar versions are not used, we should define only the var_i *)
Let tmp : gvar := vlocal RSI.
Let off : gvar := vlocal RDI.
Let vlr : gvar := vlocal XMM2.

Let rsp : gvar := mk_lvar rspi.
Let zf : gvar := vlocal ZF.
Let tmpi : var_i := gv tmp.
Let offi : var_i := gv off.
Let vlri : var_i := gv vlr.
Let zfi : var_i := gv zf.

Notation rvar v := (Rexpr (Fvar v)) (only parsing).
Notation rconst ws imm := (Rexpr (fconst ws imm)) (only parsing).

Definition loop_small_cmd (lbl : label) ws_align ws (stk_max : Z) : lcmd :=
  (* tmp = rsp; *)
  let i0 := Lopn [:: LLvar tmpi ] (Ox86 (MOV U64)) [:: rvar rspi ] in

  (* rsp &= - (wsize_size ws_align); *)
  let i1 :=
    Lopn
      (flags_lexprs ++ [:: LLvar rspi ])
      (Ox86 (AND U64))
      [:: rvar rspi; rconst U64 (- wsize_size ws_align) ]
  in

  (* rsp -= stk_max *)
  let i2 :=
    Lopn
      (flags_lexprs ++ [:: LLvar rspi ])
      (Ox86 (SUB U64))
      [:: rvar rspi; rconst U64 stk_max ]
  in

  (* off = stk_max; *)
  let i3 :=
    Lopn
      [:: LLvar offi ]
      (Ox86 (MOV U64))
      [:: rconst U64 stk_max ]
  in

  (* l1: *)
  let i4 := Llabel InternalLabel lbl in

  (* ?{zf}, off = #SUB(off, wsize_size ws); *)
  let i5 :=
    Lopn
      (flags_lexprs ++ [:: LLvar offi ])
      (Ox86 (SUB U64))
      [:: rvar offi; rconst U64 (wsize_size ws) ]
  in

  (* (ws)[rsp + off] = 0; *)
  let i6 :=
    Lopn [:: Store Aligned ws rspi (Fvar offi) ] (Ox86 (MOV ws)) [:: rconst ws 0 ]
  in

  (* if (!zf) goto l1 *)
  let i7 := Lcond (Fapp1 Onot (Fvar zfi)) lbl in

  (* rsp = tmp *)
  let i8 :=
    Lopn [:: LLvar rspi ] (Ox86 (MOV U64)) [:: rvar tmpi ] in

  map (MkLI dummy_instr_info) [:: i0; i1; i2; i3; i4; i5; i6; i7; i8 ].

Definition loop_small_vars :=
  sv_of_list v_var [:: tmpi, offi & vflags].

(* FIXME: Is this comment still true?
   we read rsp first, so that we are sure that we don't modify it ; otherwise,
   we would have to add hypotheses like rsp <> XMM2 *)
Definition loop_large_cmd (lbl : label) ws_align ws (stk_max : Z) : lcmd :=
  (* tmp = rsp; *)
  let i0 := Lopn [:: LLvar tmpi ] (Ox86 (MOV U64)) [:: rvar rspi ] in

  (* ymm = #set0_ws(); *)
  let i1 := Lopn [:: LLvar vlri ] (Oasm (ExtOp (Oset0 ws))) [::] in

  (* rsp &= - (wsize_size ws_align); *)
  let i2 :=
    Lopn
      (flags_lexprs ++ [:: LLvar rspi ])
      (Ox86 (AND U64))
      [:: rvar rspi; rconst U64 (- wsize_size ws_align) ]
  in

  (* rsp -= stk_max *)
  let i3 :=
    Lopn
      (flags_lexprs ++ [:: LLvar rspi ])
      (Ox86 (SUB U64))
      [:: rvar rspi; rconst U64 stk_max ]
  in

  (* off = stk_max; *)
  let i4 :=
    Lopn [:: LLvar offi ] (Ox86 (MOV U64)) [:: rconst U64 stk_max ]
  in

  (* l1: *)
  let i5 := Llabel InternalLabel lbl in

  (* ?{zf}, off = #SUB(off, wsize_size ws); *)
  let i6 :=
    Lopn
      (flags_lexprs ++ [:: LLvar offi ])
      (Ox86 (SUB U64))
      [:: rvar offi; rconst U64 (wsize_size ws) ]
  in

  (* (ws)[rsp + off] = ymm; *)
  let i7 :=
    Lopn [:: Store Aligned ws rspi (Fvar offi) ] (Ox86 (VMOVDQU ws)) [:: rvar vlri ]
  in

  (* if (!zf) goto l1 *)
  let i8 := Lcond (Fapp1 Onot (Fvar zfi)) lbl in

  (* rsp = tmp *)
  let i9 :=
    Lopn [:: LLvar rspi ] (Ox86 (MOV U64)) [:: rvar tmpi ] in

  map (MkLI dummy_instr_info) [:: i0; i1; i2; i3; i4; i5; i6; i7; i8; i9 ].

Definition loop_large_vars :=
  sv_of_list v_var [:: vlri, tmpi, offi & vflags].

Definition x86_stack_zero_loop lbl ws_align ws stk_max :=
  if (ws <= U64)%CMP then
    (loop_small_cmd lbl ws_align ws stk_max, loop_small_vars)
  else
    (loop_large_cmd lbl ws_align ws stk_max, loop_large_vars).

(* FIXME: is the LFENCE added at the right place? *)
Definition x86_stack_zero_loopSCT lbl ws_align ws stk_max :=
  let (cmd, vars) := x86_stack_zero_loop lbl ws_align ws stk_max in
  (cmd ++ [:: MkLI dummy_instr_info (Lopn [::] (Ox86 LFENCE) [::])], vars).

Definition unrolled_small_cmd ws_align ws (stk_max : Z) : lcmd :=
  (* tmp = rsp; *)
  let i0 := Lopn [:: LLvar tmpi ] (Ox86 (MOV U64)) [:: rvar rspi ] in

  (* rsp &= - (wsize_size ws_align); *)
  let i1 :=
    Lopn
      (flags_lexprs ++ [:: LLvar rspi ])
      (Ox86 (AND U64))
      [:: rvar rspi; rconst U64 (- wsize_size ws_align) ]
  in

  (* rsp -= stk_max *)
  let i2 :=
    Lopn
      (flags_lexprs ++ [:: LLvar rspi ])
      (Ox86 (SUB U64))
      [:: rvar rspi; rconst U64 stk_max ]
  in

  (* (ws)[rsp + off] = 0; *)
  let f off :=
    Lopn
      [:: Store Aligned ws rspi (fconst U64 off) ]
      (Ox86 (MOV ws))
      [:: rconst ws 0 ]
  in

  let offs := map (fun x => x * wsize_size ws)%Z (rev (ziota 0 (stk_max / wsize_size ws))) in

  (* rsp = tmp *)
  let i3 :=
    Lopn [:: LLvar rspi ] (Ox86 (MOV U64)) [:: rvar tmpi ] in

  map (MkLI dummy_instr_info) [:: i0, i1, i2 & map f offs ++ [:: i3]].

Definition unrolled_small_vars :=
  sv_of_list v_var [:: tmpi & vflags].

Definition unrolled_large_cmd ws_align ws (stk_max : Z) : lcmd :=
  (* tmp = rsp; *)
  let i0 := Lopn [:: LLvar tmpi ] (Ox86 (MOV U64)) [:: rvar rspi ] in

  (* ymm = #set0_ws(); *)
  let i1 := Lopn [:: LLvar vlri ] (Oasm (ExtOp (Oset0 ws))) [::] in

  (* rsp &= - (wsize_size ws_align); *)
  let i2 :=
    Lopn
      (flags_lexprs ++ [:: LLvar rspi ])
      (Ox86 (AND U64))
      [:: rvar rspi; rconst U64 (- wsize_size ws_align) ]
  in

  (* rsp -= stk_max *)
  let i3 :=
    Lopn
      (flags_lexprs ++ [:: LLvar rspi ])
      (Ox86 (SUB U64))
      [:: rvar rspi; rconst U64 stk_max ]
  in

  (* (ws)[rsp + off] = ymm; *)
  let f off :=
    Lopn
      [:: Store Aligned ws rspi (fconst U64 off) ]
      (Ox86 (VMOVDQU ws))
      [:: rvar vlri ]
  in

  let offs := map (fun x => x * wsize_size ws)%Z (rev (ziota 0 (stk_max / wsize_size ws))) in

  (* rsp = tmp *)
  let i4 :=
    Lopn [:: LLvar rspi ] (Ox86 (MOV U64)) [:: rvar tmpi ] in

  map (MkLI dummy_instr_info) [:: i0, i1, i2, i3 & map f offs ++ [:: i4]].

Definition unrolled_large_vars :=
  sv_of_list v_var [:: vlri, tmpi & vflags].

Definition x86_stack_zero_unrolled ws_align ws stk_max :=
  if (ws <= U64)%CMP then
    (unrolled_small_cmd ws_align ws stk_max, unrolled_small_vars)
  else
    (unrolled_large_cmd ws_align ws stk_max, unrolled_large_vars).

End RSP.

Definition x86_stack_zero_cmd
  (szs : stack_zero_strategy) rspn (lbl : label) ws_align ws (stk_max : Z) : cexec (lcmd * Sv.t) :=
  match szs with
  | SZSloop => ok (x86_stack_zero_loop rspn lbl ws_align ws stk_max)
  | SZSloopSCT => ok (x86_stack_zero_loopSCT rspn lbl ws_align ws stk_max)
  | SZSunrolled => ok (x86_stack_zero_unrolled rspn ws_align ws stk_max)
  end.

End STACK_ZEROIZATION.
