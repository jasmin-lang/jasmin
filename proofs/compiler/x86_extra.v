(* -------------------------------------------------------------------- *)
From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import Utf8.
Require Import compiler_util.
Require Import
  arch_decl
  expr
  fexpr
  wsize
  asm_gen.
Require Import
  x86_decl
  x86_instr_decl
  x86.
Require Export arch_extra.
Import sopn.

Module E.

Definition pass_name := "asmgen"%string.

Definition error (ii : instr_info) (msg : string) :=
  {|
    pel_msg := compiler_util.pp_s msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := Some ii;
    pel_vi := None;
    pel_pass := Some pass_name;
    pel_internal := true;
  |}.

Definition se_update_arguments (ii : instr_info) : pp_error_loc :=
  compiler_util.pp_internal_error_s_at pass_name ii "x86_update_msf arguments are invalid.".

Definition se_protect_arguments (ii : instr_info) : pp_error_loc :=
  compiler_util.pp_internal_error_s_at pass_name ii "x86_protect arguments are invalid.".

Definition se_protect_ptr (ii : instr_info) : pp_error_loc :=
  compiler_util.pp_internal_error_s_at pass_name ii "Found protect_ptr.".

End E.


(* -------------------------------------------------------------------- *)

#[only(eqbOK)] derive
Variant x86_extra_op : Type :=
| Oset0     of wsize  (* set register + flags to 0 (implemented using XOR x x or VPXOR x x) *)
| Oconcat128          (* concatenate 2 128 bits word into 1 256 word register *)
| Ox86MOVZX32
| Ox86MULX  of wsize
| Ox86MULX_hi of wsize

| Ox86SLHinit
| Ox86SLHupdate
| Ox86SLHmove
| Ox86SLHprotect of reg_kind & wsize
.

HB.instance Definition _ := hasDecEq.Build x86_extra_op x86_extra_op_eqb_OK.

Local Notation E n := (ADExplicit n ACR_any).

Section Section.
Context {atoI : arch_toIdent}.

Definition Oset0_instr sz  :=
  if (sz <= U64)%CMP then
    mk_instr_desc_safe (pp_sz "set0" sz)
             [::] [::]
             (map atype_of_ltype (b5w_ty sz)) (map sopn_arg_desc implicit_flags ++ [:: E 0])
             (let vf := Some false in
              let vt := Some true in
              (::vf, vf, vf, vt, vt & (0%R: word sz)))
              true [:: IBool true; IBool true; IBool true; IBool true; IBool true; IBool true]
  else
    mk_instr_desc_safe (pp_sz "set0" sz)
             [::] [::]
             (map atype_of_ltype (w_ty sz)) [::E 0]
             (0%R: word sz) true [:: IBool true].

Definition Oconcat128_instr :=
  mk_instr_desc_safe (pp_s "concat_2u128")
           [:: aword U128; aword U128 ] [:: E 1; E 2]
           [:: aword U256] [:: E 0]
           (λ h l : u128, make_vec U256 [::l;h])
           true [:: IBool true]. 

Definition Ox86MOVZX32_instr :=
  mk_instr_desc_safe (pp_s "MOVZX32")
           [:: aword U32] [:: E 1]
           [:: aword U64] [:: E 0]
           (λ x : u32, zero_extend U64 x)
           true [:: IBool true].

Definition x86_MULX sz (v1 v2: word sz) : tpl (w2_ty sz sz) :=
  wumul v1 v2.

Definition Ox86MULX_instr sz :=
   let name := "MULX"%string in
   mk_instr_desc_safe (pp_sz name sz)
        [:: aword sz; aword sz] [::ADImplicit (to_var RDX); E 2]
        [:: aword sz; aword sz] [:: E 0; E 1] (* hi, lo *)
        (@x86_MULX sz) (size_32_64 sz) [:: IBool true; IBool true].

Definition x86_MULX_hi sz (v1 v2: word sz) : tpl (w_ty sz) :=
  wmulhu v1 v2.

Definition Ox86MULX_hi_instr sz :=
   let name := "MULX_hi"%string in
   mk_instr_desc_safe (pp_sz name sz)
        [:: aword sz; aword sz] [::ADImplicit (to_var RDX); E 1]
        [:: aword sz] [:: E 0]
        (@x86_MULX_hi sz) (size_32_64 sz) [:: IBool true].

Definition Ox86SLHinit_str := append "Ox86_" SLHinit_str.
Definition Ox86SLHinit_instr :=
  mk_instr_desc_safe (pp_s Ox86SLHinit_str)
      [::]
      [::]
      [:: ty_msf ]
      [:: E 0 ]
      se_init_sem
      true
      [:: IBool true].

Definition x86_se_update_sem (b:bool) (w: wmsf) : wmsf * wmsf :=
  let aux :=  wrepr Uptr (-1) in
  let w := if ~~b then aux else w in
  (aux, w).

Definition Ox86SLHupdate_str := append "Ox86_" SLHupdate_str.
Definition Ox86SLHupdate_instr :=
  mk_instr_desc_safe (pp_s Ox86SLHupdate_str)
                [:: abool; ty_msf]
                [:: E 0; E 1]
                [:: ty_msf; ty_msf]
                [:: E 2; E 1]
                x86_se_update_sem
                true
                [:: IBool true; IBool true].

Definition Ox86SLHmove_str := append "Ox86_" SLHmove_str.
Definition Ox86SLHmove_instr :=
  mk_instr_desc_safe (pp_s Ox86SLHmove_str)
      [:: ty_msf ]
      [:: E 1 ]
      [:: ty_msf ]
      [:: E 0 ]
      se_move_sem
      true
      [:: IBool true].

Definition se_protect_small_sem
  (ws:wsize) (w:word ws) (msf:word ws) : (sem_ltuple (b5w_ty ws)) :=
   x86_OR w msf.

Definition se_protect_mmx_sem
  (ws:wsize) (w:word ws) (msf:word ws) : (word ws) :=
  wor w msf.

Definition se_protect_large_sem
  (ws:wsize) (w:word ws) (msf:wmsf) : word ws * word ws :=
  let aux := wpbroadcast ws msf in
  (aux, wor w aux).

Definition Ox86SLHprotect_str := append "Ox86_" SLHprotect_str.
Definition Ox86SLHprotect_instr rk :=
  let out := map sopn_arg_desc implicit_flags ++ [:: E 0] in
  fun (ws:wsize) =>
  if rk is Extra then
    mk_instr_desc_safe (pp_sz SLHprotect_str ws)
      [:: aword ws; aword ws]
      [:: E 0; E 1 ]
      [:: aword ws ]
      [:: E 0 ]
      (@se_protect_mmx_sem ws)
      (ws == reg_size)
      [:: IBool true]
  else if (ws <= Uptr)%CMP then
    mk_instr_desc_safe (pp_sz SLHprotect_str ws)
                  [:: aword ws; aword ws]
                  [:: E 0; E 1]
                  [:: abool; abool; abool; abool; abool; aword ws]
                  out
                  (@se_protect_small_sem ws)
                  true
                  [:: IBool true; IBool true; IBool true; IBool true; IBool true; IBool true]
  else
    mk_instr_desc_safe (pp_sz SLHprotect_str ws)
                  [:: aword ws; ty_msf]
                  [:: E 0; E 1]
                  [:: aword ws; aword ws]
                  [:: E 2; E 0]
                  (@se_protect_large_sem ws)
                  (Uptr < ws)%CMP
                  [:: IBool true; IBool true].

Definition get_instr_desc o :=
  match o with
  | Oset0 ws         => Oset0_instr ws
  | Oconcat128       => Oconcat128_instr
  | Ox86MOVZX32      => Ox86MOVZX32_instr
  | Ox86MULX ws      => Ox86MULX_instr ws
  | Ox86MULX_hi ws   => Ox86MULX_hi_instr ws

  | Ox86SLHinit       => Ox86SLHinit_instr
  | Ox86SLHupdate     => Ox86SLHupdate_instr
  | Ox86SLHmove       => Ox86SLHmove_instr
  | Ox86SLHprotect rk ws => Ox86SLHprotect_instr rk ws
  end.

Definition prim_string :=
  [:: ("set0"%string, primP Oset0)
    ; ("concat_2u128"%string, primM Oconcat128)
      (* Ox86MOVZX32 is ignored on purpose *)
    ; ("MULX"%string, prim_32_64 Ox86MULX)
    ; ("MULX_hi"%string, prim_32_64 Ox86MULX_hi)
    (* SLH operators are ignored on purpose. *)
  ].

Definition re_i ws (i:Z) := Rexpr (fconst ws i).
Definition re8_0 := re_i U8 0.
Definition re8_1 := re_i U8 1.

#[local] Notation "x ::= o e" := ((None, o), x, e) (at level 70, no associativity, o at level 0, only parsing).

Definition assemble_slh_init
  (les : seq lexpr) : cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  ok
    [:: [::] ::= LFENCE [::];
        les  ::= (MOV U64) [:: re_i U64 0 ]
    ].

Definition assemble_slh_update
  (ii : instr_info)
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  if (les, res) is ([:: LLvar aux; ms0 ], [:: Rexpr b; msf ])
  then
    Let _ := assert (~~(Sv.mem aux (free_vars b) || Sv.mem aux (free_vars_r msf)) &&
                      convertible (vtype aux) (aword U64))
                    (E.se_update_arguments ii) in
    let res' := [:: Rexpr (Fapp1 Onot b); Rexpr (Fvar aux); msf ] in
    ok
      [::
         [:: LLvar aux ] ::= (MOV U64) [:: re_i U64 (-1) ];
               [:: ms0 ] ::= (CMOVcc U64) res'
      ]
  else
    Error (E.se_update_arguments ii).

Definition assemble_slh_protect
  (ii : instr_info)
  (rk : reg_kind)
  (ws : wsize)
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  if (ws <= U64)%CMP then
    ok [:: les ::= (if rk is Extra then POR else OR ws) res ]
  else if (les, res) is ([:: LLvar aux; y], [:: x; msf ]) then
     (* aux = VPINSR msf 0;
        aux = VPINSR msf 1;
        aux = VINSERTI128 aux aux 1; // only for size 256
        y   = VPOR x aux
      *)
      Let _ := assert (~~(Sv.mem aux (free_vars_r x) || Sv.mem aux (free_vars_r msf)))
                      (E.se_protect_arguments ii) in
      let eaux := Rexpr (Fvar aux) in
      let laux := [:: LLvar aux] in
      ok ([::                     laux ::= (VPINSR VE64) [:: eaux; msf; re8_0]       ;
                                  laux ::= (VPINSR VE64) [:: eaux; msf; re8_1]       ] ++
          (if ws == U256 then [:: laux ::= (VINSERTI128) [:: eaux; eaux; re8_1]] else [::]) ++
          [::                   [:: y] ::= (VPOR ws)     [:: x; eaux]])
  else Error (E.se_protect_arguments ii).

Definition assemble_slh_move
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  let lmmx := if les is [:: LLvar x ] then is_regx x else false in
  let rmmx := if res is [:: Rexpr (Fvar x) ] then is_regx x else false in
  let op := if lmmx || rmmx then MOVX else MOV in
  ok [:: les ::= (op Uptr) res ].

Definition assemble_extra ii o outx inx : cexec (seq (asm_op_msb_t * lexprs * rexprs)) :=
  match o with
  | Oset0 sz =>
    let op :=
      if (sz <= U64)%CMP then
        if sz == U64 then (Some U64, XOR U32)
        else (None, XOR sz)
      else (None, VPXOR sz) in
    Let x :=
      match rev outx with
      | LLvar x :: _ =>  ok (Rexpr (Fvar x))
      | _ => Error (E.error ii "set0 : destination is not a register")
      end in
    ok [:: (op, outx, [:: x; x ]) ]
  | Ox86MOVZX32 =>
    Let _ :=
      match outx with
      | [:: LLvar _ ] =>  ok tt
      | _ => Error (E.error ii "Ox86MOVZX32: destination is not a register")
      end in
    ok [:: outx ::= (MOV U32) inx ]
  | Oconcat128 =>
    Let inx :=
      match inx with
      | [:: h; Rexpr (Fvar _) as l] => ok [:: l; h; re8_1]
      |  _ => Error (E.error ii "Oconcat: assert false")
      end in
    ok [:: outx ::= VINSERTI128 inx ]
  | Ox86MULX sz =>
    Let outx :=
      match outx with
      | [:: LLvar hi as h; LLvar lo as l ] =>
          Let _ := assert (v_var lo != v_var hi) (E.error ii "Ox86MULX: lo = hi") in
          ok [:: l; h]
      | _ => Error (E.error ii "Ox86MULX: assert false")
      end in
    ok [:: outx ::= (MULX_lo_hi sz) inx]

  | Ox86MULX_hi sz =>
    Let outx :=
      match outx with
      | [:: LLvar hi] => ok [::LLvar hi; LLvar hi]
      | _ => Error (E.error ii "Ox86MULX_hi: assert false")
      end in
    ok [:: outx ::= (MULX_lo_hi sz) inx]

  | Ox86SLHinit => assemble_slh_init outx
  | Ox86SLHupdate => assemble_slh_update ii outx inx
  | Ox86SLHmove => assemble_slh_move outx inx
  | Ox86SLHprotect rk ws => assemble_slh_protect ii rk ws outx inx
  end.

#[global]
Instance eqC_x86_extra_op : eqTypeC x86_extra_op :=
  { ceqP := x86_extra_op_eqb_OK }.

(* Without priority 1, this instance is selected when looking for an [asmOp],
   meaning that extra ops are the only possible ops. With that priority,
   [arch_extra.asm_opI] is selected first and we have both base and extra ops.
*)
#[global]
Instance x86_extra_op_decl : asmOp x86_extra_op | 1 :=
  { asm_op_instr := get_instr_desc;
    prim_string := prim_string }.

#[global]
Instance x86_extra : asm_extra register register_ext xmm_register rflag condt x86_op x86_extra_op :=
  { to_asm := assemble_extra }.

(* This concise name is convenient in OCaml code. *)
Definition x86_extended_op :=
  @extended_op _ _ _ _ _ _ _ x86_extra.

Definition Ox86 o : @sopn x86_extended_op _ := Oasm (BaseOp (None, o)).

End Section.
