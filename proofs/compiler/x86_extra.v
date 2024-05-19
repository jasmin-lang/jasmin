(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import Utf8.
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

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Variant x86_extra_op : Type :=
| Oset0     of wsize  (* set register + flags to 0 (implemented using XOR x x or VPXOR x x) *)
| Oconcat128          (* concatenate 2 128 bits word into 1 256 word register *)   
| Ox86MOVZX32
| Ox86MULX  of wsize
| Ox86MULX_hi of wsize

| Ox86SLHinit
| Ox86SLHupdate
| Ox86SLHmove
| Ox86SLHprotect of wsize

.

Scheme Equality for x86_extra_op.

Lemma x86_extra_op_eq_axiom : Equality.axiom x86_extra_op_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_x86_extra_op_dec_bl
       internal_x86_extra_op_dec_lb).
Qed.

Definition x86_extra_op_eqMixin     := Equality.Mixin x86_extra_op_eq_axiom.
Canonical  x86_extra_op_eqType      := Eval hnf in EqType x86_extra_op x86_extra_op_eqMixin.

Local Notation E n := (ADExplicit n None).

Section Section.
Context {atoI : arch_toIdent}.

Definition Oset0_instr sz  :=
  if (sz <= U64)%CMP then 
    mk_instr_desc (pp_sz "set0" sz)
             [::] [::]
             (b5w_ty sz) (map sopn_arg_desc implicit_flags ++ [:: E 0])
             (let vf := Some false in
              let vt := Some true in
              ok (::vf, vf, vf, vt, vt & (0%R: word sz)))
             [::]
  else 
    mk_instr_desc (pp_sz "set0" sz)
             [::] [::]  
             (w_ty sz) [::E 0] 
             (ok (0%R: word sz)) [::].

Definition Oconcat128_instr := 
  mk_instr_desc (pp_s "concat_2u128") 
           [:: sword128; sword128 ] [:: E 1; E 2] 
           [:: sword256] [:: E 0] 
           (λ h l : u128, ok (make_vec U256 [::l;h]))
           [::].

Definition Ox86MOVZX32_instr := 
  mk_instr_desc (pp_s "MOVZX32") 
           [:: sword32] [:: E 1] 
           [:: sword64] [:: E 0] 
           (λ x : u32, ok (zero_extend U64 x)) 
           [::].

Definition x86_MULX sz (v1 v2: word sz) : ex_tpl (w2_ty sz sz) :=
  Let _ := check_size_32_64 sz in
  ok (wumul v1 v2).

Definition Ox86MULX_instr sz :=
   let name := "MULX"%string in
   mk_instr_desc (pp_sz name sz)
        (w2_ty sz sz) [::ADImplicit (to_var RDX); E 2]
        (w2_ty sz sz) [:: E 0; E 1] (* hi, lo *)
        (@x86_MULX sz) [::].

Definition x86_MULX_hi sz (v1 v2: word sz) : ex_tpl (w_ty sz) :=
  Let _ := check_size_32_64 sz in
  ok (wmulhu v1 v2). 

Definition Ox86MULX_hi_instr sz :=
   let name := "MULX_hi"%string in
   mk_instr_desc (pp_sz name sz)
        (w2_ty sz sz) [::ADImplicit (to_var RDX); E 1]
        (w_ty sz) [:: E 0] 
        (@x86_MULX_hi sz) [::].


Definition Ox86SLHinit_str := append "Ox86_" SLHinit_str.
Definition Ox86SLHinit_instr :=
  mk_instr_desc (pp_s Ox86SLHinit_str)
      [::]
      [::]
      [:: ty_msf ]
      [:: E 0 ]
      se_init_sem
      [::].

Definition x86_se_update_sem (b:bool) (w: wmsf) : exec (wmsf * wmsf) :=
  let aux :=  wrepr Uptr (-1) in
  let w := if ~~b then aux else w in
  ok (aux, w).

Definition Ox86SLHupdate_str := append "Ox86_" SLHupdate_str.
Definition Ox86SLHupdate_instr :=
  mk_instr_desc (pp_s Ox86SLHupdate_str)
                [:: sbool; ty_msf]
                [:: E 0; E 1]
                [:: ty_msf; ty_msf]
                [:: E 2; E 1]
                x86_se_update_sem
                [::].

Definition Ox86SLHmove_str := append "Ox86_" SLHmove_str.
Definition Ox86SLHmove_instr :=
  mk_instr_desc (pp_s Ox86SLHmove_str)
      [:: ty_msf ]
      [:: E 1 ]
      [:: ty_msf ]
      [:: E 0 ]
      se_move_sem
      [::].

Definition se_protect_small_sem
  (ws:wsize) (w:word ws) (msf:word ws) : exec (sem_tuple (b5w_ty ws)) :=
   x86_OR w msf.

Definition se_protect_large_sem
  (ws:wsize) (w:word ws) (msf:wmsf) : exec (word ws * word ws) :=
   Let _ := assert (Uptr < ws )%CMP ErrType in
   let aux := wpbroadcast ws msf in
   ok (aux, wor w aux).

Definition Ox86SLHprotect_str := append "Ox86_" SLHprotect_str.
Definition Ox86SLHprotect_instr :=
  let out := map sopn_arg_desc implicit_flags ++ [:: E 0] in
  fun (ws:wsize) =>
  if (ws <= Uptr)%CMP then
     mk_instr_desc (pp_sz SLHprotect_str ws)
                  [:: sword ws; sword ws]
                  [:: E 0; E 1]
                  [:: sbool; sbool; sbool; sbool; sbool; sword ws]
                  out
                  (@se_protect_small_sem ws)
                  [::]
   else
     mk_instr_desc (pp_sz SLHprotect_str ws)
                  [:: sword ws; ty_msf]
                  [:: E 0; E 1]
                  [:: sword ws; sword ws]
                  [:: E 2; E 0]
                  (@se_protect_large_sem ws)
                  [::].

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
  | Ox86SLHprotect ws => Ox86SLHprotect_instr ws
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
                     (vtype aux == sword U64))
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
  (ws : wsize)
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * seq lexpr * seq rexpr)) :=
  if (ws <= U64)%CMP
  then ok [:: les ::= (OR ws) res ]
  else
    if (les, res) is ([:: LLvar aux; y], [:: x; msf ]) then
     (* aux = VPINSR msf 0;
        aux = VPINSR msf 1;
        aux = VINSERTI128 aux aux 1; // only for size 256
        y   = VPOR x aux
      *)
      Let _ := assert (~~(Sv.mem aux (free_vars_r x) || Sv.mem aux (free_vars_r msf)))
                      (E.se_update_arguments ii) in
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
    let op := if (sz <= U64)%CMP then (XOR sz) else (VPXOR sz) in
    Let x :=
      match rev outx with
      | LLvar x :: _ =>  ok (Rexpr (Fvar x))
      | _ => Error (E.error ii "set0 : destination is not a register")
      end in
    ok [:: outx ::= op [:: x; x ] ]
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
  | Ox86SLHprotect ws => assemble_slh_protect ii ws outx inx
  end.

#[global]
Instance eqC_x86_extra_op : eqTypeC x86_extra_op :=
  { ceqP := x86_extra_op_eq_axiom }.

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
