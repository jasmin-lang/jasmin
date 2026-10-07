(* ARMv8-A (AArch64) extra (pseudo-)operations, expanded into base
   instructions at assembly generation. *)

From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.

Require Import
  compiler_util
  expr
  fexpr
  sopn
  sopn_semi
  utils.
Require Export
  arch_decl
  arch_extra
  armv8a_params_core.
Require Import
  armv8a_decl
  armv8a_instr_decl
  armv8a.


#[only(eqbOK)] derive
Variant armv8a_extra_op : Type :=
  | Oarmv8a_swap of wsize
  | Oarmv8a_add_large_imm
  | Oarmv8a_smart_li of wsize (* Load an immediate to a register. *)

  (* Speculative execution operators. *)
  | Oarmv8a_SLHinit
  | Oarmv8a_SLHupdate
  | Oarmv8a_SLHmove
  | Oarmv8a_SLHprotect of wsize
.

HB.instance Definition _ := hasDecEq.Build armv8a_extra_op armv8a_extra_op_eqb_OK.

#[ export ]
Instance eqTC_armv8a_extra_op : eqTypeC armv8a_extra_op :=
  { ceqP := armv8a_extra_op_eqb_OK }.

(* Extra instructions descriptions. *)

Local Notation E n := (sopn.ADExplicit n sopn.ACR_any).

(* [conflicts] ensures that the returned register is distinct from the first
   argument. *)
Definition Oarmv8a_add_large_imm_instr : instruction_desc :=
  let ty := aword armv8a_reg_size in
  let cty := eval_atype ty in
  let ctin := [:: cty; cty] in
  let semi := fun (x y : word armv8a_reg_size) => (x + y)%w in
  {| str    := (fun _ => "add_large_imm"%string)
   ; tin    := [:: ty; ty]
   ; i_in   := [:: E 1; E 2]
   ; tout   := [:: ty]
   ; i_out  := [:: E 0]
   ; conflicts := [:: (APout 0, APin 0)]
   ; i_semi_total := semi
   ; i_safe := [::]
   ; i_err := ErrArith
   ; i_init := [:: IBool true ]
   ; i_valid := true
   ; i_doit := DOIT
   ; i_wf := refl_equal
   ; semu   := @values.vuincl_app_sopn_v ctin [:: cty]
                 (@mk_semi _ ctin [:: cty] [::] ErrArith [:: IBool true ] semi) refl_equal
 |}.

Definition smart_li_instr (ws : wsize) : instruction_desc :=
  mk_instr_desc_safe
    (pp_sz "smart_li" ws)
    [:: aword ws ] [:: E 0 ]
    [:: aword ws ] [:: E 1 ]
    (fun x => x)
    [:: IBool true ] true DOIT.

(* Speculative execution operators, expanded at assembly generation
   ([assemble_slh_*] below). The misspeculation flag is 0 when not
   misspeculating and -1 otherwise.
   An operator is DOIT when its expansion only uses DOIT instructions: [init]
   and [protect] contain barriers, which are not. *)

Definition Oarmv8a_SLHinit_instr : instruction_desc :=
  mk_instr_desc_safe (pp_s (append "Oarmv8a_" SLHinit_str))
    [::] [::]
    [:: ty_msf ] [:: E 0 ]
    se_init_sem
    [:: IBool true ] true NOT_DOIT.

Definition armv8a_se_update_sem (b : bool) (msf : wmsf) : wmsf * wmsf :=
  let aux := wrepr msf_size (-1) in
  (aux, if b then msf else aux).

(* The temporary [aux] is written before [msf] is read: [conflicts] ensures
   that they are distinct registers. *)
Definition Oarmv8a_SLHupdate_instr : instruction_desc :=
  let ctin := [:: cbool; cty_msf ] in
  let ctout := [:: cty_msf; cty_msf ] in
  {| str    := pp_s (append "Oarmv8a_" SLHupdate_str)
   ; tin    := [:: abool; ty_msf ]
   ; i_in   := [:: E 3; E 1 ]
   ; tout   := [:: ty_msf; ty_msf ]
   ; i_out  := [:: E 2; E 0 ]
   ; conflicts := [:: (APout 0, APin 1) ]
   ; i_semi_total := armv8a_se_update_sem
   ; i_safe := [::]
   ; i_err := ErrArith
   ; i_init := [:: IBool true; IBool true ]
   ; i_valid := true
   ; i_doit := DOIT
   ; i_wf := refl_equal
   ; semu   :=
       @values.vuincl_app_sopn_v ctin ctout
         (@mk_semi ctin ctout [::] ErrArith [:: IBool true; IBool true ]
            armv8a_se_update_sem)
         refl_equal
 |}.

Definition Oarmv8a_SLHmove_instr : instruction_desc :=
  mk_instr_desc_safe (pp_s (append "Oarmv8a_" SLHmove_str))
    [:: ty_msf ] [:: E 1 ]
    [:: ty_msf ] [:: E 0 ]
    se_move_sem
    [:: IBool true ] true DOIT.

Definition armv8a_se_protect_sem (ws : wsize) (x msf : word ws) : word ws :=
  wor x msf.

Definition Oarmv8a_SLHprotect_instr (ws : wsize) : instruction_desc :=
  mk_instr_desc_safe (pp_sz (append "Oarmv8a_" SLHprotect_str) ws)
    [:: aword ws; aword ws ] [:: E 1; E 2 ]
    [:: aword ws ] [:: E 0 ]
    (@armv8a_se_protect_sem ws)
    [:: IBool true ] ((ws == U32) || (ws == U64)) NOT_DOIT.

Definition get_instr_desc (o: armv8a_extra_op) : instruction_desc :=
  match o with
  | Oarmv8a_swap sz => Oswap_instr (aword sz)
  | Oarmv8a_add_large_imm => Oarmv8a_add_large_imm_instr
  | Oarmv8a_smart_li ws => smart_li_instr ws
  | Oarmv8a_SLHinit => Oarmv8a_SLHinit_instr
  | Oarmv8a_SLHupdate => Oarmv8a_SLHupdate_instr
  | Oarmv8a_SLHmove => Oarmv8a_SLHmove_instr
  | Oarmv8a_SLHprotect ws => Oarmv8a_SLHprotect_instr ws
  end.

(* Without priority 1, this instance is selected when looking for an [asmOp],
 * meaning that extra ops are the only possible ops. With that priority,
 * [arch_extra.asm_opI] is selected first and we have both base and extra ops.
*)
#[ export ]
Instance armv8a_extra_op_decl : asmOp armv8a_extra_op | 1 :=
  {
    asm_op_instr := get_instr_desc;
    prim_string := [::];
  }.

Module E.

Definition pass_name := "asmgen"%string.

Definition internal_error (ii : instr_info) (msg : string) :=
  {|
    pel_msg := compiler_util.pp_s msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := Some ii;
    pel_vi := None;
    pel_pass := Some pass_name;
    pel_internal := true;
  |}.

Definition error (ii : instr_info) (msg : string) :=
  {|
    pel_msg := compiler_util.pp_s msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := Some ii;
    pel_vi := None;
    pel_pass := Some pass_name;
    pel_internal := false;
  |}.

End E.

Definition asm_args_of_opn_args
  : seq ARMv8AFopn_core.opn_args -> seq (asm_op_msb_t * lexprs * rexprs) :=
  map (fun '(les, aop, res) => ((None, aop), les, res)).

Definition uncons_LLvar
  (ii : instr_info) (les : seq lexpr) : cexec (var_i * seq lexpr) :=
  if les is LLvar x :: les
  then ok (x, les)
  else Error (E.internal_error ii "invalid lvals").

Definition uncons_wconst
  (ii : instr_info) (res : seq rexpr) : cexec (Z * seq rexpr) :=
  if res is Rexpr (Fapp1 (Oword_of_int _) (Fconst imm)) :: res'
  then ok (imm, res')
  else Error (E.internal_error ii "invalid arguments").

Definition smart_li_args ii ws les res :=
  (* [ARMv8AFopn_core.li] materializes immediates at the two A64 operand
     widths (X and W); other sizes have no MOVZ/MOVK form, so they are
     rejected here by design. *)
  Let _ :=
    assert
      ((ws == U64) || (ws == U32))
      (E.error ii "smart immediate assignment is only valid for u64 and u32 variables")
  in
  Let: (x, les) := uncons_LLvar ii les in
  (* After register allocation the destination is a machine register
     variable, whose type is always the full register size. *)
  Let _ :=
    assert (convertible (vtype (v_var x)) (aword reg_size)) (E.internal_error ii "invalid type")
  in
  Let _ := assert (nilp les) (E.internal_error ii "invalid lvals") in
  Let: (imm, res) := uncons_wconst ii res in
  ok (x, imm, res).

Definition assemble_smart_li ii ws les res :=
  Let: (x, imm, _) := smart_li_args ii ws les res in
  ok (asm_args_of_opn_args (ARMv8AFopn_core.li ws x imm)).

Definition barrier mn : asm_op_msb_t * lexprs * rexprs :=
  ((None, ARMv8A_op mn default_opts), [::], [::]).

Definition assemble_slh_init (les : seq lexpr) :=
  [:: barrier DSB;
      barrier ISB;
      ((None, ARMv8A_op MOV default_opts), les, [:: rconst U64 0 ]) ].

Definition assemble_slh_update ii les res :=
  if (les, res) is ([:: LLvar aux; msf' ], [:: Rexpr b; msf ])
  then
    Let _ :=
      assert
        [&& ~~ Sv.mem aux (free_vars b), ~~ Sv.mem aux (free_vars_r msf)
          & convertible (vtype aux) (aword U64) ]
        (E.internal_error ii "invalid update_msf arguments")
    in
    ok
      (asm_args_of_opn_args [:: ARMv8AFopn_core.movn U64 aux 0 0 ] ++
       [:: ((None, ARMv8A_op CSEL default_opts), [:: msf' ],
            [:: msf; rvar aux; Rexpr b ]) ])
  else Error (E.internal_error ii "invalid update_msf arguments").

(* The CSDB prevents the protected value from being used with predicted
   condition flags or data values of earlier instructions, among which the
   CSEL of [update_msf] and the load that produced it. It does not constrain
   branches (ARM DDI 0487, CSDB): a protected value must not be tested by a
   branch that reads a register (CBZ, TBZ), which the compiler does not
   emit. *)
Definition assemble_slh_protect ii ws les res :=
  if (ws == U32) || (ws == U64)
  then
    ok [:: ((None, ARMv8A_op ORR (opts_at ws)), les, res); barrier CSDB ]
  else Error (E.internal_error ii "invalid protect size").

Definition assemble_extra
           (ii: instr_info)
           (o: armv8a_extra_op)
           (outx: lexprs)
           (inx: rexprs)
           : cexec (seq (asm_op_msb_t * lexprs * rexprs)) :=
  match o with
  | Oarmv8a_swap sz =>
    if (sz == U64)%CMP then
      match outx, inx with
      | [:: LLvar x; LLvar y], [:: Rexpr (Fvar z); Rexpr (Fvar w)] =>
        (* x, y = swap(z, w) *)
        Let _ := assert (v_var x != v_var w)
          (E.internal_error ii "bad armv8a swap : x = w") in
        Let _ := assert (v_var y != v_var x)
          (E.internal_error ii "bad armv8a swap : y = x") in
        Let _ := assert (all (fun (x:var_i) => convertible (vtype x) (aword U64)) [:: x; y; z; w])
          (E.error ii "armv8a swap is only valid for registers of type u64") in

        ok [:: ((None, ARMv8A_op EOR default_opts), [:: LLvar x], [:: Rexpr (Fvar z); Rexpr (Fvar w)]);
               (* x = z ^ w *)
               ((None, ARMv8A_op EOR default_opts), [:: LLvar y], [:: Rexpr (Fvar x); Rexpr (Fvar w)]);
               (* y = x ^ w = z ^ w ^ w = z *)
               ((None, ARMv8A_op EOR default_opts), [:: LLvar x], [:: Rexpr (Fvar x); Rexpr (Fvar y)])
           ]   (* x = x ^ y = z ^ w ^ z = w *)
      | _, _ => Error (E.error ii "only registers are accepted on source and destination of the swap instruction on armv8a")
      end
    else
      Error (E.error ii "armv8a swap is only valid for registers of type u64")
  | Oarmv8a_add_large_imm =>
    match outx, inx with
    | [:: LLvar x], [:: Rexpr (Fvar y); Rexpr (Fapp1 (Oword_of_int ws) (Fconst imm))] =>
      Let _ := assert (v_var x != v_var y)
         (E.internal_error ii "bad armv8a_add_large_imm: invalid register") in
      Let _ := assert (all (fun (x:var_i) => convertible (vtype x) (aword U64)) [:: x; y])
          (E.error ii "armv8a_add_large_imm is only valid for registers of type u64") in
      ok (asm_args_of_opn_args (ARMv8AFopn_core.smart_addi x y imm))
    | _, _ =>
      Error (E.internal_error ii "bad armv8a_add_large_imm: invalid args or dests")
    end
  | Oarmv8a_smart_li ws => assemble_smart_li ii ws outx inx
  | Oarmv8a_SLHinit => ok (assemble_slh_init outx)
  | Oarmv8a_SLHupdate => assemble_slh_update ii outx inx
  | Oarmv8a_SLHmove =>
      ok [:: ((None, ARMv8A_op MOV default_opts), outx, inx) ]
  | Oarmv8a_SLHprotect ws => assemble_slh_protect ii ws outx inx
  end.

#[ export ]
Instance armv8a_extra {atoI : arch_toIdent} :
  asm_extra register register_ext xregister rflag condt armv8a_asm_op armv8a_extra_op :=
  { to_asm := assemble_extra }.

(* This concise name is convenient in OCaml code. *)
Definition armv8a_extended_op {atoI : arch_toIdent} :=
  @extended_op _ _ _ _ _ _ _ armv8a_extra.

Definition Oarmv8a {atoI : arch_toIdent} o : @sopn armv8a_extended_op _ := Oasm (BaseOp (None, o)).
