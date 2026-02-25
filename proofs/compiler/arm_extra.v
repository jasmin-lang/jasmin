From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.

Require Import
  compiler_util
  expr
  fexpr
  sopn
  utils.
Require Export
  arch_decl
  arch_extra
  arm_params_core.
Require Import
  arm_decl
  arm_instr_decl
  arm.


#[only(eqbOK)] derive
Variant arm_extra_op : Type :=
  | Oarm_swap of wsize
  | Oarm_add_large_imm
  | Osmart_li of wsize    (* Load an immediate to a register. *)
  | Osmart_li_cc of wsize (* Conditional [Osmart_li]. *)
.

HB.instance Definition _ := hasDecEq.Build arm_extra_op arm_extra_op_eqb_OK.

#[ export ]
Instance eqTC_arm_extra_op : eqTypeC arm_extra_op :=
  { ceqP := arm_extra_op_eqb_OK }.

(* Extra instructions descriptions. *)

Local Notation E n := (sopn.ADExplicit n sopn.ACR_any).

(* [conflicts] ensures that the returned register is distinct from the first
   argument. *)
Definition Oarm_add_large_imm_instr : instruction_desc :=
  let ty := aword arm_reg_size in
  let cty := cword arm_reg_size in
  let ctin := [:: cty; cty] in
  let semi := fun (x y : word arm_reg_size) => (x + y)%w in
  {| str    := (fun _ => "add_large_imm"%string)
   ; tin    := [:: ty; ty]
   ; i_in   := [:: E 1; E 2]
   ; tout   := [:: ty]
   ; i_out  := [:: E 0]
   ; conflicts := [:: (APout 0, APin 0)]
   ; semi   := fun _ => sem_prod_ok ctin semi
   ; semu   := fun _ => @values.vuincl_app_sopn_v ctin [:: cty] (sem_prod_ok ctin semi) refl_equal
   ; i_safe := [::]
   ; i_valid := true
   ; i_safe_wf := refl_equal
   ; i_semi_errty :=  fun _ _ => sem_prod_ok_error (tin:=ctin) semi _
   ; i_semi_safe := fun _ _ => values.sem_prod_ok_safe (tin:=ctin) semi
 |}.

Definition smart_li_instr (ws : wsize) : instruction_desc :=
  mk_instr_desc_safe
    (pp_sz "smart_li" ws)
    [:: aword ws ] [:: E 0 ]
    [:: aword ws ] [:: E 1 ]
    (fun x => x)
    true.

Definition smart_li_instr_cc (ws : wsize) : instruction_desc :=
  mk_instr_desc_safe
    (pp_sz "smart_li_cc" ws)
    [:: aword ws; abool; aword ws ] [:: E 0; E 2; E 1 ]
    [:: aword ws ] [:: E 1 ]
    (fun x b y => if b then x else y)
    true.

Definition get_instr_desc (o: arm_extra_op) : instruction_desc :=
  match o with
  | Oarm_swap sz => Oswap_instr (aword sz)
  | Oarm_add_large_imm => Oarm_add_large_imm_instr
  | Osmart_li ws => smart_li_instr ws
  | Osmart_li_cc ws => smart_li_instr_cc ws
  end.

(* Without priority 1, this instance is selected when looking for an [asmOp],
 * meaning that extra ops are the only possible ops. With that priority,
 * [arch_extra.asm_opI] is selected first and we have both base and extra ops.
*)
#[ export ]
Instance arm_extra_op_decl : asmOp arm_extra_op | 1 :=
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

Definition li_condition_modified ii :=
  error
    ii
    "assignment needs to be split but condition is modified by assignment".
End E.

Definition asm_args_of_opn_args
  : seq ARMFopn_core.opn_args -> seq (asm_op_msb_t * lexprs * rexprs) :=
  map (fun '(les, aop, res) => ((None, aop), les, res)).

Definition uncons X (ii : instr_info) (xs : seq X) : cexec (X * seq X) :=
  if xs is x :: xs
  then ok (x, xs)
  else Error (E.internal_error ii "invalid uncons").

Definition uncons_LLvar
  (ii : instr_info) (les : seq lexpr) : cexec (var_i * seq lexpr) :=
  if les is LLvar x :: les
  then ok (x, les)
  else Error (E.internal_error ii "invalid lvals").

Definition uncons_rvar
  (ii : instr_info) (res : seq rexpr) : cexec (var_i * seq rexpr) :=
  if res is Rexpr (Fvar x) :: res
  then ok (x, res)
  else Error (E.internal_error ii "invalid arguments").

Definition uncons_wconst
  (ii : instr_info) (res : seq rexpr) : cexec (Z * seq rexpr) :=
  if res is Rexpr (Fapp1 (Oword_of_int _) (Fconst imm)) :: res'
  then ok (imm, res')
  else Error (E.internal_error ii "invalid arguments").

Definition smart_li_args ii ws les res :=
  (* FIXME: This check is because [ARMFopn_core.li] only works with register
     size, it should not be the case. *)
  Let _ :=
    assert
      (ws == reg_size)
      (E.error ii "smart immediate assignment is only valid for u32 variables")
  in
  Let: (x, les) := uncons_LLvar ii les in
  Let _ :=
    assert (convertible (vtype (v_var x)) (aword ws)) (E.internal_error ii "invalid type")
  in
  Let _ := assert (nilp les) (E.internal_error ii "invalid lvals") in
  Let: (imm, res) := uncons_wconst ii res in
  ok (x, imm, res).

Definition assemble_smart_li ii ws les res :=
  Let: (x, imm, _) := smart_li_args ii ws les res in
  ok (asm_args_of_opn_args (ARMFopn_core.li x imm)).

Definition assemble_smart_li_cc
  ii ws les res : cexec (seq (asm_op_msb_t * lexprs * rexprs)) :=
  Let: (x, imm, res) := smart_li_args ii ws les res in
  Let: (cond, res) := uncons ii res in
  Let _ :=
    assert (~~ Sv.mem x (free_vars_r cond)) (E.li_condition_modified ii)
  in
  Let: (oldx, _) := uncons_rvar ii res in
  let mk '(les, ARM_op mn opts, res) :=
    let opts := set_is_conditional opts in
    ok ((None, ARM_op mn opts), les, res ++ [:: cond; rvar oldx ])
  in
  mapM mk (ARMFopn_core.li x imm).

Definition assemble_extra
           (ii: instr_info)
           (o: arm_extra_op)
           (outx: lexprs)
           (inx: rexprs)
           : cexec (seq (asm_op_msb_t * lexprs * rexprs)) :=
  match o with
  | Oarm_swap sz =>
    if (sz == U32)%CMP then
      match outx, inx with
      | [:: LLvar x; LLvar y], [:: Rexpr (Fvar z); Rexpr (Fvar w)] =>
        (* x, y = swap(z, w) *)
        Let _ := assert (v_var x != v_var w)
          (E.internal_error ii "bad arm swap : x = w") in
        Let _ := assert (v_var y != v_var x)
          (E.internal_error ii "bad arm swap : y = x") in
        Let _ := assert (all (fun (x:var_i) => convertible (vtype x) (aword U32)) [:: x; y; z; w])
          (E.error ii "arm swap only valid for register of type u32") in

        ok [:: ((None, ARM_op EOR default_opts), [:: LLvar x], [:: Rexpr (Fvar z); Rexpr (Fvar w)]);
               (* x = z ^ w *)
               ((None, ARM_op EOR default_opts), [:: LLvar y], [:: Rexpr (Fvar x); Rexpr (Fvar w)]);
               (* y = x ^ w = z ^ w ^ w = z *)
               ((None, ARM_op EOR default_opts), [:: LLvar x], [:: Rexpr (Fvar x); Rexpr (Fvar y)])
           ]   (* x = x ^ y = z ^ w ^ z = w *)
      | _, _ => Error (E.error ii "only register is accepted on source and destination of the swap instruction on arm")
      end
    else
      Error (E.error ii "arm swap only valid for register of type u32")
  | Oarm_add_large_imm =>
    match outx, inx with
    | [:: LLvar x], [:: Rexpr (Fvar y); Rexpr (Fapp1 (Oword_of_int ws) (Fconst imm))] =>
      Let _ := assert (v_var x != v_var y)
         (E.internal_error ii "bad arm_add_large_imm: invalid register") in
      Let _ := assert (all (fun (x:var_i) => convertible (vtype x) (aword U32)) [:: x; y])
          (E.error ii "arm swap only valid for register of type u32") in
      ok (asm_args_of_opn_args (ARMFopn_core.smart_addi x y imm))
    | _, _ =>
      Error (E.internal_error ii "bad arm_add_large_imm: invalid args or dests")
    end
  | Osmart_li ws => assemble_smart_li ii ws outx inx
  | Osmart_li_cc ws => assemble_smart_li_cc ii ws outx inx
  end.

#[ export ]
Instance arm_extra {atoI : arch_toIdent} :
  asm_extra register register_ext xregister rflag condt arm_op arm_extra_op :=
  { to_asm := assemble_extra }.

(* This concise name is convenient in OCaml code. *)
Definition arm_extended_op {atoI : arch_toIdent} :=
  @extended_op _ _ _ _ _ _ _ arm_extra.

Definition Oarm {atoI : arch_toIdent} o : @sopn arm_extended_op _ := Oasm (BaseOp (None, o)).
