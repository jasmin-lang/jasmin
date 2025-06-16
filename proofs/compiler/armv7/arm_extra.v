From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.

From lang Require Import
  expr
  fexpr
  sopn
  utils.
From arch Require Export
  arch_decl
  arch_extra.
From compiler Require Import
  compiler_util.
Require Import
  arm_decl
  arm_instr_decl
  arm.
Require Export
  arm_params_core.


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
  let ty := sword arm_reg_size in
  let tin := [:: ty; ty] in
  let semi := fun (x y : word arm_reg_size) => (x + y)%R in
  {| str    := (fun _ => "add_large_imm"%string)
   ; tin    := tin
   ; i_in   := [:: E 1; E 2]
   ; tout   := [:: ty]
   ; i_out  := [:: E 0]
   ; conflicts := [:: (APout 0, APin 0)]
   ; semi   := sem_prod_ok tin semi
   ; semu   := @values.vuincl_app_sopn_v [:: ty; ty] [:: ty] (sem_prod_ok tin semi) refl_equal
   ; i_safe := [::]
   ; i_valid := true
   ; i_safe_wf := refl_equal
   ; i_semi_errty :=  fun _ => sem_prod_ok_error (tin:=tin) semi _
   ; i_semi_safe := fun _ => values.sem_prod_ok_safe (tin:=tin) semi
 |}.

Definition smart_li_instr (ws : wsize) : instruction_desc :=
  mk_instr_desc_safe
    (pp_sz "smart_li" ws)
    [:: sword ws ] [:: E 0 ]
    [:: sword ws ] [:: E 1 ]
    (fun x => x)
    true.

Definition smart_li_instr_cc (ws : wsize) : instruction_desc :=
  mk_instr_desc_safe
    (pp_sz "smart_li_cc" ws)
    [:: sword ws; sbool; sword ws ] [:: E 0; E 2; E 1 ]
    [:: sword ws ] [:: E 1 ]
    (fun x b y => if b then x else y)
    true.

Definition get_instr_desc (o: arm_extra_op) : instruction_desc :=
  match o with
  | Oarm_swap sz => Oswap_instr (sword sz)
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

Definition asm_args_of_opn_args
  : seq ARMFopn_core.opn_args -> seq (asm_op_msb_t * lexprs * rexprs) :=
  map (fun '(les, aop, res) => ((None, aop), les, res)).

Definition uncons X (xs : seq X) : result (bool * string) (X * seq X) :=
  if xs is x :: xs
  then ok (x, xs)
  else Error (true, "invalid uncons"%string).

Definition uncons_LLvar
  (les : seq lexpr) : result (bool * string) (var_i * seq lexpr) :=
  if les is LLvar x :: les
  then ok (x, les)
  else Error (true, "invalid lvals"%string).

Definition uncons_rvar
  (res : seq rexpr) : result (bool * string) (var_i * seq rexpr) :=
  if res is Rexpr (Fvar x) :: res
  then ok (x, res)
  else Error (true, "invalid arguments"%string).

Definition uncons_wconst
  (res : seq rexpr) : result (bool * string) (Z * seq rexpr) :=
  if res is Rexpr (Fapp1 (Oword_of_int _) (Fconst imm)) :: res'
  then ok (imm, res')
  else Error (true, "invalid arguments"%string).

Definition smart_li_args ws les res :=
  (* FIXME: This check is because [ARMFopn_core.li] only works with register
     size, it should not be the case. *)
  Let _ :=
    assert
      (ws == reg_size)
      (false, "smart immediate assignment is only valid for u32 variables"%string)
  in
  Let: (x, les) := uncons_LLvar les in
  Let _ :=
    assert (vtype (v_var x) == sword ws) (true, "invalid type"%string)
  in
  Let _ := assert (nilp les) (true, "invalid lvals"%string) in
  Let: (imm, res) := uncons_wconst res in
  ok (x, imm, res).

Definition assemble_smart_li ws les res :=
  Let: (x, imm, _) := smart_li_args ws les res in
  ok (asm_args_of_opn_args (ARMFopn_core.li x imm)).

Definition assemble_smart_li_cc
  ws les res : result (bool * string) (seq (asm_op_msb_t * lexprs * rexprs)) :=
  Let: (x, imm, res) := smart_li_args ws les res in
  Let: (cond, res) := uncons res in
  Let _ :=
    assert (~~ Sv.mem x (free_vars_r cond))
           (false, "assignment needs to be split but condition is modified by assignment"%string)
  in
  Let: (oldx, _) := uncons_rvar res in
  let mk '(les, ARM_op mn opts, res) :=
    let opts := set_is_conditional opts in
    ok ((None, ARM_op mn opts), les, res ++ [:: cond; rvar oldx ])
  in
  mapM mk (ARMFopn_core.li x imm).

Definition assemble_extra
           (_ii: instr_info)
           (o: arm_extra_op)
           (outx: lexprs)
           (inx: rexprs)
           : result (bool * string) (seq (asm_op_msb_t * lexprs * rexprs)) :=
  match o with
  | Oarm_swap sz =>
    if (sz == U32)%CMP then
      match outx, inx with
      | [:: LLvar x; LLvar y], [:: Rexpr (Fvar z); Rexpr (Fvar w)] =>
        (* x, y = swap(z, w) *)
        Let _ := assert (v_var x != v_var w)
          (true, "bad arm swap : x = w"%string) in
        Let _ := assert (v_var y != v_var x)
          (true, "bad arm swap : y = x"%string) in
        Let _ := assert (all (fun (x:var_i) => vtype x == sword U32) [:: x; y; z; w])
          (false, "arm swap only valid for register of type u32")%string in

        ok [:: ((None, ARM_op EOR default_opts), [:: LLvar x], [:: Rexpr (Fvar z); Rexpr (Fvar w)]);
               (* x = z ^ w *)
               ((None, ARM_op EOR default_opts), [:: LLvar y], [:: Rexpr (Fvar x); Rexpr (Fvar w)]);
               (* y = x ^ w = z ^ w ^ w = z *)
               ((None, ARM_op EOR default_opts), [:: LLvar x], [:: Rexpr (Fvar x); Rexpr (Fvar y)])
           ]   (* x = x ^ y = z ^ w ^ z = w *)
      | _, _ => Error (false, "only register is accepted on source and destination of the swap instruction on arm")%string
      end
    else
      Error (false, "arm swap only valid for register of type u32")%string
  | Oarm_add_large_imm =>
    match outx, inx with
    | [:: LLvar x], [:: Rexpr (Fvar y); Rexpr (Fapp1 (Oword_of_int ws) (Fconst imm))] =>
      Let _ := assert (v_var x != v_var y)
         (true, "bad arm_add_large_imm: invalid register"%string) in
      Let _ := assert (all (fun (x:var_i) => vtype x == sword U32) [:: x; y])
          (false, "arm swap only valid for register of type u32"%string) in
      ok (asm_args_of_opn_args (ARMFopn_core.smart_addi x y imm))
    | _, _ =>
      Error (true, "bad arm_add_large_imm: invalid args or dests"%string)
    end
  | Osmart_li ws => assemble_smart_li ws outx inx
  | Osmart_li_cc ws => assemble_smart_li_cc ws outx inx
  end.

#[ export ]
Instance arm_extra {atoI : arch_toIdent} :
  asm_extra register register_ext xregister rflag condt arm_op arm_extra_op :=
  { to_asm := assemble_extra }.

(* This concise name is convenient in OCaml code. *)
Definition arm_extended_op {atoI : arch_toIdent} :=
  @extended_op _ _ _ _ _ _ _ arm_extra.

Definition Oarm {atoI : arch_toIdent} o : @sopn arm_extended_op _ := Oasm (BaseOp (None, o)).
