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


Variant arm_extra_op : Type :=
  | Oarm_swap of wsize
  | Oarm_add_large_imm
  | Osmart_li of wsize    (* Load an immediate to a register. *)
  | Osmart_li_cc of wsize (* Conditional [Osmart_li]. *)
  | Olarge_load of wsize & Z (* Same as LDR with an immediate offset, but the
                                offset is loaded to a register with
                                [Osmart_li]. *)
  | Olarge_store of wsize & Z
  | Olarge_load_cc of wsize & Z
  | Olarge_store_cc of wsize & Z
.

Scheme Equality for arm_extra_op.

Lemma arm_extra_op_eq_axiom : Equality.axiom arm_extra_op_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_arm_extra_op_dec_bl
       internal_arm_extra_op_dec_lb).
Qed.

HB.instance Definition _ := hasDecEq.Build arm_extra_op arm_extra_op_eq_axiom.

#[ export ]
Instance eqTC_arm_extra_op : eqTypeC arm_extra_op :=
  { ceqP := arm_extra_op_eq_axiom }.

(* Extra instructions descriptions. *)

#[local]
Notation E := (fun n => sopn.ADExplicit n None).

#[local]
Notation Ea := (fun n => sopn.ADExplicit n None).

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

Definition large_load_instr (ws : wsize) (off : Z) : instruction_desc :=
  let f x := (wrepr reg_size off, zero_extend reg_size x) in
  let semi x := ok (f x) in
  let tin := [:: sword ws ] in
  {|
    str := pp_sz "large_load" ws;
    tin := tin;
    i_in := [:: E 0 ];
    tout := [:: sreg; sreg ];
    i_out := [:: E 1; E 2 ];
    conflicts := [:: (APout 0, APin 0) ];
    semi := semi;
    semu := @values.vuincl_app_sopn_v tin [:: sreg; sreg ] semi refl_equal;
    i_safe := [::];
    i_valid := true;
    i_safe_wf := refl_equal;
    i_semi_errty :=  fun _ => sem_prod_ok_error (tin := tin) f _;
    i_semi_safe := fun _ => values.sem_prod_ok_safe (tin := tin) f;
  |}.

Definition large_load_instr_cc (ws : wsize) (off : Z) : instruction_desc :=
  let woff := wrepr reg_size off in
  let f x b old_x := (woff, if b then zero_extend reg_size x else old_x) in
  let semi x b o := ok (f x b o) in
  let tin := [:: sword ws; sbool; sreg ] in
  {|
    str := pp_sz "large_load_cc" ws;
    tin := [:: sword ws; sbool; sreg ];
    i_in := [:: E 0; Ea 3; E 2 ];
    tout := [:: sreg; sreg ];
    i_out := [:: E 1; E 2 ];
    conflicts := [:: (APout 0, APin 0) ];
    semi := semi;
    semu := @values.vuincl_app_sopn_v tin [:: sreg; sreg ] semi refl_equal;
    i_safe := [::];
    i_valid := true;
    i_safe_wf := refl_equal;
    i_semi_errty :=  fun _ => sem_prod_ok_error (tin := tin) f _;
    i_semi_safe := fun _ => values.sem_prod_ok_safe (tin := tin) f;
  |}.

Definition large_store_instr (ws : wsize) (off : Z) : instruction_desc :=
  let f x := (wrepr reg_size off, zero_extend ws x) in
  let semi x := ok (f x) in
  let tin := [:: sword ws ] in
  {|
    str := pp_sz "large_store" ws;
    tin := [:: sword ws ];
    i_in := [:: E 0 ];
    tout := [:: sreg; sword ws ];
    i_out := [:: E 1; E 2 ];
    conflicts := [:: (APout 0, APin 0) ];
    semi := semi;
    semu := @values.vuincl_app_sopn_v tin [:: sreg; sword ws ] semi refl_equal;
    i_safe := [::];
    i_valid := true;
    i_safe_wf := refl_equal;
    i_semi_errty :=  fun _ => sem_prod_ok_error (tin := tin) f _;
    i_semi_safe := fun _ => values.sem_prod_ok_safe (tin := tin) f;
  |}.

Definition large_store_instr_cc (ws : wsize) (off : Z) : instruction_desc :=
  let woff := wrepr reg_size off in
  let f x b old_x := (woff, if b then zero_extend ws x else old_x) in
  let semi x b o := ok (f x b o) in
  let tin := [:: sword ws; sbool; sword ws ] in
  {|
    str := pp_sz "large_store_cc" ws;
    tin := tin;
    i_in := [:: E 0; Ea 3; E 2 ];
    tout := [:: sreg; sword ws ];
    i_out := [:: E 1; E 2 ];
    conflicts := [:: (APout 0, APin 0) ];
    semi := semi;
    semu := @values.vuincl_app_sopn_v tin [:: sreg; sword ws ] semi refl_equal;
    i_safe := [::];
    i_valid := true;
    i_safe_wf := refl_equal;
    i_semi_errty :=  fun _ => sem_prod_ok_error (tin := tin) f _;
    i_semi_safe := fun _ => values.sem_prod_ok_safe (tin := tin) f;
  |}.

Definition get_instr_desc (o: arm_extra_op) : instruction_desc :=
  match o with
  | Oarm_swap sz => Oswap_instr (sword sz)
  | Oarm_add_large_imm => Oarm_add_large_imm_instr
  | Osmart_li ws => smart_li_instr ws
  | Osmart_li_cc ws => smart_li_instr_cc ws
  | Olarge_load ws off => large_load_instr ws off
  | Olarge_store ws off => large_store_instr ws off
  | Olarge_load_cc ws off => large_load_instr_cc ws off
  | Olarge_store_cc ws off => large_store_instr_cc ws off
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

Definition condition_err := "assignment needs to be split but".

Definition condition_modified ii :=
  error ii (append condition_err " condition is modified by it").

Definition invalid_previous ii :=
  let msg :=
    [:: "conditional"; condition_err; "previous value is invalid" ]
  in
  error ii (concat " " msg).

Definition previous_modified ii :=
  let msg :=
    [:: "conditional"; condition_err; "previous value is modified by it" ]
  in
  error ii (concat " " msg).

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

Definition uncons_Store
  (ii : instr_info)
  (les : seq lexpr) :
  cexec (aligned * wsize * var_i * fexpr * seq lexpr) :=
  if les is Store al ws xbase e :: les
  then ok (al, ws, xbase, e, les)
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

Definition uncons_Load
  (ii : instr_info)
  (res : seq rexpr) :
  (cexec (aligned * wsize * var_i * fexpr * seq rexpr)) :=
  if res is Load al ws xbase eoff :: res'
  then ok (al, ws, xbase, eoff, res')
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
    assert (vtype (v_var x) == sword ws) (E.internal_error ii "invalid type")
  in
  Let _ := assert (nilp les) (E.internal_error ii "invalid lvals") in
  Let: (imm, res) := uncons_wconst ii res in
  ok (x, imm, res).

Definition assemble_smart_li ii ws les res :=
  Let: (x, imm, _) := smart_li_args ii ws les res in
  ok (asm_args_of_opn_args (ARMFopn_core.li x imm)).

Definition cond_opn_args
  (cond : rexpr)
  (old : seq rexpr)
  (args : ARMFopn_core.opn_args) :
  asm_op_msb_t * lexprs * rexprs :=
  let '(les, ARM_op mn opts, res) := args in
  let opts := set_is_conditional opts in
  ((None, ARM_op mn opts), les, res ++ cond :: old).

Definition assemble_smart_li_cc
  ii ws les res : cexec (seq (asm_op_msb_t * lexprs * rexprs)) :=
  Let: (x, imm, res) := smart_li_args ii ws les res in
  Let: (cond, res) := uncons ii res in
  Let _ :=
    assert (~~ Sv.mem x (free_vars_r cond)) (E.condition_modified ii)
  in
  Let: (oldx, _) := uncons_rvar ii res in
  ok (map (cond_opn_args cond [:: rvar oldx ]) (ARMFopn_core.li x imm)).

Definition chk_assemble_large_load
  (err : string -> pp_error_loc)
  (ws : wsize)
  (woff : word reg_size)
  (ws' : wsize)
  (xbase tmp : var_i)
  (eoff : fexpr) :
  cexec unit :=
  Let _ := assert (ws == ws') (err "word size differs") in
  let msg := "offset differs" in
  Let _ := assert (is_fwconst reg_size eoff == Some woff)%CMP (err msg) in
  Let _ := assert (v_var xbase != v_var tmp) (err "base and tmp clash") in
  assert (vtype tmp == sword reg_size) (err "tmp is not wreg").

Definition assemble_large_load
  (ii : instr_info)
  (ws : wsize)
  (off : Z)
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * lexprs * rexprs)) :=
  Let mn := o2r (E.condition_modified ii) (uload_mn_of_wsize ws) in
  Let: (tmp, les) := uncons_LLvar ii les in
  Let: (x, _) := uncons_LLvar ii les in
  Let: (al, ws', xbase, eoff, _) := uncons_Load ii res in
  let err s :=
    E.internal_error ii (append "invalid large_load arguments: " s)
  in
  Let _ :=
    chk_assemble_large_load err ws (wrepr reg_size off) ws' xbase tmp eoff
  in
  let pre := asm_args_of_opn_args (ARMFopn_core.li tmp off) in
  let re := Load al ws xbase (Fvar tmp) in
  let i := ((None, ARM_op mn default_opts), [:: LLvar x ], [:: re ]) in
  ok (rcons pre i).

Definition assemble_large_load_cc
  (ii : instr_info)
  (ws : wsize)
  (off : Z)
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * lexprs * rexprs)) :=
  let err := E.internal_error ii "invalid large_load size" in
  Let mn := o2r err (uload_mn_of_wsize ws) in
  Let: (tmp, les) := uncons_LLvar ii les in
  Let: (x, _) := uncons_LLvar ii les in
  Let: (al, ws', xbase, eoff, res) := uncons_Load ii res in
  Let: (cond, res) := uncons ii res in
  Let _ :=
    assert (~~ Sv.mem tmp (free_vars_r cond)) (E.condition_modified ii)
  in
  Let _ :=
    assert (~~ Sv.mem tmp (free_vars_rs res)) (E.previous_modified ii)
  in
  let err s :=
    E.internal_error ii (append "invalid large_load arguments: " s)
  in
  Let _ :=
    chk_assemble_large_load err ws (wrepr reg_size off) ws' xbase tmp eoff
  in
  let pre := asm_args_of_opn_args (ARMFopn_core.li tmp off) in
  let opts := set_is_conditional default_opts in
  let res := [:: Load al ws xbase (Fvar tmp); cond ] ++ res in
  let i := ((None, ARM_op mn opts), [:: LLvar x ], res) in
  ok (rcons pre i).

Definition chk_assemble_large_store
  (err : string -> pp_error_loc)
  (ws : wsize)
  (woff : word reg_size)
  (ws' : wsize)
  (x xbase tmp : var_i)
  (eoff : fexpr) :
  cexec unit :=
  Let _ := chk_assemble_large_load err ws woff ws' xbase tmp eoff in
  assert (v_var x != v_var tmp) (err "source and tmp clash").

Definition assemble_large_store
  (ii : instr_info)
  (ws : wsize)
  (off : Z)
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * lexprs * rexprs)) :=
  let err := E.internal_error ii "invalid store_load size" in
  Let mn := o2r err (store_mn_of_wsize ws) in
  Let: (tmp, les) := uncons_LLvar ii les in
  Let: (al, ws', xbase, eoff, _) := uncons_Store ii les in
  Let: (x, _) := uncons_rvar ii res in
  let err s :=
    E.internal_error ii (append "invalid large_store arguments: " s)
  in
  Let _ :=
    chk_assemble_large_store err ws (wrepr reg_size off) ws' x xbase tmp eoff
  in
  let pre := asm_args_of_opn_args (ARMFopn_core.li tmp off) in
  let le := Store al ws xbase (Fvar tmp) in
  let i := ((None, ARM_op mn default_opts), [:: le ], res) in
  ok (rcons pre i).

Definition assemble_large_store_cc
  (ii : instr_info)
  (ws : wsize)
  (off : Z)
  (les : seq lexpr)
  (res : seq rexpr) :
  cexec (seq (asm_op_msb_t * lexprs * rexprs)) :=
  let err := E.internal_error ii "invalid store_load size" in
  Let mn := o2r err (store_mn_of_wsize ws) in
  Let: (tmp, les) := uncons_LLvar ii les in
  Let: (al, ws', xbase, eoff, _) := uncons_Store ii les in
  Let: (x, res) := uncons_rvar ii res in
  Let: (cond, res) := uncons ii res in
  Let: (al', ws'', xbase', eoff', _) := uncons_Load ii res in
  Let _ :=
    assert (~~ Sv.mem tmp (free_vars_r cond)) (E.condition_modified ii)
  in
  Let _ :=
    assert
      [&& v_var xbase == v_var xbase' & eq_fexpr eoff eoff' ]
      (E.invalid_previous ii)
  in
  let err s :=
    E.internal_error ii (append "invalid large_store arguments: " s)
  in
  Let _ :=
    chk_assemble_large_store err ws (wrepr reg_size off) ws' x xbase tmp eoff
  in
  let pre := asm_args_of_opn_args (ARMFopn_core.li tmp off) in
  let opts := set_is_conditional default_opts in
  let le := Store al ws xbase (Fvar tmp) in
  let re := Load al' ws'' xbase' (Fvar tmp) in
  let i := ((None, ARM_op mn opts), [:: le ], [:: rvar x; cond; re ]) in
  ok (rcons pre i).

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
        Let _ := assert (all (fun (x:var_i) => vtype x == sword U32) [:: x; y; z; w])
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
      Let _ := assert (all (fun (x:var_i) => vtype x == sword U32) [:: x; y])
          (E.error ii "arm swap only valid for register of type u32") in
      ok (asm_args_of_opn_args (ARMFopn_core.smart_addi x y imm))
    | _, _ =>
      Error (E.internal_error ii "bad arm_add_large_imm: invalid args or dests")
    end
  | Osmart_li ws => assemble_smart_li ii ws outx inx
  | Osmart_li_cc ws => assemble_smart_li_cc ii ws outx inx
  | Olarge_load ws off => assemble_large_load ii ws off outx inx
  | Olarge_store ws off => assemble_large_store ii ws off outx inx
  | Olarge_load_cc ws off => assemble_large_load_cc ii ws off outx inx
  | Olarge_store_cc ws off => assemble_large_store_cc ii ws off outx inx
  end.

#[ export ]
Instance arm_extra {atoI : arch_toIdent} :
  asm_extra register register_ext xregister rflag condt arm_op arm_extra_op :=
  { to_asm := assemble_extra }.

(* This concise name is convenient in OCaml code. *)
Definition arm_extended_op {atoI : arch_toIdent} :=
  @extended_op _ _ _ _ _ _ _ arm_extra.

Definition Oarm {atoI : arch_toIdent} o : @sopn arm_extended_op _ := Oasm (BaseOp (None, o)).
