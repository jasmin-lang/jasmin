Require Import compiler_util expr operators.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
(* Require Export psem. *)

Section ASM_OP.

Context `{asmop:asmOp}.


Definition emin_signed sz := Pconst (wmin_signed sz).
Definition emax_signed sz := Pconst (wmax_signed sz).
Definition ezero := Pconst 0.
Definition emax_unsigned sz := Pconst (wmax_unsigned sz).

(* Definition eint_of_wint sg sz e := Papp1 (Owi1 sg (WIint_of_word sz)) e. *)

Definition eint_of_word (sg:signedness) sz e := Papp1 (Oint_of_word sz) e.
Definition word_of_int (sg:signedness) sz i := Papp1 (Oword_of_int sz) (Pconst i).

Definition emuli e1 e2 :=
    Papp2 (Omul Op_int) e1 e2.

Definition eaddi e1 e2 :=
    Papp2 (Oadd Op_int) e1 e2.

Definition emk_scale aa sz e :=
  if (aa == AAdirect) then e
  else emuli e (Pconst (wsize_size sz)).

Definition e_to_assert (e:pexpr) t : instr_r := Cassert t Cas e.

Definition instrr_to_instr (ii: instr_info) (ir: instr_r) : instr :=
  MkI ii ir.

Definition sc_e_to_instr (sc_e : pexprs) (ii : instr_info): seq instr :=
  map (fun e => instrr_to_instr ii (e_to_assert e Assert)) sc_e.


Fixpoint get_var_contract (v: var_i) (vs: seq var_i) (vs': seq var_i) : option var_i :=
    match vs, vs' with
      | x::vs, x'::vs' =>
        if var_beq v x then Some x' else get_var_contract v vs vs'
      | _, _ => None
    end.


Fixpoint replace_vars_contract (vs:seq var_i) (vs': seq var_i) (e:pexpr): pexpr:=
    match e with 
    | Parr_init_elem e l => 
        let e := replace_vars_contract vs vs' e in
        Parr_init_elem e l
    | Pvar x =>
        match get_var_contract x.(gv) vs vs' with
        | Some x' => Plvar x'
        | _ => e
        end
    | Pget a aa ws x e =>
        let e := replace_vars_contract vs vs' e in
        match get_var_contract x.(gv) vs vs' with
            | Some x' => Pget a aa ws (mk_lvar x') e
            | _ => e
        end
    | Psub aa ws l x e =>
        let e := replace_vars_contract vs vs' e in
        match get_var_contract x.(gv) vs vs' with
            | Some x' => Psub aa ws l (mk_lvar x') e
            | _ => e
        end
    | Pload a ws x e =>
        let e := replace_vars_contract vs vs' e in
        match get_var_contract x vs vs' with
            | Some x' => Pload a ws x' e
            | _ => e
        end
    | Papp1 o e =>
        let e := replace_vars_contract vs vs' e in
        Papp1 o e
    | Papp2 o e1 e2 =>
        let e1 := replace_vars_contract vs vs' e1 in
        let e2 := replace_vars_contract vs vs' e2 in
        Papp2 o e1 e2
    | PappN o es =>
        let es := map (replace_vars_contract vs vs') es in
        PappN o es
    | Pif ty e1 e2 e3 =>
        let e1 := replace_vars_contract vs vs' e1 in
        let e2 := replace_vars_contract vs vs' e2 in
        let e3 := replace_vars_contract vs vs' e3 in
        Pif ty e1 e2 e3
    | Pbig e1 o x e2 e3 e4 =>
        let e1 := replace_vars_contract vs vs' e1 in
        let e2 := replace_vars_contract vs vs' e2 in
        let e3 := replace_vars_contract vs vs' e3 in
        let e4 := replace_vars_contract vs vs' e4 in
        match get_var_contract x vs vs' with
            | Some x' => Pbig e1 o x' e2 e3 e4
            | _ => e
        end
    | Pis_var_init x =>
        match get_var_contract x vs vs' with
            | Some x' => Pis_var_init x'
            | _ => e
        end
    | Pis_arr_init x e1 e2 =>
        let e1 := replace_vars_contract vs vs' e1 in
        let e2 := replace_vars_contract vs vs' e2 in
        match get_var_contract x vs vs' with
            | Some x' => Pis_arr_init x' e1 e2
            | _ => e
        end
    | Pis_barr_init x e1 e2 =>
        let e1 := replace_vars_contract vs vs' e1 in
        let e2 := replace_vars_contract vs vs' e2 in
        match get_var_contract x vs vs' with
            | Some x' => Pis_barr_init x' e1 e2
            | _ => e
        end
    | Pis_mem_init e1 e2 =>
        let e1 := replace_vars_contract vs vs' e1 in
        let e2 := replace_vars_contract vs vs' e2 in
        Pis_mem_init e1 e2
    | _ => e
    end.

Definition lval_to_vare (lv: lval) : option pexpr :=
    match lv with
    | Lnone vi ty => None
    | Lvar x
    | Lmem _ _ x _
    | Laset _ _ _ x _
    | Lasub _ _ _ x _ => Some (Plvar x)
    end.

Fixpoint get_expr_contract (v: var_i) (vs: seq var_i) (es:seq (option pexpr)) : option pexpr :=
    match vs, es with
      | x::vs, (Some x')::es =>
        if var_beq v x then Some x' else get_expr_contract v vs es
      | _, _ => None
    end.


Fixpoint replace_expr_contract (vs:seq var_i) (es:seq (option pexpr)) (e:pexpr): pexpr:=
    match e with 
    | Parr_init_elem e l => 
        let e := replace_expr_contract vs es e in
        Parr_init_elem e l
    | Pvar x =>
        match get_expr_contract x.(gv) vs es with
        | Some x' => x'
        | _ => e
        end
    | Pget a aa ws x e =>
        let e := replace_expr_contract vs es e in
        match get_expr_contract x.(gv) vs es with
            | Some (Pvar x') => Pget a aa ws x' e
            | _ => e
        end
    | Psub aa ws l x e =>
        let e := replace_expr_contract vs es e in
        match get_expr_contract x.(gv) vs es with
            | Some (Pvar x') => Psub aa ws l x' e
            | _ => e
        end
    | Pload a ws x e =>
        let e := replace_expr_contract vs es e in
        match get_expr_contract x vs es with
            | Some (Pvar x') => Pload a ws x'.(gv) e
            | _ => e
        end
    | Papp1 o e =>
        let e := replace_expr_contract vs es e in
        Papp1 o e
    | Papp2 o e1 e2 =>
        let e1 := replace_expr_contract vs es e1 in
        let e2 := replace_expr_contract vs es e2 in
        Papp2 o e1 e2
    | PappN o es' =>
        let es' := map (replace_expr_contract vs es) es' in
        PappN o es'
    | Pif ty e1 e2 e3 =>
        let e1 := replace_expr_contract vs es e1 in
        let e2 := replace_expr_contract vs es e2 in
        let e3 := replace_expr_contract vs es e3 in
        Pif ty e1 e2 e3
    | Pbig e1 o x e2 e3 e4 =>
        let e1 := replace_expr_contract vs es e1 in
        let e2 := replace_expr_contract vs es e2 in
        let e3 := replace_expr_contract vs es e3 in
        let e4 := replace_expr_contract vs es e4 in
        match get_expr_contract x vs es with
            | Some (Pvar x') => Pbig e1 o x'.(gv) e2 e3 e4
            | _ => e
        end
    | Pis_var_init x =>
        match get_expr_contract x vs es with
            | Some (Pvar x') => Pis_var_init x'.(gv)
            | _ => e
        end
    | Pis_arr_init x e1 e2 =>
        let e1 := replace_expr_contract vs es e1 in
        let e2 := replace_expr_contract vs es e2 in
        match get_expr_contract x vs es with
            | Some (Pvar x') => Pis_arr_init x'.(gv) e1 e2
            | _ => e
        end
    | Pis_barr_init x e1 e2 =>
        let e1 := replace_expr_contract vs es e1 in
        let e2 := replace_expr_contract vs es e2 in
        match get_expr_contract x vs es with
            | Some (Pvar x') => Pis_barr_init x'.(gv) e1 e2
            | _ => e
        end
    | Pis_mem_init e1 e2 =>
        let e1 := replace_expr_contract vs es e1 in
        let e2 := replace_expr_contract vs es e2 in
        Pis_mem_init e1 e2
    | _ => e
    end.

End ASM_OP.