Require Import expr compiler_util utils safety_shared operators.
From mathcomp Require Import eqtype .

Section PROG.
Context `{asmop:asmOp}.
Context {pT: progT}.

Section CMD.

Variable contracts_asserts_i: (funname -> option ufundef) -> instr -> cmd.

Definition contracts_asserts gf c : cmd := conc_map (contracts_asserts_i gf) c.

End CMD.

Fixpoint has_var_e (xs: seq var_i) (e: pexpr) : bool :=
  match e with
  | Pconst _ => false
  | Pbool _ => false
  | Parr_init _ => false
  | Papp1 _ e
  | Pload _ _ e => has_var_e xs e
  | Pvar x => List.existsb (fun x' => var_beq x.(gv).(v_var) x'.(v_var)) xs
  | Pget _ _ _ x e
  | Psub _ _ _ x e => List.existsb (fun x' => var_beq x.(gv).(v_var) x'.(v_var)) xs || has_var_e xs e
  | Pis_mem_init e1 e2
  | Papp2 _ e1 e2 => has_var_e xs e1 || has_var_e xs e2
  | PappN _ es => has (fun e => has_var_e xs e) es
  | Pif _ e1 e2 e3 =>
      has_var_e xs e1 || has_var_e xs e2 || has_var_e xs e3
  | Pbig e1 _ x e2 e3 e4 =>
    has_var_e xs e1 || has_var_e xs e2 || has_var_e xs e3 || has_var_e xs e4 || List.existsb (fun x' => var_beq x.(v_var) x'.(v_var)) xs
  | Pis_var_init x => List.existsb (fun x' => var_beq x.(v_var) x'.(v_var)) xs
  end.


Definition lval_to_vare (lv: lval) : option pexpr :=
  match lv with
  | Lnone vi ty => None
  | Lmem _ _ _ e => Some e
  | Lvar x
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
  | Pload a ws e =>
    let e := replace_expr_contract vs es e in
    Pload a ws e
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
  | Pis_mem_init e1 e2 =>
    let e1 := replace_expr_contract vs es e1 in
    let e2 := replace_expr_contract vs es e2 in
    Pis_mem_init e1 e2
  | _ => e
  end.

Definition disjoint_assign (lvs: seq lval) (es: pexprs) : bool :=
  let lvs := read_rvs lvs in
  let es := read_es es in
  Sv.is_empty (Sv.inter lvs es).

Fixpoint contracts_asserts_i (gf:funname-> option ufundef) i:=
  let 'MkI ii ir := i in
  match ir with
  | Ccall lvs n es =>
    match gf n with
    | Some f' =>
      match f'.(f_contra) with
      | (Some ci) =>
        let asserts := conc_map (fun (e:assertion) =>
            if (disjoint_assign lvs es) then
              let (_,e) := e in
              let lvs := map (fun x => lval_to_vare x) lvs in
              let es := map (fun e => Some e) es in
              let e := replace_expr_contract ci.(f_iparams) es e in
              let e :=  replace_expr_contract ci.(f_ires) lvs e in
              if has_var_e (ci.(f_iparams) ++ ci.(f_ires)) e then [::]
              else safe_assert ii [::e]
            else [::]
        ) ci.(f_post) in
        i :: asserts
      | _ => [::i]
      end
    | _ => [::i]
    end
  | Cif e c1 c2 =>
    let c1 := contracts_asserts contracts_asserts_i gf c1 in
    let c2 := contracts_asserts contracts_asserts_i gf c2 in
    [:: MkI ii (Cif e c1 c2)]
  | Cfor x r c =>
    let c := contracts_asserts contracts_asserts_i gf c in
    [:: MkI ii (Cfor x r c)]
  | Cwhile a c1 e w_ii c2 =>
    let c1 := contracts_asserts contracts_asserts_i gf c1 in
    let c2 := contracts_asserts contracts_asserts_i gf c2 in
    [:: MkI ii (Cwhile a c1 e w_ii c2)]
  | _ => [::i]
  end.

Definition contracts_asserts_cmd gf c : cmd := contracts_asserts contracts_asserts_i gf c.

Fixpoint replace_vars_contract (vs:seq var_i) (vs': seq var_i) (e:pexpr): pexpr:=
  match e with
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
  | Pload a ws e =>
    let e := replace_vars_contract vs vs' e in
    Pload a ws e
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
  | Pis_mem_init e1 e2 =>
    let e1 := replace_vars_contract vs vs' e1 in
    let e2 := replace_vars_contract vs vs' e2 in
    Pis_mem_init e1 e2
  | _ => e
  end.

Definition pre_cond_asserts (ci:fun_contract) (params: seq var_i) :=
  let do_c (c:assertion) :=
    let (_,e):= c in
    replace_vars_contract ci.(f_iparams) params e in
  let pre := map do_c ci.(f_pre) in
  safe_assert dummy_instr_info pre.

Definition contracts_asserts_f gf (f:ufundef) : ufundef :=
  let 'MkFun ii ci si p c so r ev := f in
  let asserts :=
    match ci with
    | Some ci => pre_cond_asserts ci p
    | None => [::]
    end in
  let c := contracts_asserts_cmd gf c in
  MkFun ii ci si p (asserts++c) so r ev.

Definition contracts_asserts_prog (p:_uprog) : _uprog :=
  let get_f := get_fundef p.(p_funcs) in
  map_prog (contracts_asserts_f get_f) p.

End PROG.
