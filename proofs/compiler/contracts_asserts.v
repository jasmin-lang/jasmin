Require Import expr compiler_util utils safety_util operators.
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
    | Parr_init_elem e _ => has_var_e xs e
    | Pvar x => List.existsb (fun x' => var_beq x.(gv).(v_var) x'.(v_var)) xs
    | Pget _ _ _ x e 
    | Psub _ _ _ x e => List.existsb (fun x' => var_beq x.(gv).(v_var) x'.(v_var)) xs || has_var_e xs e
    | Pload _ _ x e => List.existsb (fun x' => var_beq x.(v_var) x'.(v_var)) xs || has_var_e xs e
    | Pis_mem_init e1 e2
    | Papp2 _ e1 e2 => has_var_e xs e1 || has_var_e xs e2
    | PappN _ es => has (fun e => has_var_e xs e) es
    | Pif _ e1 e2 e3 => 
        has_var_e xs e1 || has_var_e xs e2 || has_var_e xs e3
    | Pbig e1 _ x e2 e3 e4 => 
      has_var_e xs e1 || has_var_e xs e2 || has_var_e xs e3 || has_var_e xs e4 || List.existsb (fun x' => var_beq x.(v_var) x'.(v_var)) xs
    | Pis_var_init x => List.existsb (fun x' => var_beq x.(v_var) x'.(v_var)) xs
    | Pis_arr_init x e1 e2 
    | Pis_barr_init x e1 e2 =>  has_var_e xs e1 || has_var_e xs e2 || List.existsb (fun x' => var_beq x.(v_var) x'.(v_var)) xs
    end.

Fixpoint contracts_asserts_i (gf:funname-> option ufundef) i:=
    let 'MkI ii ir := i in
    match ir with
    | Ccall lvs n es => 
        match gf n with
        | Some f' =>
            match f'.(f_contra) with
            | (Some ci) =>
                let asserts := conc_map (fun (e:assertion_prover*pexpr) => 
                    let (_,e) := e in
                    let lvs := map (fun x => lval_to_vare x) lvs in
                    let es := map (fun e => Some e) es in
                    let e := replace_expr_contract ci.(f_iparams) es e in
                    let e :=  replace_expr_contract ci.(f_ires) lvs e in
                    if has_var_e (ci.(f_iparams) ++ ci.(f_ires)) e then [::]
                    else [:: instrr_to_instr ii (e_to_assert e Assert) ]
                ) ci.(f_post) in
                i :: asserts
            | _ => [::i]
            end
        | _ => [::i]
        end
    | Cif e c1 c2 => 
        let c1 := contracts_asserts contracts_asserts_i gf c1 in
        let c2 := contracts_asserts contracts_asserts_i gf c2 in
        [:: instrr_to_instr ii (Cif e c1 c2)]
    | Cfor x r c =>
        let c := contracts_asserts contracts_asserts_i gf c in
        [:: instrr_to_instr ii (Cfor x r c)]
    | Cwhile a c1 e w_ii c2 =>
        let c1 := contracts_asserts contracts_asserts_i gf c1 in
        let c2 := contracts_asserts contracts_asserts_i gf c2 in
        [:: instrr_to_instr ii (Cwhile a c1 e w_ii c2)]
    | _ => [::i]
    end.

Definition contracts_asserts_cmd gf c : cmd := contracts_asserts contracts_asserts_i gf c.


Definition pre_cond_asserts (ci:fun_contract) (params: seq var_i) :=
    let pre := map (fun (c:assertion_prover * pexpr) =>
        let (_,e):= c in
        replace_vars_contract ci.(f_iparams) params e
    ) ci.(f_pre) in
    sc_e_to_instr pre dummy_instr_info.


Definition contracts_asserts_f gf (f:ufundef) : ufundef :=
    let 'MkFun ii ci si p c so r ev := f in
    let asserts := match ci with
                   | Some ci => pre_cond_asserts ci p
                   | None => [::]
                   end in
    let c := contracts_asserts_cmd gf c in
    MkFun ii ci si p (asserts++c) so r ev.

Definition contracts_asserts_prog (p:_uprog) : uprog :=
  let get_f := get_fundef p.(p_funcs) in
  map_prog (contracts_asserts_f get_f) p.

End PROG.