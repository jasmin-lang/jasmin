Require Import expr.
Require Import compiler_util.
Require Import operators.


Section ASM_OP.
Context `{asmop:asmOp}.
Context (create_var : v_kind -> string -> stype -> var_info -> var).

Fixpoint map3 {A B C D} (f: A -> B -> C -> D) (l1: list A) (l2: list B) (l3: list C) : list D :=
  match l1, l2, l3 with
  | x1::l1', x2::l2', x3::l3' => f x1 x2 x3 :: map3 f l1' l2' l3'
  | _, _, _ => [::]
  end.

Fixpoint map_with_index {A B} (f: A -> nat -> B) (l: list A) (i: nat) : list B :=
  match l with
  | x::l' => f x i :: map_with_index f l' (S i)
  | _ => [::]
  end.


Definition create_fresh_var (name : string) (ty: stype): var_i :=
    let x := create_var (Reg(Normal, Direct)) name ty dummy_var_info in
    mk_var_i x.  

Section INSTR.    
Context (get_fun: funname -> option ufundef).

Fixpoint extra_vars_call_i (i:instr) : cmd :=
    let 'MkI ii ir := i in
    match ir with 
    | Cif e c1 c2 => 
        let c1 := conc_map extra_vars_call_i c1 in
        let c2 := conc_map extra_vars_call_i c2 in
        let i := MkI ii (Cif e c1 c2) in
        [::i]
    | Cwhile a c1 e ii_w c2 => 
        let c1 := conc_map extra_vars_call_i c1 in
        let c2 := conc_map extra_vars_call_i c2 in
        let i := MkI ii (Cwhile a c1 e ii_w c2) in
        [::i]
    | Cfor x r c =>
        let c := conc_map extra_vars_call_i c in
        let i := MkI ii (Cfor x r c) in
        [::i]
    | Ccall lvs n es =>
        match get_fun n with
         | Some (MkFun _ _ ty_in _ _ ty_out _ _) =>
            let params := map (create_fresh_var "param") ty_in in
            let xs := map (create_fresh_var "result") ty_out in 
            let pre := map3 (fun ty x e => MkI ii (Cassgn (Lvar x) AT_inline ty e)) ty_in params es in
            let params := map (Plvar) params in
            let post :=  map3 (fun ty lv x => MkI ii (Cassgn lv AT_inline ty (Plvar x))) ty_out lvs xs in
            let xs := map (Lvar) xs in
            pre ++ [::MkI ii (Ccall xs n params)] ++ post
         | _ => [::i]
        end
    | _ => [::i]
    end.
    



Definition extra_vars_call_cmd (c:cmd) : cmd := conc_map extra_vars_call_i c.

Definition extra_vars_call_fn (f: ufundef) : ufundef :=
    let 'MkFun ii ci si p c so r ev := f in
    let c := extra_vars_call_cmd c in
    MkFun ii ci si p c so r ev.
    
End INSTR.


Definition extra_vars_call_prog (p:_uprog) : _uprog :=
  let get_f := get_fundef p.(p_funcs) in
  map_prog (extra_vars_call_fn get_f) p.

End ASM_OP.
