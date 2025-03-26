Require Import expr.
Require Import safety_cond.
Require Import constant_prop.
Require Import flag_combination.
Require Import dead_code.
Require Import operators.



Section EXPR.
Context `{asmop:asmOp}.
Context {msfsz : MSFsize}.
Context {fcp : FlagCombinationParams}.
Context {pT: progT}.
Context (is_move_op : asm_op_t -> bool).


Context (B : var -> var).


Definition not_array (var:var) : bool :=
  match var.(vtype) with
  | sarr _ => false
  | _ => true
  end.

(* Transforms an init_cond to an equivalent pexpr *)
Fixpoint ic_to_e vs ic: pexpr :=
  match ic with
  | IBool b => Pbool b
  | IConst c => Pconst c
  | IVar n => 
    match List.nth_error vs n with
    | Some x => x
    | None => Pbool false
    end
  | IOp1 op e1 => Papp1 op (ic_to_e vs e1)
  | IOp2 op e1 e2 => Papp2 op (ic_to_e vs e1) (ic_to_e vs e2)
  end.

Definition expr_true := Pbool true.
Definition expr_false := Pbool false.

Definition var_i_to_bvar x := {| v_var:= B x.(v_var) ; v_info:=x.(v_info)|}.
Definition var_to_bvar x := {| v_var:= B x ; v_info:=dummy_var_info|}.

(* Receives an expression, if it is [is_var_init x] it substitutes it by its corresponding boolean variable *)
Definition rm_var_init_e (e : pexpr) : pexpr :=
  match e with
  | Pis_var_init x => Plvar (var_i_to_bvar x)
  | _ => e
  end.

Definition get_lv_lval (lv : lval) : option var_i  :=
  match lv with
  | Lvar x => if not_array x.(v_var) then Some x else None
  | _ => None
  end.

(* Creates an instruction that assigns the boolean variable of x to a given expression e *)
Definition assign_bvar_i_e (ii:instr_info) (e: pexpr) (x : var_i) : cmd :=
    let x := Lvar(var_i_to_bvar x) in
    [:: (instrr_to_instr ii (Cassgn x AT_inline sbool e))].

Definition assign_bvar_e (ii:instr_info) (e: pexpr) (x : var) : cmd :=
    let x := Lvar(var_to_bvar x) in
    [:: (instrr_to_instr ii (Cassgn x AT_inline sbool e))].

(* Check if there is an assignment to a variable and if so, change the corresponding boolean variable *)
Definition assign_bvar_lval (ii:instr_info) (e:pexpr) (lv: lval)  : cmd :=
    match get_lv_lval lv with
    | Some x => assign_bvar_i_e ii e x
    | None => [::]
    end.

  
(* Get a list with a initialization condition for each output of the given operation *)
Definition get_sopn_init_conds es (o: sopn) : seq pexpr :=
  let instr_descr := get_instr_desc o in
  map (ic_to_e es) instr_descr.(i_init).

Fixpoint rm_var_init_i (i : instr) : cmd :=
  let: (MkI ii ir) := i in
  match ir with
  | Cassgn lv _ _ e => assign_bvar_lval ii expr_true lv ++ [::i]
  | Csyscall lvs _ es | Ccall lvs _ es => conc_map (assign_bvar_lval ii expr_true) lvs  ++ [::i]
  | Copn lvs _ o es  => 
    flatten (map2 (assign_bvar_lval ii) (get_sopn_init_conds es o) lvs) ++ [::i] 
  | Cif e c1 c2 =>
    let c1 := conc_map rm_var_init_i c1 in
    let c2 := conc_map rm_var_init_i c2 in
    let ir := instrr_to_instr ii (Cif e c1 c2) in
    [:: ir]
  | Cfor x r c =>
    let c := conc_map rm_var_init_i c in
    let b := assign_bvar_i_e ii expr_true x in
    let ir := instrr_to_instr ii (Cfor x r c) in
    b ++[:: ir]
  | Cwhile a c1 e ii_w c2 =>
    let c1 := conc_map rm_var_init_i c1 in
    let c2 := conc_map rm_var_init_i c2 in
    let ir := instrr_to_instr ii (Cwhile a c1 e ii_w c2) in
    [:: ir]
  | Cassert ak ap e =>
    let e := rm_var_init_e e in
    [:: instrr_to_instr ii (Cassert ak ap e)]
  end.

Definition rm_var_init_cmd (c : cmd) : cmd := conc_map rm_var_init_i c.
  

Definition rm_var_init_f (f:ufundef): _ufundef :=
  let body := rm_var_init_cmd f.(f_body) in
  let X := Sv.elements (vars_fd f) in
  let args_varsL := vars_l f.(f_params) in
  (*
   For each variable in the function, initializes the correspondent boolean variable
   with true if it is in the parameters otherwise to false
  *)
  let init_bvars := 
    match f.(f_body) with
    | [::] => [::]
    | (MkI ii ir) :: t => 
      conc_map (fun v =>
        if not_array v then
          let expr := if (Sv.mem v args_varsL) then expr_true else expr_false in
          assign_bvar_e ii expr v
        else [::]
      ) X
    end in
  {|
    f_info   := f.(f_info) ;
    f_contra := f.(f_contra) ;
    f_tyin   := f.(f_tyin) ;
    f_params := f.(f_params) ;
    f_body   :=  init_bvars ++ body ;
    f_tyout  := f.(f_tyout) ;
    f_res    := f.(f_res) ;
    f_extra  := f.(f_extra) ;
  |}.

Definition rm_var_init_prog (p:_uprog) : uprog :=
  let sc_funcs := map (fun f => 
    match f with
     |(fn,fd) => (fn,(rm_var_init_f fd))
    end
  ) p.(p_funcs) in
  {| p_globs := p.(p_globs) ;
     p_funcs := sc_funcs ;
     p_abstr := p.(p_abstr) ;
     p_extra := p.(p_extra) ;
  |}.

Definition all_b_vars vars := Sv.fold (fun x acc => Sv.add (B x) acc) vars Sv.empty.

(* Remove is_var_init and then use constant prop to remove trivial assertions *)
Definition rm_var_init_prog_prop (p: _uprog) : uprog :=
  let p := rm_var_init_prog p in
  let bX := all_b_vars(vars_p (p_funcs p)) in
  (* Function for const_prop to only propagate the B variables *)
  let fun_cp := fun lv _ _ =>
              let x := get_lv_lval lv in
              match x with
              | Some x => Sv.mem x bX
              | None => false
              end
  in
  const_prop_prog_fun false p fun_cp
.

Definition rm_var_init_prog_dc (p: _uprog) : _uprog :=
  let p:prog := rm_var_init_prog_prop p in
  match dead_code_prog is_move_op p false with
    | Ok p => p
    | Error e => p
  end.

  
  

End EXPR.