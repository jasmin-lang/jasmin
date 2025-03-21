Require Import expr.
Require Import safety_cond.
Require Import constant_prop.
Require Import flag_combination.


Section EXPR.
Context `{asmop:asmOp}.
Context {msfsz : MSFsize}.
Context {fcp : FlagCombinationParams}.
Context {pT: progT}.


Context (B : var -> var).

Definition not_array (var:var) : bool :=
  match var.(vtype) with
  | sarr _ => false
  | _ => true
  end.

Definition iop_kind_to_op_kind (o: iop_kind) : op_kind :=
  match o with
  | IOp_int => Op_int
  | IOp_w s => Op_w s
  end.

Definition icmp_kind_to_cmp_kind (o: icmp_kind) : cmp_kind :=
  match o with
  | ICmp_int => Cmp_int
  | ICmp_w s w => Cmp_w s w
  end.

Definition iop1_to_sop1 (op: iop1) : sop1 :=
 match op with
 | IOword_of_int s => Oword_of_int s
 | IOint_of_word s => Oint_of_word s
 | IOsignext s1 s2 => Osignext s1 s2
 | IOzeroext s1 s2 => Ozeroext s1 s2
 | IOnot => Onot   
 | IOlnot s => Olnot s
 | IOneg o => Oneg (iop_kind_to_op_kind o)
 end.

Definition iop2_to_sop2 (op: iop2): sop2 :=
  match op with
  | IObeq => Obeq
  | IOand => Oand
  | IOor => Oor
  | IOadd o => Oadd (iop_kind_to_op_kind o)
  | IOmul o => Omul (iop_kind_to_op_kind o)
  | IOsub o => Osub (iop_kind_to_op_kind o)
  | IOdiv o => Odiv (icmp_kind_to_cmp_kind o)
  | IOmod o => Omod (icmp_kind_to_cmp_kind o)
  | IOland s => Oland s
  | IOlor s => Olor s
  | IOlxor s => Olxor s
  | IOlsr s => Olsr s
  | IOlsl o => Olsl (iop_kind_to_op_kind o)
  | IOasr o => Oasr (iop_kind_to_op_kind o)
  | IOror s => Oror s
  | IOrol s => Orol s
  | IOeq o => Oeq (iop_kind_to_op_kind o)
  | IOneq o => Oneq (iop_kind_to_op_kind o)
  | IOlt o => Olt (icmp_kind_to_cmp_kind o)
  | IOle o => Ole (icmp_kind_to_cmp_kind o)
  | IOgt o => Ogt (icmp_kind_to_cmp_kind o)
  | IOge o => Oge (icmp_kind_to_cmp_kind o)
  end.

Fixpoint ic_to_e vs ic: pexpr :=
  match ic with
  | IBool b => Pbool b
  | IConst c => Pconst c
  | IVar n => 
    match List.nth_error vs n with
    | Some x => x
    | None => Pbool false
    end
  | IOp1 op e1 =>
    let e1 := ic_to_e vs e1 in
    let op := iop1_to_sop1 op in
    Papp1 op e1
  | IOp2 op e1 e2 =>
    let e1 := ic_to_e vs e1 in
    let e2 := ic_to_e vs e2 in
    let op := iop2_to_sop2 op in
    Papp2 op e1 e2
  end.

Definition expr_true := Pbool true.
Definition expr_false := Pbool false.

Definition var_i_to_bvar x := {| v_var:= B x.(v_var) ; v_info:=x.(v_info)|}.
Definition var_to_bvar x := {| v_var:= B x ; v_info:=dummy_var_info|}.

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

Definition assign_bvar_i_e (ii:instr_info) (c: pexpr) (x : var_i) : cmd :=
    let x := Lvar(var_i_to_bvar x) in
    [:: (instrr_to_instr ii (Cassgn x AT_inline sbool c))].

Definition assign_bvar_e (ii:instr_info) (c: pexpr) (x : var) : cmd :=
    let x := Lvar(var_to_bvar x) in
    [:: (instrr_to_instr ii (Cassgn x AT_inline sbool c))].


Definition assign_bvar_lval (ii:instr_info) (e:pexpr) (lv: lval)  : cmd :=
    match get_lv_lval lv with
    | Some x => assign_bvar_i_e ii e x
    | None => [::]
    end.

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
  let init_bvars := conc_map (fun v =>
    if not_array v then
      let expr := if (Sv.mem v args_varsL) then expr_true else expr_false in
      assign_bvar_e dummy_instr_info expr v
    else [::]
  ) X in
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


Definition rm_var_init_prog_prop (p: _uprog) : _uprog :=
  let p := rm_var_init_prog p in
  let fun_cp := fun i =>
          match i with
          | Cassgn lv _ _ e =>
              let value := get_lv_lval lv in
              let X := vars_p (p_funcs p) in
              match value with
              | Some x => Sv.mem x (all_b_vars X)
              | None => false
              end
          | _ => false
          end in
  const_prop_prog_fun false p fun_cp. (*FIXME: see what the bool stands for*)
  
  

End EXPR.