Require Import expr.
Require Import safety_cond.

Section EXPR.
Context `{asmop:asmOp}.
Context {msfsz : MSFsize}.


Context (B : var -> var).


Definition expr_true := Pbool true.

Definition var_to_bvar x := {| v_var:= B x.(v_var) ; v_info:=x.(v_info)|}.

Definition rm_var_init_e (e : pexpr) : pexpr :=
  match e with
  | Pis_var_init x => Plvar (var_to_bvar x)
  | _ => e
  end.

Definition get_lv_lval (lv : lval) : option var_i  :=
  match lv with
  | Lvar x => Some x
  | _ => None
  end.

Definition assign_bvar_e (ii:instr_info) (c: pexpr) (x : var_i) : cmd :=
    let x := Lvar(var_to_bvar x) in
    [:: (instrr_to_instr ii (Cassgn x AT_keep sbool c))].


Definition assign_bvar_lval (ii:instr_info) (e:pexpr) (lv: lval)  : cmd :=
    match get_lv_lval lv with
    | Some x => assign_bvar_e ii e x
    | None => [::]
    end.

Definition get_sopn_init_conds (o: sopn) : seq pexpr :=
  let instr_descr := get_instr_desc o in
  map (fun x => (Pbool true)) instr_descr.(i_out). (*TODO: create init_cond field to instr_desc*)

Fixpoint rm_var_init_i (i : instr) : cmd :=
  let: (MkI ii ir) := i in
  match ir with
  | Cassgn lv _ _ e => assign_bvar_lval ii expr_true lv ++ [::i]
  | Csyscall lvs _ es | Ccall lvs _ es => conc_map (assign_bvar_lval ii expr_true) lvs  ++ [::i]
  | Copn lvs _ o es  => 
    flatten (map2 (assign_bvar_lval ii) (get_sopn_init_conds o) lvs) ++ [::i] 
  | Cif e c1 c2 =>
    let c1 := conc_map rm_var_init_i c1 in
    let c2 := conc_map rm_var_init_i c2 in
    let ir := instrr_to_instr ii (Cif e c1 c2) in
    [:: ir]
  | Cfor x r c =>
    let c := conc_map rm_var_init_i c in
    let ir := instrr_to_instr ii (Cfor x r c) in
    [:: ir]
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

Definition rm_var_init_f (f:_ufundef): _ufundef :=
  let body := rm_var_init_cmd f.(f_body) in
  let init_params := conc_map (assign_bvar_e dummy_instr_info expr_true) f.(f_params) in (*FIXME - Fix instruction info*)
  {|
    f_info   := f.(f_info) ;
    f_contra := f.(f_contra) ;
    f_tyin   := f.(f_tyin) ;
    f_params := f.(f_params) ;
    f_body   := init_params ++ body ;
    f_tyout  := f.(f_tyout) ;
    f_res    := f.(f_res) ;
    f_extra  := f.(f_extra) ;
  |}.

Definition rm_var_init_prog (p:_uprog) : _uprog :=
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
  
  

End EXPR.