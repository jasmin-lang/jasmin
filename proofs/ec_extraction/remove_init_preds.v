Require Import expr.
Require Import safety_shared.
Require Import constant_prop_extraction.
Require Import flag_combination.
Require Import dead_code.
Require Import compiler_util.
Require Import operators.
Require Import pseudo_operator.



Section EXPR.
Context `{asmop:asmOp}.
Context {msfsz : MSFsize}.
Context {fcp : FlagCombinationParams}.
Context {pT: progT}.
Context (is_move_op : asm_op_t -> bool).
Context (B : var -> var).


Definition not_array (var:var) : bool :=
  match var.(vtype) with
  | aarr _ _ => false
  | _ => true
  end.

Definition arr_size (v:var) :=
  match v.(vtype) with
  | aarr ws n => ok (Z.to_pos (arr_size ws n))
  | _ => type_error
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

Section IS_VAR_INIT.

Variable rm_is_var_init: var_i -> pexpr.

(* FIXME : move this *)
Definition is_Ois_arr_init o :=
  match o with
  | Ois_arr_init len => Some len
  | _ => None
  end.

(* Receives an expression, if it is [is_var_init x] it substitutes it by its corresponding boolean variable *)
Fixpoint rm_var_init_e (e : pexpr) : pexpr :=
  match e with
  | Pis_var_init x => rm_is_var_init x(*Plvar (var_i_to_bvar x)*)

  | Papp1 op e1 =>
    let e1 := rm_var_init_e e1 in
    Papp1 op e1

  | Papp2 op e1 e2 =>
    let e1 := rm_var_init_e e1 in
    let e2 := rm_var_init_e e2 in
    Papp2 op e1 e2

  | PappN op es =>
    let es := map rm_var_init_e es in
    match is_Ois_arr_init op, es with
    | Some len, Pvar x :: es =>
      let xb := var_i_to_bvar (gv x) in
      PappN (Ois_barr_init len) (Pvar (Gvar xb (gs x)) :: es)
    | Some len, Psub aa ws l x i :: es =>
      let xb := var_i_to_bvar (gv x) in
      let xb := Psub aa ws l (Gvar xb (gs x)) i in
      PappN (Ois_barr_init len) (xb :: es)
    | _, _ => PappN op es
    end

  | Pif ty e e1 e2 =>
    let e := rm_var_init_e e in
    let e1 := rm_var_init_e e1 in
    let e2 := rm_var_init_e e2 in
    Pif ty e e1 e2

  | Pbig idx op var e1 e2 e3  =>
    let idx := rm_var_init_e idx in
    let e1 := rm_var_init_e e1 in
    let e2 := rm_var_init_e e2 in
    let e3 := rm_var_init_e e3 in
    Pbig idx op var e1 e2 e3

  | _ => e
  end.

Definition lv_get_scalar_var (lv : lval) : option var_i  :=
  match lv with
  | Lvar x => if not_array x.(v_var) then Some x else None
  | _ => None
  end.

Definition lv_get_var (lv : lval) : option var_i  :=
  match lv with
  | Lvar x => Some x
  | _ => None
  end.

(* Creates an instruction that assigns the boolean variable of x to a given expression e *)
Definition assign_bvar_i_e (ii:instr_info) (e: pexpr) (x : var_i) : cmd :=
  let x := Lvar(var_i_to_bvar x) in
  [:: (MkI ii (Cassgn x AT_inline abool e))].

Definition assign_bvar_e (ii:instr_info) (e: pexpr) (x : var) : cmd :=
  let x := Lvar(var_to_bvar x) in
  [:: (MkI ii (Cassgn x AT_inline abool e))].

(* Check if there is an assignment to a variable and if so, change the corresponding boolean variable *)
Definition assign_bvar_lval (ii:instr_info) (e:pexpr) (lv: lval)  : cmd :=
  match lv_get_scalar_var lv with
  | Some x => assign_bvar_i_e ii e x
  | None =>
    match lv with
    | Laset a aa ws x e =>
      let e := emk_scale aa ws e in
      let x := var_i_to_bvar x in
      let x := Laset a AAdirect ws x e in
      let c := Papp1 (Oword_of_int ws) (Pconst (-1)) in
      [:: (MkI ii (Cassgn x AT_inline (aword ws) c))]
    | _ => [::]
    end
  end.

(* If x is global variable - the lv will be fully initialized,
otherwise will be equal to b_x *)
Definition assign_arr_bvar (ii:instr_info) (lv: lval) (t:atype) (e:pexpr)  : cmd :=
  match t with
  | aarr ws len =>
    match e with
    | Pvar x =>
      let e :=
        if is_glob x then Papp1 (Oarr_make (Z.to_pos (type.arr_size ws len))) (word_of_int Unsigned U8 (-1))
        else
          let x := x.(gv) in
          Plvar(var_i_to_bvar x)
      in
      [:: MkI ii (Cassgn lv AT_inline t e)]
    | Psub aa ws len x i =>
      let e :=
        if is_glob x then Papp1 (Oarr_make len) (word_of_int Unsigned U8 (-1))
        else
          let x := x.(gv) in
          let x := Plvar (var_i_to_bvar x) in
          Psub aa ws len x i
      in
      [:: (MkI ii (Cassgn lv AT_inline t e))]
    | _ => [::]
    end
  | _ => [::]
  end.

(* When there is an assignment there are a few cases
  where we need to generate extra instructions:
  - Laset: change the boolean array variable of the positions that were initialized
  - Lvar: if it is a scalar variables, assign the boolean variable to true
          if it is an array, so a = b, then create assignment b_a = b_b
                             or a = b[i:j], then create assignment b_a = b_b[i:j]
  - Lasub: similar to Lvar for arrays
*)
Definition cassign_bvar (ii:instr_info) (lv: lval) (t:atype) (e:pexpr)  : cmd :=
  match lv with
  | Laset a aa ws x e =>
    let e := emk_scale aa ws e in
    let x := var_i_to_bvar x in
    let x := Laset a AAdirect ws x e in
    let c := Papp1 (Oword_of_int ws) (Pconst (-1)) in
    [:: (MkI ii (Cassgn x AT_inline (aword ws) c))]
  | Lvar x =>
    if not_array x.(v_var) then
      assign_bvar_i_e ii expr_true x
    else
      let x := var_i_to_bvar x in
      assign_arr_bvar ii (Lvar x) t e
  | Lasub aa ws len x i =>
    let x := var_i_to_bvar x in
    let lv := Lasub aa ws len x i in
    assign_arr_bvar ii lv t e
  | _ => [::]
  end.

(* Get a list with a initialization condition for each output of the given operation *)
Definition get_sopn_init_conds (es:pexprs) (o: sopn) : seq pexpr :=
  let instr_descr := get_instr_desc o in
  map (ic_to_e es) instr_descr.(i_init).

(*Add boolean array variables in params and return values of function call*)
Definition change_ccall_signature lvs es : seq lval * seq pexpr :=
  let lvs :=  conc_map (fun lv =>
    match lv with
      | Lnone _ (aarr _ _) => [::lv;lv]
      | Lvar x =>
         if not_array x.(v_var) then
          [:: lv]
         else
          [:: lv; Lvar (var_i_to_bvar x)]
      | Lasub aa ws len x i =>
        let x := var_i_to_bvar x in
        let blv := Lasub aa ws len x i in
        [:: lv; blv]
      | _ => [:: lv]
      end
  ) lvs in
    let es := conc_map (fun e =>
    match e with
    | Pvar x =>
      if not_array x.(gv).(v_var) then
        [:: e]
      else
        [:: e; Plvar (var_i_to_bvar x.(gv))]
    | Psub aa ws len x i =>
      let x := Plvar (var_i_to_bvar x.(gv)) in
      let be := Psub aa ws len x i in
      [:: e; be]
    | _ => [:: e]
    end
  ) es in
  (lvs,es).

Definition lval_to_blvar (lv:lval) : lval :=
  match lv with
  | Lvar x => Lvar (var_i_to_bvar x)
  | Lasub aa ws len x i => Lasub aa ws len (var_i_to_bvar x) i
  | _ => lv
  end.

Definition e_to_bexpr (e:pexpr) : pexpr :=
  match e with
  | Pvar x => Plvar (var_i_to_bvar x.(gv))
  | Psub aa ws len x i =>
    let x := Plvar (var_i_to_bvar x.(gv)) in
    Psub aa ws len x i
  | _ => e
  end.



(* Remove is_var_init and is_arr_init from the instruction and replace them with the corresponding boolean variables *)


Definition rm_init_swap ii ws n lvs es : instr :=
  let lvs := map lval_to_blvar lvs in
  let es := map e_to_bexpr es in
  MkI ii (Copn lvs AT_inline (Opseudo_op (Oswap (aarr ws n))) es).

Definition rm_init_copy ii ws (n:positive) lv e : instr :=
  let lv := lval_to_blvar lv in
  let e := e_to_bexpr e in
  MkI ii (Cassgn lv AT_inline (aarr ws n) e).

Definition assign_bvar_syscall (lvs:seq lval) ws (l:positive) (ii:instr_info) : cmd :=
  match lvs with
  | [::Lvar x] =>
    if not_array x.(v_var) then
      [::]
    else
      let x := Lvar (var_i_to_bvar x) in
      let e := Papp1 (Oarr_make (Z.to_pos (type.arr_size ws l))) (word_of_int Unsigned U8 (-1)) in
      let i := Cassgn x AT_inline (aarr ws l) e in
      let i := MkI ii i in
      [:: i]
  | _ => [::]
  end.

(* Remove is_var_init and is_arr_init from the instruction and replace them with the corresponding boolean variables *)
Fixpoint rm_var_init_i (i : instr) : cmd :=
  let: (MkI ii ir) := i in
  match ir with
  | Cassgn lv _ t e => cassign_bvar ii lv t e ++ [::i]
  | Csyscall lvs (RandomBytes ws l) _ =>
    assign_bvar_syscall lvs ws l ii ++ [::i]
  | Ccall lvs n es =>
    let (lvs,es) := change_ccall_signature lvs es in
    let i := MkI ii (Ccall lvs n es) in
    conc_map (assign_bvar_lval ii expr_true) lvs ++ [::i]
  | Copn lvs _ (Opseudo_op (Oswap (aarr ws n))) es =>
    [:: rm_init_swap ii ws n lvs es;i]
  | Copn lvs _ o es  =>
    match o with
    | Opseudo_op (Ocopy ws n) =>
      let n := Z.to_nat (wsize_size ws) * (Z.to_nat n) in
      let n := Pos.of_nat n in
      match lvs, es with
      | [:: lv], [:: e] => [:: rm_init_copy ii ws n lv e;i]
      | _,_ => [::i]
      end
    | Oslh (SLHprotect_ptr ws n)
    | Oslh (SLHprotect_ptr_fail ws n) =>
      match lvs, es with
      | [:: lv], [:: e; _] =>[:: rm_init_copy ii ws n lv e;i]
      | _,_ => [::i]
      end
    | _ => flatten (map2 (assign_bvar_lval ii) (get_sopn_init_conds es o) lvs) ++ [::i]
    end
  | Cif e c1 c2 =>
    let c1 := conc_map rm_var_init_i c1 in
    let c2 := conc_map rm_var_init_i c2 in
    let ir := MkI ii (Cif e c1 c2) in
    [:: ir]
  | Cfor x r c =>
    let c := conc_map rm_var_init_i c in
    let b := assign_bvar_i_e ii expr_true x in
    let ir := MkI ii (Cfor x r c) in
    b ++ [:: ir]
  | Cwhile a c1 e ii_w c2 =>
    let c1 := conc_map rm_var_init_i c1 in
    let c2 := conc_map rm_var_init_i c2 in
    let ir := MkI ii (Cwhile a c1 e ii_w c2) in
    [:: ir]
  | Cassert (ak,e) =>
    let e := rm_var_init_e e in
    [:: MkI ii (Cassert (ak,e))]
  end.

Definition rm_var_init_cmd (c : cmd) : cmd := conc_map rm_var_init_i c.

End IS_VAR_INIT.

Definition add_bvar_arr xs :=
  conc_map (fun x =>
    if not_array x.(v_var) then
      [:: x]
    else
      [:: x; var_i_to_bvar x]
  ) xs.

(* Change function declaration types and variables to add boolean arrays -
everytime there is an array a, there will be a new variable b_a with the same size as a.
b_a[i] represents the initialization of byte i of a (0 - Not initialized; 1 - Initialized) *)
Definition add_barray_fun_decl (f:ufundef) :=
  let aux_ty := conc_map (fun x =>
    match x with
      | aarr ws n => [:: x; x]
      | _ => [:: x]
    end
  ) in
  let tyin := aux_ty f.(f_tyin) in
  let tyout := aux_ty f.(f_tyout) in

  let params := add_bvar_arr f.(f_params) in
  let res := add_bvar_arr f.(f_res) in

  (tyin, params, tyout, res).

(* Add boolean arrays variables to contract variables and
remove is_var_init and is_arr_init from the pre and post conditions *)
Definition update_fun_contra c : option fun_contract :=
  match c with
  | None => None
  | Some c =>
    let iparams :=  add_bvar_arr c.(f_iparams) in
    let ires :=  add_bvar_arr c.(f_ires) in

    let aux (e:assertion) :=
      let (a,e) := e in
      (a,rm_var_init_e (fun _ => Pbool true) e)
    in
    let f_pre := map aux c.(f_pre) in
    let f_post := map aux c.(f_post) in
    Some (MkContra iparams ires f_pre f_post)
  end.

(*
 For each variable in the function, initializes the correspondent boolean variable
 with true if it is in the parameters otherwise to false
 For array variables not in the parameters, initializes the correspondent array of booleans with 0
*)
Definition init_bvars ii (f:ufundef) :=
  let X := Sv.elements (vars_fd f) in
  let args_varsL := vars_l f.(f_params) in
  conc_map (fun v =>
    match arr_size v with
    | Error _ =>
      if (Sv.mem v args_varsL) then assign_bvar_e ii expr_true v
      else assign_bvar_e ii expr_false v
    | Ok sz =>
      if (Sv.mem v args_varsL) then [::]
      else
        let e:= Papp1 (Oarr_make sz) (word_of_int Unsigned U8 0) in
        assign_bvar_e ii e v
    end
  ) X
.

(* Remove is_var_init and is_arr_init - replacing with corresponding boolean variables *)
Definition rm_var_init_f (f:ufundef): ufundef :=
  let: (f_tyin, f_params,f_tyout,f_res) := add_barray_fun_decl f in
  let f_contra := update_fun_contra f.(f_contra) in
  let body := rm_var_init_cmd (fun x => Plvar (var_i_to_bvar x)) f.(f_body) in
  let init_bvars := match body with
    | [::] => [::]
    | (MkI ii _) :: _ => init_bvars ii f
    end in
  {|
    f_info   := f.(f_info) ;
    f_contra := f_contra ;
    f_tyin   := f_tyin ;
    f_params := f_params ;
    f_body   := init_bvars ++ body ;
    f_tyout  := f_tyout ;
    f_res    := f_res ;
    f_extra  := f.(f_extra) ;
  |}.


Definition rm_var_init_prog (p:_uprog) : _uprog :=
  map_prog rm_var_init_f p.

Definition all_b_vars vars := Sv.fold (fun x acc => Sv.add (B x) acc) vars Sv.empty.

(* Use constant prop to remove trivial assertions *)
Definition rm_var_init_const_prop (p: uprog) : uprog :=
  let bX := all_b_vars(vars_p (p_funcs p)) in
  (* Function for const_prop to only propagate the B variables *)
  let fun_cp := fun lv _ _ =>
              let x := lv_get_var lv in
              match x with
              | Some x => Sv.mem x bX
              | None => false
              end
  in
  const_prop_prog_fun false p fun_cp
.

Definition rm_var_init_dc (p: uprog) :  _uprog :=
  match dead_code_prog is_move_op p false with
  | Ok p => p
  | Error e => p
  end.

End EXPR.
