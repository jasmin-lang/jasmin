(* * Generation of the safety conditions of a program.

   [sc_prog] instruments a program with the assertions that must hold for it to
   be safe: array accesses in bounds and initialised, memory accesses valid and
   aligned, no division by zero, no wint overflow.  The instrumented program is
   meant to be discharged under the defensive semantics ([withcatch], see
   [WithCatch] in sem_params.v), which is the one EasyCrypt implements. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Coq Require Import ZArith.
Require Import expr compiler_util word sopn_semi op_semi.
Require Export safety_common.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "safety".

  Definition ierror msg := {|
    pel_msg      := PPEstring msg;
    pel_fn       := None;
    pel_fi       := None;
    pel_ii       := None;
    pel_vi       := None;
    pel_pass     := Some pass;
    pel_internal := true
  |}.

End E.

Section SAFETY.
Context `{asmop:asmOp} {pd: PointerData} {msfsz : MSFsize}.

(* ------------------------------------------------------------------------- *)
(* Variables                                                                  *)

(* An array variable is always "defined" as a value, the initialisation of the
   cells an access reads is checked at that access, by [sc_arr_get]. *)
Definition sc_var (x:var_i) : safety_cond :=
  if is_aarr (vtype x) then [::]
  else [:: Pis_var_init x].

Definition sc_gvar (x:gvar) : safety_cond :=
  if is_lvar x then sc_var (gv x)
  else [::].

(* ------------------------------------------------------------------------- *)
(* Translation of the conditions of the semantics                             *)

(* The safety conditions of an operator, and those of an array or memory
   access, are asserted through the generic translation of [safe_cond]s, with
   the word-to-integer coercion of the source language. *)
Definition safe_cond_to_e (vs : pexprs) (c : safe_cond) : eassert :=
  sc_to_eassert eint_of_word vs c.

(* ------------------------------------------------------------------------- *)
(* Arrays and memory                                                          *)

Definition efalse := Pbool false.
Definition sc_false : safety_cond := [:: Pexpr efalse].

(* The conditions under which an access succeeds are the ones the semantics
   itself checks ([sopn_semi.v]): they are written on the values of the
   arguments of the access and asserted on the argument expressions.  The error
   attached to each condition plays no role here. *)
Definition sc_access (vs : pexprs) (scs : seq (safe_cond * error)) : safety_cond :=
  map (safe_cond_to_e vs) (unzip1 scs).

(* [sc_get] without its last condition, the initialisation of the cells read:
   a global array is fully initialised, which [sc_prog] checks with
   [check_glob], so the condition is not emitted for it. *)
Definition sc_get_noinit len al aa ws : seq (safe_cond * error) :=
  take 2 (sc_get len al aa ws).

(* The arguments of an array access, in the order of [sc_get]: the array, then
   the index. *)
Definition sc_arr_get (x:gvar) al aa sz e : safety_cond :=
  match vtype (gv x) with
  | aarr ws len =>
    let n := arr_size ws len in
    sc_access [:: Pvar x; e]
      (if is_lvar x then sc_get n al aa sz else sc_get_noinit n al aa sz)
  | _ => sc_false
  end.

Definition sc_arr_set (x:var_i) al aa sz e : safety_cond :=
  match vtype x with
  | aarr ws len => sc_access [:: Plvar x; e] (sc_set (arr_size ws len) al aa sz)
  | _ => sc_false
  end.

Definition sc_arr_get_sub (x:gvar) aa sz len e : safety_cond :=
  match vtype (gv x) with
  | aarr ws lenx => sc_access [:: Pvar x; e] (sc_get_sub (arr_size ws lenx) aa sz len)
  | _ => sc_false
  end.

Definition sc_arr_set_sub (x:var_i) aa sz len e : safety_cond :=
  match vtype x with
  | aarr ws lenx => sc_access [:: Plvar x; e] (sc_set_sub (arr_size ws lenx) aa sz len)
  | _ => sc_false
  end.

(* The validity of a memory access depends on the memory, so it is not a
   condition on the arguments: it stays the assertion [Pis_mem_init].  Only the
   alignment of the pointer comes from the conditions of the semantics. *)
Definition sc_mem al sz e : safety_cond :=
  safe_cond_to_e [:: e] (sc_mem_aligned al sz 0)
    :: [:: Pis_mem_init e (Pconst (wsize_size sz))].

(* ------------------------------------------------------------------------- *)
(* Operators                                                                  *)

Definition sc_op1 (o : sop1) (e : pexpr) : safety_cond :=
  map (safe_cond_to_e [:: e]) (op1_safe o).

Definition sc_op2 (o : sop2) (e1 e2 : pexpr) : safety_cond :=
  map (safe_cond_to_e [:: e1; e2]) (op2_safe o).

(* ------------------------------------------------------------------------- *)
(* Expressions                                                                *)

Definition type_of_expr (e:pexpr) : atype :=
  match e with
  | Pconst _ => aint
  | Pbool _ => abool
  | Parr_init ws len => aarr ws len
  | Pvar x => vtype (gv x)
  | Pget al aa ws x e => aword ws
  | Psub aa ws len x e => aarr ws len
  | Pload al ws e => aword ws
  | Papp1 o e => (type_of_op1 o).2
  | Papp2 o e1 e2 => (type_of_op2 o).2
  | PappN o es => (type_of_opN o).2
  | Pif ty e1 e2 e3 => ty
  end.

Fixpoint sc_pexpr (e : pexpr) : safety_cond :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ _ => [::]
  | Pvar x => sc_gvar x

  | Pget al aa ws x e =>
    sc_pexpr e ++ sc_arr_get x al aa ws e

  | Psub aa ws len x e =>
    sc_pexpr e ++ sc_arr_get_sub x aa ws len e

  | Pload al ws e =>
    sc_pexpr e ++ sc_mem al ws e

  | Papp1 op e =>
    sc_pexpr e ++ sc_op1 op e

  | Papp2 op e1 e2 =>
    sc_pexpr e1 ++ sc_pexpr e2 ++ sc_op2 op e1 e2

  | PappN op es => List.flat_map sc_pexpr es

  | Pif ty e e1 e2 =>
    sc_pexpr e ++ sc_pexpr e1 ++ sc_pexpr e2
  end.

Fixpoint sc_eassert (a : eassert) : safety_cond :=
  match a with
  | Pexpr e => sc_pexpr e
  | PappN_safety _ es => List.flat_map sc_pexpr es
  | Pis_var_init _ => [::]
  | Pis_mem_init e1 e2 => sc_pexpr e1 ++ sc_pexpr e2
  | Pand a1 a2 => sc_eassert a1 ++ sc_eassert a2
  end.

(* ------------------------------------------------------------------------- *)
(* Left values                                                                *)

Definition sc_lval (lv : lval) : safety_cond :=
  match lv with
  | Lnone _ _ => [::]
  | Lvar x => [::]
  | Lmem al ws x e =>
    sc_pexpr e ++ sc_mem al ws e
  | Laset al aa ws x e =>
    sc_pexpr e ++ sc_arr_set x al aa ws e
  | Lasub aa ws len x e =>
    sc_pexpr e ++ sc_arr_set_sub x aa ws len e
  end.

(* The conditions of the left values are asserted *before* the assignment, so
   they must not read what the assignment writes. [check_xs] checks it. *)
Definition sc_lvals (lvs:lvals) okmem : safety_cond :=
  let scs := map sc_lval lvs in
  Pexpr (Pbool (check_xs read_easserts use_mem_eassert okmem Sv.empty lvs scs))
    :: flatten scs.

(* ------------------------------------------------------------------------- *)
(* Operators of instructions                                                  *)

Definition get_sopn_safe_conds (es: pexprs) (o: sopn) : safety_cond :=
  map (safe_cond_to_e es) (get_instr_desc o).(i_safe).

(* [exec_sopn] fails with [ErrType] when its arguments are ill-typed; this is
   not a safety condition, but the assertion is emitted so that the instrumented
   program is total. *)
Definition get_sopn_wt (es: pexprs) (o: sopn) : eassert :=
  Pexpr (Pbool (all2 (fun ty e => convertible (type_of_expr e) ty)
                     (get_instr_desc o).(tin) es)).

(* ------------------------------------------------------------------------- *)
(* Instructions                                                               *)

Fixpoint sc_instr_ir ii (ir : instr_r) : (safety_cond * instr_r) :=
  match ir with
  | Cassgn lv _ _ e =>
    (sc_lval lv ++ sc_pexpr e, ir)
  | Copn lvs _ o es =>
    (get_sopn_wt es o :: sc_lvals lvs true ++ get_sopn_safe_conds es o ++
       List.flat_map sc_pexpr es, ir)
  | Csyscall lvs _ es =>
    (sc_lvals lvs true ++ List.flat_map sc_pexpr es, ir)
  | Ccall lvs _ es =>
    (sc_lvals lvs false ++ List.flat_map sc_pexpr es, ir)
  | Cif e c1 c2 =>
    (sc_pexpr e, Cif e (List.flat_map sc_instr c1) (List.flat_map sc_instr c2))
  | Cfor x (d,e1,e2) c =>
    (sc_pexpr e1 ++ sc_pexpr e2, Cfor x (d,e1,e2) (List.flat_map sc_instr c))
  | Cwhile a c1 e ii_w c2 =>
    (* the condition is evaluated at the end of [c1], so its safety conditions
       are asserted there and not in front of the loop *)
    let sc_e := safe_assert ii (sc_pexpr e) in
    ([::], Cwhile a (List.flat_map sc_instr c1 ++ sc_e) e ii_w (List.flat_map sc_instr c2))
  | Cassert a =>
    (sc_eassert a.2, ir)
  end
with sc_instr (i:instr) : cmd :=
  let (ii,ir) := i in
  let ir := sc_instr_ir ii ir in
  rcons (safe_assert ii ir.1) (MkI ii ir.2).

(* ------------------------------------------------------------------------- *)
(* Functions and program                                                      *)

(* A contract is asserted as a single [eassert], so its own safety conditions
   are conjoined in front of it rather than emitted as separate assertions. *)
Definition sc_a_and (a : assertion) : assertion :=
  (a.1, aands (rcons (sc_eassert a.2) a.2)).

Definition sc_ci ci :=
  MkContra ci.(f_iparams) ci.(f_ires)
    (map sc_a_and ci.(f_pre)) (map sc_a_and ci.(f_post)).

Definition sc_fun (f: ufundef) : ufundef :=
  let 'MkFun ii ci tin p c tout r ev := f in
  let ci := omap sc_ci ci in
  let c := List.flat_map sc_instr c in
  (* the results must be initialised on exit *)
  let c := c ++ safe_assert dummy_instr_info (List.flat_map sc_var r) in
  MkFun ii ci tin p c tout r ev.

Definition check_glob (gd : glob_decl) :=
  match gd.2 with
  | Gword _ _ => true
  | Garr len t => all (WArray.is_init t) (ziota 0 len)
  end.

Definition sc_prog (p:_uprog) : result pp_error_loc _uprog :=
  Let _ := assert (all check_glob p.(p_globs))
                  (E.ierror "global arrays not fully initialised"%string) in
  ok (map_prog sc_fun p).

End SAFETY.
