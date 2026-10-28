(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Coq Require Import ZArith.
Require Import expr compiler_util sopn safety_cond safety_common
  pseudo_operator slh_ops syscall psem_defs.

Local Open Scope seq_scope.

(* ** The initialisation state made explicit

   Every variable [x] gets a companion [mask x] that records the
   initialisation of [x]: a boolean for a scalar, an array of the same shape
   for an array, whose cells hold the byte 0xFF where the cells of [x] are
   initialised. The pass maintains the masks along the writes to [x], and
   turns the initialisation predicates of the assertions ([Pis_var_init],
   [Ois_arr_init]) into reads of the masks ([Ois_barr_init]).

   The program it produces reads nothing that is not initialised, and its
   assertions are ordinary expressions on ordinary variables: this is what the
   extraction to EasyCrypt needs, where a value carries no initialisation
   bit.

   The masks are exact: a mask holds exactly where the variable is
   initialised. The pass fails when it cannot place a mask exactly; it
   checks that its input is in the normal form produced by [normalize_calls]
   (see [check_i]), that the arrays whose initialisation its assertions test
   are local variables, sub-arrays of local variables or declared global
   arrays ([check_arr_init])
   and that the globals are initialised exactly in their bounds. It also
   checks the masks that the caller gives ([check_masks]): they are fresh,
   distinct, and of the expected types. *)

Module Import E.

  Definition pass : string := "explicit init".

  Definition dest_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii
      "a call, a system call or an operator with several destinations writes an array cell, a sub-array or the memory".

  Definition arr_init_error :=
    pp_internal_error_s pass "an assertion tests the initialisation of an array that is neither a local variable nor a declared global".

  Definition contract_error :=
    pp_internal_error_s pass "a contract reads a variable it does not bind".

  Definition glob_init_error :=
    pp_internal_error_s pass "a global array is not initialised exactly in its bounds".

  Definition mask_error :=
    pp_internal_error_s pass "the masks are not fresh and distinct variables of the expected types".

End E.

Section ASM_OP.

Context `{asmop:asmOp} {pd: PointerData} {msfsz : MSFsize}.

(* The mask variable of a variable, given by the caller: for an array, a
   variable of the same type; for a scalar, a boolean. *)
Context (mask : var -> var).

Definition mask_v (x : var_i) : var_i :=
  {| v_var := mask x.(v_var); v_info := x.(v_info); |}.

Definition mask_gv (x : gvar) : gvar :=
  {| gv := mask_v (gv x); gs := gs x; |}.

(* The array of [len] [ws]-words whose bytes in [lo, lo + n) are [z], the
   others zero. *)
Definition efill ws len (lo n : pexpr) (z : Z) : pexpr :=
  PappN (Oarr_fill ws len) [:: lo; n; Papp1 (Oword_of_int U8) (Pconst z)].

(* The mask of a fully initialised array: every byte is all ones; the mask of
   an array with no initialised cell: every byte is zero. *)
Definition efull_mask ws len := efill ws len (Pconst 0) (Pconst (arr_size ws len)) (-1).
Definition eempty_mask ws len := efill ws len (Pconst 0) (Pconst 0) 0.

(* ------------------------------------------------------------------------- *)
(* Assertions                                                                 *)

(* The expressions of an array type: a variable, a sub-array, [ArrayInit], a
   literal array, a conditional between arrays. No operator returns an array. *)
Definition is_arr_expr (e : pexpr) : bool :=
  match e with
  | Pvar x => is_arr_var (gv x)
  | Psub _ _ _ _ _ | Parr_init _ _ | PappN (Oarray _) _ | PappN (Oarr_fill _ _) _ => true
  | Pif ty _ _ _ => is_aarr ty
  | _ => false
  end.

(* The mask of the sub-array at [i] of a global array of type [ty]: a byte of
   the sub-array is initialised exactly when it lies within the global, whose
   cells are initialised exactly in its bounds ([check_glob_init]). *)
Definition eglob_sub_mask (ty : atype) aa ws len (i : pexpr) : pexpr :=
  if ty is aarr wsg leng then
    let start := Papp2 (Omul Op_int) i (Pconst (mk_scale aa ws)) in
    efill ws len (Papp1 (Oneg Op_int) start) (Pconst (arr_size wsg leng)) (-1)
  else Pbool false.

(* The mask of an array expression, cell by cell exact: the mask of a local
   variable or sub-array; the full mask for a global array, which is
   initialised exactly in its bounds ([check_glob_init]) and has no mask, and
   for a literal array, whose cells are all written; the empty mask for
   [ArrayInit]; the conditional between the masks of the branches. An
   expression of another type has no mask. *)
Fixpoint mask_of (e : pexpr) : pexpr :=
  match e with
  | Pvar x =>
    if is_glob x then
      if vtype (gv x) is aarr ws len then efull_mask ws len else Pbool false
    else Pvar (mask_gv x)
  | Psub aa ws len x i =>
    if is_glob x then eglob_sub_mask (vtype (gv x)) aa ws len i
    else Psub aa ws len (mask_gv x) i
  | Parr_init ws len => eempty_mask ws len
  | PappN (Oarray len) _ => efull_mask U8 len
  | PappN (Oarr_fill ws len) _ => efull_mask ws len
  | Pif ty b e1 e2 => Pif ty b (mask_of e1) (mask_of e2)
  | _ => Pbool false
  end.

Section ASSERT.

(* What an [is_var_init x] becomes: inside a function body, the mask of [x];
   in a contract, [true]. *)
Context (var_init : var_i -> pexpr).

(* The array [e] whose initialisation is tested is a local variable, a
   sub-array of a local variable or a global array ([check_arr_init]): its mask
   is a variable, the same sub-array of a variable or the full mask. *)
Fixpoint explicit_init_a (a : eassert) : eassert :=
  match a with
  | Pexpr _ | Pis_mem_init _ _ => a
  | Pis_var_init x => Pexpr (var_init x)
  | PappN_safety (Ois_arr_init len) [:: e; lo; n] =>
    PappN_safety (Ois_barr_init len) [:: mask_of e; lo; n]
  | PappN_safety _ _ => a
  | Pand a1 a2 => Pand (explicit_init_a a1) (explicit_init_a a2)
  end.

End ASSERT.

(* An array is always initialised, a scalar has a mask. *)
Definition explicit_init_body_a :=
  explicit_init_a (fun x => if is_arr_var x then Pbool true else Plvar (mask_v x)).

(* A contract reads only the variables it binds ([check_ci]): the
   arguments of the call and its results, which are initialised. *)
Definition explicit_init_contract_a := explicit_init_a (fun _ => Pbool true).

(* ------------------------------------------------------------------------- *)
(* Writes to the masks                                                        *)

(* [mask x := e], for a scalar [x]. *)
Definition set_mask ii (x : var_i) (e : pexpr) : instr :=
  MkI ii (Cassgn (Lvar (mask_v x)) AT_inline abool e).

(* The mask of an array written at [lv] is written at the same place: 0xFF
   bytes for a cell, the mask of the source for a whole array or a sub-array. *)
Definition mask_lv (lv : lval) : lval :=
  match lv with
  | Lvar x => Lvar (mask_v x)
  | Laset al aa ws x e => Laset al aa ws (mask_v x) e
  | Lasub aa ws len x e => Lasub aa ws len (mask_v x) e
  | Lnone _ _ | Lmem _ _ _ _ => lv
  end.

(* The mask of a cell of [ws] bytes written at [lv]. *)
Definition set_cell_mask ii (lv : lval) ws : instr :=
  MkI ii (Cassgn (mask_lv lv) AT_inline (aword ws) (Papp1 (Oword_of_int ws) (Pconst (-1)))).

Definition explicit_init_assgn ii (lv : lval) (ty : atype) (e : pexpr) : cmd :=
  let copy_mask := [:: MkI ii (Cassgn (mask_lv lv) AT_inline ty (mask_of e))] in
  match lv with
  | Lvar x => if is_arr_var x then copy_mask else [:: set_mask ii x (Pbool true)]
  | Laset _ _ ws _ _ => [:: set_cell_mask ii lv ws]
  | Lasub _ _ _ _ _ => copy_mask
  | Lnone _ _ | Lmem _ _ _ _ => [::]
  end.

(* The mask of a scalar output of an instruction: for a boolean, the
   initialisation condition of the instruction descriptor, an expression
   ([i_init_expr]) rendered on the argument expressions; an output of another
   type is always defined. *)
Definition out_mask (es : pexprs) (ty : atype) (c : safety_cond) : pexpr :=
  if ty is abool then sc_to_e eint_of_word es c
  else Pbool true.

(* The mask of a destination, given the mask of the scalar written: 0xFF bytes
   for an array cell. No instruction but the pseudo-operations handled in
   [explicit_init_i] outputs a whole array: the instructions of the
   architectures take and return words only.

   The masks of the destinations of an instruction are written before it: the
   index of a cell is evaluated in the state before the instruction, which is
   where the instruction evaluates it when the cell is its only destination;
   an instruction with several destinations writes variables only
   ([check_i]). *)
Definition explicit_init_out ii (lv : lval) (c : pexpr) : cmd :=
  match lv with
  | Lvar x => if is_arr_var x then [::] else [:: set_mask ii x c]
  | Laset _ _ ws _ _ => [:: set_cell_mask ii lv ws]
  | Lasub _ _ _ _ _ | Lnone _ _ | Lmem _ _ _ _ => [::]
  end.

Definition explicit_init_opn ii (lvs : lvals) (o : sopn) (es : pexprs) : cmd :=
  let d := get_instr_desc o in
  flatten (map2 (explicit_init_out ii) lvs (map2 (out_mask es) d.(tout) d.(i_init))).

(* The pseudo-operations that move whole arrays move their masks too. *)
Definition mask_lvs lvs := map mask_lv lvs.
Definition mask_es es := map mask_of es.

Definition set_arr_mask ii ws len (lv : lval) (m : pexpr) : instr :=
  MkI ii (Cassgn (mask_lv lv) AT_inline (aarr ws len) m).

(* The arguments and the results of a call carry their masks: an array is
   followed by its mask, a scalar is unchanged. The results of a call are
   variables ([check_i]). *)
Definition with_mask_lv (lv : lval) : lvals :=
  match lv with
  | Lnone _ (aarr _ _) => [:: lv; lv]
  | Lvar x => if is_arr_var x then [:: lv; mask_lv lv] else [:: lv]
  | Lnone _ _ | Laset _ _ _ _ _ | Lasub _ _ _ _ _ | Lmem _ _ _ _ => [:: lv]
  end.

Definition with_mask_e (e : pexpr) : pexprs :=
  if is_arr_expr e then [:: e; mask_of e] else [:: e].

Definition with_mask_x (x : var_i) : seq var_i :=
  if is_arr_var x then [:: x; mask_v x] else [:: x].

Definition with_mask_ty (ty : atype) : seq atype :=
  if ty is aarr _ _ then [:: ty; ty] else [:: ty].

(* ------------------------------------------------------------------------- *)
(* Instructions                                                               *)

(* The masks are written before the instruction, when it still reads its
   arguments, and read nothing the instruction writes; but for a call, see
   below. *)
Fixpoint explicit_init_i (i : instr) : cmd :=
  let ei_c := List.flat_map explicit_init_i in
  let: MkI ii ir := i in
  match ir with
  | Cassgn lv _ ty e => explicit_init_assgn ii lv ty e ++ [:: i]
  | Copn lvs tg o es =>
    match o, lvs, es with
    | Opseudo_op (Oswap (aarr ws len)), _, _ =>
      [:: MkI ii (Copn (mask_lvs lvs) tg o (mask_es es)); i]
    (* a copy writes every cell of its result *)
    | Opseudo_op (Ocopy ws len), [:: lv], [:: _] =>
      [:: set_arr_mask ii ws len lv (efull_mask ws len); i]
    (* the protection of a pointer returns its argument *)
    | Oslh (SLHprotect_ptr ws len), [:: lv], [:: e; _]
    | Oslh (SLHprotect_ptr_fail ws len), [:: lv], [:: e; _] =>
      [:: set_arr_mask ii ws len lv (mask_of e); i]
    | _, _, _ => explicit_init_opn ii lvs o es ++ [:: i]
    end
  | Csyscall lvs (RandomBytes ws len) _ =>
    match lvs with
    (* the random bytes fill the array *)
    | [:: Lvar _ as lv] => [:: set_arr_mask ii ws len lv (efull_mask ws len); i]
    | _ => [:: i]
    end
  (* A scalar result is defined; its mask is written after the call, with the
     results. *)
  | Ccall lvs fn es =>
    MkI ii (Ccall (List.flat_map with_mask_lv lvs) fn (List.flat_map with_mask_e es))
      :: List.flat_map (fun lv => explicit_init_out ii lv (Pbool true)) lvs
  | Cif e c1 c2 =>
    [:: MkI ii (Cif e (ei_c c1) (ei_c c2))]
  (* the counter is written at each iteration, not when the range is empty *)
  | Cfor x r c =>
    [:: MkI ii (Cfor x r (set_mask ii x (Pbool true) :: ei_c c))]
  | Cwhile a c1 e ii_w c2 =>
    [:: MkI ii (Cwhile a (ei_c c1) e ii_w (ei_c c2))]
  | Cassert (lbl, a) => [:: MkI ii (Cassert (lbl, explicit_init_body_a a))]
  end.

Definition explicit_init_c (c : cmd) : cmd := List.flat_map explicit_init_i c.

(* ------------------------------------------------------------------------- *)
(* Functions and program                                                      *)

(* On entry, the mask of a scalar parameter is set (its value comes from the
   call, and no mask accompanies a scalar), the mask of any other variable of
   the function is empty. The total mode would read the same for a mask never
   written; the writes are there for the extraction, where an unassigned local
   has an arbitrary value. *)
Definition init_masks ii (fd : ufundef) : cmd :=
  let params := vars_l fd.(f_params) in
  List.flat_map (fun x =>
    let in_params := Sv.mem x params in
    match vtype x with
    | aarr ws len =>
      if in_params then [::]
      else [:: MkI ii (Cassgn (Lvar (mask_v (mk_var_i x))) AT_inline (aarr ws len) (eempty_mask ws len))]
    | _ => [:: set_mask ii (mk_var_i x) (Pbool in_params)]
    end) (Sv.elements (vars_fd fd)).

Definition explicit_init_ci (ci : fun_contract) : fun_contract :=
  let on_a (a : assertion) := (a.1, explicit_init_contract_a a.2) in
  MkContra (List.flat_map with_mask_x ci.(f_iparams))
           (List.flat_map with_mask_x ci.(f_ires))
           (map on_a ci.(f_pre))
           (map on_a ci.(f_post)).

Definition explicit_init_fd (fd : ufundef) : ufundef :=
  let 'MkFun ii ci tin params c tout res ev := fd in
  let c := explicit_init_c c in
  let c := init_masks (if c is MkI ii _ :: _ then ii else dummy_instr_info) fd ++ c in
  MkFun ii (omap explicit_init_ci ci)
    (List.flat_map with_mask_ty tin) (List.flat_map with_mask_x params)
    c
    (List.flat_map with_mask_ty tout) (List.flat_map with_mask_x res)
    ev.

(* ------------------------------------------------------------------------- *)
(* The checks                                                                 *)

(* The array argument of an initialisation test is a local variable, a
   sub-array of a local variable or a global array of [gd], as the safety pass
   produces it (the argument of a copy can be a sub-array): a local array
   always has a value, and its mask is a variable, or the same sub-array of a
   variable, that describes it; a global of [gd] has a value, and its mask, the
   full one, describes it. The mask of a global reads nothing of it: without
   the test that the global is declared, the instrumented assertion would hold
   where the original one fails. A sub-array of a global is refused: its mask
   holds the cells within the global even when the sub-array is out of its
   bounds. *)
Fixpoint check_arr_init (gd : glob_decls) (a : eassert) : bool :=
  match a with
  | PappN_safety (Ois_arr_init _) es =>
    match es with
    | [:: Pvar x; _; _] => is_lvar x || is_ok (get_global gd x.(gv))
    | [:: Psub _ _ _ x _; _; _] => is_lvar x
    | _ => false
    end
  | Pand a1 a2 => check_arr_init gd a1 && check_arr_init gd a2
  | Pexpr _ | PappN_safety _ _ | Pis_var_init _ | Pis_mem_init _ _ => true
  end.

Definition is_var_lv (lv : lval) : bool :=
  if lv is (Lvar _ | Lnone _ _) then true else false.

(* The destinations of a call, of a system call and of an operator with several
   destinations are variables, as [normalize_calls] produces them: the masks of
   the destinations of such an instruction are then exact. *)
Fixpoint check_i (gd : glob_decls) (i : instr) : cexec unit :=
  let: MkI ii ir := i in
  let check_lvs lvs := assert (all is_var_lv lvs) (E.dest_error ii) in
  match ir with
  | Cassgn _ _ _ _ => ok tt
  | Copn lvs _ _ _ => if 1 < size lvs then check_lvs lvs else ok tt
  | Csyscall lvs _ _ | Ccall lvs _ _ => check_lvs lvs
  | Cassert (_, a) => add_iinfo ii (assert (check_arr_init gd a) E.arr_init_error)
  | Cif _ c1 c2 | Cwhile _ c1 _ _ c2 => Let _ := allM (check_i gd) c1 in allM (check_i gd) c2
  | Cfor _ _ c => allM (check_i gd) c
  end.

(* A precondition reads only the parameters of the contract, a postcondition
   only its parameters and results. *)
Definition check_ci (gd : glob_decls) (ci : fun_contract) : cexec unit :=
  let params := vars_l ci.(f_iparams) in
  let pre := [seq a.2 | a <- ci.(f_pre)] in
  let post := [seq a.2 | a <- ci.(f_post)] in
  Let _ := assert (Sv.subset (read_easserts pre) params) E.contract_error in
  Let _ := assert (Sv.subset (read_easserts post) (Sv.union params (vars_l ci.(f_ires))))
                  E.contract_error in
  assert (all (check_arr_init gd) (pre ++ post)) E.arr_init_error.

Definition check_fd (gd : glob_decls) (fd : ufundef) : cexec unit :=
  Let _ := allM (check_i gd) fd.(f_body) in
  oapp (check_ci gd) (ok tt) fd.(f_contract).

(* A global array is initialised in its bounds and nowhere else: its mask is
   the full one. *)
Definition check_glob_init (g : glob_decl) : bool :=
  if g.2 is Garr len t then
    WArray.all_init t 0 len
    && Mz.all (fun i _ => (0 <=? i) && (i <? len))%Z (WArray.arr_data t)
  else true.

(* The variables that a contract binds. *)
Definition contract_vars (ci : fun_contract) : Sv.t :=
  vars_l (f_iparams ci ++ f_ires ci).

(* The variables of the program: those of its functions and of their
   contracts. *)
Definition explicit_init_vars (p : _uprog) : Sv.t :=
  foldr (fun (f : ufun_decl) X =>
    Sv.union (Sv.union (vars_fd f.2) (oapp contract_vars Sv.empty f.2.(f_contract))) X)
    Sv.empty p.(p_funcs).

(* The masks of the variables [xs] are of the expected types, pairwise
   distinct and not in [X]. *)
Fixpoint check_masks (X : Sv.t) (xs : seq var) : bool :=
  if xs is x :: xs then
    let mx := mask x in
    let ty := if is_arr_var x then vtype x else abool in
    [&& vtype mx == ty, ~~ Sv.mem mx X & check_masks (Sv.add mx X) xs]
  else true.

(* The masks are checked once the program is instrumented: the caller may
   create the masks when they are first asked for, and they are then created
   in the order of the instrumented program. *)
Definition explicit_init_prog (p : _uprog) : cexec _uprog :=
  Let _ := assert (all check_glob_init p.(p_globs)) E.glob_init_error in
  Let _ := allM (fun f => add_funname f.1 (add_finfo f.2.(f_info) (check_fd p.(p_globs) f.2)))
                p.(p_funcs) in
  let p' := map_prog explicit_init_fd p in
  let X := explicit_init_vars p in
  Let _ := assert (check_masks X (Sv.elements X)) E.mask_error in
  ok p'.

End ASM_OP.
