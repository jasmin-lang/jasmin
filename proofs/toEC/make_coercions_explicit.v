From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import word_ssrZ.
Require Import compiler_util expr sopn syscall arch_decl arch_extra.

Module Import E.

  Definition pass : string := "make coercions explicit".

  Definition array_mismatch_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii
      "array coercion between mismatched byte sizes".

  Definition unknown_fun_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "call to an unknown function".

  Definition return_type_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii
      "function result variable types do not match the declared output types".

End E.

Section MAKE_COERCIONS_EXPLICIT.

(* Like [remove_baseop_casts.v]/[normalize_calls.v]: this pass never
   pattern-matches an architecture-specific operator, but it does compute
   [sopn_tin]/[sopn_tout] (site 4), which need a [PointerData]/[MSFsize]
   pair -- sourcing those from the ambient [asm_extra] context, rather than
   from a bare, unrelated Context variable, keeps them the SAME instances
   [toEC_jazz.v]'s own composition already uses for every other pass in
   this pipeline. *)
Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  (p : _uprog)
.

#[local] Existing Instance progUnit.

(* The static type of an expression, mirroring [safety_common.v]'s
   [etype_of_expr] but landing directly in [atype] (no sign tag is needed:
   the only coercion this pass ever inserts is a zero-extension between two
   word types, and its correctness does not depend on signedness). *)
Definition ty_expr (e : pexpr) : atype :=
  match e with
  | Pconst _ => aint
  | Pbool _ => abool
  | Parr_init ws len => aarr ws len
  | Pvar x => vtype (gv x).(v_var)
  | Pget al aa ws x e => aword ws
  | Psub aa ws len x e => aarr ws len
  | Pload al ws e => aword ws
  | Papp1 o e => (type_of_op1 o).2
  | Papp2 o e1 e2 => (type_of_op2 o).2
  | PappN o es => (type_of_opN o).2
  | Pif ty _ _ _ => ty
  end.

(* Two types are "compatible" when a value of one can stand in for the
   other with no coercion at all: equal, except arrays of the same byte
   size (the return-boundary analogue of [mce_coerce]'s array case --
   REQUIREMENTS.md's own [required_alignment.jazz]-style precedent, e.g.
   [array_cast.jazz]'s [store] function returning a [reg ptr u16[32]] view
   of a [reg ptr u64[8]] parameter: legal array reinterpretation, not a
   type error). *)
Definition ty_compat (t1 t2 : atype) : bool :=
  match t1, t2 with
  | aarr ws n, aarr ws' n' => arr_size ws n == arr_size ws' n'
  | _, _ => t1 == t2
  end.

(* Coerce (an already rewritten) expression [e], of static type [ty_expr e],
   down to the declared type [t_o] required at its use site:
   - equal types: identity;
   - both word types, [t_o] strictly narrower: explicit zero-extension
     ([Ozeroext] truncates on this side, since its declared input type is
     the wider of the two -- the only implicit conversion the source
     semantics performs on a scalar);
   - both array types: the pass never rewrites array-typed expressions (no
     Jasmin operator can reinterpret an array), so it can only check the
     REQUIREMENTS-mandated invariant that a coercion between differently
     shaped arrays never occurs implicitly by comparing byte sizes, failing
     with a proper error instead of the printer's assertion;
   - every other mismatch (e.g. a genuine word widening, or an int/bool
     mismatch): cannot evaluate successfully in the source semantics
     ([of_val]/[truncate_val] only ever narrow), so inserting anything here
     would turn a failing execution into a defined one; left unchanged. *)
Definition mce_coerce (ii : instr_info) (t_o : atype) (e : pexpr) : cexec pexpr :=
  match t_o, ty_expr e with
  | aword wso, aword wsi =>
    ok (if (wso < wsi)%CMP then Papp1 (Ozeroext wso wsi) e else e)
  | aarr ws n, aarr ws' n' =>
    if arr_size ws n == arr_size ws' n' then ok e
    else Error (E.array_mismatch_error ii)
  | _, _ => ok e
  end.

Fixpoint mce_coerce_es
  (ii : instr_info) (tys : seq atype) (es : seq pexpr) : cexec (seq pexpr) :=
  match tys, es with
  | [::], [::] => ok [::]
  | ty :: tys, e :: es =>
    Let e := mce_coerce ii ty e in
    Let es := mce_coerce_es ii tys es in
    ok (e :: es)
  | _, _ => ok es
  end.

(* Recursive expression rewriting: coerce every operator operand down to the
   operator's own declared input type (site 2) and every [Pif] branch down
   to its declared type (site 3); every other node is a plain structural
   recursion, mirroring [normalize_cond_e]'s shape. Neither site can hit the
   array branch of [mce_coerce] in practice (no Jasmin operator declares an
   array-typed input or takes array-typed [Pif] branches), so this Fixpoint
   only ever fails, if at all, transitively through a sub-expression -- kept
   as [cexec] regardless, for uniformity with [mce_coerce]. *)
Fixpoint mce_e (ii : instr_info) (e : pexpr) : cexec pexpr :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ _ | Pvar _ => ok e
  | Pget al aa ws x e =>
    Let e := mce_e ii e in
    ok (Pget al aa ws x e)
  | Psub aa ws len x e =>
    Let e := mce_e ii e in
    ok (Psub aa ws len x e)
  | Pload al ws e =>
    Let e := mce_e ii e in
    ok (Pload al ws e)
  | Papp1 o e =>
    Let e := mce_e ii e in
    Let e := mce_coerce ii (type_of_op1 o).1 e in
    ok (Papp1 o e)
  | Papp2 o e1 e2 =>
    Let e1 := mce_e ii e1 in
    Let e2 := mce_e ii e2 in
    let tys := type_of_op2 o in
    Let e1 := mce_coerce ii tys.1.1 e1 in
    Let e2 := mce_coerce ii tys.1.2 e2 in
    ok (Papp2 o e1 e2)
  | PappN o es =>
    Let es := mapM (mce_e ii) es in
    Let es := mce_coerce_es ii (type_of_opN o).1 es in
    ok (PappN o es)
  | Pif ty b e1 e2 =>
    Let b := mce_e ii b in
    Let e1 := mce_e ii e1 in
    Let e2 := mce_e ii e2 in
    Let e1 := mce_coerce ii ty e1 in
    Let e2 := mce_coerce ii ty e2 in
    ok (Pif ty b e1 e2)
  end.

Definition mce_es (ii : instr_info) := mapM (mce_e ii).

Definition mce_lval (ii : instr_info) (x : lval) : cexec lval :=
  match x with
  | Lnone _ _ | Lvar _ => ok x
  | Lmem al ws vi e =>
    Let e := mce_e ii e in
    ok (Lmem al ws vi e)
  | Laset al aa ws x e =>
    Let e := mce_e ii e in
    ok (Laset al aa ws x e)
  | Lasub aa ws len x e =>
    Let e := mce_e ii e in
    ok (Lasub aa ws len x e)
  end.

Definition mce_lvals (ii : instr_info) := mapM (mce_lval ii).

Fixpoint mce_eassert (ii : instr_info) (a : eassert) : cexec eassert :=
  match a with
  | Pexpr e =>
    Let e := mce_e ii e in
    ok (Pexpr e)
  | PappN_safety o es =>
    Let es := mapM (mce_e ii) es in
    ok (PappN_safety o es)
  | Pis_var_init x => ok (Pis_var_init x)
  | Pis_mem_init e1 e2 =>
    Let e1 := mce_e ii e1 in
    Let e2 := mce_e ii e2 in
    ok (Pis_mem_init e1 e2)
  | Pand a1 a2 =>
    Let a1 := mce_eassert ii a1 in
    Let a2 := mce_eassert ii a2 in
    ok (Pand a1 a2)
  end.

Definition mce_assertion (ii : instr_info) (a : assertion) : cexec assertion :=
  let '(lbl, e) := a in
  Let e := mce_eassert ii e in
  ok (lbl, e).

Let mce_ii_aux mc (i : instr) : cexec instr :=
  let 'MkI ii ir := i in
  Let ir := mc ii ir in
  ok (MkI ii ir).

Let mce_c_aux mc (c : cmd) : cexec cmd := mapM (mce_ii_aux mc) c.

Fixpoint mce_i (ii : instr_info) (i : instr_r) : cexec instr_r :=
  let rec := mce_c_aux mce_i in
  match i with
  | Cassgn x tg ty e =>
    Let x := mce_lval ii x in
    Let e := mce_e ii e in
    Let e := mce_coerce ii ty e in
    ok (Cassgn x tg ty e)
  | Copn xs t o es =>
    Let xs := mce_lvals ii xs in
    Let es := mce_es ii es in
    Let es := mce_coerce_es ii (sopn_tin o) es in
    ok (Copn xs t o es)
  | Csyscall xs o es =>
    Let xs := mce_lvals ii xs in
    Let es := mce_es ii es in
    Let es := mce_coerce_es ii (syscall_sig_u o).(scs_tin) es in
    ok (Csyscall xs o es)
  | Cassert a =>
    Let a := mce_assertion ii a in
    ok (Cassert a)
  | Cif e c1 c2 =>
    Let e := mce_e ii e in
    Let c1 := rec c1 in
    Let c2 := rec c2 in
    ok (Cif e c1 c2)
  | Cfor x (dir, lo, hi) c =>
    Let lo := mce_e ii lo in
    Let hi := mce_e ii hi in
    Let c := rec c in
    ok (Cfor x (dir, lo, hi) c)
  | Cwhile al c1 e info c2 =>
    Let c1 := rec c1 in
    Let e := mce_e ii e in
    Let c2 := rec c2 in
    ok (Cwhile al c1 e info c2)
  | Ccall xs f es =>
    Let xs := mce_lvals ii xs in
    Let es := mce_es ii es in
    Let fd :=
      match get_fundef (p_funcs p) f with
      | Some fd => ok fd
      | None => Error (E.unknown_fun_error ii)
      end
    in
    Let es := mce_coerce_es ii fd.(f_tyin) es in
    ok (Ccall xs f es)
  end.

Definition mce_ii := mce_ii_aux mce_i.
Definition mce_c := mce_c_aux mce_i.

Definition mce_fd (fd : _fundef unit) : cexec (_fundef unit) :=
  Let body := mce_c fd.(f_body) in
  Let _ :=
    assert
      (all2 ty_compat [seq vtype (v_var x) | x <- fd.(f_res)] fd.(f_tyout))
      (E.return_type_error (entry_info_of_fun_info fd.(f_info)))
  in
  ok {|
    f_info := f_info fd;
    f_contract := f_contract fd;
    f_tyin := f_tyin fd;
    f_params := f_params fd;
    f_body := body;
    f_tyout := f_tyout fd;
    f_res := f_res fd;
    f_extra := f_extra fd;
  |}.

Definition mce_prog : cexec _uprog :=
  Let funcs := map_cfprog mce_fd (p_funcs p) in
  ok {|
    p_funcs := funcs;
    p_globs := p_globs p;
    p_extra := p_extra p;
  |}.

End MAKE_COERCIONS_EXPLICIT.
