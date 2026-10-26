(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From Coq Require Import ZArith.
From mathcomp Require Import word_ssrZ.
Require Import expr compiler_util psem_defs.

Local Open Scope seq_scope.

(* ** Simplification of the assertions: constants and full masks

   A forward analysis of each function body computes, at each program point,
   facts on some local variables, true on every path that reaches the point:
   - [Aconst c]: the variable holds the value of the literal [c] (a boolean,
     an integer or a word of the type of the variable), written by an
     assignment of [c] on every path, or established by an assertion [x] for a
     boolean [x];
   - [Afull]: the variable is an array whose bytes are all 0xFF, in its
     bounds: a full initialisation mask;
   - [Acopy y]: the variable is an array that holds the value of the array
     [y].
   At a join of paths, the facts on which both paths agree remain. At the
   head of a loop, the facts are those on entry that the body preserves: the
   fixpoint of the join with the state after the body, reached in fewer
   iterations than there are facts on entry. An assertion that holds
   establishes facts after it: a boolean variable it asserts is [true], a mask
   whose bytes it tests over the whole array is full.

   The assertions are rewritten with these facts; the rest of the code is
   left unchanged. A variable with a known constant is replaced by the
   constant; a closed operation on literals is replaced by its value, computed
   by the semantics of the total mode, in which the assertions are evaluated;
   an initialisation test [Ois_barr_init] on a full mask becomes the
   condition on its bounds that it amounts to; a conjunct [true] is removed,
   and an assertion that becomes [true] is removed.

   The rewriting drops no subexpression whose evaluation could fail: the
   rewritten expression evaluates exactly as the original one, but for the
   initialisation test on a full mask, whose rewriting reads the same
   arguments and keeps their type conditions. When the rewritten assertion
   holds, so does the original one. *)

Section ASM_OP.

Context `{asmop:asmOp}.

(* ------------------------------------------------------------------------- *)
(* The literals and the folding of closed operations                          *)

Definition val_of_lit (e : pexpr) : option value :=
  match e with
  | Pbool b => Some (Vbool b)
  | Pconst z => Some (Vint z)
  | Papp1 (Oword_of_int ws) (Pconst z) => Some (Vword (wrepr ws z))
  | _ => None
  end.

Definition lit_of_val (v : value) : option pexpr :=
  match v with
  | Vbool b => Some (Pbool b)
  | Vint z => Some (Pconst z)
  | Vword ws w => Some (wconst w)
  | _ => None
  end.

(* An operation whose arguments are literals is replaced by the literal of
   its value, when it evaluates; it is kept otherwise. A literal is kept as
   it is. *)
Definition fold_app1 (o : sop1) (e1 : pexpr) : pexpr :=
  let e := Papp1 o e1 in
  if val_of_lit e is Some _ then e
  else if val_of_lit e1 is Some v1 then
    if sem_sop1 (sm := total) o v1 is Ok v then odflt e (lit_of_val v) else e
  else e.

Definition fold_app2 (o : sop2) (e1 e2 : pexpr) : pexpr :=
  let e := Papp2 o e1 e2 in
  match val_of_lit e1, val_of_lit e2 with
  | Some v1, Some v2 =>
    if sem_sop2 (sm := total) o v1 v2 is Ok v then odflt e (lit_of_val v) else e
  | _, _ => e
  end.

(* ------------------------------------------------------------------------- *)
(* The abstract state                                                         *)

Variant aval :=
  | Aconst of pexpr
  | Afull
  | Acopy of var.

Definition aval_beq (a1 a2 : aval) : bool :=
  match a1, a2 with
  | Aconst e1, Aconst e2 => eq_expr e1 e2
  | Afull, Afull => true
  | Acopy x1, Acopy x2 => x1 == x2
  | _, _ => false
  end.

Definition astate := Mvar.t aval.

(* The facts that hold on both paths. *)
Definition ajoin (s1 s2 : astate) : astate :=
  Mvar.map2 (fun _ o1 o2 =>
    match o1, o2 with
    | Some a1, Some a2 => if aval_beq a1 a2 then Some a1 else None
    | _, _ => None
    end) s1 s2.

Definition asize (s : astate) : nat := size (Mvar.elements s).

(* After a write to the variables of [xs]: no fact on them, nor on the copies
   of them. *)
Definition akill (s : astate) (xs : Sv.t) : astate :=
  Mvar.filter_map (fun y a =>
    if Sv.mem y xs then None
    else if a is Acopy z then if Sv.mem z xs then None else Some a
    else Some a) s.

Definition akill1 s x := akill s (Sv.singleton x).

(* [x] is full, and so are the arrays equal to it. *)
Definition aset_full (s : astate) (x : var) : astate :=
  let xs := if Mvar.get s x is Some (Acopy y) then Sv.add y (Sv.singleton x) else Sv.singleton x in
  let s := Mvar.map (fun a => if a is Acopy z then if Sv.mem z xs then Afull else a else a) s in
  Sv.fold (fun y s => Mvar.set s y Afull) xs s.

(* ------------------------------------------------------------------------- *)
(* Expressions                                                                *)

Definition alocal (s : astate) (x : gvar) : option aval :=
  if is_lvar x then Mvar.get s x.(gv) else None.

(* The variables with a known constant are replaced by it, the closed
   operations are folded. *)
Fixpoint simpl_e (s : astate) (e : pexpr) : pexpr :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ _ => e
  | Pvar x => if alocal s x is Some (Aconst c) then c else e
  | Pget al aa ws x e => Pget al aa ws x (simpl_e s e)
  | Psub aa ws len x e => Psub aa ws len x (simpl_e s e)
  | Pload al ws e => Pload al ws (simpl_e s e)
  | Papp1 o e1 => fold_app1 o (simpl_e s e1)
  | Papp2 o e1 e2 => fold_app2 o (simpl_e s e1) (simpl_e s e2)
  | PappN o es => PappN o (map (simpl_e s) es)
  | Pif ty b e1 e2 => Pif ty (simpl_e s b) (simpl_e s e1) (simpl_e s e2)
  end.

(* The arguments of [Oarr_fill ws len] that fill the whole array with the byte
   0xFF. *)
Definition is_full_fill ws len (es : pexprs) : bool :=
  match es with
  | [:: Pconst lo; Pconst n; Papp1 (Oword_of_int U8) (Pconst z)] =>
    [&& (lo <=? 0)%Z, (arr_size ws len <=? lo + n)%Z & wrepr U8 z == wrepr U8 (-1)]
  | _ => false
  end.

(* The expression is a full mask of [n] bytes: a local array known to be
   full, or a fill of the whole array with 0xFF. *)
Definition is_full (s : astate) (n : Z) (e : pexpr) : bool :=
  match e with
  | Pvar x =>
    if (alocal s x, vtype x.(gv)) is (Some Afull, aarr ws len) then arr_size ws len == n
    else false
  | PappN (Oarr_fill ws len) es => (arr_size ws len == n) && is_full_fill ws len es
  | _ => false
  end.

Definition eint_le e1 e2 := Papp2 (Ole Cmp_int) e1 e2.

(* The cells [lo, lo + n) of an array of [len] bytes whose cells are all
   initialised are initialised when [n <= 0] or [0 <= lo /\ lo + n <= len];
   the first disjunct is left out when [n] is a positive constant. *)
Definition ebounds (len : Z) (lo n : pexpr) : pexpr :=
  let inb := eand (eint_le (Pconst 0) lo)
                  (eint_le (Papp2 (Oadd Op_int) lo n) (Pconst len)) in
  if n is Pconst k then if (0 <? k)%Z then inb else eor (eint_le n (Pconst 0)) inb
  else eor (eint_le n (Pconst 0)) inb.

(* The literals of the bound condition are folded. *)
Fixpoint fold_e (e : pexpr) : pexpr :=
  match e with
  | Papp1 o e1 => fold_app1 o (fold_e e1)
  | Papp2 o e1 e2 => fold_app2 o (fold_e e1) (fold_e e2)
  | _ => e
  end.

(* ------------------------------------------------------------------------- *)
(* Assertions                                                                 *)

(* [None] stands for the assertion [true]. *)
Definition aand (a1 a2 : option eassert) : option eassert :=
  match a1, a2 with
  | None, a | a, None => a
  | Some a1, Some a2 => Some (Pand a1 a2)
  end.

(* A conjunction of booleans is the conjunction of the assertions: both
   evaluate both sides and require booleans. *)
Fixpoint simpl_pexpr_a (e : pexpr) : option eassert :=
  match e with
  | Pbool true => None
  | Papp2 Oand e1 e2 => aand (simpl_pexpr_a e1) (simpl_pexpr_a e2)
  | _ => Some (Pexpr e)
  end.

Fixpoint simpl_a (s : astate) (a : eassert) : option eassert :=
  match a with
  | Pexpr e => simpl_pexpr_a (simpl_e s e)
  | PappN_safety o es =>
    let es := map (simpl_e s) es in
    match o, es with
    | Ois_barr_init len, [:: m; lo; n] =>
      if is_full s len m then simpl_pexpr_a (fold_e (ebounds len lo n))
      else Some (PappN_safety o es)
    | _, _ => Some (PappN_safety o es)
    end
  | Pis_var_init _ => Some a
  | Pis_mem_init e1 e2 => Some (Pis_mem_init (simpl_e s e1) (simpl_e s e2))
  | Pand a1 a2 => aand (simpl_a s a1) (simpl_a s a2)
  end.

(* What an assertion that holds establishes: a boolean variable is [true]; a
   mask whose bytes are tested over the whole array is full. *)
Fixpoint learn_a (s : astate) (a : eassert) : astate :=
  match a with
  | Pexpr (Pvar x) =>
    if is_lvar x && (vtype x.(gv) == abool) then Mvar.set s x.(gv) (Aconst (Pbool true))
    else s
  | PappN_safety (Ois_barr_init n) [:: Pvar x; Pconst lo; Pconst k] =>
    if is_lvar x && (lo <=? 0)%Z && (n <=? lo + k)%Z then
      if vtype x.(gv) is aarr ws len then
        if arr_size ws len == n then aset_full s x.(gv) else s
      else s
    else s
  | Pand a1 a2 => learn_a (learn_a s a1) a2
  | _ => s
  end.

(* ------------------------------------------------------------------------- *)
(* Instructions                                                               *)

(* The fact on [x] after [x := e], [e] simplified, assigned at type [ty]. *)
Definition aval_of_e (s : astate) (x : var) (ty : atype) (e : pexpr) : option aval :=
  if ty != vtype x then None
  else
    match e, ty with
    | Pbool _, abool | Pconst _, aint => Some (Aconst e)
    | Papp1 (Oword_of_int ws) (Pconst _), aword ws' => if ws == ws' then Some (Aconst e) else None
    | Pvar y, aarr _ _ =>
      if is_lvar y && (vtype y.(gv) == ty) then
        match Mvar.get s y.(gv) with
        | Some (Aconst _) => None
        | Some Afull => Some Afull
        | Some (Acopy z) => Some (Acopy z)
        | None => Some (Acopy y.(gv))
        end
      else None
    | PappN (Oarr_fill ws len) es, aarr _ _ =>
      if (aarr ws len == ty) && is_full_fill ws len es then Some Afull else None
    | _, _ => None
    end.

Definition aassign (s : astate) (x : var) (oa : option aval) : astate :=
  let s := akill1 s x in
  match oa with
  | None => s
  | Some (Acopy y) => if y == x then s else Mvar.set s x (Acopy y)
  | Some a => Mvar.set s x a
  end.

Definition is_afull (oa : option aval) : bool :=
  if oa is Some Afull then true else false.

(* The value written by a cell write at type [ws]: all-ones bytes. *)
Definition is_ones ws (ty : atype) (e : pexpr) : bool :=
  if e is Papp1 (Oword_of_int ws') (Pconst z) then
    [&& ws' == ws, ty == aword ws & wrepr ws z == wrepr ws (-1)]
  else false.

(* A full mask stays full when a cell is written with all-ones bytes, or a
   sub-array with a full mask: in the total mode, a write out of the bounds of
   the array leaves it unchanged. Any other write to an array forgets what is
   known of it. *)
Definition aassgn (s : astate) (lv : lval) (ty : atype) (e : pexpr) : astate :=
  let e := simpl_e s e in
  match lv with
  | Lvar x => aassign s x (aval_of_e s x ty e)
  | Laset _ _ ws x _ =>
    let full := is_afull (Mvar.get s x) && is_ones ws ty e in
    let s := akill1 s x in
    if full then Mvar.set s x Afull else s
  | Lasub _ ws len x _ =>
    let full := is_afull (Mvar.get s x) && (ty == aarr ws len)
                && is_full s (arr_size ws len) e in
    let s := akill1 s x in
    if full then Mvar.set s x Afull else s
  | Lnone _ _ | Lmem _ _ _ _ => s
  end.

Section LOOP.

(* The analysis of the body of a loop from the state at its head: the state
   where the loop exits, the state at the end of the body, and the rewritten
   commands. For [while { c1 } (e) { c2 }], the loop exits after [c1] and the
   body ends after [c2]. *)
Context (body : astate -> astate * astate * cmd * cmd).

(* The state at the head of the loop is the join of the state on entry with
   the states after the body: a decreasing sequence of states, each a subset
   of the previous one, which is stable once its size is; [n] bounds the
   number of iterations by the size of the state on entry. *)
Fixpoint wloop (n : nat) (s : astate) : astate * cmd * cmd :=
  let: (s1, s2, c1, c2) := body s in
  let s' := ajoin s s2 in
  if asize s' == asize s then (s1, c1, c2)
  else if n is S n then wloop n s'
  else let: (s1, _, c1, c2) := body (Mvar.empty _) in (s1, c1, c2).

End LOOP.

Section CMD.

Context (simpl_i : astate -> instr -> astate * cmd).

Fixpoint simpl_c (s : astate) (c : cmd) : astate * cmd :=
  match c with
  | [::] => (s, [::])
  | i :: c =>
    let: (s, ci) := simpl_i s i in
    let: (s, c) := simpl_c s c in
    (s, ci ++ c)
  end.

End CMD.

Fixpoint simpl_i (s : astate) (i : instr) : astate * cmd :=
  let: MkI ii ir := i in
  match ir with
  | Cassgn lv _ ty e => (aassgn s lv ty e, [:: i])
  | Copn lvs _ _ _ | Csyscall lvs _ _ | Ccall lvs _ _ => (akill s (vrvs lvs), [:: i])
  | Cassert (lbl, a) =>
    match simpl_a s a with
    | None => (s, [::])
    | Some a => (learn_a s a, [:: MkI ii (Cassert (lbl, a))])
    end
  | Cif e c1 c2 =>
    let: (s1, c1) := simpl_c simpl_i s c1 in
    let: (s2, c2) := simpl_c simpl_i s c2 in
    (ajoin s1 s2, [:: MkI ii (Cif e c1 c2)])
  (* the counter is written at the start of each iteration; the loop exits
     at the head *)
  | Cfor x r c =>
    let body s :=
      let: (s2, c) := simpl_c simpl_i (akill1 s x) c in
      (s, s2, c, [::]) in
    let: (s, c, _) := wloop body (S (asize s)) s in
    (s, [:: MkI ii (Cfor x r c)])
  | Cwhile a c1 e ii_w c2 =>
    let body s :=
      let: (s1, c1) := simpl_c simpl_i s c1 in
      let: (s2, c2) := simpl_c simpl_i s1 c2 in
      (s1, s2, c1, c2) in
    let: (s1, c1, c2) := wloop body (S (asize s)) s in
    (s1, [:: MkI ii (Cwhile a c1 e ii_w c2)])
  end.

Definition simplify_asserts_fd (fd : ufundef) : ufundef :=
  with_body fd (simpl_c simpl_i (Mvar.empty _) fd.(f_body)).2.

Definition simplify_asserts_prog (p : _uprog) : _uprog :=
  map_prog simplify_asserts_fd p.

End ASM_OP.
