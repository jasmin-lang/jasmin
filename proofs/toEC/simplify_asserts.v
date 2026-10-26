(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From Coq Require Import ZArith.
From mathcomp Require Import word_ssrZ.
Require Import expr pseudo_operator compiler_util psem_defs.

Local Open Scope seq_scope.

(* ** Simplification of the assertions: constants and initialisation masks

   A forward analysis of each function body computes, at each program point,
   facts on some local variables, true on every path that reaches the point:
   - [Aconst c]: the variable holds the value of the literal [c] (a boolean,
     an integer or a word of the type of the variable), written by an
     assignment of [c] on every path, or established by an assertion [x] for a
     boolean [x];
   - [Afull]: the variable is an array whose bytes are all 0xFF, in its
     bounds: a full initialisation mask;
   - [Acopy y]: the variable is an array that holds the value of the array
     [y];
   - [Afill lo n]: the variable is an array whose bytes are 0xFF in
     [lo, lo + n) and 0 elsewhere, written by an assignment of an [Oarr_fill]
     (the mask of a sub-array of a global array), where [lo] and [n] are
     integer expressions over integer local variables written by no
     instruction since;
   - [Ainit l]: the variable is an array whose bytes in the intervals of
     constants of [l] are 0xFF: a partially initialised mask, whose cells are
     written at literal indices.
   At a join of paths, the facts on which both paths agree remain, and of two
   facts on the bytes of an array, the bytes known on both paths. At the head
   of a loop, the facts are those on entry that the body preserves: the
   fixpoint of the join with the state after the body. An assertion that
   holds establishes facts after it: a boolean variable it asserts is
   [true], the bytes of a mask it tests at literal bounds are 0xFF.

   The assertions are rewritten with these facts; the rest of the code is
   left unchanged. A variable with a known constant is replaced by the
   constant; a closed operation on literals is replaced by its value, computed
   by the semantics of the total mode, in which the assertions are evaluated;
   an initialisation test [Ois_barr_init] becomes [true] when it tests no
   cell or bytes known to be 0xFF, and the condition on its bounds that it
   amounts to when its mask is full, a sub-array of a full local mask, or a
   local mask known to be a fill [Afill lo n]; a conjunct [true] is removed,
   and an assertion that becomes [true] is removed.

   The rewriting drops no subexpression whose evaluation could fail: the
   rewritten expression evaluates exactly as the original one, but for the
   initialisation tests, whose rewriting reads the same scalar arguments
   (the bounds of the test, the index of the sub-array) with the same type
   conditions, drops only the reads of array variables, which do not fail,
   and reads the bounds of a fill [Afill lo n]: these were evaluated by the
   assignment of the fill, and the variables they read have not been written
   since, so that they evaluate again to the same integers. A test on no
   cell, or on bytes known to be 0xFF, drops only literals and the read of a
   local array or of its sub-array at a literal index, or a fill of literals,
   which do not fail in the total mode. When
   the rewritten assertion holds, so does the original one. *)

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
  | Acopy of var
  | Afill of pexpr & pexpr
  | Ainit of seq (Z * Z).

Definition aval_beq (a1 a2 : aval) : bool :=
  match a1, a2 with
  | Aconst e1, Aconst e2 => eq_expr e1 e2
  | Afull, Afull => true
  | Acopy x1, Acopy x2 => x1 == x2
  | Afill lo1 n1, Afill lo2 n2 => eq_expr lo1 lo2 && eq_expr n1 n2
  | Ainit l1, Ainit l2 => l1 == l2
  | _, _ => false
  end.

Definition astate := Mvar.t aval.

Definition eint_le e1 e2 := Papp2 (Ole Cmp_int) e1 e2.
Definition eint_add e1 e2 := Papp2 (Oadd Op_int) e1 e2.

(* ------------------------------------------------------------------------- *)
(* Sets of bytes                                                              *)

(* A set of bytes is a list of intervals [[a, b)], sorted, nonempty, and
   neither overlapping nor adjacent: the bytes of an interval are in the set
   exactly when it is included in one of the intervals. The operations below
   take and return such lists. *)

(* The union of [[a, b)] and [l]. *)
Fixpoint iv_add (a b : Z) (l : seq (Z * Z)) : seq (Z * Z) :=
  if (b <=? a)%Z then l
  else
    match l with
    | [::] => [:: (a, b)]
    | (c, d) :: l' =>
      if (b <? c)%Z then (a, b) :: l
      else if (d <? a)%Z then (c, d) :: iv_add a b l'
      else iv_add (Z.min a c) (Z.max b d) l'
    end.

(* [l1] is any list of intervals. *)
Definition iv_union (l1 l2 : seq (Z * Z)) : seq (Z * Z) :=
  foldr (fun ab l => iv_add ab.1 ab.2 l) l2 l1.

Definition iv_inter (l1 l2 : seq (Z * Z)) : seq (Z * Z) :=
  foldr (fun ab l =>
    foldr (fun cd l => iv_add (Z.max ab.1 cd.1) (Z.min ab.2 cd.2) l) l l2) [::] l1.

(* The bytes of [l] out of [[a, b)]. *)
Definition iv_remove (l : seq (Z * Z)) (a b : Z) : seq (Z * Z) :=
  foldr (fun cd l => iv_add cd.1 (Z.min cd.2 a) (iv_add (Z.max cd.1 b) cd.2 l)) [::] l.

Definition iv_shift (k : Z) (l : seq (Z * Z)) : seq (Z * Z) :=
  map (fun ab => (ab.1 + k, ab.2 + k)%Z) l.

(* The bytes of [[a, b)] are in [l]. *)
Definition iv_incl (l : seq (Z * Z)) (a b : Z) : bool :=
  (b <=? a)%Z || has (fun cd => (cd.1 <=? a) && (b <=? cd.2))%Z l.

(* The bytes of [[0, len)]. *)
Definition iv_bounds (len : Z) : seq (Z * Z) := iv_add 0 len [::].

(* The number of intervals kept in a fact. *)
Definition iv_max := 16%nat.

(* The size in bytes of an array variable. *)
Definition arr_len (x : var) : Z :=
  if vtype x is aarr ws len then arr_size ws len else 0.

(* The fact that the bytes of [l] of an array of [len] bytes are 0xFF: none
   when no byte of [l] is in its bounds, [Afull] when [l] covers them. Beyond
   [iv_max] intervals, the first ones only: a subset of the bytes. *)
Definition aof_ivs (len : Z) (l : seq (Z * Z)) : option aval :=
  let l := take iv_max (iv_inter l (iv_bounds len)) in
  if l is [::] then None
  else if iv_incl l 0 len then Some Afull
  else Some (Ainit l).

(* The bytes known to be 0xFF in an array of [len] bytes with the fact [a]: a
   fill of 0xFF at literal bounds has them in its bounds ([WArray.fill]). *)
Definition ivs_of_aval (len : Z) (a : aval) : seq (Z * Z) :=
  match a with
  | Afull => iv_bounds len
  | Ainit l => l
  | Afill (Pconst lo) (Pconst n) => iv_inter (iv_add lo (lo + n) [::]) (iv_bounds len)
  | _ => [::]
  end.

(* The facts that hold on both paths: the same fact, or the bytes of an array
   that are 0xFF on both paths. *)
Definition ajoin (s1 s2 : astate) : astate :=
  Mvar.map2 (fun x o1 o2 =>
    match o1, o2 with
    | Some a1, Some a2 =>
      if aval_beq a1 a2 then Some a1
      else
        let len := arr_len x in
        aof_ivs len (iv_inter (ivs_of_aval len a1) (ivs_of_aval len a2))
    | _, _ => None
    end) s1 s2.

Definition asize (s : astate) : nat := size (Mvar.elements s).

(* The same facts. *)
Definition aeq (s1 s2 : astate) : bool :=
  (asize s1 == asize s2) &&
  all (fun xa => if Mvar.get s2 xa.1 is Some a then aval_beq xa.2 a else false)
      (Mvar.elements s1).

(* A fact on a variable not in [xs] that a write to the variables of [xs]
   preserves: not a copy of one of them, nor a fill whose bounds read them. *)
Definition akeep (xs : Sv.t) (a : aval) : bool :=
  match a with
  | Acopy z => ~~ Sv.mem z xs
  | Afill lo n => disjoint (read_e (eint_add lo n)) xs
  | _ => true
  end.

(* After a write to the variables of [xs]: no fact on them, nor on the copies
   of them, nor fills whose bounds read them. *)
Definition akill (s : astate) (xs : Sv.t) : astate :=
  Mvar.filter_map (fun y a =>
    if Sv.mem y xs then None
    else if akeep xs a then Some a else None) s.

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

(* The local array [x] is a full mask: known to be full, or a copy of an
   array known to be full. *)
Definition is_full_var (s : astate) (x : gvar) : bool :=
  match alocal s x with
  | Some Afull => true
  | Some (Acopy y) => if Mvar.get s y is Some Afull then true else false
  | _ => false
  end.

(* The expression is a full mask of [n] bytes: a local array known to be
   full, or a fill of the whole array with 0xFF. *)
Definition is_full (s : astate) (n : Z) (e : pexpr) : bool :=
  match e with
  | Pvar x =>
    if vtype x.(gv) is aarr ws len then is_full_var s x && (arr_size ws len == n)
    else false
  | PappN (Oarr_fill ws len) es => (arr_size ws len == n) && is_full_fill ws len es
  | _ => false
  end.

(* The cells [lo, lo + n) are all initialised when [n <= 0] or [inb], the
   condition that each of them is initialised; the first disjunct is left out
   when [n] is a positive constant. *)
Definition eall_cells (n inb : pexpr) : pexpr :=
  if n is Pconst k then if (0 <? k)%Z then inb else eor (eint_le n (Pconst 0)) inb
  else eor (eint_le n (Pconst 0)) inb.

(* The interval [lo, lo + n) lies within [0, len). *)
Definition ein_bounds (len : Z) (lo n : pexpr) : pexpr :=
  eand (eint_le (Pconst 0) lo) (eint_le (eint_add lo n) (Pconst len)).

(* The cells [lo, lo + n) of an array of [len] bytes whose cells are all
   initialised are initialised when [n <= 0] or [0 <= lo /\ lo + n <= len]. *)
Definition ebounds (len : Z) (lo n : pexpr) : pexpr :=
  eall_cells n (ein_bounds len lo n).

(* The sub-array [Psub aa ws slen x i] of an array [x] of [lenx] bytes whose
   cells are all initialised: in the total mode ([WArray.get_sub]), its byte
   [k], for [0 <= k < arr_size ws slen], is the byte [start + k] of [x], with
   [start = i * mk_scale aa ws], when [0 <= start + k < lenx], and is not
   initialised otherwise. Its cells [lo, lo + n) are initialised when
   [n <= 0] or both [lo, lo + n) lies within the sub-array of [len] bytes and
   [start + lo, start + lo + n) within [x]. The index [i] is read as in the
   original expression. *)
Definition esub_bounds (len lenx : Z) aa ws (i lo n : pexpr) : pexpr :=
  let sc := mk_scale aa ws in
  let start := if sc == 1%Z then i else Papp2 (Omul Op_int) i (Pconst sc) in
  let lo' := if lo is Pconst 0 then start else eint_add start lo in
  eall_cells n (eand (ein_bounds len lo n) (ein_bounds lenx lo' n)).

(* The array of [len] bytes filled with 0xFF in [flo, flo + fn) and with 0
   elsewhere ([Oarr_fill]): its cells [lo, lo + n) are initialised when
   [n <= 0] or [lo, lo + n) lies within both [0, len) and [flo, flo + fn)
   ([WArray.fill] keeps the bytes in [0, len) only). *)
Definition efill_bounds (len : Z) (flo fn lo n : pexpr) : pexpr :=
  eall_cells n (eand (ein_bounds len lo n)
                     (eand (eint_le flo lo) (eint_le (eint_add lo n) (eint_add flo fn)))).

(* The integer expressions whose evaluation, once it has succeeded, succeeds
   again with the same value as long as the variables they read are not
   written: constants, integer local variables, opposite, sum, difference and
   product. *)
Fixpoint is_stable_int (e : pexpr) : bool :=
  match e with
  | Pconst _ => true
  | Pvar x => is_lvar x && (vtype x.(gv) == aint)
  | Papp1 (Oneg Op_int) e1 => is_stable_int e1
  | Papp2 (Oadd Op_int | Osub Op_int | Omul Op_int) e1 e2 => is_stable_int e1 && is_stable_int e2
  | _ => false
  end.

(* The arguments [lo; n; w] of [Oarr_fill], with the byte [w] equal to 0xFF
   and stable bounds [lo] and [n]. *)
Definition is_ones_fill (es : pexprs) : option (pexpr * pexpr) :=
  match es with
  | [:: lo; n; Papp1 (Oword_of_int U8) (Pconst z)] =>
    if [&& wrepr U8 z == wrepr U8 (-1), is_stable_int lo & is_stable_int n] then Some (lo, n)
    else None
  | _ => None
  end.

(* The bytes known to be 0xFF in the array variable [x]: those of its fact,
   or of the fact of the array [y] when [x] is known to be a copy of [y]. *)
Definition ivs_of_var (s : astate) (x : var) : seq (Z * Z) :=
  let len := arr_len x in
  match Mvar.get s x with
  | Some (Acopy y) => if Mvar.get s y is Some a then ivs_of_aval len a else [::]
  | Some a => ivs_of_aval len a
  | None => [::]
  end.

(* The bytes known to be 0xFF in the value of [e], an array of [len] bytes:
   - a local array variable;
   - a sub-array at a literal index [i] of a local array variable: in the
     total mode ([WArray.get_sub]), its byte [k] is the byte [start + k] of
     the array, with [start = i * mk_scale aa ws], when it lies in the bounds
     of the array, and is not initialised otherwise;
   - a fill with 0xFF at literal bounds, in the bounds of the array
     ([WArray.fill]).
   Each of these expressions evaluates without failure in the total mode. *)
Definition ivs_of_e (s : astate) (len : Z) (e : pexpr) : seq (Z * Z) :=
  match e with
  | Pvar x =>
    if is_lvar x && (arr_len x.(gv) == len) then ivs_of_var s x.(gv) else [::]
  | Psub aa ws slen x (Pconst i) =>
    if is_lvar x && (arr_size ws slen == len) then
      let start := (i * mk_scale aa ws)%Z in
      iv_shift (- start) (iv_inter (ivs_of_var s x.(gv)) (iv_add start (start + len) [::]))
    else [::]
  | PappN (Oarr_fill ws flen) [:: Pconst lo; Pconst n; Papp1 (Oword_of_int U8) (Pconst z)] =>
    if (arr_size ws flen == len) && (wrepr U8 z == wrepr U8 (-1)) then
      iv_inter (iv_add lo (lo + n) [::]) (iv_bounds len)
    else [::]
  | _ => [::]
  end.

(* An initialisation test at literal bounds of at least one cell, all of
   whose bytes are known to be 0xFF. The mask is then one of the expressions
   of [ivs_of_e], which do not fail to evaluate. *)
Definition is_init_ivs (s : astate) (len : Z) (m lo n : pexpr) : bool :=
  match lo, n with
  | Pconst lo, Pconst k => (0 <? k)%Z && iv_incl (ivs_of_e s len m) lo (lo + k)
  | _, _ => false
  end.

(* An initialisation test on no cell: its length [n] is a literal [<= 0], so
   that [ziota lo n] is empty and the test holds whatever the mask. The test
   is recognised only when the arguments it drops cannot fail to evaluate:
   [lo] is a literal, and the mask [m] of [len] bytes is a local array
   variable or a sub-array at a literal index of a local array variable (in
   the total mode, [WArray.get_sub] does not fail). A test whose [lo] or
   mask reads a scalar (a variable that may be undefined, the index of a
   sub-array) is left to the other cases. *)
Definition is_no_cell (len : Z) (m lo n : pexpr) : bool :=
  let safe_mask :=
    match m with
    | Pvar x =>
      is_lvar x && if vtype x.(gv) is aarr ws xlen then arr_size ws xlen == len else false
    | Psub _ ws slen x (Pconst _) =>
      [&& is_lvar x, arr_size ws slen == len & if vtype x.(gv) is aarr _ _ then true else false]
    | _ => false
    end in
  match lo, n with
  | Pconst _, Pconst k => (k <=? 0)%Z && safe_mask
  | _, _ => false
  end.

(* The condition on the bounds that an initialisation test on the mask [m]
   of [len] bytes amounts to, when it tests no cell or bytes known to be
   0xFF, or when [m] is a full mask, a sub-array of a full local mask of the
   same size, or a local mask of the same size known to be a fill. *)
Definition is_init_bounds (s : astate) (len : Z) (m lo n : pexpr) : option pexpr :=
  if is_no_cell len m lo n || is_init_ivs s len m lo n then Some (Pbool true)
  else if is_full s len m then Some (ebounds len lo n)
  else
    match m with
    | Psub aa ws slen x i =>
      if vtype x.(gv) is aarr wsx lenx then
        if is_full_var s x && (arr_size ws slen == len) then
          Some (esub_bounds len (arr_size wsx lenx) aa ws i lo n)
        else None
      else None
    | Pvar x =>
      if (alocal s x, vtype x.(gv)) is (Some (Afill flo fn), aarr ws xlen) then
        if arr_size ws xlen == len then Some (efill_bounds len flo fn lo n) else None
      else None
    | _ => None
    end.

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
      if is_init_bounds s len m lo n is Some c then simpl_pexpr_a (fold_e c)
      else Some (PappN_safety o es)
    | _, _ => Some (PappN_safety o es)
    end
  | Pis_var_init _ => Some a
  | Pis_mem_init e1 e2 => Some (Pis_mem_init (simpl_e s e1) (simpl_e s e2))
  | Pand a1 a2 => aand (simpl_a s a1) (simpl_a s a2)
  end.

(* The bytes [[a, b)] of the array variable [x] are 0xFF: the fact is set on
   [x], or on [y] when [x] is known to be a copy of [y], which keeps the copy;
   when this covers the array, [x] is full. A fill [Afill lo n] at bounds that
   are not literals is kept as it is: its bytes are known exactly. *)
Definition aadd_ivs (s : astate) (x : var) (a b : Z) : astate :=
  let l := ivs_of_var s x in
  let y := if Mvar.get s x is Some (Acopy y) then y else x in
  if iv_incl l a b then s
  else if Mvar.get s y is Some (Afill _ _) then s
  else
    match aof_ivs (arr_len x) (iv_add a b l) with
    | Some Afull => aset_full s x
    | Some f => Mvar.set s y f
    | None => s
    end.

(* What an assertion that holds establishes: a boolean variable is [true]; the
   bytes of a mask tested at literal bounds are 0xFF, and a mask whose bytes
   are tested over the whole array is full. *)
Fixpoint learn_a (s : astate) (a : eassert) : astate :=
  match a with
  | Pexpr (Pvar x) =>
    if is_lvar x && (vtype x.(gv) == abool) then Mvar.set s x.(gv) (Aconst (Pbool true))
    else s
  | PappN_safety (Ois_barr_init n) [:: Pvar x; Pconst lo; Pconst k] =>
    if is_lvar x then
      if vtype x.(gv) is aarr ws len then
        if arr_size ws len == n then
          if (lo <=? 0)%Z && (n <=? lo + k)%Z then aset_full s x.(gv)
          else aadd_ivs s x.(gv) lo (lo + k)
        else s
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
        | Some (Afill lo n) => Some (Afill lo n)
        | Some (Ainit l) => Some (Ainit l)
        | None => Some (Acopy y.(gv))
        end
      else None
    | Psub _ _ _ _ _, aarr _ _ => aof_ivs (arr_len x) (ivs_of_e s (arr_len x) e)
    | PappN (Oarr_fill ws len) es, aarr _ _ =>
      if aarr ws len != ty then None
      else if is_full_fill ws len es then Some Afull
      else if is_ones_fill es is Some (lo, n) then Some (Afill lo n)
      else None
    | _, _ => None
    end.

Definition aassign (s : astate) (x : var) (oa : option aval) : astate :=
  let s := akill1 s x in
  match oa with
  | None => s
  | Some (Acopy y) => if y == x then s else Mvar.set s x (Acopy y)
  | Some a => Mvar.set s x a
  end.

(* The value written by a cell write at type [ws]: all-ones bytes. *)
Definition is_ones ws (ty : atype) (e : pexpr) : bool :=
  if e is Papp1 (Oword_of_int ws') (Pconst z) then
    [&& ws' == ws, ty == aword ws & wrepr ws z == wrepr ws (-1)]
  else false.

(* [x] has the bytes [l] known to be 0xFF, after a write to it. *)
Definition aset_ivs (s : astate) (x : var) (l : seq (Z * Z)) : astate :=
  let s := akill1 s x in
  if aof_ivs (arr_len x) l is Some a then Mvar.set s x a else s.

(* The bytes known to be 0xFF after a write to an array. In the total mode, a
   write sets the bytes in the bounds of the array and ignores the others
   ([WArray.set8], [WArray.set_sub_data]); the index of the write is
   evaluated in the state before it, where the constants are known.
   - A cell of [ws] bytes at the offset [off = i * mk_scale aa ws] written
     with all-ones bytes: the bytes [[off, off + ws)] are 0xFF in addition to
     the known ones when [i] is a literal; at another index, the known ones
     stay 0xFF, the write adds 0xFF bytes only.
   - A cell written with another value at a literal index: its bytes are
     unknown, the others stay; at another index, any byte may change and
     nothing is known.
   - A sub-array of [n] bytes at the literal offset [off]: its byte [k] is
     copied to the byte [off + k] when it lies in the bounds, which are then
     known to be 0xFF when the byte [k] of the value is; the other bytes stay.
     At another index, the known bytes stay when the value is known to be
     full, which writes 0xFF bytes only; otherwise nothing is known. *)
Definition aassgn (s : astate) (lv : lval) (ty : atype) (e : pexpr) : astate :=
  let e := simpl_e s e in
  match lv with
  | Lvar x => aassign s x (aval_of_e s x ty e)
  | Laset _ aa ws x i =>
    let l := ivs_of_var s x in
    let off := if simpl_e s i is Pconst k then Some (k * mk_scale aa ws)%Z else None in
    let l :=
      match is_ones ws ty e, off with
      | true, Some off => iv_add off (off + wsize_size ws) l
      | true, None => l
      | false, Some off => iv_remove l off (off + wsize_size ws)
      | false, None => [::]
      end in
    aset_ivs s x l
  | Lasub aa ws len x i =>
    let n := arr_size ws len in
    let l := ivs_of_var s x in
    let le := if ty == aarr ws len then ivs_of_e s n e else [::] in
    let l :=
      if simpl_e s i is Pconst k then
        let off := (k * mk_scale aa ws)%Z in
        iv_union (iv_shift off le) (iv_remove l off (off + n))
      else if iv_incl le 0 n then l
      else [::] in
    aset_ivs s x l
  | Lnone _ _ | Lmem _ _ _ _ => s
  end.

(* After [x1, x2 := swap(e1, e2)] on arrays of the type of the swap, [x1] holds
   the value of [e2] and [x2] that of [e1], both evaluated before the writes:
   the facts on [e2] and [e1] in the state before, that the writes preserve.
   Any other instruction forgets what is known of the variables it writes. *)
Definition aopn (s : astate) (lvs : lvals) (o : sopn) (es : pexprs) : astate :=
  let xs := vrvs lvs in
  let s' := akill s xs in
  match o, lvs, es with
  | Opseudo_op (Oswap (aarr _ _ as ty)), [:: Lvar x1; Lvar x2], [:: e1; e2] =>
    if [&& vtype x1 == ty, vtype x2 == ty & x1.(v_var) != x2.(v_var)] then
      let add x e s1 :=
        if aval_of_e s x ty (simpl_e s e) is Some a then
          if akeep xs a then Mvar.set s1 x a else s1
        else s1 in
      add x1 e2 (add x2 e1 s')
    else s'
  | _, _, _ => s'
  end.

Section LOOP.

(* The analysis of the body of a loop from the state at its head: the state
   where the loop exits, the state at the end of the body, and the rewritten
   commands. For [while { c1 } (e) { c2 }], the loop exits after [c1] and the
   body ends after [c2]. *)
Context (body : astate -> astate * astate * cmd * cmd).

(* The state at the head of the loop is the join of the state on entry with
   the states after the body: a decreasing sequence of states, each fact
   being the one of the previous state or a weaker one, until it is stable.
   [n] bounds the number of iterations; beyond it, the body is analysed from
   no fact, which holds at the head of the loop. *)
Fixpoint wloop (n : nat) (s : astate) : astate * cmd * cmd :=
  let: (s1, s2, c1, c2) := body s in
  let s' := ajoin s s2 in
  if aeq s' s then (s1, c1, c2)
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
  | Copn lvs _ o es => (aopn s lvs o es, [:: i])
  | Csyscall lvs _ _ | Ccall lvs _ _ => (akill s (vrvs lvs), [:: i])
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
    let: (s, c, _) := wloop body (iv_max * S (asize s)) s in
    (s, [:: MkI ii (Cfor x r c)])
  | Cwhile a c1 e ii_w c2 =>
    let body s :=
      let: (s1, c1) := simpl_c simpl_i s c1 in
      let: (s2, c2) := simpl_c simpl_i s1 c2 in
      (s1, s2, c1, c2) in
    let: (s1, c1, c2) := wloop body (iv_max * S (asize s)) s in
    (s1, [:: MkI ii (Cwhile a c1 e ii_w c2)])
  end.

Definition simplify_asserts_fd (fd : ufundef) : ufundef :=
  with_body fd (simpl_c simpl_i (Mvar.empty _) fd.(f_body)).2.

Definition simplify_asserts_prog (p : _uprog) : _uprog :=
  map_prog simplify_asserts_fd p.

End ASM_OP.
