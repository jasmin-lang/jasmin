From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import expr compiler_util.
Require dead_code.
Import Utf8.

(* Turns every [for] loop into a [while] loop.

   For [for x = e1 to e2 { c }], where [c] does not write [x], let [lo] and
   [hi] stand for [e1] and [e2]. The bound read at each iteration ([hi] for
   [to], [lo] for [downto]) is used as it is when the loop cannot change its
   value: it reads neither the memory nor [x] nor a variable written by [c];
   otherwise it is copied first into a fresh integer variable. The other
   bound is read before the loop only, and is never copied.

   When [x] is not live after the loop, its value after the loop does not
   matter:
     [x := lo; while (x < hi) { c; x := x + 1 }]
     [x := hi; while (lo < x) { c; x := x - 1 }]  (for [downto])
   Otherwise the loop is guarded, so that [x] is not written when the range
   is empty and holds the last index of the range after the loop:
     [if (lo < hi) { x := lo; while (x < hi) { c; x := x + 1 }; x := hi - 1 }]
     [if (lo < hi) { x := hi; while (lo < x) { c; x := x - 1 }; x := lo + 1 }]

   The live sets are those that [dead_code] computes on the source program. *)

Module Import E.

  Definition pass : string := "for to while".

  Definition fresh_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "fresh bound variable is not fresh".

  Definition written_index_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "the index of the loop is written by its body".

End E.

Section FOR_TO_WHILE.

Context `{asmop : asmOp} {LC : LoopCounter}.
Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).

Definition fresh_bound (ii : instr_info) (x : var_i) (suffix : string) : var_i :=
  let name :=
    fresh_var_ident (Ident.id_kind x.(vname)) ii (Ident.id_name x.(vname) ++ suffix) aint
  in
  {| v_var := {| vtype := aint; vname := name |}; v_info := var_info_of_ii ii |}.

(* Whether [e] has the same value all along the loop, whose index and body
   write the variables [W] and possibly the memory; the globals are never
   written. *)
Definition stable_bound (W : Sv.t) (e : pexpr) : bool :=
  disjoint (read_e e) W && ~~ use_mem e.

(* The bound [e] used as it is, or copied into a fresh variable; [V] is the
   set of the variables in use, extended with the fresh variable. *)
Definition loop_bound (ii : instr_info) (V W : Sv.t) (x : var_i) (suffix : string)
  (e : pexpr) : cexec (Sv.t * cmd * pexpr) :=
  if stable_bound W e then ok (V, [::], e)
  else
    let b := fresh_bound ii x suffix in
    Let _ := assert (~~ Sv.mem b V) (E.fresh_error ii) in
    ok (Sv.add b V, [:: MkI ii (Cassgn (Lvar b) AT_none aint e)], Plvar b).

Definition assign_int (ii : instr_info) (x : var_i) (e : pexpr) : instr :=
  MkI ii (Cassgn (Lvar x) AT_none aint e).

(* The loop on [x] from [lo] to [hi] in the direction [d], with body [c]. *)
Definition while_of_for (ii : instr_info) (x : var_i) (d : dir)
  (lo hi : pexpr) (c : cmd) : cmd :=
  let ex := Plvar x in
  let '(start, cond, step) :=
    match d with
    | UpTo => (lo, elti ex hi, eaddi ex (Pconst 1))
    | DownTo => (hi, elti lo ex, esubi ex (Pconst 1))
    end
  in
  [:: assign_int ii x start;
      MkI ii (Cwhile NoAlign [::] cond ii (c ++ [:: assign_int ii x step]))].

(* [x] holds the last index of the range after the loop. *)
Definition guarded_while_of_for (ii : instr_info) (x : var_i) (d : dir)
  (lo hi : pexpr) (c : cmd) : cmd :=
  let last :=
    match d with
    | UpTo => esubi hi (Pconst 1)
    | DownTo => eaddi lo (Pconst 1)
    end
  in
  [:: MkI ii (Cif (elti lo hi)
                (while_of_for ii x d lo hi c ++ [:: assign_int ii x last])
                [::])].

Definition for_to_while_c (ftw_i : instr -> Sv.t -> cexec (Sv.t * cmd))
  (c : cmd) (s : Sv.t) : cexec (Sv.t * cmd) :=
  dead_code.dead_code_c ftw_i c s.

(* [V] is the set of the variables in use: those of the function and the
   fresh variables of the enclosing loops. [s] is the set of the variables
   live after [i]; the result starts with the set of the variables live
   before [i]. *)
Fixpoint for_to_while_i (V : Sv.t) (i : instr) (s : Sv.t) {struct i} :
  cexec (Sv.t * cmd) :=
  let 'MkI ii ir := i in
  match ir with
  | Cassgn x _ _ e =>
    ok (read_rv_rec (read_e_rec (Sv.diff s (write_i ir)) e) x, [:: i])

  | Copn xs _ _ es | Csyscall xs _ es | Ccall xs _ es =>
    ok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i])

  | Cassert a => ok (read_eassert_rec s a.2, [:: i])

  | Cif b c1 c2 =>
    Let sc1 := for_to_while_c (for_to_while_i V) c1 s in
    Let sc2 := for_to_while_c (for_to_while_i V) c2 s in
    let: (s1, c1) := sc1 in
    let: (s2, c2) := sc2 in
    ok (read_e_rec (Sv.union s1 s2) b, [:: MkI ii (Cif b c1 c2)])

  | Cfor x (d, e1, e2) c =>
    let W := write_c c in
    Let _ := assert (~~ Sv.mem x W) (E.written_index_error ii) in
    (* the bound read at each iteration *)
    let '(e, suffix) := if d is UpTo then (e2, "_hi"%string) else (e1, "_lo"%string) in
    Let rb := loop_bound ii V (Sv.add x W) x suffix e in
    let '(V, cb, b) := rb in
    let '(lo, hi) := if d is UpTo then (e1, b) else (b, e2) in
    Let sc := dead_code.loop (for_to_while_c (for_to_while_i V) c) ii loop_counter
                (read_rv (Lvar x)) (vrv (Lvar x)) s in
    let: (s', c) := sc in
    let w :=
      if Sv.mem x s then guarded_while_of_for ii x d lo hi c
      else while_of_for ii x d lo hi c
    in
    ok (read_e_rec (read_e_rec s' e2) e1, cb ++ w)

  | Cwhile a c e info c' =>
    let dobody s_o :=
      let s_o' := read_e_rec s_o e in
      Let sci := for_to_while_c (for_to_while_i V) c s_o' in
      let: (s_i, c) := sci in
      Let sci' := for_to_while_c (for_to_while_i V) c' s_i in
      let: (s_i', c') := sci' in
      ok (s_i', (s_i, (c, c'))) in
    Let sc := dead_code.wloop dobody ii loop_counter s in
    let: (s, (c, c')) := sc in
    ok (s, [:: MkI ii (Cwhile a c e info c')])
  end.

Context {pT : progT}.

(* The results are read at the end of the function. *)
Definition for_to_while_fd (fd : fundef) : cexec fundef :=
  let s := read_es (map Plvar fd.(f_res)) in
  Let sc := for_to_while_c (for_to_while_i (vars_fd fd)) fd.(f_body) s in
  ok (with_body fd sc.2).

Definition for_to_while_prog (p : prog) : cexec prog :=
  Let funcs := map_cfprog for_to_while_fd (p_funcs p) in
  ok {| p_funcs := funcs; p_globs := p_globs p; p_extra := p_extra p |}.

End FOR_TO_WHILE.
