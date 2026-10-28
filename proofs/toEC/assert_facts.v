(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From Coq Require Import ZArith.
From mathcomp Require Import word_ssrZ.
Require Import expr compiler_util.

Local Open Scope seq_scope.

(* ** The assertions already established

   A forward analysis of each function body computes, at each program point,
   a set of facts: conjuncts of assertions evaluated to [true] earlier on
   every path that reaches the point, such that nothing they read has been
   written since. The evaluation of an assertion is deterministic and depends
   only on the variables it reads, on the content of the memory when it
   loads from it, and on the readable bytes of the memory: a fact still
   holds. A conjunct of an assertion that a fact implies is removed, and so
   is an assertion with no conjunct left; the rest of the code is unchanged.

   A fact implies a conjunct when they are equal (up to the information on
   the variables), or when both test the initialisation of the same mask, on
   constant ranges, the range of the conjunct included in that of the fact:
   the mask evaluates as it did, to an array of the right length.

   A write to a variable removes the facts that read it. A write to the
   memory, a call and a system call remove the facts that load from the
   memory; no instruction makes a readable byte of the memory unreadable, so
   the facts [Pis_mem_init] still hold. At the head of a loop, the facts that
   read what the loop writes are removed; the others hold at each iteration. *)

Section ASM_OP.

Context `{asmop:asmOp}.

(* ------------------------------------------------------------------------- *)
(* Facts                                                                      *)

(* The conjuncts of an assertion: those of [Pand] and of the boolean
   conjunction, both of which evaluate their two sides and require
   booleans. *)
Fixpoint conj_pexpr (e : pexpr) : seq eassert :=
  match e with
  | Papp2 Oand e1 e2 => conj_pexpr e1 ++ conj_pexpr e2
  | _ => [:: Pexpr e]
  end.

Fixpoint conjuncts (a : eassert) : seq eassert :=
  match a with
  | Pand a1 a2 => conjuncts a1 ++ conjuncts a2
  | Pexpr e => conj_pexpr e
  | _ => [:: a]
  end.

Fixpoint mk_and (a : eassert) (as_ : seq eassert) : eassert :=
  if as_ is a' :: as_ then Pand a (mk_and a' as_) else a.

Definition implies (f a : eassert) : bool :=
  eq_eassert f a ||
  match f, a with
  | PappN_safety (Ois_barr_init len) [:: m; Pconst lo; Pconst n],
    PappN_safety (Ois_barr_init len') [:: m'; Pconst lo'; Pconst n'] =>
    [&& len == len', eq_expr m m'
      & (n' <=? 0)%Z || (lo <=? lo')%Z && (lo' + n' <=? lo + n)%Z]
  | _, _ => false
  end.

(* The assertion loads from the memory. *)
Definition load_mem (a : eassert) : bool :=
  let fix aux a :=
    match a with
    | Pexpr e => use_mem e
    | PappN_safety _ es => has use_mem es
    | Pis_var_init _ => false
    | Pis_mem_init e1 e2 => use_mem e1 || use_mem e2
    | Pand a1 a2 => aux a1 || aux a2
    end in
  aux a.

(* The facts after a write to the variables [xs], and to the memory if
   [mem]. *)
Definition fkill (fs : seq eassert) (xs : Sv.t) (mem : bool) : seq eassert :=
  filter (fun f => Sv.is_empty (Sv.inter (read_eassert f) xs) && ~~ (mem && load_mem f)) fs.

(* The facts on both paths. *)
Definition fjoin (fs1 fs2 : seq eassert) : seq eassert :=
  filter (fun f => has (eq_eassert f) fs2) fs1.

(* The assertion [a] given the facts [fs]: the conjuncts that remain (none
   when the assertion is removed) and the facts after it. *)
Definition fassert (fs : seq eassert) (a : eassert) : seq eassert * seq eassert :=
  foldl (fun (acc : seq eassert * seq eassert) c =>
           let: (fs, keep) := acc in
           if has (implies^~ c) fs then acc else (c :: fs, rcons keep c))
    (fs, [::]) (conjuncts a).

(* ------------------------------------------------------------------------- *)
(* Instructions                                                               *)

Fixpoint write_mem_i (i : instr) : bool :=
  let: MkI _ ir := i in
  match ir with
  | Cassgn lv _ _ _ => lv_write_mem lv
  | Copn lvs _ _ _ => has lv_write_mem lvs
  | Csyscall _ _ _ | Ccall _ _ _ => true
  | Cassert _ => false
  | Cif _ c1 c2 | Cwhile _ c1 _ _ c2 => has write_mem_i c1 || has write_mem_i c2
  | Cfor _ _ c => has write_mem_i c
  end.

Section CMD.

Context (facts_i : seq eassert -> instr -> seq eassert * cmd).

Fixpoint facts_c (fs : seq eassert) (c : cmd) : seq eassert * cmd :=
  match c with
  | [::] => (fs, [::])
  | i :: c =>
    let: (fs, ci) := facts_i fs i in
    let: (fs, c) := facts_c fs c in
    (fs, ci ++ c)
  end.

End CMD.

Fixpoint facts_i (fs : seq eassert) (i : instr) : seq eassert * cmd :=
  let: MkI ii ir := i in
  match ir with
  | Cassgn lv _ _ _ => (fkill fs (vrv lv) (lv_write_mem lv), [:: i])
  | Copn lvs _ _ _ => (fkill fs (vrvs lvs) (has lv_write_mem lvs), [:: i])
  | Csyscall lvs _ _ | Ccall lvs _ _ => (fkill fs (vrvs lvs) true, [:: i])
  | Cassert (lbl, a) =>
    let: (fs', keep) := fassert fs a in
    let c :=
      match keep with
      | [::] => [::]
      | k :: ks =>
        (* an assertion with all its conjuncts is left as it is *)
        if size keep == size (conjuncts a) then [:: i]
        else [:: MkI ii (Cassert (lbl, mk_and k ks))]
      end in
    (fs', c)
  | Cif e c1 c2 =>
    let: (fs1, c1) := facts_c facts_i fs c1 in
    let: (fs2, c2) := facts_c facts_i fs c2 in
    (fjoin fs1 fs2, [:: MkI ii (Cif e c1 c2)])
  | Cfor x r c =>
    let fs := fkill fs (Sv.add x (write_c c)) (has write_mem_i c) in
    let: (_, c) := facts_c facts_i fs c in
    (fs, [:: MkI ii (Cfor x r c)])
  (* the loop exits after [c1] *)
  | Cwhile al c1 e ii_w c2 =>
    let fs := fkill fs (Sv.union (write_c c1) (write_c c2))
                    (has write_mem_i c1 || has write_mem_i c2) in
    let: (fs1, c1) := facts_c facts_i fs c1 in
    let: (_, c2) := facts_c facts_i fs1 c2 in
    (fs1, [:: MkI ii (Cwhile al c1 e ii_w c2)])
  end.

Definition assert_facts_fd (fd : ufundef) : ufundef :=
  with_body fd (facts_c facts_i [::] fd.(f_body)).2.

Definition assert_facts_prog (p : _uprog) : _uprog :=
  map_prog assert_facts_fd p.

End ASM_OP.
