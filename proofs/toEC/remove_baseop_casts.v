From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util expr arch_decl arch_extra.

Module Import E.

  Definition pass : string := "remove baseop casts".

  Definition fresh_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "fresh auxiliary variable is not fresh".

  Definition aliasing_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii
      "widened output aliases another destination's address".

End E.

Section REMOVE_BASEOP_CASTS.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
.

#[local] Existing Instance progUnit.

(* [fresh_var_ident] is memoized by the OCaml oracle on (kind, instruction,
   name, type) (`Conv.fresh_var_ident`): two calls at the same instruction
   with the same name and type return the *same* variable, not two fresh
   ones. A single [Copn] can have several outputs of the same type (e.g.
   several boolean flags), so each output's auxiliary needs a name that
   depends on its position [k] in the output list, not just on its type. *)
Fixpoint pos_tally (k : nat) : string :=
  match k with
  | 0 => ""%string
  | S k => ("x" ++ pos_tally k)%string
  end.

Definition remove_baseop_casts_aux_var
  (ii : instr_info) (k : nat) (ty : atype) : var :=
  {| vtype := ty;
     vname :=
       fresh_var_ident (wsize.Reg (Normal, Direct)) ii
         ("aux" ++ pos_tally k) ty;
  |}.

Definition remove_baseop_casts_rhs (aux : var) (ty ty' : atype) : pexpr :=
  let e := Plvar {| v_var := aux; v_info := dummy_var_info; |} in
  match ty, ty' with
  | aword ws, aword ws' => if ws == ws' then e else Papp1 (Ozeroext ws' ws) e
  | _, _ => e
  end.

(* An output position needs the aux+[Cassgn] indirection only when it is a
   word whose size actually changes; every other position (in particular
   every [cbool] output, and any word output whose size is unchanged) can be
   written directly by the bare [Copn] and needs no bridging at all. *)
Definition remove_baseop_casts_needs_widen (ty ty' : atype) : bool :=
  match ty, ty' with
  | aword ws, aword ws' => ws != ws'
  | _, _ => false
  end.

Fixpoint remove_baseop_casts_auxs
  (acc : Sv.t) (X : Sv.t) (ii : instr_info) (k : nat)
  (touts touts' : seq atype) : cexec (Sv.t * seq (option var)) :=
  match touts, touts' with
  | [::], [::] => ok (acc, [::])
  | ty :: touts, ty' :: touts' =>
    if remove_baseop_casts_needs_widen ty ty' then
      let x := remove_baseop_casts_aux_var ii k ty in
      Let _ := assert (~~ Sv.mem x (Sv.union X acc)) (E.fresh_error ii) in
      Let acc_xs :=
        remove_baseop_casts_auxs (Sv.add x acc) X ii (S k) touts touts'
      in
      ok (acc_xs.1, Some x :: acc_xs.2)
    else
      Let acc_xs := remove_baseop_casts_auxs acc X ii (S k) touts touts' in
      ok (acc_xs.1, None :: acc_xs.2)
  | _, _ => ok (acc, [::])
  end.

(* The set of *real* destination variables of the positions classified
   [Some] by [remove_baseop_casts_auxs] (i.e. genuinely widened): during
   the bare [Copn]'s own [write_lvals] these positions are NOT written at
   all (a fresh aux is written instead, [remove_baseop_casts_dests]
   below), so this is exactly the "pending / not yet resolved" set that
   the aliasing check right below must keep disjoint from every
   destination's own read set. *)
Fixpoint widen_vars (lvs : seq lval) (opts : seq (option var)) : Sv.t :=
  match lvs, opts with
  | lv :: lvs, Some _ :: opts => Sv.union (vrv lv) (widen_vars lvs opts)
  | _ :: lvs, None :: opts => widen_vars lvs opts
  | _, _ => Sv.empty
  end.

(* The non-widened, resp. widened, positions' own lvalues, split out of
   [lvs]. A position's own self-read of its own destination (e.g. a
   [Laset]/[Lasub] reading its own array variable) is never a hazard --
   [remove_baseop_casts_dests] resolves each position's own write together
   with that very position, whether in the bare [Copn] (non-widened) or in
   its dedicated [Cassgn] catch-up (widened) -- so splitting the two kinds
   of positions apart before comparing reads against writes avoids every
   such spurious self-overlap. *)
Fixpoint nonwiden_lvs (lvs : seq lval) (opts : seq (option var)) : seq lval :=
  match lvs, opts with
  | lv :: lvs, Some _ :: opts => nonwiden_lvs lvs opts
  | lv :: lvs, None :: opts => lv :: nonwiden_lvs lvs opts
  | _, _ => [::]
  end.

Fixpoint widen_lvs (lvs : seq lval) (opts : seq (option var)) : seq lval :=
  match lvs, opts with
  | lv :: lvs, Some _ :: opts => lv :: widen_lvs lvs opts
  | _ :: lvs, None :: opts => widen_lvs lvs opts
  | _, _ => [::]
  end.

(* Whether a lvalue's OWN address ([Lmem]) or index ([Laset]/[Lasub])
   expression reads memory ([use_mem], [expr.v]). See the fifth
   correction below (at the [aliasing_error] assert): [read_rv]/[vrv],
   being plain [Sv.t]s, cannot see this at all. *)
Definition lv_use_mem (lv : lval) : bool :=
  match lv with
  | Lmem _ _ _ e | Laset _ _ _ _ e | Lasub _ _ _ _ e => use_mem e
  | _ => false
  end.

Fixpoint remove_baseop_casts_dests
  (ii : instr_info) (t : assgn_tag)
  (lvs : seq lval) (touts touts' : seq atype) (opts : seq (option var))
  : seq lval * cmd :=
  match lvs, touts, touts', opts with
  | lv :: lvs, ty :: touts, ty' :: touts', o :: opts =>
    let '(lvs', cs') :=
      remove_baseop_casts_dests ii t lvs touts touts' opts
    in
    match o with
    | Some x =>
      (Lvar {| v_var := x; v_info := dummy_var_info; |} :: lvs',
       MkI ii (Cassgn lv t ty' (remove_baseop_casts_rhs x ty ty')) :: cs')
    | None => (lv :: lvs', cs')
    end
  | _, _, _, _ => ([::], [::])
  end.

Definition remove_baseop_casts_copn
  (acc : Sv.t) (X : Sv.t) (ii : instr_info)
  (lvs : seq lval) (t : assgn_tag) (ws : wsize) (o : asm_op) (es : pexprs)
  : cexec (Sv.t * cmd) :=
  let bare : extended_op := BaseOp (None, o) in
  let op : extended_op := BaseOp (Some ws, o) in
  let touts := sopn_tout (Oasm bare) in
  let touts' := sopn_tout (Oasm op) in
  Let acc_opts := remove_baseop_casts_auxs acc X ii 0 touts touts' in
  let '(acc', opts) := acc_opts in
  (* Splitting the [Copn] into a bare op over a mixed destination list
     (fresh aux for widened positions, the original lval elsewhere)
     followed by trailing per-widened-position [Cassgn]s changes the
     write order within this one instruction, in TWO ways:
     - a non-widened position's own lvalue (only [Lmem]'s address is at
       risk, since it is the only lvalue-kind that can *read* a variable)
       must not read a variable that is itself another, genuinely-widened
       position's destination: the bare [Copn] (phase A) writes a fresh
       aux there instead of that destination, so its real value is still
       the pre-instruction one when this read happens, whereas the
       original's single sequential [write_lvals] may already have
       applied it (if the widened position comes first).
     - symmetrically, a widened position's own lvalue is resolved only in
       its [Cassgn] catch-up, strictly AFTER every non-widened position's
       real write has already landed (they are all part of the one bare
       [Copn]) -- so it must not read a variable that is itself another,
       non-widened position's destination: the original evaluates that
       read at the widened position's own (possibly earlier) place in the
       sequence, before the non-widened position (if it comes later) has
       written it, whereas the split code always evaluates it after.
     Neither direction fires for any current instruction (checked against
     x86_instr_decl.v: multi-word outputs share a width uniformly and
     flags always precede words, so no instruction mixes widened and
     non-widened positions at all), but neither is derivable from the
     abstract [asm_op_decl] interface, so both are checked here rather
     than merely assumed. A position's own self-read of its own
     destination (e.g. a [Laset] reading its own array variable) is not a
     cross-position hazard, hence the split into [nonwiden_lvs]/
     [widen_lvs] before comparing reads against the other group's writes,
     rather than comparing the whole [lvs] against itself.

     Third correction (found while proving the write-order fix above,
     phase-4 of the proof): the two [Sv]-based checks above only protect
     against a position's OWN LVALUE READING a variable written by the
     other group -- [Lmem]'s write itself (the memory cell it stores to)
     is invisible to [vrv]/[read_rv] ([vrv] of an [Lmem] is always
     [Sv.empty], since a memory write touches no variable at all), so
     they give NO protection against the write ORDER of two [Lmem] destinations
     straddling the widened/non-widened split: the bare [Copn] (phase A)
     applies every non-widened [Lmem] write, in original relative order,
     strictly BEFORE any widened [Lmem]'s [Cassgn] catch-up (phase B),
     whereas the original, single, sequential [write_lvals] may interleave
     them in either relative order. If two such addresses alias at
     runtime, the final memory content depends on which write is applied
     last, and the split code's phase-A/phase-B batching can disagree with
     the original's per-position order whenever a widened [Lmem] precedes
     a non-widened one (or vice versa) in [lvs]. This can never happen for
     any current instruction (no x86 instruction mixes widened/
     non-widened positions at all, per the point above, so there is never
     a widened AND a non-widened [Lmem] in the same instruction), but is
     not derivable from the two [Sv]-based checks, so it is checked
     directly here too.

     Fourth correction (found while proving the write-order fix, phase-4
     of the proof, same session as the third): the first two [Sv]-based
     checks compare a position's [read_rv] (what that lvalue itself
     READS -- an [Lmem] address, a [Laset]/[Lasub] index) against the
     OTHER group's WRITES ([vrv]s). They give no protection at all
     against two positions -- one widened, one non-widened -- that both
     WRITE the *same* variable (e.g. two [Lvar]-destinations naming the
     same [var]): [read_rv (Lvar x) = Sv.empty] ([expr.v]'s
     [read_rv_rec]: an [Lvar] does not read the variable it overwrites),
     so such a pair is invisible to both [Sv]-based conjuncts, yet it is
     a genuine hazard distinct from the [Lmem]-write-order one above: if
     the non-widened position comes AFTER the widened one in [lvs], the
     original's single sequential [write_lvals] gives the NON-widened
     write the last word on that variable, whereas the split code always
     applies the widened position's [Cassgn] catch-up last (strictly
     after the whole bare [Copn], which is where the non-widened write
     lives), so the split code would incorrectly let the WIDENED value
     win instead. Not excluded by any current check (verified: the
     existing three conjuncts say nothing about [vrv] vs [vrv]), and not
     derivable from the abstract [asm_op_decl] interface for the same
     reason as the other three (it needs 2+ word outputs of differing
     native width in one instruction -- the same precondition that makes
     all four checks currently vacuous). Closed the same way: a fourth
     checked conjunct, comparing [vrvs] against [vrvs] (equivalently,
     since [widen_vars lvs opts] and [vrvs (widen_lvs lvs opts)] are the
     same set by construction, [disjoint] is symmetric in its own
     argument, so one direction suffices, matching the existing
     one-directional style of the first two conjuncts).

     Fifth correction (found while proving the write-order fix, phase-4
     of the proof, same session as the third and fourth): all four
     checks above reason about a lvalue's [read_rv]/[vrv] -- a SET OF
     VARIABLES -- but [Lmem]'s address and [Laset]/[Lasub]'s index are
     arbitrary [pexpr]s ([expr.v]'s [pexpr] has a [Pload] constructor),
     so a destination's OWN address/index expression can itself read
     MEMORY, a dependency [read_rv] cannot see at all (it only ever
     returns variables). If [lvs] contains an actual memory WRITE
     ([lv_write_mem], necessarily in only one of the two groups per the
     third conjunct) and some OTHER position's address/index expression
     [use_mem]s ([expr.v]), reordering the two groups (phase A applies
     every non-widened write, in original order, strictly before phase
     B's widened catch-up) can change what that memory-dependent
     sub-expression observes, even though every [read_rv]/[vrv] set
     stays exactly as before -- a hazard invisible to all four preceding
     conjuncts. Not a hypothetical concern specific to this pass: the
     project already has the identical concept, checked the identical
     way, for the identical reason, at
     [compiler/makeReferenceArguments.v]'s [wflv] (its [Lasub] case is
     exactly [~~ use_mem e]) and at [compiler/slh_lowering.v]'s
     [assert (~~ use_mem cond) ...] -- both existing precedents for
     "moving/reordering code relative to a lvalue's own expression
     requires that expression to not read memory". Harmless for any
     current x86 instruction (a [BaseOp]'s destination address/index
     expressions, as generated for the test corpus, never contain a
     memory load), but -- like all the checks above -- not derivable
     from the abstract interface, so checked directly: if any position
     writes memory, no position's own address/index expression may read
     memory. *)
  Let _ :=
    assert
      (disjoint (read_rvs (nonwiden_lvs lvs opts)) (widen_vars lvs opts) &&
       disjoint (read_rvs (widen_lvs lvs opts)) (vrvs (nonwiden_lvs lvs opts)) &&
       ~~ (has lv_write_mem (nonwiden_lvs lvs opts) &&
           has lv_write_mem (widen_lvs lvs opts)) &&
       disjoint (vrvs (nonwiden_lvs lvs opts)) (widen_vars lvs opts) &&
       (has lv_write_mem lvs ==> ~~ has lv_use_mem lvs))
      (E.aliasing_error ii)
  in
  let '(lvs', cmds') :=
    remove_baseop_casts_dests ii t lvs touts touts' opts
  in
  ok (acc', MkI ii (Copn lvs' t (Oasm bare) es) :: cmds').

Section CMD.

Context (remove_baseop_casts_i : Sv.t -> Sv.t -> instr -> cexec (Sv.t * cmd)).

Fixpoint remove_baseop_casts_c
  (acc : Sv.t) (X : Sv.t) (c : cmd) : cexec (Sv.t * cmd) :=
  match c with
  | [::] => ok (acc, [::])
  | i :: c =>
    Let ai := remove_baseop_casts_i acc X i in
    Let ac := remove_baseop_casts_c ai.1 X c in
    ok (ac.1, ai.2 ++ ac.2)
  end.

End CMD.

Fixpoint remove_baseop_casts_i
  (acc : Sv.t) (X : Sv.t) (i : instr) : cexec (Sv.t * cmd) :=
  let 'MkI ii ir := i in
  match ir with
  | Cassgn _ _ _ _ | Csyscall _ _ _ | Cassert _ | Ccall _ _ _ =>
    ok (acc, [:: i])
  | Copn lvs t o es =>
    match o with
    | Oasm (BaseOp (Some ws, bo)) =>
      remove_baseop_casts_copn acc X ii lvs t ws bo es
    | _ => ok (acc, [:: i])
    end
  | Cif e c1 c2 =>
    Let ac1 := remove_baseop_casts_c remove_baseop_casts_i acc X c1 in
    Let ac2 := remove_baseop_casts_c remove_baseop_casts_i ac1.1 X c2 in
    ok (ac2.1, [:: MkI ii (Cif e ac1.2 ac2.2)])
  | Cfor x r c =>
    Let ac := remove_baseop_casts_c remove_baseop_casts_i acc X c in
    ok (ac.1, [:: MkI ii (Cfor x r ac.2)])
  | Cwhile al c1 e info c2 =>
    Let ac1 := remove_baseop_casts_c remove_baseop_casts_i acc X c1 in
    Let ac2 := remove_baseop_casts_c remove_baseop_casts_i ac1.1 X c2 in
    ok (ac2.1, [:: MkI ii (Cwhile al ac1.2 e info ac2.2)])
  end.

Definition remove_baseop_casts_fd (fd : _fundef unit) : cexec (_fundef unit) :=
  let X := vars_fd fd in
  Let ac :=
    remove_baseop_casts_c remove_baseop_casts_i Sv.empty X fd.(f_body)
  in
  ok {|
    f_info := f_info fd;
    f_contract := f_contract fd;
    f_tyin := f_tyin fd;
    f_params := f_params fd;
    f_body := ac.2;
    f_tyout := f_tyout fd;
    f_res := f_res fd;
    f_extra := f_extra fd;
  |}.

Definition remove_baseop_casts_prog (p : _uprog) : cexec _uprog :=
  Let funcs := map_cfprog remove_baseop_casts_fd (p_funcs p) in
  ok {|
    p_funcs := funcs;
    p_globs := p_globs p;
    p_extra := p_extra p;
  |}.

End REMOVE_BASEOP_CASTS.
