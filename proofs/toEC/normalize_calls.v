From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import word_ssrZ.
Require Import compiler_util expr sopn syscall wsize arch_decl arch_extra.

Module Import E.

  Definition pass : string := "normalize calls".

  Definition fresh_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "fresh auxiliary variable is not fresh".

  Definition unknown_fun_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "call to an unknown function".

  Definition aliasing_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii
      "rewritten destination aliases another destination's address".

End E.

Section NORMALIZE_CALLS.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
  (p : _uprog)
.

#[local] Existing Instance progUnit.

Definition ty_lval (lv : lval) : atype :=
  match lv with
  | Lnone _ ty => ty
  | Lvar x => x.(v_var).(vtype)
  | Lmem _ ws _ _ => aword ws
  | Laset _ _ ws _ _ => aword ws
  | Lasub _ ws len _ _ => aarr ws len
  end.

(* Note on array-typed mismatches: the rewrite below never needs a separate
   "array reinterpretation" well-formedness check. Unlike the REQUIREMENTS
   text's own recipe (which types the trailing [Cassgn] at [ty_lval lv_k]
   and inserts a [coerce], impossible to build for arrays of different
   shape), this pass types the [Cassgn] at the *source* type [t_k] (see
   [normalize_calls_dests] below), so [truncate_val t_k] is the identity and
   [write_lval lv_k] is called with the *exact* value/lval pair the
   original, unrewritten [write_lvals] would have used at that position --
   success or failure is identical either way, regardless of [ty_lval lv_k].
   An earlier version of this pass added such a check and it broke a real,
   previously-passing extraction test (`required_alignment.jazz`, a
   [reg ptr u8[4]] call result written into a declares-differently-shaped
   but same-byte-size [reg ptr u32[1]] destination) -- exactly the kind of
   reinterpretation the check wrongly rejected despite it being semantically
   safe by the argument above. *)

Fixpoint lvar_vars (lvs : lvals) : seq var :=
  match lvs with
  | [::] => [::]
  | Lvar x :: lvs => x.(v_var) :: lvar_vars lvs
  | _ :: lvs => lvar_vars lvs
  end.

(* Vars occurring more than once among [lvs]'s own [Lvar] destinations
   (e.g. [x, x = f(...)]): every such occurrence must go through the
   aux/[Cassgn] indirection, not just the later ones, so that the trailing
   [Cassgn]s -- which replay in the same left-to-right order as the
   original [write_lvals] -- reproduce "later write wins" exactly. *)
Fixpoint dup_vars_aux (seen dup : Sv.t) (vs : seq var) : Sv.t :=
  match vs with
  | [::] => dup
  | x :: vs =>
    if Sv.mem x seen then dup_vars_aux seen (Sv.add x dup) vs
    else dup_vars_aux (Sv.add x seen) dup vs
  end.

Definition dup_vars (lvs : lvals) : Sv.t :=
  dup_vars_aux Sv.empty Sv.empty (lvar_vars lvs).

(* [multi] is the "every destination must be a pairwise-distinct [Lvar] of
   the exact output type" requirement: always true for [Ccall]/[Csyscall],
   true for [Copn] only when it has 2+ outputs. A destination that is
   already a conforming [Lvar] of the right type, and not aliased by
   another [Lvar] destination of the same instruction, needs no rewrite. *)
Definition dest_needs_rewrite
  (multi : bool) (dups : Sv.t) (t : atype) (lv : lval) : bool :=
  match lv with
  | Lvar x => (x.(v_var).(vtype) != t) || (multi && Sv.mem x.(v_var) dups)
  | _ => multi || (ty_lval lv != t)
  end.

Fixpoint pos_tally (k : nat) : string :=
  match k with
  | 0 => ""%string
  | S k => ("x" ++ pos_tally k)%string
  end.

Definition normalize_calls_aux_var
  (ii : instr_info) (n : nat) (ty : atype) : var :=
  {| vtype := ty;
     vname :=
       fresh_var_ident (wsize.Reg (Normal, Direct)) ii
         ("aux" ++ pos_tally n) ty;
  |}.

(* The tally must be a name derived from [acc]'s own running size, not a
   per-instruction position freshly reset to 0 at every instruction:
   [flatten_while] (EJ-7) duplicates a while loop's pre-block verbatim,
   including its [instr_info], into two copies of the SAME instruction in
   one function body ("no renaming needed", by EJ-7's own design). Since
   [fresh_var_ident] memoizes on (kind, instr_info, name, type), a
   per-instruction-reset position tally would hand the SAME name (hence,
   via memoization, the SAME variable) to both copies' same-position
   output, and the very next line's freshness assert would then correctly
   -- but unhelpfully -- reject it as a genuine collision (observed empirically
   via `check-ci` on tests/success/x86-64/while.jazz and
   tests/success/arm-m4/call.jazz, both of which have a call/opn with a
   rewritten output inside a while loop's pre-block). [Sv.cardinal acc]
   increases strictly with every aux generated so far in this function
   (within one instruction's own outputs and across instructions alike),
   so the second copy's same-position aux always gets a larger tally, and
   hence -- via [fresh_var_ident]'s memoization -- a distinct variable. *)
Fixpoint normalize_calls_auxs
  (acc : Sv.t) (X : Sv.t) (ii : instr_info)
  (multi : bool) (dups : Sv.t)
  (lvs : lvals) (touts : seq atype)
  : cexec (Sv.t * seq (option var)) :=
  match lvs, touts with
  | [::], [::] => ok (acc, [::])
  | lv :: lvs, t :: touts =>
    if dest_needs_rewrite multi dups t lv then
      let x := normalize_calls_aux_var ii (Sv.cardinal acc) t in
      Let _ := assert (~~ Sv.mem x (Sv.union X acc)) (E.fresh_error ii) in
      Let acc_opts :=
        normalize_calls_auxs (Sv.add x acc) X ii multi dups lvs touts
      in
      ok (acc_opts.1, Some x :: acc_opts.2)
    else
      Let acc_opts :=
        normalize_calls_auxs acc X ii multi dups lvs touts
      in
      ok (acc_opts.1, None :: acc_opts.2)
  | _, _ => ok (acc, [::])
  end.

Fixpoint normalize_calls_dests
  (ii : instr_info) (t : assgn_tag)
  (lvs : lvals) (touts : seq atype) (opts : seq (option var))
  : lvals * cmd :=
  match lvs, touts, opts with
  | lv :: lvs, ty :: touts, o :: opts =>
    let '(lvs', cs') := normalize_calls_dests ii t lvs touts opts in
    match o with
    | Some x =>
      (Lvar {| v_var := x; v_info := dummy_var_info; |} :: lvs',
       MkI ii (Cassgn lv t ty
         (Plvar {| v_var := x; v_info := dummy_var_info; |})) :: cs')
    | None => (lv :: lvs', cs')
    end
  | _, _, _ => ([::], [::])
  end.

Fixpoint kept_lvs (lvs : lvals) (opts : seq (option var)) : lvals :=
  match lvs, opts with
  | lv :: lvs, None :: opts => lv :: kept_lvs lvs opts
  | _ :: lvs, Some _ :: opts => kept_lvs lvs opts
  | _, _ => [::]
  end.

Fixpoint rewritten_lvs (lvs : lvals) (opts : seq (option var)) : lvals :=
  match lvs, opts with
  | lv :: lvs, Some _ :: opts => lv :: rewritten_lvs lvs opts
  | _ :: lvs, None :: opts => rewritten_lvs lvs opts
  | _, _ => [::]
  end.

(* Whether a lvalue's OWN address ([Lmem]) or index ([Laset]/[Lasub])
   expression reads memory ([use_mem], [expr.v]) -- invisible to
   [read_rv]/[vrv], which only ever return variables. *)
Definition lv_use_mem (lv : lval) : bool :=
  match lv with
  | Lmem _ _ _ e | Laset _ _ _ _ e | Lasub _ _ _ _ e => use_mem e
  | _ => false
  end.

(* The mixed destination list writes every KEPT position directly, in
   original relative order, as part of the single [Copn]/[Ccall]/[Csyscall]
   -- exactly reproducing the original [write_lvals] order among kept
   positions. But every REWRITTEN position's real write is deferred to its
   own trailing [Cassgn], strictly after the WHOLE mixed write (i.e. after
   every kept position, even ones that came later in the original order).
   Mirroring remove_baseop_casts.v's own second/third/fourth/fifth
   corrections (the identical hazard, there for widened/non-widened
   positions): a kept position's own address/index expression must not
   read a variable written by a rewritten position, or vice versa; the two
   groups must not both write a variable in common; at most one of the two
   groups may write memory (else their relative memory-write order can
   differ from the original); and no destination's own address/index
   expression may read memory when any destination writes memory. Checked,
   not merely believed -- unlike EJ-8's x86-specific BaseOp case, this is
   genuinely reachable here (e.g. [a[i:2], i = f(x, y);] with a non-Lvar
   first destination and a kept second one). *)
Definition normalize_calls_aliasing_ok
  (lvs : lvals) (opts : seq (option var)) : bool :=
  let kept := kept_lvs lvs opts in
  let rewr := rewritten_lvs lvs opts in
  [&& disjoint (read_rvs kept) (vrvs rewr),
      disjoint (read_rvs rewr) (vrvs kept),
      disjoint (vrvs kept) (vrvs rewr),
      ~~ (has lv_write_mem kept && has lv_write_mem rewr)
    & (has lv_write_mem lvs ==> ~~ has lv_use_mem lvs)].

Definition normalize_calls_copn
  (acc : Sv.t) (X : Sv.t) (ii : instr_info)
  (lvs : lvals) (t : assgn_tag) (o : sopn) (es : pexprs)
  : cexec (Sv.t * cmd) :=
  let touts := sopn_tout o in
  let multi := 2 <= size lvs in
  let dups := dup_vars lvs in
  Let acc_opts := normalize_calls_auxs acc X ii multi dups lvs touts in
  let '(acc', opts) := acc_opts in
  Let _ :=
    assert (normalize_calls_aliasing_ok lvs opts) (E.aliasing_error ii)
  in
  let '(lvs', cs') := normalize_calls_dests ii t lvs touts opts in
  ok (acc', MkI ii (Copn lvs' t o es) :: cs').

Definition normalize_calls_syscall
  (acc : Sv.t) (X : Sv.t) (ii : instr_info)
  (lvs : lvals) (o : syscall_t) (es : pexprs)
  : cexec (Sv.t * cmd) :=
  let touts := (syscall_sig_u o).(scs_tout) in
  let dups := dup_vars lvs in
  Let acc_opts := normalize_calls_auxs acc X ii true dups lvs touts in
  let '(acc', opts) := acc_opts in
  Let _ :=
    assert (normalize_calls_aliasing_ok lvs opts) (E.aliasing_error ii)
  in
  let '(lvs', cs') := normalize_calls_dests ii AT_none lvs touts opts in
  ok (acc', MkI ii (Csyscall lvs' o es) :: cs').

Definition normalize_calls_call
  (acc : Sv.t) (X : Sv.t) (ii : instr_info)
  (lvs : lvals) (f : funname) (es : pexprs)
  : cexec (Sv.t * cmd) :=
  Let fd :=
    match get_fundef (p_funcs p) f with
    | Some fd => ok fd
    | None => Error (E.unknown_fun_error ii)
    end
  in
  let touts := fd.(f_tyout) in
  let dups := dup_vars lvs in
  Let acc_opts := normalize_calls_auxs acc X ii true dups lvs touts in
  let '(acc', opts) := acc_opts in
  Let _ :=
    assert (normalize_calls_aliasing_ok lvs opts) (E.aliasing_error ii)
  in
  let '(lvs', cs') := normalize_calls_dests ii AT_none lvs touts opts in
  ok (acc', MkI ii (Ccall lvs' f es) :: cs').

Section CMD.

Context (normalize_calls_i : Sv.t -> Sv.t -> instr -> cexec (Sv.t * cmd)).

Fixpoint normalize_calls_c
  (acc : Sv.t) (X : Sv.t) (c : cmd) : cexec (Sv.t * cmd) :=
  match c with
  | [::] => ok (acc, [::])
  | i :: c =>
    Let ai := normalize_calls_i acc X i in
    Let ac := normalize_calls_c ai.1 X c in
    ok (ac.1, ai.2 ++ ac.2)
  end.

End CMD.

Fixpoint normalize_calls_i
  (acc : Sv.t) (X : Sv.t) (i : instr) : cexec (Sv.t * cmd) :=
  let 'MkI ii ir := i in
  match ir with
  | Cassgn _ _ _ _ | Cassert _ => ok (acc, [:: i])
  | Copn lvs t o es => normalize_calls_copn acc X ii lvs t o es
  | Csyscall lvs o es => normalize_calls_syscall acc X ii lvs o es
  | Ccall lvs f es => normalize_calls_call acc X ii lvs f es
  | Cif e c1 c2 =>
    Let ac1 := normalize_calls_c normalize_calls_i acc X c1 in
    Let ac2 := normalize_calls_c normalize_calls_i ac1.1 X c2 in
    ok (ac2.1, [:: MkI ii (Cif e ac1.2 ac2.2)])
  | Cfor x r c =>
    Let ac := normalize_calls_c normalize_calls_i acc X c in
    ok (ac.1, [:: MkI ii (Cfor x r ac.2)])
  | Cwhile al c1 e info c2 =>
    Let ac1 := normalize_calls_c normalize_calls_i acc X c1 in
    Let ac2 := normalize_calls_c normalize_calls_i ac1.1 X c2 in
    ok (ac2.1, [:: MkI ii (Cwhile al ac1.2 e info ac2.2)])
  end.

Definition normalize_calls_fd (fd : _fundef unit) : cexec (_fundef unit) :=
  let X := vars_fd fd in
  Let ac := normalize_calls_c normalize_calls_i Sv.empty X fd.(f_body) in
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

Definition normalize_calls_prog : cexec _uprog :=
  Let funcs := map_cfprog normalize_calls_fd (p_funcs p) in
  ok {|
    p_funcs := funcs;
    p_globs := p_globs p;
    p_extra := p_extra p;
  |}.

End NORMALIZE_CALLS.
