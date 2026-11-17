From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Coq Require Import Uint63.
Require Import expr compiler_util.
Import Utf8.

(* The extraction to EasyCrypt prints a function call, a system call or an
   operator with several outputs as a procedure call or a tuple assignment,
   whose destinations must be distinct variables of the output types. This
   pass puts these instructions in that form.

   An instruction is rewritten when one of its destinations does not fit:
   a variable of another type, a variable written twice, a memory cell, an
   array cell or a sub-array. In a rewritten instruction, a destination
   becomes:

   - itself, when it is a boolean variable receiving a boolean output (a
     flag): a flag may be undefined, and an undefined value cannot go through
     a copy;
   - an auxiliary variable that is not copied, when it is [_];
   - an auxiliary variable of the output type otherwise, copied into the
     original destination after the instruction; the copies follow the order
     of the destinations.

   The pass fails on a rewritten instruction that writes a flag twice, or
   whose copied destination reads a flag that a later output writes: the
   copy would read the new value of the flag.

   The auxiliary variables are named [aux]; within a function, the k-th
   auxiliary variable of a type is shared by all the instructions, so that
   the extraction declares few variables. The arrays are compared by their
   type or, when [arrays_by_size] holds, by their size: the extraction with
   byte arrays gives one representation to arrays of the same size. *)

Module Import E.

  Definition pass : string := "normalize calls".

  Definition fresh_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "fresh auxiliary variable is not fresh".

  Definition unknown_fun_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "call to an unknown function".

  Definition flag_error (ii : instr_info) := {|
    pel_msg :=
      pp_box [:: pp_s "a flag is written twice, or a destination reads a flag";
                 pp_s "that a later output of the instruction writes"];
    pel_fn := None;
    pel_fi := None;
    pel_ii := Some ii;
    pel_vi := None;
    pel_pass := Some pass;
    pel_internal := false
  |}.

End E.

Section NORMALIZE_CALLS.

Context `{asmop : asmOp} {pd : PointerData} {msfsz : MSFsize} {pT : progT}.
Context (fresh_var_ident : v_kind -> instr_info -> int -> string -> atype -> Ident.ident).

(* Whether the arrays are compared by their size (two arrays of the same size
   have the same representation in the extraction) or by their type. *)
Context (arrays_by_size : bool).

(* Whether a destination of type [t] may receive an output of type [t']. *)
Definition fits (t t' : atype) : bool :=
  if arrays_by_size then convertible t t' else t == t'.

(* The type of the auxiliary variable receiving an output of type [t]. *)
Definition aux_type (t : atype) : atype :=
  if arrays_by_size then
    if t is aarr ws len then aarr U8 (arr_size ws len) else t
  else t.

(* A flag position: a boolean variable receiving a boolean output. *)
Definition flag_dest (lv : lval) (t : atype) : option var_i :=
  if lv is Lvar x then
    if (vtype x == abool) && (t == abool) then Some x else None
  else None.

(* The flags written by the flag positions of [lvs]. *)
Fixpoint flag_vars (lvs : lvals) (touts : seq atype) : Sv.t :=
  match lvs, touts with
  | lv :: lvs, t :: touts =>
    let s := flag_vars lvs touts in
    if flag_dest lv t is Some y then Sv.add y s else s
  | _, _ => Sv.empty
  end.

(* No flag is written twice, and no destination that is not a flag reads a
   flag that a later position writes. *)
Fixpoint flags_ok (lvs : lvals) (touts : seq atype) : bool :=
  match lvs, touts with
  | lv :: lvs, t :: touts =>
    let later := flag_vars lvs touts in
    (if flag_dest lv t is Some x then ~~ Sv.mem x later
     else disjoint (read_rv lv) later)
    && flags_ok lvs touts
  | _, _ => true
  end.

(* The type of the values written by a destination. *)
Definition ty_lval (lv : lval) : atype :=
  match lv with
  | Lnone _ t => t
  | Lvar x => vtype x
  | Lmem _ ws _ _ | Laset _ _ ws _ _ => aword ws
  | Lasub _ ws len _ _ => aarr ws len
  end.

Context (p : prog).

Section FUNDEF.

(* [fii] is the entry of the function and [X] the set of its variables. *)
Context (fii : instr_info) (X : Sv.t).

(* The auxiliary variables of an instruction are named [aux]; [acc] holds the
   ones already created for the current instruction. The [k]-th auxiliary
   variable of a type is the same variable in every instruction of the
   function: the oracle is memoising and receives the entry of the function. *)
Definition aux_rank (acc : Sv.t) (t : atype) : int :=
  Sv.fold (fun y k => if vtype y == t then Uint63.succ k else k) acc 0%uint63.

Definition fresh_aux (ii : instr_info) (acc : Sv.t) (t : atype) : cexec (Sv.t * var_i) :=
  let t := aux_type t in
  let x :=
    {| vtype := t;
       vname := fresh_var_ident (Reg (Normal, Direct)) fii (aux_rank acc t) "aux" t;
    |}
  in
  Let _ := assert (~~ Sv.mem x (Sv.union X acc)) (E.fresh_error ii) in
  ok (Sv.add x acc, {| v_var := x; v_info := var_info_of_ii ii |}).

(* The destinations that are not flags get an auxiliary variable, copied
   after the instruction unless the destination is [_]. *)
Fixpoint nc_dests (ii : instr_info) (tg : assgn_tag) (acc : Sv.t)
  (lvs : lvals) (touts : seq atype) : cexec (Sv.t * lvals * cmd) :=
  match lvs, touts with
  | lv :: lvs, t :: touts =>
    if flag_dest lv t is Some _ then
      Let: (acc, xs, c) := nc_dests ii tg acc lvs touts in
      ok (acc, lv :: xs, c)
    else
      Let: (acc, aux) := fresh_aux ii acc t in
      Let: (acc, xs, c) := nc_dests ii tg acc lvs touts in
      let c :=
        if lv is Lnone _ _ then c
        else MkI ii (Cassgn lv tg (ty_lval lv) (Plvar aux)) :: c
      in
      ok (acc, Lvar aux :: xs, c)
  | _, _ => ok (acc, [::], [::])
  end.

Definition lvar_count (x : var) (lvs : lvals) : nat :=
  count (fun lv => if lv is Lvar y then v_var y == x else false) lvs.

(* A destination that does not fit: a variable of another type or written
   twice, a memory cell, an array cell or a sub-array. *)
Definition bad_dest (lvs : lvals) (lv : lval) (t : atype) : bool :=
  match lv with
  | Lnone _ _ => false
  | Lvar x => ~~ fits (vtype x) t || (1 < lvar_count x lvs)
  | _ => true
  end.

(* Instructions whose destinations do not match the outputs are left as
   they are. *)
Definition dests_match (lvs : lvals) (touts : seq atype) : bool :=
  all2 (fun lv t => if lv is Lnone _ ty then fits ty t else true) lvs touts.

Definition needs_rewrite (lvs : lvals) (touts : seq atype) : bool :=
  dests_match lvs touts
  && has (fun '(lv, t) => bad_dest lvs lv t) (zip lvs touts).

(* The new destinations and the instructions to run after. *)
Definition normalize_dests (ii : instr_info) (tg : assgn_tag)
  (lvs : lvals) (touts : seq atype) : cexec (lvals * cmd) :=
  if needs_rewrite lvs touts then
    Let _ := assert (flags_ok lvs touts) (E.flag_error ii) in
    Let: (_, xs, c) := nc_dests ii tg Sv.empty lvs touts in
    ok (xs, c)
  else ok (lvs, [::]).

(* The instruction built by [mk] on the new destinations, followed by the
   instructions to run after. *)
Definition normalize_dests_i (ii : instr_info) (tg : assgn_tag)
  (lvs : lvals) (touts : seq atype) (mk : lvals -> instr_r) :
  cexec cmd :=
  Let: (xs, c) := normalize_dests ii tg lvs touts in
  ok (MkI ii (mk xs) :: c).

Section CMD.

Context (normalize_calls_i : instr -> cexec cmd).

Fixpoint normalize_calls_c (c : cmd) : cexec cmd :=
  match c with
  | [::] => ok [::]
  | i :: c =>
    Let ci := normalize_calls_i i in
    Let cc := normalize_calls_c c in
    ok (ci ++ cc)
  end.

End CMD.

Fixpoint normalize_calls_i (i : instr) : cexec cmd :=
  let nc_c := normalize_calls_c normalize_calls_i in
  let 'MkI ii ir := i in
  match ir with
  | Cassgn _ _ _ _ | Cassert _ => ok [:: i]
  (* an operator with a single destination is printed as an assignment *)
  | Copn lvs tg o es =>
    if 1 < size lvs then
      normalize_dests_i ii tg lvs (sopn_tout o) (fun xs => Copn xs tg o es)
    else ok [:: i]
  | Csyscall lvs o es =>
    normalize_dests_i ii AT_none lvs (scs_tout (syscall_sig_u o))
      (fun xs => Csyscall xs o es)
  | Ccall lvs f es =>
    Let fd := o2r (E.unknown_fun_error ii) (get_fundef (p_funcs p) f) in
    normalize_dests_i ii AT_none lvs (f_tyout fd) (fun xs => Ccall xs f es)
  | Cif e c1 c2 =>
    Let c1 := nc_c c1 in
    Let c2 := nc_c c2 in
    ok [:: MkI ii (Cif e c1 c2)]
  | Cfor x r c =>
    Let c := nc_c c in
    ok [:: MkI ii (Cfor x r c)]
  | Cwhile al c1 e info c2 =>
    Let c1 := nc_c c1 in
    Let c2 := nc_c c2 in
    ok [:: MkI ii (Cwhile al c1 e info c2)]
  end.

End FUNDEF.

Definition normalize_calls_fd (fd : fundef) : cexec fundef :=
  let nc_i := normalize_calls_i (entry_info_of_fun_info (f_info fd)) (vars_fd fd) in
  Let c := normalize_calls_c nc_i (f_body fd) in
  ok (with_body fd c).

Definition normalize_calls_prog : cexec prog :=
  Let funcs := map_cfprog normalize_calls_fd (p_funcs p) in
  ok {| p_funcs := funcs; p_globs := p_globs p; p_extra := p_extra p |}.

End NORMALIZE_CALLS.
