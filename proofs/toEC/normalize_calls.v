From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Coq Require Import Uint63.
Require Import expr compiler_util.
Import Utf8.

(* The extraction to EasyCrypt prints a function call, a system call or an
   operator with several outputs as a procedure call or a tuple assignment,
   whose destinations must be distinct variables of the output types. This
   pass puts these instructions in that form. After it, the destinations of
   such an instruction are variables of the output types, pairwise distinct,
   or [_].

   An instruction is rewritten when one of its destinations does not fit:
   a variable of another type, a variable written twice, a memory cell, an
   array cell or a sub-array. In a rewritten instruction, a destination
   becomes:

   - itself, when it is a boolean variable receiving a boolean output (a
     flag), unless a later destination writes the same flag; a flag may be
     undefined, and an undefined value cannot go through a copy;
   - an auxiliary variable that is not copied, when it is [_];
   - an auxiliary variable of the output type otherwise, copied into the
     original destination after the instruction; the copies follow the order
     of the destinations.

   The index or address of a copied destination may read a flag written by
   the instruction. The copy reads the value this flag would have had at this
   point: the auxiliary variable of its previous write in the instruction,
   or, if the instruction has not written it yet, a copy of the flag made
   before the instruction.

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

End E.

(* Renaming of the local variables of an expression. *)
Section RENAME.

Context (r : Mvar.t var).

Definition rename_var (x : var_i) : var_i :=
  if Mvar.get r x is Some y then {| v_var := y; v_info := v_info x |} else x.

Definition rename_gvar (x : gvar) : gvar :=
  if is_lvar x then mk_lvar (rename_var (gv x)) else x.

Fixpoint rename_e (e : pexpr) : pexpr :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ _ => e
  | Pvar x => Pvar (rename_gvar x)
  | Pget al aa ws x e => Pget al aa ws (rename_gvar x) (rename_e e)
  | Psub aa ws len x e => Psub aa ws len (rename_gvar x) (rename_e e)
  | Pload al ws e => Pload al ws (rename_e e)
  | Papp1 o e => Papp1 o (rename_e e)
  | Papp2 o e1 e2 => Papp2 o (rename_e e1) (rename_e e2)
  | PappN o es => PappN o (map rename_e es)
  | Pif t e e1 e2 => Pif t (rename_e e) (rename_e e1) (rename_e e2)
  end.

(* Only the index or address expression is renamed, not the written
   variable. *)
Definition rename_lval (lv : lval) : lval :=
  match lv with
  | Lnone _ _ | Lvar _ => lv
  | Lmem al ws vi e => Lmem al ws vi (rename_e e)
  | Laset al aa ws x e => Laset al aa ws x (rename_e e)
  | Lasub aa ws len x e => Lasub aa ws len x (rename_e e)
  end.

End RENAME.

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

(* Whether a flag position of [lvs] writes [x]. *)
Fixpoint writes_flag (x : var) (lvs : lvals) (touts : seq atype) : bool :=
  match lvs, touts with
  | lv :: lvs, t :: touts =>
    (if flag_dest lv t is Some y then v_var y == x else false)
    || writes_flag x lvs touts
  | _, _ => false
  end.

(* Whether a destination of [lvs] that is not a flag position reads [x]
   before any flag position writes [x]. *)
Fixpoint read_before_write (x : var) (lvs : lvals) (touts : seq atype) : bool :=
  match lvs, touts with
  | lv :: lvs, t :: touts =>
    if flag_dest lv t is Some y then (v_var y != x) && read_before_write x lvs touts
    else Sv.mem x (read_rv lv) || read_before_write x lvs touts
  | _, _ => false
  end.

Fixpoint flag_vars (lvs : lvals) (touts : seq atype) : Sv.t :=
  match lvs, touts with
  | lv :: lvs, t :: touts =>
    let s := flag_vars lvs touts in
    if flag_dest lv t is Some y then Sv.add y s else s
  | _, _ => Sv.empty
  end.

(* The flags whose value before the instruction is read by a copy: the copies
   run after the instruction has written them, so this value is saved before
   the instruction. *)
Definition snapshot_vars (lvs : lvals) (touts : seq atype) : seq var :=
  [seq x <- Sv.elements (flag_vars lvs touts) | read_before_write x lvs touts].

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

Fixpoint nc_snapshots (ii : instr_info) (acc : Sv.t) (xs : seq var) :
  cexec (Sv.t * Mvar.t var * cmd) :=
  match xs with
  | [::] => ok (acc, Mvar.empty var, [::])
  | x :: xs =>
    Let ra := fresh_aux ii acc (vtype x) in
    Let rs := nc_snapshots ii ra.1 xs in
    let i := MkI ii (Cassgn (Lvar ra.2) AT_none (vtype x) (Plvar (mk_var_i x))) in
    ok (rs.1.1, Mvar.set rs.1.2 x (v_var ra.2), i :: rs.2)
  end.

(* [r] maps a flag to the variable that holds the value the original
   destinations would read at this position. Every position writes a fresh
   variable, except the last flag position writing a given flag; the
   destinations that are not flags are copied after the instruction. *)
Fixpoint nc_dests (ii : instr_info) (tg : assgn_tag)
  (r : Mvar.t var) (acc : Sv.t) (lvs : lvals) (touts : seq atype) :
  cexec (Sv.t * lvals * cmd) :=
  match lvs, touts with
  | lv :: lvs, t :: touts =>
    match flag_dest lv t with
    | Some x =>
      if writes_flag x lvs touts then
        Let ra := fresh_aux ii acc t in
        Let rd := nc_dests ii tg (Mvar.set r x (v_var ra.2)) ra.1 lvs touts in
        ok (rd.1.1, Lvar ra.2 :: rd.1.2, rd.2)
      else
        Let rd := nc_dests ii tg (Mvar.remove r x) acc lvs touts in
        ok (rd.1.1, lv :: rd.1.2, rd.2)
    | None =>
      Let ra := fresh_aux ii acc t in
      Let rd := nc_dests ii tg r ra.1 lvs touts in
      let c :=
        if lv is Lnone _ _ then rd.2
        else MkI ii (Cassgn (rename_lval r lv) tg t (Plvar ra.2)) :: rd.2
      in
      ok (rd.1.1, Lvar ra.2 :: rd.1.2, c)
    end
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
  && has (fun lvt => bad_dest lvs lvt.1 lvt.2) (zip lvs touts).

(* The instructions to run before, the new destinations, and the instructions
   to run after. *)
Definition normalize_dests (ii : instr_info) (tg : assgn_tag)
  (lvs : lvals) (touts : seq atype) :
  cexec (cmd * lvals * cmd) :=
  if needs_rewrite lvs touts then
    Let rs := nc_snapshots ii Sv.empty (snapshot_vars lvs touts) in
    Let rd := nc_dests ii tg rs.1.2 rs.1.1 lvs touts in
    ok (rs.2, rd.1.2, rd.2)
  else ok ([::], lvs, [::]).

(* The instruction built by [mk] on the new destinations, between the
   instructions to run before and after. *)
Definition normalize_dests_i (ii : instr_info) (tg : assgn_tag)
  (lvs : lvals) (touts : seq atype) (mk : lvals -> instr_r) :
  cexec cmd :=
  Let r := normalize_dests ii tg lvs touts in
  ok (r.1.1 ++ MkI ii (mk r.1.2) :: r.2).

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
