From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import expr compiler_util.
Import Utf8.

(* Normalizes the destinations of function calls, of system calls and of
   operators with several outputs: in the result, such an instruction only
   writes variables of the exact output types, pairwise distinct.

   When a destination does not fit, every destination of the instruction is
   rewritten. A boolean variable receiving a boolean output (a flag) stays in
   the instruction, since its value may be undefined and an undefined value
   cannot go through a copy; a flag written again later in the same
   instruction is replaced by a fresh variable. Any other destination is
   written through a fresh variable of the output type, then copied into the
   original destination after the instruction, in the original order; [_]
   gets a fresh variable that is not copied. A copy whose index or address
   reads a flag reads the value the flag has at this position: the fresh
   variable of its previous write, or a copy of the flag made before the
   instruction. *)

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
Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).

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

Fixpoint pos_tally (k : nat) : string :=
  match k with
  | 0 => ""%string
  | S k => ("x" ++ pos_tally k)%string
  end.

(* The tally is the number of auxiliary variables already generated in the
   function: two copies of the same instruction (with the same [instr_info])
   receive distinct names from the memoising oracle. *)
Definition fresh_aux (ii : instr_info) (X acc : Sv.t) (t : atype) :
  cexec (Sv.t * var_i) :=
  let x :=
    {| vtype := t;
       vname := fresh_var_ident (Reg (Normal, Direct)) ii ("aux" ++ pos_tally (Sv.cardinal acc)) t;
    |}
  in
  Let _ := assert (~~ Sv.mem x (Sv.union X acc)) (E.fresh_error ii) in
  ok (Sv.add x acc, {| v_var := x; v_info := var_info_of_ii ii |}).

Fixpoint nc_snapshots (ii : instr_info) (X acc : Sv.t) (xs : seq var) :
  cexec (Sv.t * Mvar.t var * cmd) :=
  match xs with
  | [::] => ok (acc, Mvar.empty var, [::])
  | x :: xs =>
    Let ra := fresh_aux ii X acc (vtype x) in
    Let rs := nc_snapshots ii X ra.1 xs in
    let i := MkI ii (Cassgn (Lvar ra.2) AT_none (vtype x) (Plvar (mk_var_i x))) in
    ok (rs.1.1, Mvar.set rs.1.2 x (v_var ra.2), i :: rs.2)
  end.

(* [r] maps a flag to the variable that holds the value the original
   destinations would read at this position. Every position writes a fresh
   variable, except the last flag position writing a given flag; the
   destinations that are not flags are copied after the instruction. *)
Fixpoint nc_dests (ii : instr_info) (X : Sv.t) (tg : assgn_tag)
  (r : Mvar.t var) (acc : Sv.t) (lvs : lvals) (touts : seq atype) :
  cexec (Sv.t * lvals * cmd) :=
  match lvs, touts with
  | lv :: lvs, t :: touts =>
    match flag_dest lv t with
    | Some x =>
      if writes_flag x lvs touts then
        Let ra := fresh_aux ii X acc t in
        Let rd := nc_dests ii X tg (Mvar.set r x (v_var ra.2)) ra.1 lvs touts in
        ok (rd.1.1, Lvar ra.2 :: rd.1.2, rd.2)
      else
        Let rd := nc_dests ii X tg (Mvar.remove r x) acc lvs touts in
        ok (rd.1.1, lv :: rd.1.2, rd.2)
    | None =>
      Let ra := fresh_aux ii X acc t in
      Let rd := nc_dests ii X tg r ra.1 lvs touts in
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

(* [multi] holds for calls, system calls and operators with several
   destinations: they must write pairwise distinct variables. *)
Definition bad_dest (multi : bool) (lvs : lvals) (lv : lval) (t : atype) : bool :=
  match lv with
  | Lnone _ _ => false
  | Lvar x => (vtype x != t) || (multi && (1 < lvar_count x lvs))
  | _ => multi
  end.

(* Instructions whose destinations do not match the outputs are left as
   they are. *)
Definition dests_match (lvs : lvals) (touts : seq atype) : bool :=
  all2 (fun lv t => if lv is Lnone _ ty then ty == t else true) lvs touts.

Definition needs_rewrite (multi : bool) (lvs : lvals) (touts : seq atype) : bool :=
  dests_match lvs touts
  && has (fun lvt => bad_dest multi lvs lvt.1 lvt.2) (zip lvs touts).

(* The instructions to run before, the new destinations, and the instructions
   to run after. *)
Definition normalize_dests (ii : instr_info) (X acc : Sv.t) (tg : assgn_tag)
  (multi : bool) (lvs : lvals) (touts : seq atype) :
  cexec (Sv.t * cmd * lvals * cmd) :=
  if needs_rewrite multi lvs touts then
    Let rs := nc_snapshots ii X acc (snapshot_vars lvs touts) in
    Let rd := nc_dests ii X tg rs.1.2 rs.1.1 lvs touts in
    ok (rd.1.1, rs.2, rd.1.2, rd.2)
  else ok (acc, [::], lvs, [::]).

(* The instruction built by [mk] on the new destinations, between the
   instructions to run before and after. *)
Definition normalize_dests_i (ii : instr_info) (X acc : Sv.t) (tg : assgn_tag)
  (multi : bool) (lvs : lvals) (touts : seq atype) (mk : lvals -> instr_r) :
  cexec (Sv.t * cmd) :=
  Let r := normalize_dests ii X acc tg multi lvs touts in
  ok (r.1.1.1, r.1.1.2 ++ MkI ii (mk r.1.2) :: r.2).

Context (p : prog).

Section CMD.

Context (normalize_calls_i : Sv.t -> instr -> cexec (Sv.t * cmd)).

Fixpoint normalize_calls_c (acc : Sv.t) (c : cmd) : cexec (Sv.t * cmd) :=
  match c with
  | [::] => ok (acc, [::])
  | i :: c =>
    Let ai := normalize_calls_i acc i in
    Let ac := normalize_calls_c ai.1 c in
    ok (ac.1, ai.2 ++ ac.2)
  end.

End CMD.

Fixpoint normalize_calls_i (X acc : Sv.t) (i : instr) : cexec (Sv.t * cmd) :=
  let nc_c := normalize_calls_c (normalize_calls_i X) in
  let 'MkI ii ir := i in
  match ir with
  | Cassgn _ _ _ _ | Cassert _ => ok (acc, [:: i])
  | Copn lvs tg o es =>
    normalize_dests_i ii X acc tg (1 < size lvs) lvs (sopn_tout o)
      (fun xs => Copn xs tg o es)
  | Csyscall lvs o es =>
    normalize_dests_i ii X acc AT_none true lvs (scs_tout (syscall_sig_u o))
      (fun xs => Csyscall xs o es)
  | Ccall lvs f es =>
    Let fd := o2r (E.unknown_fun_error ii) (get_fundef (p_funcs p) f) in
    normalize_dests_i ii X acc AT_none true lvs (f_tyout fd) (fun xs => Ccall xs f es)
  | Cif e c1 c2 =>
    Let ac1 := nc_c acc c1 in
    Let ac2 := nc_c ac1.1 c2 in
    ok (ac2.1, [:: MkI ii (Cif e ac1.2 ac2.2)])
  | Cfor x r c =>
    Let ac := nc_c acc c in
    ok (ac.1, [:: MkI ii (Cfor x r ac.2)])
  | Cwhile al c1 e info c2 =>
    Let ac1 := nc_c acc c1 in
    Let ac2 := nc_c ac1.1 c2 in
    ok (ac2.1, [:: MkI ii (Cwhile al ac1.2 e info ac2.2)])
  end.

Definition normalize_calls_fd (fd : fundef) : cexec fundef :=
  Let ac := normalize_calls_c (normalize_calls_i (vars_fd fd)) Sv.empty (f_body fd) in
  ok (with_body fd ac.2).

Definition normalize_calls_prog : cexec prog :=
  Let funcs := map_cfprog normalize_calls_fd (p_funcs p) in
  ok {| p_funcs := funcs; p_globs := p_globs p; p_extra := p_extra p |}.

End NORMALIZE_CALLS.
