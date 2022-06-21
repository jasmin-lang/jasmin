(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import expr compiler_util gen_map.
(* ------- *) (* - *) Import PosSet.
Import  Utf8.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Import E.

  Definition pass : string := "dead calls".

  Definition dead_calls_error := pp_internal_error_s pass.

End E.

Section ASM_OP.

Context `{asmop:asmOp}.

(* -------------------------------------------------------------------- *)
Fixpoint i_calls (c : Sp.t) (i : instr) {struct i} : Sp.t :=
  let: MkI _ i := i in i_calls_r c i

with i_calls_r (c : Sp.t) (i : instr_r) {struct i} : Sp.t :=
  let fix c_calls (c : Sp.t) (cmd : cmd) {struct cmd} :=
    if cmd is i :: cmd' then c_calls (i_calls c i) cmd' else c
  in

  match i with
  | Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _ => c
  | Cif    _  c1 c2   => c_calls (c_calls c c1) c2
  | Cfor   _  _  c1   => c_calls c c1
  | Cwhile _ c1 _  c2   => c_calls (c_calls c c1) c2
  | Ccall  _  _  f  _ => Sp.add f c
  end.

Definition c_calls (c : Sp.t) (cmd : cmd) :=
  foldl i_calls c cmd.

(* -------------------------------------------------------------------- *)

Section Section.

Context {T} {pT:progT T}.

Definition live_calls (s: Sp.t) (p: fun_decls) : Sp.t :=
  foldl (λ c x, let '(n, d) := x in if Sp.mem n c then c_calls c (f_body d) else c) s p.

Definition dead_calls (K: Sp.t) (p: fun_decls) :=
  filter (λ x, Sp.mem x.1 K) p.

Definition dead_calls_err (c : Sp.t) (p : prog) : cexec prog :=
  let fds := p_funcs p in
  let k := live_calls c fds in
  if Sp.subset (live_calls k fds) k then
  ok {| p_funcs := dead_calls k fds; p_globs := p_globs p; p_extra := p_extra p |}
  else Error (dead_calls_error "program is not a topological sorting of the call-graph").

(* -------------------------------------------------------------------- *)
Definition dead_calls_err_seq (c : seq funname) (p : prog) : cexec prog  :=
  dead_calls_err (foldl (fun f c => Sp.add c f) Sp.empty c) p.

End Section.

End ASM_OP.
