(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import expr compiler_util gen_map.
(* ------- *) (* - *) Import PosSet.
Import  Utf8.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Fixpoint i_calls (c : Sp.t) (i : instr) {struct i} : Sp.t :=
  let: MkI _ i := i in i_calls_r c i

with i_calls_r (c : Sp.t) (i : instr_r) {struct i} : Sp.t :=
  let fix c_calls (c : Sp.t) (cmd : cmd) {struct cmd} :=
    if cmd is i :: cmd' then c_calls (i_calls c i) cmd' else c
  in

  match i with
  | Cassgn _ _  _  _ => c
  | Copn   _  _  _  _ => c
  | Cif    _  c1 c2   => c_calls (c_calls c c1) c2
  | Cfor   _  _  c1   => c_calls c c1
  | Cwhile c1 _  c2   => c_calls (c_calls c c1) c2
  | Ccall  _  _  f  _ => Sp.add f c
  end.

Definition c_calls (c : Sp.t) (cmd : cmd) :=
  foldl i_calls c cmd.

(* -------------------------------------------------------------------- *)
Definition live_calls : Sp.t → prog → Sp.t :=
  foldl (λ c x, let '(n, d) := x in if Sp.mem n c then c_calls c (f_body d) else c).

Definition dead_calls (K: Sp.t) (p: prog) :=
  filter (λ x, Sp.mem x.1 K) p.

Definition dead_calls_err (c : Sp.t) (p : prog) : cfexec prog :=
  let k := live_calls c p in
  if Sp.subset (live_calls k p) k then
  cfok (dead_calls k p)
  else cferror Ferr_topo.

(* -------------------------------------------------------------------- *)
Definition dead_calls_err_seq (c : seq funname) (p : prog) : cfexec prog :=
  dead_calls_err (foldl (fun f c => Sp.add c f) Sp.empty c) p.
