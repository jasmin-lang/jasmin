(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import expr compiler_util gen_map.
(* ------- *) (* - *) Import PosSet.

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
  | Cassgn _  _  _    => c
  | Copn   _  _  _    => c
  | Cif    _  c1 c2   => c_calls (c_calls c c1) c2
  | Cfor   _  _  c1   => c_calls c c1
  | Cwhile c1 _  c2   => c_calls (c_calls c c1) c2
  | Ccall  _  _  f  _ => Sp.add f c
  end.

Definition c_calls (c : Sp.t) (cmd : cmd) :=
  foldl i_calls c cmd.

(* -------------------------------------------------------------------- *)
Fixpoint dead_calls (c : Sp.t) (p : prog) {struct p} : prog :=
  if p is (f, fd) :: p then
    if Sp.mem f c then
      (f, fd) :: dead_calls (c_calls c fd.(f_body)) p
    else dead_calls c p
  else [::].

(* -------------------------------------------------------------------- *)
Definition dead_calls_seq (c : seq funname) (p : prog) :=
  dead_calls (foldl (fun f c => Sp.add c f) Sp.empty c) p.
