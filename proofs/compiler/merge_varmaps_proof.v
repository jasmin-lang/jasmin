(*
*)
Require Import merge_varmaps.
Import Utf8.
Import all_ssreflect.
Import psem.

Section PROG.

Context (p: sprog) (extra_free_registers: instr_info → option var).

Definition valid_writefun (w: funname → Sv.t) (f: sfun_decl) : bool :=
  Sv.subset (write_fd p extra_free_registers w f.2) (w f.1).

Lemma check_wmapP (wm: Mp.t Sv.t) (f: sfun_decl) :
  List.In f (p_funcs p) →
  check_wmap p extra_free_registers wm →
  valid_writefun (get_wmap wm) f.
Proof. by move/InP => f_in_p /allP {f_in_p}/(_ _ f_in_p); case: f. Qed.

End PROG.
