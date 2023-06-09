From mathcomp Require Import all_ssreflect all_algebra.
Require Import syscall_sem.
Require Import arch_decl arch_sem.

Section S.

Context
  {syscall_state : Type} {sc_sem : syscall_sem syscall_state}
  `{asm_d : asm} {call_conv: calling_convention}
  {asm_scsem : asm_syscall_sem}.

(* reg_pairs can contain the three kinds of registers *)
Definition asmmem0
    init_sys m0
    (reg_pairs : seq (string * Z))
    (flag_pairs : seq (string * rflagv)) : asmmem :=
  {|
    asm_rip := wrepr reg_size 0;
    asm_scs := init_sys;
    asm_mem := m0;
    asm_reg := [ffun r =>
      let z := Option.default 0%Z (xseq.assoc reg_pairs (to_string r)) in
      wrepr reg_size z];
    asm_regx := [ffun r =>
    let z := Option.default 0%Z (xseq.assoc reg_pairs (to_string r)) in
      wrepr reg_size z];
    asm_xreg := [ffun r =>
      let z := Option.default 0%Z (xseq.assoc reg_pairs (to_string r)) in
      wrepr xreg_size z];
    asm_flag := [ffun f =>
      Option.default Undef (xseq.assoc flag_pairs (to_string f))]
  |}.

Definition mk_asm_state init_sys m0 ip reg_pairs flag_values fn i : asm_state :=
  let asmmem0 := asmmem0 init_sys m0 reg_pairs flag_values in
  {|
    asm_m := asmmem0;
    asm_f := fn;
    asm_c := [::i];
    asm_ip := ip
  |}.

Definition read_ip asm_state :=
  asm_state.(asm_ip).

Definition read_reg asm_state (r:reg) :=
  wunsigned (asm_state.(asm_m).(asm_reg) r).

Definition read_regx asm_state (rx:regx) :=
  wunsigned (asm_state.(asm_m).(asm_regx) rx).

Definition read_xreg asm_state (xr:xreg) :=
  wunsigned (asm_state.(asm_m).(asm_xreg) xr).

Definition read_flag asm_state (f:rflag) :=
  asm_state.(asm_m).(asm_flag) f.

Definition of_asm_state asm_state :=
  (read_ip asm_state, List.map (read_reg asm_state) registers,
  List.map (read_regx asm_state) registerxs, List.map (read_xreg
  asm_state) xregisters, List.map (read_flag asm_state) rflags).

Definition exec_i asm_state (i:asm_i) :=
  let fd := {|
    asm_fd_align := U256;
    asm_fd_arg := [::];
    asm_fd_body := [::i];
    asm_fd_res := [::];
    asm_fd_export := true;
    asm_fd_total_stack := 0
  |} in
  let fn := asm_state.(asm_f) in
  let p := {|
    asm_globs := [::];
    asm_funcs := [::(fn, fd)]
  |} in
  eval_instr p i asm_state.

End S.
