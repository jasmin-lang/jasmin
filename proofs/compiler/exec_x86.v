From mathcomp Require Import all_ssreflect all_algebra.
Require Import syscall_sem.
Require Import arch_decl arch_sem.
Require Import x86_decl x86_extra.

Section S.

Context
  {syscall_state : Type} {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}.

Definition mem0 := low_memory.Memory.M.(init) [::] (wrepr U64 1024).

Definition asmmem0 init_sys reg_values flag_values : exec asmmem :=
  Let mem0 := mem0 in ok {|
  asm_rip := wrepr U64 0;
  asm_scs := init_sys;
  asm_mem := mem0;
  asm_reg := [ffun r =>
    let n := seq.index r registers in
    let z := nth 0%Z reg_values n in
    wrepr U64 z];
  asm_regx := [ffun=> wrepr U64 0];
  asm_xreg := [ffun=> wrepr U256 0];
  asm_flag := [ffun f =>
    let n := seq.index f rflags in
    nth Undef flag_values n]
|}.

Definition mk_asm_state init_sys ip reg_values flag_values fn i : exec asm_state :=
  Let asmmem0 := asmmem0 init_sys reg_values flag_values in ok {|
    asm_m := asmmem0;
    asm_f := fn;
    asm_c := [::i];
    asm_ip := ip
  |}.

Definition read_ip asm_state :=
  asm_state.(asm_ip).

Definition read_reg asm_state (r:register) :=
  wunsigned (asm_state.(asm_m).(asm_reg) r).

Definition read_flag asm_state (f:rflag) :=
  asm_state.(asm_m).(asm_flag) f.

Definition of_asm_state asm_state :=
  (read_ip asm_state, List.map (read_reg asm_state) registers, List.map (read_flag asm_state) rflags).

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
