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

(* FIXME: there should exist a better way to initialize all regs *)
Definition asmmem0 init_sys regs : exec asmmem :=
  Let mem0 := mem0 in ok {|
  asm_rip := wrepr U64 0;
  asm_scs := init_sys;
  asm_mem := mem0;
  asm_reg := finfun (fun r =>
    wrepr U64 (nth 0%Z regs
      match r with
      | RAX => 0
      | RCX => 1
      | RDX => 2
      | RBX => 3
      | RSP => 4
      | RBP => 5
      | RSI => 6
      | RDI => 7
      | R8 => 8
      | R9 => 9
      | R10 => 10
      | R11 => 11
      | R12 => 12
      | R13 => 13
      | R14 => 14
      | R15 => 15
      end));
  asm_regx := [ffun=> wrepr U64 0];
  asm_xreg := [ffun=> wrepr U256 0];
  asm_flag := [ffun=> Undef]
|}.

Definition asm_state0 init_sys regs fn i : exec asm_state :=
  Let asmmem0 := asmmem0 init_sys regs in ok {|
    asm_m := asmmem0;
    asm_f := fn;
    asm_c := [::i];
    asm_ip := 0
  |}.

Definition exec_i init_sys regs fn i : exec (nat * seq Z * seq rflagv) :=
  let fd := {|
    asm_fd_align := U256;
    asm_fd_arg := [::];
    asm_fd_body := [::i];
    asm_fd_res := [::];
    asm_fd_export := true;
    asm_fd_total_stack := 0
  |} in
  let p := {|
    asm_globs := [::];
    asm_funcs := [::(fn, fd)]
  |} in
  Let asm_state0 := asm_state0 init_sys regs fn i in
  Let asm_state1 := eval_instr p i asm_state0 in
  let asmmem1 := asm_state1.(asm_m) in
  let regs1 := [seq wunsigned (asmmem1.(asm_reg) x) | x : register] in
  let flags1 := [seq asmmem1.(asm_flag) f | f : rflag] in
  ok (asm_state1.(asm_ip), regs1, flags1).

End S.
