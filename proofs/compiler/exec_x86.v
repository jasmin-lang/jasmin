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
    match r with
    | RAX => wrepr U64 (nth 0%Z regs 0)
    | RCX => wrepr U64 (nth 0%Z regs 1)
    | RDX => wrepr U64 (nth 0%Z regs 2)
    | RBX => wrepr U64 (nth 0%Z regs 3)
    | RSP => wrepr U64 (nth 0%Z regs 4)
    | RBP => wrepr U64 (nth 0%Z regs 5)
    | RSI => wrepr U64 (nth 0%Z regs 6)
    | RDI => wrepr U64 (nth 0%Z regs 7)
    | R8 => wrepr U64 (nth 0%Z regs 8)
    | R9 => wrepr U64 (nth 0%Z regs 9)
    | R10 => wrepr U64 (nth 0%Z regs 10)
    | R11 => wrepr U64 (nth 0%Z regs 11)
    | R12 => wrepr U64 (nth 0%Z regs 12)
    | R13 => wrepr U64 (nth 0%Z regs 13)
    | R14 => wrepr U64 (nth 0%Z regs 14)
    | R15 => wrepr U64 (nth 0%Z regs 15)
    end);
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
