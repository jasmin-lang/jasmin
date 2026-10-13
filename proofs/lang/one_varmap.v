(** This module defines common definitions related to the “one-varmap” intermediate language.
This language is structured (as jasmin-source) and is used just before linearization: there is a single environment (varmap) shared across function calls.
*)
Require Import expr compiler_util.
Import Utf8.
From mathcomp Require Import ssreflect ssrfun ssrbool.

Record ovm_syscall_sig_t := 
  { scs_vin : seq var; scs_vout : seq var }.

Class one_varmap_info := { 
  syscall_sig  : syscall_t -> ovm_syscall_sig_t;
  all_vars     : Sv.t;
  callee_saved : Sv.t;
  vflags       : Sv.t;
  vflagsP      : forall x, Sv.In x vflags -> vtype x = abool
}.

Definition syscall_kill {ovm_i : one_varmap_info} :=
  Sv.diff all_vars callee_saved.

(* Registers that a linker-inserted veneer (a long-branch thunk) may destroy
   between a call and its callee.  A veneer is synthesised when the caller and
   the callee may end up far apart, which under -function-sections is the case
   for every call internal to a compilation unit; it runs after the call
   instruction has recorded the return address and before the first
   instruction of the callee.  The registers are the ABI's
   intra-procedure-call scratch registers: r12 on ARM, x16/x17 on AArch64; on
   x86-64 and RISC-V no veneer is synthesised and the set is empty.  It is a
   class, so that it is threaded implicitly, the way [one_varmap_info] is;
   this file is architecture-independent and only ever sees the set.  On an
   architecture it is not a parameter of its own: [asm_gen.veneer_i] builds it
   from the machine-level register list [arch_decl.veneer_regs] -- the very
   list the assembly semantics havocs at a call -- mapped through [to_var],
   exactly as [ovm_i] builds [callee_saved] from the calling convention.  The
   whole development is universally quantified over that list, so the empty
   one (the default, and the only possibility when the functions of a unit
   are not laid out in sections of their own) constrains nothing. *)
Class veneer_info := { call_kill : Sv.t }.

(* Keep [call_kill] atomic under [simpl]: on an architecture the instance is a
   concrete one ([asm_gen.veneer_i]) and unfolding it would leave the goals of
   the proofs with two syntactically different forms of the same set. *)
Arguments call_kill : simpl never.

Section Section.

Context {pd: PointerData} {asm_op} {asmop:asmOp asm_op} {ovm_i : one_varmap_info}
  {vinfo : veneer_info}
  (p: sprog)
.

Let vgd : var := vid p.(p_extra).(sp_rip).
Let vrsp : var := vid p.(p_extra).(sp_rsp).

Definition magic_variables : Sv.t :=
  Sv.add vgd (Sv.singleton vrsp).

Definition savedstackreg (ss: saved_stack) :=
  if ss is SavedStackReg r then Sv.singleton r else Sv.empty.

Definition saved_stack_vm fd : Sv.t :=
  savedstackreg fd.(f_extra).(sf_save_stack).

(* The set of registers that are undefined at the entry of a function.

   [tmp] is what the linearization pass uses to set up the stack pointer of an
   export function.  [call_kill] is what a veneer may destroy on the way to the
   callee of an internal call, so it is undefined at the entry of a function
   that is entered by such a call, i.e. one whose return address is passed in
   a register (RAreg) or on the stack (RAstack).

   It is deliberately NOT added to the RAnone case: an export function is
   entered by a caller outside the compilation unit, under the ABI, where
   those registers are the intra-procedure-call scratch registers and carry
   nothing.  (On the architectures that have a non-empty [call_kill] the
   RAnone case covers them anyway: r12 is the ARM linearization temporary, so
   it is in [tmp].)

   The *results* of a function need no such treatment: a subroutine returns
   with an indirect branch (Ligoto, `bx lr`), which the linker never routes
   through a veneer. *)
Definition ra_vm (e: stk_fun_extra) (tmp: Sv.t) : Sv.t :=
  match e.(sf_return_address) with
  | RAreg ra _ =>
    Sv.union call_kill (Sv.singleton ra)
  | RAstack ra_call _ _ _ =>
    Sv.union call_kill (sv_of_option ra_call)
  | RAnone =>
    Sv.union tmp vflags
  end.

(* TODO: ra_vm, ra_undef, ra_undef_vm... -> pick better names *)
Definition ra_vm_return (e : stk_fun_extra) : Sv.t :=
  match e.(sf_return_address) with
  | RAstack _ ra_return _ _ => sv_of_option ra_return
  | _ => Sv.empty
  end.

Definition ra_undef fd (tmp: Sv.t) :=
  Sv.union (ra_vm fd.(f_extra) tmp) (saved_stack_vm fd).

Definition tmp_call (e: stk_fun_extra) : Sv.t :=
  match e.(sf_return_address) with
  | RAreg _ (Some r) | RAstack _ _ _ (Some r) => Sv.singleton r
  | _ => Sv.empty
  end.

Definition fd_tmp_call (p:sprog) f :=
  match get_fundef (p_funcs p) f with
  | None => Sv.empty
  | Some fd => tmp_call fd.(f_extra)
  end.

End Section.
