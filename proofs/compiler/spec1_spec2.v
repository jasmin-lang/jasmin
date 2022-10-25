(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect.
Require Import expr psem compiler_util ZArith.
Require Import asm_op_spec1 asm_op_spec2 propagate_inline.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Section ASM_OP.

Context `{asmop : asmOp}.
Context {pd : PointerData}.

Definition asm_spec1_to_asm_spec2 (o : asm_op_spec1) : asm_op_spec2 :=
match o with 
| asm_op_spec1.Oprotect w => asm_op_spec2.Oprotect w
| asm_op_spec1.Oset_msf => asm_op_spec2.Oset_msf
| asm_op_spec1.Oinit_msf => asm_op_spec2.Oinit_msf
| asm_op_spec1.Omov_msf => asm_op_spec2.Omov_msf
| asm_op_spec1.Oasm o => asm_op_spec2.Oasm o
end.

Definition sopn_spec1_to_spec2 (o :  @sopn asm_op_spec1 asmOp_spec1) :
@sopn asm_op_spec2 asmOp_spec2 := 
match o with 
| Ocopy w p => Ocopy w p
| Onop => Onop
| Omulu w => Omulu w
| Oaddcarry w => Oaddcarry w
| Osubcarry w => Osubcarry w
| sopn.Oasm o => sopn.Oasm (asm_spec1_to_asm_spec2 o)
end.

End ASM_OP.

Section CMD.

Context `{asmop : asmOp}.
Context {pd : PointerData}.

Variable i_spec1_to_spec2 : @instr asm_op_spec1 asmOp_spec1 -> 
                            seq (@instr asm_op_spec2 asmOp_spec2).

Fixpoint c_spec1_to_spec2 
(cmd : seq (@instr asm_op_spec1 asmOp_spec1)) : seq (@instr asm_op_spec2 asmOp_spec2) :=
match cmd with 
| [::] => [::]
| i :: c => i_spec1_to_spec2 i ++ c_spec1_to_spec2 c
end.

End CMD.

Section INST.

Context `{asmop : asmOp}.
Context {pd : PointerData}.

Fixpoint ir_spec1_to_spec2 ii (ir: @instr_r asm_op_spec1 asmOp_spec1) {struct ir}
: seq (@instr asm_op_spec2 asmOp_spec2) := 
match ir with 
| Cassgn x tag ty e => [:: MkI ii (@Cassgn asm_op_spec2 asmOp_spec2 x tag ty e)]
| Copn xs tag o es => [:: MkI ii (@Copn asm_op_spec2 asmOp_spec2 xs tag 
                                    ((sopn_spec1_to_spec2 o)) es)]
| Csyscall xs o es => [:: MkI ii (@Csyscall asm_op_spec2 asmOp_spec2 xs o es)]
| Cif b c1 c2 => let c1 := (c_spec1_to_spec2 i_spec1_to_spec2 c1) in
                 let c2 := (c_spec1_to_spec2 i_spec1_to_spec2 c2) in 
                 [:: MkI ii (@Cif asm_op_spec2 asmOp_spec2 b c1 c2)]
| Cfor x (dir, e1, e2) c => let c := (c_spec1_to_spec2 i_spec1_to_spec2 c) in 
                            [:: MkI ii (@Cfor asm_op_spec2 asmOp_spec2 x (dir, e1, e2) c)]
| Cwhile a c e c' => let c := (c_spec1_to_spec2 i_spec1_to_spec2 c) in 
                     let c' := (c_spec1_to_spec2 i_spec1_to_spec2 c') in 
                     [:: MkI ii (@Cwhile asm_op_spec2 asmOp_spec2 a c e c')]
| Ccall ini xs fn es => [:: MkI ii (@Ccall asm_op_spec2 asmOp_spec2 ini xs fn es)]
end 

with i_spec1_to_spec2 (i : @instr asm_op_spec1 asmOp_spec1)
: seq (@instr asm_op_spec2 asmOp_spec2) := 
let (ii,ir) := i in
(ir_spec1_to_spec2 ii ir).

End INST.

Section Section.

Context `{asmop : asmOp}.
Context {pd : PointerData}.
Context {T} {pT:progT T}.

Definition fun_spec1_to_spec2 (f:@fundef asm_op_spec1 asmOp_spec1 _ _)
: @fundef asm_op_spec2 asmOp_spec2 _ _ :=
  let 'MkFun ii si p c so r ev := f in
  let c := c_spec1_to_spec2 i_spec1_to_spec2 c in
  MkFun ii si p c so r ev.

Variable map_spec1_to_spec2 : 
(@fundef asm_op_spec1 asmOp_spec1 _ _ -> 
@fundef asm_op_spec2 asmOp_spec2 _ _) -> 
@prog asm_op_spec1 asmOp_spec1 _ _ -> 
@prog asm_op_spec2 asmOp_spec2 _ _.

Definition prog_spec1_to_spec2 (p:@prog asm_op_spec1 asmOp_spec1 _ _) : 
@prog asm_op_spec2 asmOp_spec2 _ _ := 
map_spec1_to_spec2 fun_spec1_to_spec2 p.

End Section.

Section PROOF.

Context
  {syscall_state asm_op : Type}
  `{asmop : asmOp}
  {fcp : FlagCombinationParams}
  {pd : PointerData}
  {sc_sem : syscall_sem syscall_state}.

Existing Instance progUnit.

Variable (ev:extra_val_t).
Variable (p: @prog asm_op_spec1 asmOp_spec1 _ _).

Variable map_spec1_to_spec2 : 
(@fundef asm_op_spec1 asmOp_spec1 _ _ -> 
@fundef asm_op_spec2 asmOp_spec2 _ _) -> 
@prog asm_op_spec1 asmOp_spec1 _ _ -> 
@prog asm_op_spec2 asmOp_spec2 _ _.

Let p' := prog_spec1_to_spec2 map_spec1_to_spec2 p.

Let Pi s1 i :=
  exists s2, sem p' ev s1 (i_spec1_to_spec2 i) s2. 

End PROOF.


