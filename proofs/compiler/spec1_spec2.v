(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect.
Require Import expr psem compiler_util ZArith.
Require Import asm_op_spec1 asm_op_spec2 propagate_inline.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "spec transform".

  Definition spec_transform_error := pp_internal_error_s pass.

End E.

Definition cond_env_rec (e : pexpr) :=
if use_mem e then None else Some e.

Definition cond_env := option pexpr.

Definition cond_env_empty : cond_env := None.

Definition var_env := Sv.t.

Definition env := (cond_env * var_env)%type.

Definition empty_env := (cond_env_empty, Sv.empty).

Definition is_some (e : cond_env) := 
match e with 
| Some e => true 
| None => false
end.

Definition is_some_mem_op_free (E : cond_env) := 
match E with 
| Some e' => let r := cond_env_rec e' in
             (*let re := eq_expr e' e in *)
             if is_some r then true else false
| None => false
end.
 
(* FIX ME *)
Definition update_cond_env (E : cond_env) : cond_env := E.

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

Variable i_spec1_to_spec2 : env -> @instr asm_op_spec1 asmOp_spec1 -> 
                            cexec (env * seq (@instr asm_op_spec2 asmOp_spec2))%type.

Fixpoint c_spec1_to_spec2 (envi : env) (cmd : seq (@instr asm_op_spec1 asmOp_spec1)) 
: cexec (env * seq (@instr asm_op_spec2 asmOp_spec2)) :=
match cmd with 
| [::] => ok (envi, [::])%type
| i :: c => Let ir := i_spec1_to_spec2 envi i in 
            Let cr := c_spec1_to_spec2 ir.1 c in 
            ok (cr.1, ir.2 ++ cr.2)
end.

End CMD.

Section INST.

Context `{asmop : asmOp}.
Context {pd : PointerData}.

Fixpoint ir_spec1_to_spec2 envi ii (ir: @instr_r asm_op_spec1 asmOp_spec1) {struct ir}
: cexec (env * seq (@instr asm_op_spec2 asmOp_spec2)) := 
match ir with 
| Cassgn x tag ty e => ok (envi, [:: MkI ii (@Cassgn asm_op_spec2 asmOp_spec2 x tag ty e)])
| Copn xs tag o es => let cr := [:: MkI ii (@Copn asm_op_spec2 asmOp_spec2 xs tag 
                                            ((sopn_spec1_to_spec2 o)) es)] in
                      match o with 
                      | Ocopy _ _ => ok (envi, cr) 
                      | Onop => ok (envi, cr) 
                      | Omulu _ => ok (envi, cr)
                      | Oaddcarry _ => ok (envi, cr)
                      | Osubcarry _ => ok (envi, cr)
                      (* xs := init_msf 
                         X = xs U X 
                         E = .... *)
                      | sopn.Oasm asm_op_spec1.Oinit_msf =>
                        match es with 
                        | [::] => let cenv := update_cond_env envi.1 in 
                                  let venv := vrvs_rec envi.2 xs in  
                                  ok ((cenv, venv), cr)
                        | _ => Error (spec_transform_error "Too many arguments")
                        end 
                      (* xs := set_msf (e, y) 
                         here y represents the msf flag and e is the boolean 
                         X = xs U X (E is Some e and y in X) 
                         X = X (y not in X) *)
                      | sopn.Oasm asm_op_spec1.Oset_msf =>
                        match es with 
                        | [:: e ; y] => 
                          let cenv := update_cond_env envi.1 in
                          let r1 := is_some_mem_op_free envi.1 in 
                          let rs := read_e_rec Sv.empty y in
                          let r2 := disjoint rs envi.2 in
                          if r1 && negb r2
                          then ok ((cenv, vrvs_rec envi.2 xs), cr)
                          else ok ((cenv, envi.2), cr)
                        | _ =>  Error (spec_transform_error "Too many arguments")
                         end 
                      (* xs := protect (e, y)
                         should fail if y is not in X *)
                      | sopn.Oasm (asm_op_spec1.Oprotect w) => 
                        match es with 
                        | [:: e; y] =>
                          let cenv := update_cond_env envi.1 in 
                          let rs := read_e_rec Sv.empty y in 
                          let r := disjoint rs envi.2 in 
                          if r 
                          then Error (spec_transform_error "Msf variable not present")
                          else ok ((cenv, envi.2), cr)
                        | _ => Error (spec_transform_error "Too many arguments")
                        end
                      (* xs := mov_msf(y) 
                         if y is present in msf set then xs U X else X *)
                      | sopn.Oasm asm_op_spec1.Omov_msf => 
                        match es with
                        | [:: y] => 
                          let rs := read_e_rec Sv.empty y in 
                          let r := disjoint rs envi.2 in
                          if r 
                          then ok ((update_cond_env envi.1, envi.2), cr)
                          else ok ((update_cond_env envi.1, vrvs_rec envi.2 xs), cr)
                        | _ => Error (spec_transform_error "Too many arguments")
                        end
                      | sopn.Oasm o => 
                        ok (envi, cr) 
                      end
 (* FIX ME *)                   
| Csyscall xs o es => ok (envi, [:: MkI ii (@Csyscall asm_op_spec2 asmOp_spec2 xs o es)])
(* FIX ME *)
| Cif b c1 c2 => Let rc1 := (c_spec1_to_spec2 i_spec1_to_spec2 (Some b, envi.2) c1) in 
                 Let rc2 := (c_spec1_to_spec2 i_spec1_to_spec2 (Some b, envi.2) c2) in 
                 ok ((None, Sv.inter rc1.1.2 rc2.1.2), [:: MkI ii (@Cif asm_op_spec2 asmOp_spec2 b rc1.2 rc2.2)])
| Cfor x (dir, e1, e2) c => Let cr := c_spec1_to_spec2 i_spec1_to_spec2 envi c in 
                            ok (cr.1, [:: MkI ii (@Cfor asm_op_spec2 asmOp_spec2 x (dir, e1, e2) cr.2)])
| Cwhile a c e c' => (*let c := (c_spec1_to_spec2 i_spec1_to_spec2 c) in 
                     let c' := (c_spec1_to_spec2 i_spec1_to_spec2 c') in 
                     [:: MkI ii (@Cwhile asm_op_spec2 asmOp_spec2 a c e c')]*) ok (envi, [::])
| Ccall ini xs fn es => ok (envi, [:: MkI ii (@Ccall asm_op_spec2 asmOp_spec2 ini xs fn es)])
end 

with i_spec1_to_spec2 (envi: env) (i : @instr asm_op_spec1 asmOp_spec1)
: cexec (env * seq (@instr asm_op_spec2 asmOp_spec2)) := 
let (ii,ir) := i in
(ir_spec1_to_spec2 envi ii ir).

End INST.

Section Section.

Context `{asmop : asmOp}.
Context {pd : PointerData}.
Context {T} {pT:progT T}.

Definition fun_spec1_to_spec2 (f:@fundef asm_op_spec1 asmOp_spec1 _ _)
: cexec (env * @fundef asm_op_spec2 asmOp_spec2 _ _) :=
  let 'MkFun ii si p c so r ev := f in
  Let c := c_spec1_to_spec2 i_spec1_to_spec2 empty_env c in
  ok (c.1, MkFun ii si p c.2 so r ev).

Variable map_spec1_to_spec2 : 
(@fundef asm_op_spec1 asmOp_spec1 _ _ -> 
cexec (env * @fundef asm_op_spec2 asmOp_spec2 _ _)) -> 
@prog asm_op_spec1 asmOp_spec1 _ _ -> 
(@prog asm_op_spec2 asmOp_spec2 _ _).

Definition prog_spec1_to_spec2 (p:@prog asm_op_spec1 asmOp_spec1 _ _) : 
(@prog asm_op_spec2 asmOp_spec2 _ _) := 
map_spec1_to_spec2 fun_spec1_to_spec2 p.

End Section.

Section PROOF.

Search concl : semCallParams.

Context
  {syscall_state asm_op : Type}
  `{asmop : asmOp}
  {fcp : FlagCombinationParams}
  {pd : PointerData}
  {sc_sem : syscall_sem syscall_state}.

Existing Instance progUnit.

Variable (ev:extra_val_t).
Variable (p: @prog asm_op_spec1 asmOp_spec1 _ _).

(*Context {T:eqType} {pT:progT T} `{sCP: semCallParams}.
Variable (ev:extra_val_t).
Variable (p: @prog asm_op_spec1 asmOp_spec1 _ _).
Variable (sppe: SemPexprParams asm_op syscall_state).*)

Variable map_spec1_to_spec2 : 
(@fundef asm_op_spec1 asmOp_spec1 _ _ -> 
cexec (env * @fundef asm_op_spec2 asmOp_spec2 _ _)) -> 
@prog asm_op_spec1 asmOp_spec1 _ _ -> 
@prog asm_op_spec2 asmOp_spec2 _ _.

Let p' := prog_spec1_to_spec2 map_spec1_to_spec2 p.

Let Pi_r s1 ii (i: @instr_r asm_op_spec1 asmOp_spec1) (envi : env) :=
match (ir_spec1_to_spec2 envi ii i) with
 | Ok (envi', c') => exists s2, sem p' ev s1 c' s2
 | _ => True
end.

Let Pi s1 i (envi : env) :=
match (i_spec1_to_spec2 envi i) with
 | Ok (envi', c') => exists s2, sem p' ev s1 c' s2
 | _ => True
end.

Let Pc s1 c (envi : env) :=
match (c_spec1_to_spec2 (i_spec1_to_spec2) envi c) with
 | Ok (envi', c') => exists s2, sem p' ev s1 c' s2
 | _ => True
end.

Let Pfor s1 c (envi : env) vs i :=
match (c_spec1_to_spec2 (i_spec1_to_spec2) envi c) with
 | Ok (envi', c') => exists s2, sem_for p' ev i vs s1 c' s2
 | _ => True
end.
