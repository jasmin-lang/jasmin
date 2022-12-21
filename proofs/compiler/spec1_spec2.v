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

(* expression defining the boolean condition and Sv.t defining the 
   free variables present in e *)
Definition cond_env := option (pexpr * Sv.t).

Definition cond_env_empty : cond_env := None.

Definition var_env := Sv.t.

Definition env := (cond_env * var_env)%type.

Definition empty_env := (cond_env_empty, Sv.empty).

Definition get_fv (env : cond_env) : Sv.t :=
match env with 
| Some e => e.2
| None => Sv.empty
end.

Definition update_cond_env (X: Sv.t) (E : cond_env) : cond_env :=
match E with 
| Some (e, fv) => if Sv.subset X fv then None else E
| None => None
end.

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
| Copn xs tag o es => 
  let cr := [:: MkI ii (@Copn asm_op_spec2 asmOp_spec2 xs tag ((sopn_spec1_to_spec2 o)) es)] in
  match o with 
  | Ocopy _ _ | Onop | Omulu _ | Oaddcarry _ | Osubcarry _ => ok (envi, cr)
    (* xs := init_msf 
       X = xs U X 
       E = update E based on whether X is present in E or not *)
  | sopn.Oasm asm_op_spec1.Oinit_msf =>
    match es with 
    | [::] => let cenv := update_cond_env envi.2 envi.1 in 
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
    | [:: e ; y] => let cenv := update_cond_env envi.2 envi.1 in
                    let rs := read_e_rec Sv.empty y in
                    let r2 := disjoint rs envi.2 in
                    if r2
                    then ok ((cenv, envi.2), cr)
                    else ok ((cenv, vrvs_rec envi.2 xs), cr)
    | _ =>  Error (spec_transform_error "Too many arguments")
   end 
   (* xs := protect (e, y)
      should fail if y is not in X *)
  | sopn.Oasm (asm_op_spec1.Oprotect w) => 
    match es with 
    | [:: e; y] => let cenv := update_cond_env envi.2 envi.1 in 
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
    | [:: y] => let rs := read_e_rec Sv.empty y in 
                let r := disjoint rs envi.2 in
                if r 
                then ok ((update_cond_env envi.2 envi.1, envi.2), cr)
                else ok ((update_cond_env envi.2 envi.1, vrvs_rec envi.2 xs), cr)
    | _ => Error (spec_transform_error "Too many arguments")
    end
  | sopn.Oasm o => ok (envi, cr) 
  end
 (* FIX ME *)                   
| Csyscall xs o es => ok (envi, [:: MkI ii (@Csyscall asm_op_spec2 asmOp_spec2 xs o es)])
(* FIX ME *)
| Cif b c1 c2 => 
  Let rc1 := (c_spec1_to_spec2 i_spec1_to_spec2 (Some (b, get_fv envi.1), envi.2) c1) in 
  Let rc2 := (c_spec1_to_spec2 i_spec1_to_spec2 (Some ((enot b), get_fv envi.1), envi.2) c2) in 
  ok ((update_cond_env envi.2 envi.1, Sv.inter rc1.1.2 rc2.1.2), [:: MkI ii (@Cif asm_op_spec2 asmOp_spec2 b rc1.2 rc2.2)])
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






