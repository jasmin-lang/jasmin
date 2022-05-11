(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Utf8.
Require Import compiler_util.
Require Import wsize sopn expr arch_decl x86_decl x86_instr_decl x86_sem.
Require Export arch_extra.
Import sopn.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)

Variant x86_extra_op : Type :=
| Oset0     of wsize  (* set register + flags to 0 (implemented using XOR x x or VPXOR x x) *)
| Oconcat128          (* concatenate 2 128 bits word into 1 256 word register *)   
| Ox86MOVZX32.

Scheme Equality for x86_extra_op.

Lemma x86_extra_op_eq_axiom : Equality.axiom x86_extra_op_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_x86_extra_op_dec_bl.
  by apply: internal_x86_extra_op_dec_lb.
Qed.

Definition x86_extra_op_eqMixin     := Equality.Mixin x86_extra_op_eq_axiom.
Canonical  x86_extra_op_eqType      := Eval hnf in EqType x86_extra_op x86_extra_op_eqMixin.

Local Notation E n := (ADExplicit n None).

Definition Oset0_instr sz  :=
  if (sz <= U64)%CMP then 
    mk_instr_desc (pp_sz "set0" sz)
             [::] [::]
             (b5w_ty sz) (map sopn_arg_desc implicit_flags ++ [:: E 0])
             (let vf := Some false in
              let vt := Some true in
              ok (::vf, vf, vf, vt, vt & (0%R: word sz)))
             sz [::]
  else 
    mk_instr_desc (pp_sz "set0" sz)
             [::] [::]  
             (w_ty sz) [::E 0] 
             (ok (0%R: word sz)) sz [::].

Definition Oconcat128_instr := 
  mk_instr_desc (pp_s "concat_2u128") 
           [:: sword128; sword128 ] [:: E 1; E 2] 
           [:: sword256] [:: E 0] 
           (λ h l : u128, ok (make_vec U256 [::l;h]))
           U128 [::].

Definition Ox86MOVZX32_instr := 
  mk_instr_desc (pp_s "MOVZX32") 
           [:: sword32] [:: E 1] 
           [:: sword64] [:: E 0] 
           (λ x : u32, ok (zero_extend U64 x)) 
           U32 [::].

Definition get_instr_desc o :=
  match o with
  | Oset0 ws => Oset0_instr ws
  | Oconcat128 => Oconcat128_instr
  | Ox86MOVZX32 => Ox86MOVZX32_instr
  end.


(* TODO: to be removed? can we have one module for all asmgen errors? *)
Module E.

Definition pass_name := "asmgen"%string.

Definition error (ii:instr_info) (msg:string) := 
  {| pel_msg      := compiler_util.pp_s msg
   ; pel_fn       := None
   ; pel_fi       := None
   ; pel_ii       := Some ii
   ; pel_vi       := None
   ; pel_pass     := Some pass_name
   ; pel_internal := true
  |}.

End E.

Definition assemble_extra ii o outx inx : cexec (asm_op_msb_t * lvals * pexprs) :=
  match o with
  | Oset0 sz =>
    let op := if (sz <= U64)%CMP then (XOR sz) else (VPXOR sz) in
    Let x := 
      match rev outx with 
      | Lvar x :: _ =>  ok x
      | _ => Error (E.error ii "set0 : destination is not a register")
      end in
    ok ((None, op), outx, [::Plvar x; Plvar x])
  | Ox86MOVZX32 =>
    Let x := 
      match outx with 
      | [::Lvar x] =>  ok x
      | _ => Error (E.error ii "Ox86MOVZX32: destination is not a register")
      end in
    ok ((None, MOV U32), outx, inx)
  | Oconcat128 =>
    Let inx := 
        match inx with
        | [:: h; Pvar _ as l] => ok [:: l; h; @wconst U8 1%R]
        |  _ => Error (E.error ii "Oconcat: assert false")
        end in
    ok ((None, VINSERTI128), outx, inx)
  end.

Instance eqC_x86_extra_op : eqTypeC x86_extra_op :=
  { ceqP := x86_extra_op_eq_axiom }.

(* Without priority 1, this instance is selected when looking for an [asmOp],
   meaning that extra ops are the only possible ops. With that priority,
   [arch_extra.asm_opI] is selected first and we have both base and extra ops.
*)
Instance x86_extra_op_decl : asmOp x86_extra_op | 1 :=
  { asm_op_instr := get_instr_desc }.

Instance x86_extra : asm_extra register xmm_register rflag condt x86_op x86_extra_op :=
  { to_asm := assemble_extra }.

(* This concise name is convenient in OCaml code. *)
Definition x86_extended_op :=
  @extended_op _ _ _ _ _ _ x86_extra.

Definition Ox86 o : @sopn x86_extended_op _ := Oasm (BaseOp (None, o)).
