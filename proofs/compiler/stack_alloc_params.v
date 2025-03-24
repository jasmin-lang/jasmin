From mathcomp Require Import ssreflect.
Require Import expr.

Section WITH_PARAMS.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
.

Variant mov_kind :=
  | MK_LEA
  | MK_MOV.

Record stack_alloc_params :=
  {
    (* Return an instruction that computes an address from an base address and
     an offset. *)
    sap_mov_ofs :
      lval            (* The variable to save the address to. *)
      -> assgn_tag    (* The tag present in the source. *)
      -> mov_kind     (* The kind of address to compute. *)
      -> pexpr        (* Variable with base address. *)
      -> pexpr        (* Offset. *)
      -> option instr_r;
    (* Build an instruction that assigns an immediate value *)
    sap_immediate : var_i -> Z -> instr_r;
    (* Build an instruction that swap two registers *)
    (* [sap_swap t d1 d2 s1 s2] is equivalent to d1,d2 = s2, s1 *)
    sap_swap : assgn_tag -> var_i -> var_i -> var_i -> var_i -> instr_r;

  }.

(* TODO: Defined both in stack_alloc and here. Factorize *)
Definition add {pd:PointerData} := Papp2 (Oadd (Op_w Uptr)).

End WITH_PARAMS.
