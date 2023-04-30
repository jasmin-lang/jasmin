(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import strings utils gen_map.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require x86_decl_core arm_decl_core.

Module Type IDENT.

  Parameter ident : Type.

  (* Equality *)
  Parameter ident_eqb : ident -> ident -> bool.

  Parameter ident_eq_axiom : Equality.axiom ident_eqb.

  Definition ident_eqMixin := Equality.Mixin ident_eq_axiom.

  Definition ident_eqType  := EqType ident ident_eqMixin.
  Canonical ident_eqType.

  Declare Module Mid : MAP with Definition K.t := [eqType of ident].

  (* Name *)

  Parameter name : Type.

  Parameter id_name : ident -> name.

  (* A dummy ident needed in stac_ alloc_proof_2  (should have type sbool).
     It will be nice to remove it. *)
  Parameter dummy : ident.

  (* Needed in makeReferenceArguments *)
  Parameter p__ : name.
  (* Needed in stack_alloc *)
  Parameter len__ : name.


  (* Idents needed for x86 *)

  Module X86.

  Parameter RAX   : ident.
  Parameter RCX   : ident.
  Parameter RDX   : ident.
  Parameter RBX   : ident.
  Parameter RSP   : ident.
  Parameter RBP   : ident.
  Parameter RSI   : ident.
  Parameter RDI   : ident.
  Parameter R8    : ident.
  Parameter R9    : ident.
  Parameter R10   : ident.
  Parameter R11   : ident.
  Parameter R12   : ident.
  Parameter R13   : ident.
  Parameter R14   : ident.
  Parameter R15   : ident.

  Parameter MM0   : ident.
  Parameter MM1   : ident.
  Parameter MM2   : ident.
  Parameter MM3   : ident.
  Parameter MM4   : ident.
  Parameter MM5   : ident.
  Parameter MM6   : ident.
  Parameter MM7   : ident.

  Parameter XMM0  : ident.
  Parameter XMM1  : ident.
  Parameter XMM2  : ident.
  Parameter XMM3  : ident.
  Parameter XMM4  : ident.
  Parameter XMM5  : ident.
  Parameter XMM6  : ident.
  Parameter XMM7  : ident.
  Parameter XMM8  : ident.
  Parameter XMM9  : ident.
  Parameter XMM10 : ident.
  Parameter XMM11 : ident.
  Parameter XMM12 : ident.
  Parameter XMM13 : ident.
  Parameter XMM14 : ident.
  Parameter XMM15 : ident.

  Parameter CF    : ident.
  Parameter PF    : ident.
  Parameter ZF    : ident.
  Parameter SF    : ident.
  Parameter OF    : ident.

  Definition id_registers :=
    [:: RAX; RCX; RDX; RBX; RSP; RBP; RSI; RDI ;
        R8 ; R9 ; R10; R11; R12; R13; R14; R15 ].

  Definition id_regxs :=
    [:: MM0; MM1 ; MM2 ; MM3 ; MM4 ; MM5 ; MM6 ; MM7 ].

  Definition id_xmm_registers :=
    [:: XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7; XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15 ].

  Definition id_rflags :=
    [:: CF; PF; ZF; SF; OF ].

  Parameter id_registers_uniq : uniq id_registers.
  Parameter id_regxs_uniq : uniq id_regxs.
  Parameter id_xmm_registers_uniq : uniq id_xmm_registers.
  Parameter id_rflags_uniq : uniq id_rflags.
  Parameter reg_regx : all (fun x => ~~ (x \in id_regxs)) id_registers.

  End X86.

  (* Idents needed for x86 *)
  Module ARM.
  Parameter R00   : ident.
  Parameter R01   : ident.
  Parameter R02   : ident.
  Parameter R03   : ident.
  Parameter R04   : ident.
  Parameter R05   : ident.
  Parameter R06   : ident.
  Parameter R07   : ident.
  Parameter R08   : ident.
  Parameter R09   : ident.
  Parameter R10   : ident.
  Parameter R11   : ident.
  Parameter R12   : ident.
  Parameter LR    : ident.
  Parameter SP    : ident.

  Parameter NF    : ident.
  Parameter ZF    : ident.
  Parameter CF    : ident.
  Parameter VF    : ident.

  Definition id_registers :=
    [:: R00; R01; R02; R03; R04; R05; R06; R07; R08; R09; R10; R11; R12; LR; SP ].

  Definition id_rflags := [:: NF; ZF; CF; VF ].

  Parameter id_registers_uniq : uniq id_registers.

  Parameter id_rflags_uniq : uniq id_rflags.

  End ARM.

End IDENT.

Module Ident : IDENT with Definition ident := string
                     with Definition ident_eqb := string_beq
                     with Definition ident_eq_axiom := string_eqP
                     with Definition ident_eqMixin := string_eqMixin
                     with Definition ident_eqType := string_eqType.

  Definition ident := string.

  (* Equality *)
  Definition ident_eqb : ident -> ident -> bool := string_beq.

  Definition ident_eq_axiom := string_eqP.

  Definition ident_eqMixin := string_eqMixin.

  Definition ident_eqType  := string_eqType.

  Module Mid := Ms.

  (* Name *)

  Definition name := string.

  Definition id_name (x: ident) : name := x.

  (* A dummy ident needed in stack alloc *)
  Definition dummy : string := ""%string.

  (* Needed in makeReferenceArguments *)
  Definition p__ : name := "__p__"%string.

  (* Needed in stack_alloc *)
  Definition len__ : name := "__len__"%string.

  Module X86. Import x86_decl_core.

  Definition RAX   := string_of_register RAX.
  Definition RCX   := string_of_register RCX.
  Definition RDX   := string_of_register RDX.
  Definition RBX   := string_of_register RBX.
  Definition RSP   := string_of_register RSP.
  Definition RBP   := string_of_register RBP.
  Definition RSI   := string_of_register RSI.
  Definition RDI   := string_of_register RDI.
  Definition R8    := string_of_register R8.
  Definition R9    := string_of_register R9.
  Definition R10   := string_of_register R10.
  Definition R11   := string_of_register R11.
  Definition R12   := string_of_register R12.
  Definition R13   := string_of_register R13.
  Definition R14   := string_of_register R14.
  Definition R15   := string_of_register R15.

  Definition MM0   := string_of_regx MM0.
  Definition MM1   := string_of_regx MM1.
  Definition MM2   := string_of_regx MM2.
  Definition MM3   := string_of_regx MM3.
  Definition MM4   := string_of_regx MM4.
  Definition MM5   := string_of_regx MM5.
  Definition MM6   := string_of_regx MM6.
  Definition MM7   := string_of_regx MM7.

  Definition XMM0  := string_of_xmm_register XMM0.
  Definition XMM1  := string_of_xmm_register XMM1.
  Definition XMM2  := string_of_xmm_register XMM2.
  Definition XMM3  := string_of_xmm_register XMM3.
  Definition XMM4  := string_of_xmm_register XMM4.
  Definition XMM5  := string_of_xmm_register XMM5.
  Definition XMM6  := string_of_xmm_register XMM6.
  Definition XMM7  := string_of_xmm_register XMM7.
  Definition XMM8  := string_of_xmm_register XMM8.
  Definition XMM9  := string_of_xmm_register XMM9.
  Definition XMM10 := string_of_xmm_register XMM10.
  Definition XMM11 := string_of_xmm_register XMM11.
  Definition XMM12 := string_of_xmm_register XMM12.
  Definition XMM13 := string_of_xmm_register XMM13.
  Definition XMM14 := string_of_xmm_register XMM14.
  Definition XMM15 := string_of_xmm_register XMM15.

  Definition CF    := string_of_rflag CF.
  Definition PF    := string_of_rflag PF.
  Definition ZF    := string_of_rflag ZF.
  Definition SF    := string_of_rflag SF.
  Definition OF    := string_of_rflag OF.

  Definition id_registers :=
    [:: RAX; RCX; RDX; RBX; RSP; RBP; RSI; RDI ;
        R8 ; R9 ; R10; R11; R12; R13; R14; R15 ].

  Definition id_regxs :=
    [:: MM0; MM1 ; MM2 ; MM3 ; MM4 ; MM5 ; MM6 ; MM7 ].

  Definition id_xmm_registers :=
    [:: XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7; XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15 ].

  Definition id_rflags :=
    [:: CF; PF; ZF; SF; OF ].

  Lemma id_registers_uniq : uniq id_registers.
  Proof. done. Qed.

  Lemma id_regxs_uniq : uniq id_regxs.
  Proof. done. Qed.

  Lemma id_xmm_registers_uniq : uniq id_xmm_registers.
  Proof. done. Qed.

  Lemma id_rflags_uniq : uniq id_rflags.
  Proof. done. Qed.

  Lemma reg_regx : all (fun x => ~~ (x \in id_regxs)) id_registers.
  Proof. done. Qed.

  End X86.

  Module ARM. Import arm_decl_core.

  Definition R00   := string_of_register R00.
  Definition R01   := string_of_register R01.
  Definition R02   := string_of_register R02.
  Definition R03   := string_of_register R03.
  Definition R04   := string_of_register R04.
  Definition R05   := string_of_register R05.
  Definition R06   := string_of_register R06.
  Definition R07   := string_of_register R07.
  Definition R08   := string_of_register R08.
  Definition R09   := string_of_register R09.
  Definition R10   := string_of_register R10.
  Definition R11   := string_of_register R11.
  Definition R12   := string_of_register R12.
  Definition LR    := string_of_register LR.
  Definition SP    := string_of_register SP.

  Definition NF    := string_of_rflag NF.
  Definition ZF    := string_of_rflag ZF.
  Definition CF    := string_of_rflag CF.
  Definition VF    := string_of_rflag VF.

  Definition id_registers :=
    [:: R00; R01; R02; R03; R04; R05; R06; R07; R08; R09; R10; R11; R12; LR; SP ].

  Definition id_rflags := [:: NF; ZF; CF; VF ].

  Lemma id_registers_uniq : uniq id_registers.
  Proof. done. Qed.

  Lemma id_rflags_uniq : uniq id_rflags.
  Proof. done. Qed.

  End ARM.

End Ident.
