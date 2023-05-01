(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import Sint63 strings utils gen_map tagged.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require x86_decl_core arm_decl_core.

Module Type CORE_IDENT.

  Parameter t  : Type.
  Parameter tag : t -> int.
  Parameter tagI : injective tag.

  Parameter name : Type.

  Parameter id_name : t -> name.

  (* A dummy ident needed in stack alloc *)
  Parameter dummy : t.

  (* Needed in makeReferenceArguments *)
  Parameter p__ : name.

  (* Needed in stack_alloc *)
  Parameter len__ : name.

  (* This is only use to be able to specify the spec *)
  Module ForSpec.

  Definition eqb (x y : t) : bool := (tag x =? tag y)%uint63.

  Fixpoint mem (x:t) (s:list t) :=
    match s with
    | [::] => false
    | y :: s' => eqb x y || mem x s'
    end.

  Fixpoint uniq (s:list t) :=
    match s with
    | [::] => true
    | x :: s' => ~~(mem x s') && uniq s'
    end.

  End ForSpec. Import ForSpec.

  (* For the declaration of X86 *)
  Module X86.

  Parameter RAX : t.
  Parameter RCX : t.
  Parameter RDX : t.
  Parameter RBX : t.
  Parameter RSP : t.
  Parameter RBP : t.
  Parameter RSI : t.
  Parameter RDI : t.
  Parameter R8  : t.
  Parameter R9  : t.
  Parameter R10 : t.
  Parameter R11 : t.
  Parameter R12 : t.
  Parameter R13 : t.
  Parameter R14 : t.
  Parameter R15 : t.

  Parameter MM0 : t.
  Parameter MM1 : t.
  Parameter MM2 : t.
  Parameter MM3 : t.
  Parameter MM4 : t.
  Parameter MM5 : t.
  Parameter MM6 : t.
  Parameter MM7 : t.

  Parameter XMM0  : t.
  Parameter XMM1  : t.
  Parameter XMM2  : t.
  Parameter XMM3  : t.
  Parameter XMM4  : t.
  Parameter XMM5  : t.
  Parameter XMM6  : t.
  Parameter XMM7  : t.
  Parameter XMM8  : t.
  Parameter XMM9  : t.
  Parameter XMM10 : t.
  Parameter XMM11 : t.
  Parameter XMM12 : t.
  Parameter XMM13 : t.
  Parameter XMM14 : t.
  Parameter XMM15 : t.

  Parameter CF : t.
  Parameter PF : t.
  Parameter ZF : t.
  Parameter SF : t.
  Parameter OF : t.

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
  Parameter reg_regx : all (fun x => ~~ (mem x id_regxs)) id_registers.

  End X86.

  (* For the declaration of arm-v7 *)
  Module ARM.

  Parameter R00 : t.
  Parameter R01 : t.
  Parameter R02 : t.
  Parameter R03 : t.
  Parameter R04 : t.
  Parameter R05 : t.
  Parameter R06 : t.
  Parameter R07 : t.
  Parameter R08 : t.
  Parameter R09 : t.
  Parameter R10 : t.
  Parameter R11 : t.
  Parameter R12 : t.
  Parameter LR  : t.
  Parameter SP  : t.

  Parameter NF  : t.
  Parameter ZF  : t.
  Parameter CF  : t.
  Parameter VF  : t.

  Definition id_registers :=
    [:: R00; R01; R02; R03; R04; R05; R06; R07; R08; R09; R10; R11; R12; LR; SP ].

  Definition id_rflags := [:: NF; ZF; CF; VF ].

  Parameter id_registers_uniq : uniq id_registers.

  Parameter id_rflags_uniq : uniq id_rflags.

  End ARM.

End CORE_IDENT.

(* An implementation of CORE_IDENT.
   The extraction overwrite it ... *)
Module Cident : CORE_IDENT.

  Definition t : Type := int.
  Definition tag (x : t) : int := x.

  Lemma tagI : injective tag.
  Proof. done. Qed.

  Definition name : Type := int.

  Definition id_name (x : t) : name := x.

  Definition dummy : t := 0%uint63.

  Definition p__ : name := 1%uint63.

  Definition len__ : name := 2%uint63.

  Module ForSpec.

  Definition eqb (x y : t) : bool := (tag x =? tag y)%uint63.

  Fixpoint mem (x:t) (s:list t) :=
    match s with
    | [::] => false
    | y :: s' => eqb x y || mem x s'
    end.

  Fixpoint uniq (s:list t) :=
    match s with
    | [::] => true
    | x :: s' => ~~(mem x s') && uniq s'
    end.

  End ForSpec. Import ForSpec.

  (* For the declaration of X86 *)
  Module X86.

  Definition RAX   := 3%uint63.
  Definition RCX   := 4%uint63.
  Definition RDX   := 5%uint63.
  Definition RBX   := 6%uint63.
  Definition RSP   := 7%uint63.
  Definition RBP   := 8%uint63.
  Definition RSI   := 9%uint63.
  Definition RDI   := 10%uint63.
  Definition R8    := 11%uint63.
  Definition R9    := 12%uint63.
  Definition R10   := 13%uint63.
  Definition R11   := 14%uint63.
  Definition R12   := 15%uint63.
  Definition R13   := 16%uint63.
  Definition R14   := 17%uint63.
  Definition R15   := 18%uint63.

  Definition MM0   := 19%uint63.
  Definition MM1   := 20%uint63.
  Definition MM2   := 21%uint63.
  Definition MM3   := 22%uint63.
  Definition MM4   := 23%uint63.
  Definition MM5   := 24%uint63.
  Definition MM6   := 25%uint63.
  Definition MM7   := 26%uint63.

  Definition XMM0  := 27%uint63.
  Definition XMM1  := 28%uint63.
  Definition XMM2  := 29%uint63.
  Definition XMM3  := 30%uint63.
  Definition XMM4  := 31%uint63.
  Definition XMM5  := 32%uint63.
  Definition XMM6  := 33%uint63.
  Definition XMM7  := 34%uint63.
  Definition XMM8  := 35%uint63.
  Definition XMM9  := 36%uint63.
  Definition XMM10 := 37%uint63.
  Definition XMM11 := 38%uint63.
  Definition XMM12 := 39%uint63.
  Definition XMM13 := 40%uint63.
  Definition XMM14 := 41%uint63.
  Definition XMM15 := 42%uint63.

  Definition CF    := 43%uint63.
  Definition PF    := 44%uint63.
  Definition ZF    := 45%uint63.
  Definition SF    := 46%uint63.
  Definition OF    := 47%uint63.

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

  Lemma reg_regx : all (fun x => ~~ (mem x id_regxs)) id_registers.
  Proof. done. Qed.

  End X86.

  (* For the declaration of arm-v7 *)
  Module ARM.

  Definition R00   := 3%uint63.
  Definition R01   := 4%uint63.
  Definition R02   := 5%uint63.
  Definition R03   := 6%uint63.
  Definition R04   := 7%uint63.
  Definition R05   := 8%uint63.
  Definition R06   := 9%uint63.
  Definition R07   := 10%uint63.
  Definition R08   := 11%uint63.
  Definition R09   := 12%uint63.
  Definition R10   := 13%uint63.
  Definition R11   := 14%uint63.
  Definition R12   := 15%uint63.
  Definition LR    := 16%uint63.
  Definition SP    := 17%uint63.

  Definition NF    := 18%uint63.
  Definition ZF    := 19%uint63.
  Definition CF    := 20%uint63.
  Definition VF    := 21%uint63.

  Definition id_registers :=
    [:: R00; R01; R02; R03; R04; R05; R06; R07; R08; R09; R10; R11; R12; LR; SP ].

  Definition id_rflags := [:: NF; ZF; CF; VF ].

  Lemma id_registers_uniq : uniq id_registers.
  Proof. done. Qed.

  Lemma id_rflags_uniq : uniq id_rflags.
  Proof. done. Qed.

  End ARM.

End Cident.

Module Tident <: TAGGED with Definition t := Cident.t
  := Tagged (Cident).

#[global] Canonical ident_eqType  := Eval compute in Tident.t_eqType.

Module WrapIdent.
  Definition t := Cident.t.
  Definition name  := Cident.name.
End WrapIdent.

Module Type IDENT.
  Definition ident := WrapIdent.t.
  Declare Module Mid : MAP with Definition K.t := [eqType of ident].
End IDENT.


Module Ident <: IDENT.

  Definition ident := WrapIdent.t.
  Definition name  := WrapIdent.name.
  Definition id_name : ident -> name := Cident.id_name.

  Module Mid := Tident.Mt.

  Definition dummy : ident := Cident.dummy.
  Definition p__   : name := Cident.p__.
  Definition len__ : name := Cident.len__.

  Module ForDummyProof.

    Lemma memE (x:ident) (s:list ident) : Cident.ForSpec.mem x s = (x \in s).
    Proof. by elim: s => //= y s hrec; rewrite in_cons hrec. Qed.

    Lemma uniqE (s:list ident) : Cident.ForSpec.uniq s = uniq s.
    Proof. by elim: s => //= x s hrec; rewrite memE hrec. Qed.

  End ForDummyProof. Import ForDummyProof.

  Module X86.

    Import Cident.X86.

    Definition RAX   : ident := RAX.
    Definition RCX   : ident := RCX.
    Definition RDX   : ident := RDX.
    Definition RBX   : ident := RBX.
    Definition RSP   : ident := RSP.
    Definition RBP   : ident := RBP.
    Definition RSI   : ident := RSI.
    Definition RDI   : ident := RDI.
    Definition R8    : ident := R8.
    Definition R9    : ident := R9.
    Definition R10   : ident := R10.
    Definition R11   : ident := R11.
    Definition R12   : ident := R12.
    Definition R13   : ident := R13.
    Definition R14   : ident := R14.
    Definition R15   : ident := R15.

    Definition MM0   : ident := MM0.
    Definition MM1   : ident := MM1.
    Definition MM2   : ident := MM2.
    Definition MM3   : ident := MM3.
    Definition MM4   : ident := MM4.
    Definition MM5   : ident := MM5.
    Definition MM6   : ident := MM6.
    Definition MM7   : ident := MM7.

    Definition XMM0  : ident := XMM0.
    Definition XMM1  : ident := XMM1.
    Definition XMM2  : ident := XMM2.
    Definition XMM3  : ident := XMM3.
    Definition XMM4  : ident := XMM4.
    Definition XMM5  : ident := XMM5.
    Definition XMM6  : ident := XMM6.
    Definition XMM7  : ident := XMM7.
    Definition XMM8  : ident := XMM8.
    Definition XMM9  : ident := XMM9.
    Definition XMM10 : ident := XMM10.
    Definition XMM11 : ident := XMM11.
    Definition XMM12 : ident := XMM12.
    Definition XMM13 : ident := XMM13.
    Definition XMM14 : ident := XMM14.
    Definition XMM15 : ident := XMM15.

    Definition CF    : ident := CF.
    Definition PF    : ident := PF.
    Definition ZF    : ident := ZF.
    Definition SF    : ident := SF.
    Definition OF    : ident := OF.

    Definition id_registers : list ident :=
      [:: RAX; RCX; RDX; RBX; RSP; RBP; RSI; RDI ;
          R8 ; R9 ; R10; R11; R12; R13; R14; R15 ].

    Definition id_regxs : list ident :=
      [:: MM0; MM1 ; MM2 ; MM3 ; MM4 ; MM5 ; MM6 ; MM7 ].

    Definition id_xmm_registers : list ident :=
      [:: XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7; XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15 ].

    Definition id_rflags : list ident :=
      [:: CF; PF; ZF; SF; OF ].

    Lemma id_registers_uniq : uniq id_registers.
    Proof. by rewrite -uniqE id_registers_uniq. Qed.

    Lemma id_regxs_uniq : uniq id_regxs.
    Proof. by rewrite -uniqE id_regxs_uniq. Qed.

    Lemma id_xmm_registers_uniq : uniq id_xmm_registers.
    Proof. by rewrite -uniqE id_xmm_registers_uniq. Qed.

    Lemma id_rflags_uniq : uniq id_rflags.
    Proof. by rewrite -uniqE id_rflags_uniq. Qed.

    Lemma reg_regx : all (fun x => ~~ (x \in id_regxs)) id_registers.
    Proof. by rewrite (eq_all (a2:= fun x => ~~(Cident.ForSpec.mem x id_regxs))) ?reg_regx. Qed.

  End X86.

  Module ARM.
    Import Cident.ARM.

    Definition R00 : ident := R00.
    Definition R01 : ident := R01.
    Definition R02 : ident := R02.
    Definition R03 : ident := R03.
    Definition R04 : ident := R04.
    Definition R05 : ident := R05.
    Definition R06 : ident := R06.
    Definition R07 : ident := R07.
    Definition R08 : ident := R08.
    Definition R09 : ident := R09.
    Definition R10 : ident := R10.
    Definition R11 : ident := R11.
    Definition R12 : ident := R12.
    Definition LR  : ident := LR.
    Definition SP  : ident := SP.

    Definition NF  : ident := NF.
    Definition ZF  : ident := ZF.
    Definition CF  : ident := CF.
    Definition VF  : ident := VF.

    Definition id_registers : list ident :=
      [:: R00; R01; R02; R03; R04; R05; R06; R07; R08; R09; R10; R11; R12; LR; SP ].

    Definition id_rflags : list ident := [:: NF; ZF; CF; VF ].

    Lemma id_registers_uniq : uniq id_registers.
    Proof. by rewrite -uniqE id_registers_uniq. Qed.

    Lemma id_rflags_uniq : uniq id_rflags.
    Proof. by rewrite -uniqE id_rflags_uniq. Qed.

  End ARM.

End Ident.
