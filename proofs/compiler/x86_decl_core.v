Require Import
  utils
  strings
  wsize.

(* Import Memory. *)

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* --------------------------------------------- *)
Definition x86_reg_size  := U64.
Definition x86_xreg_size := U256.

(* -------------------------------------------------------------------- *)
Variant register : Type :=
  | RAX | RCX | RDX | RBX | RSP | RBP | RSI | RDI
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.

Definition string_of_register (r : register) : string :=
  match r with
  | RAX => "RAX"
  | RCX => "RCX"
  | RDX => "RDX"
  | RBX => "RBX"
  | RSP => "RSP"
  | RBP => "RBP"
  | RSI => "RSI"
  | RDI => "RDI"
  | R8  => "R8"
  | R9  => "R9"
  | R10 => "R10"
  | R11 => "R11"
  | R12 => "R12"
  | R13 => "R13"
  | R14 => "R14"
  | R15 => "R15"
  end.

(* -------------------------------------------------------------------- *)
Variant register_ext : Type :=
  | MM0 | MM1 | MM2 | MM3 | MM4 | MM5 | MM6 | MM7.

Definition string_of_regx (r : register_ext) : string :=
  match r with
  | MM0 => "MM0"
  | MM1 => "MM1"
  | MM2 => "MM2"
  | MM3 => "MM3"
  | MM4 => "MM4"
  | MM5 => "MM5"
  | MM6 => "MM6"
  | MM7 => "MM7"
  end.

(* -------------------------------------------------------------------- *)
Variant xmm_register : Type :=
  | XMM0 | XMM1 | XMM2 | XMM3
  | XMM4 | XMM5 | XMM6 | XMM7
  | XMM8 | XMM9 | XMM10 | XMM11
  | XMM12 | XMM13 | XMM14 | XMM15.

Definition string_of_xmm_register (r : xmm_register) : string :=
  match r with
  | XMM0 => "XMM0"
  | XMM1 => "XMM1"
  | XMM2 => "XMM2"
  | XMM3 => "XMM3"
  | XMM4 => "XMM4"
  | XMM5 => "XMM5"
  | XMM6 => "XMM6"
  | XMM7 => "XMM7"
  | XMM8 => "XMM8"
  | XMM9 => "XMM9"
  | XMM10 => "XMM10"
  | XMM11 => "XMM11"
  | XMM12 => "XMM12"
  | XMM13 => "XMM13"
  | XMM14 => "XMM14"
  | XMM15 => "XMM15"
  end.

(* -------------------------------------------------------------------- *)
Variant rflag : Type :=
  | CF | PF | ZF | SF | OF.

Definition string_of_rflag (rf : rflag) : string :=
  match rf with
 | CF => "CF"
 | PF => "PF"
 | ZF => "ZF"
 | SF => "SF"
 | OF => "OF"
 end.



