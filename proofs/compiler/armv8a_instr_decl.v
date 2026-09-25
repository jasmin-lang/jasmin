(* ARMv8-A (AArch64) instruction set.

   A64 base instructions. Data-processing instructions come in two forms
   selected by the [opts_size] option: the 64-bit (X registers) form and
   the 32-bit (W registers) form, which zeroes the upper 32 bits of
   destination registers. Advanced SIMD (NEON) instructions, on 64-bit or
   128-bit vectors held in the SIMD&FP registers, have their own mnemonics
   and descriptions (see [armv8a_vmnemonic] below). Instruction
   documentation is quoted from the ARM Architecture Reference Manual for
   A-profile architecture, ARM DDI 0487 M.a (the machine-readable
   extraction lives in compiler/doc/armv8a_isa_docs.json). *)

From elpi.apps Require Import derive.std.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype fintype.
From mathcomp Require Import ssralg word_ssrZ.

Require Import
  sem_type
  shift_kind
  strings
  utils
  waes
  word.
Require xseq.
Require Import
  values
  sopn
  sopn_semi
  arch_decl
  arch_utils.
Require Import armv8a_decl.


Module E.
  Definition no_semantics : error := ErrSemUndef.
End E.


(* -------------------------------------------------------------------- *)
(* ARMv8-A instruction options.
   Unlike ARMv7-M, A64 has no conditional execution and flag-setting
   variants are distinct mnemonics (ADDS, SUBS, ...). The options select
   the operand size ([U64] for the X form, [U32] for the W form) and an
   optional shift of the last register operand of data-processing
   instructions. *)

#[only(eqbOK)] derive
Record armv8a_options :=
  {
    has_shift : option shift_kind;
    opts_size : wsize;
  }.

#[ export ]
Instance eqTC_armv8a_options : eqTypeC armv8a_options :=
  { ceqP := armv8a_options_eqb_OK }.

Canonical armv8a_options_eqType := @ceqT_eqType _ eqTC_armv8a_options.

Definition default_opts : armv8a_options :=
  {|
    has_shift := None;
    opts_size := U64;
  |}.

Definition opts_at (ws : wsize) : armv8a_options :=
  {|
    has_shift := None;
    opts_size := ws;
  |}.


(* -------------------------------------------------------------------- *)
(* ARMv8-A instruction mnemonics. *)

#[only(eqbOK)] derive
Variant armv8a_mnemonic : Type :=
(* Arithmetic *)
| ADD                            (* Add without carry *)
| ADDS                           (* Add without carry, setting flags *)
| ADC                            (* Add with carry *)
| ADCS                           (* Add with carry, setting flags *)
| SUB                            (* Subtract without carry *)
| SUBS                           (* Subtract without carry, setting flags *)
| SBC                            (* Subtract with carry *)
| SBCS                           (* Subtract with carry, setting flags *)
| NEG                            (* Negate *)
| MUL                            (* Multiply and write the least significant
                                    bits of the result *)
| MADD                           (* Multiply and add *)
| MSUB                           (* Multiply and subtract *)
| SDIV                           (* Signed division *)
| UDIV                           (* Unsigned division *)
| UMULL                          (* Unsigned multiply long *)
| SMULL                          (* Signed multiply long *)
| UMADDL                         (* Unsigned multiply-add long *)
| SMADDL                         (* Signed multiply-add long *)
| UMULH                          (* Unsigned multiply high *)
| SMULH                          (* Signed multiply high *)

(* Logical *)
| AND                            (* Bitwise AND *)
| ANDS                           (* Bitwise AND, setting flags *)
| BIC                            (* Bitwise AND with bitwise NOT *)
| BICS                           (* Bitwise AND with bitwise NOT, setting flags *)
| ORR                            (* Bitwise OR *)
| EOR                            (* Bitwise XOR *)
| MVN                            (* Bitwise NOT *)

(* Shifts *)
| ASR                            (* Arithmetic shift right *)
| LSL                            (* Logical shift left *)
| LSR                            (* Logical shift right *)
| ROR                            (* Rotate right *)

(* Bit manipulation *)
| RBIT                           (* Reverse bits *)
| REV                            (* Reverse bytes *)
| REV16                          (* Reverse bytes in 16-bit halfwords *)
| REV32                          (* Reverse bytes in 32-bit words *)
| CLZ                            (* Count leading zeros *)
| CLS                            (* Count leading sign bits *)

(* Bit field operations *)
| BFC                            (* Bitfield clear *)
| BFI                            (* Bitfield insert *)
| BFXIL                          (* Bitfield extract and insert at low end *)
| SBFX                           (* Signed bitfield extract *)
| UBFX                           (* Unsigned bitfield extract *)
| EXTR                           (* Extract register from a register pair *)

(* Other data processing instructions *)
| MOV                            (* Copy operand to destination *)
| MOVN                           (* Move wide with NOT *)
| MOVZ                           (* Move wide with zero *)
| MOVK                           (* Move wide with keep *)
| ADR                            (* Form PC-relative address *)
| SXTB                           (* Sign extend byte *)
| SXTH                           (* Sign extend halfword *)
| SXTW                           (* Sign extend word *)
| UXTB                           (* Zero extend byte *)
| UXTH                           (* Zero extend halfword *)
| UXTW                           (* Zero extend word *)

(* Comparisons *)
| CMP                            (* Compare *)
| CMN                            (* Compare negative *)
| TST                            (* Test *)

(* Conditional selection *)
| CSEL                           (* Conditional select *)
| CSINC                          (* Conditional select increment *)
| CSINV                          (* Conditional select invert *)
| CSNEG                          (* Conditional select negate *)
| CSET                           (* Conditional set *)
| CSETM                          (* Conditional set mask *)

(* Loads *)
| LDR                            (* Load a word or doubleword *)
| LDRB                           (* Load a zero extended byte *)
| LDRH                           (* Load a zero extended halfword *)
| LDRSB                          (* Load a sign extended byte *)
| LDRSH                          (* Load a sign extended halfword *)
| LDRSW                          (* Load a sign extended word *)
| LDP                            (* Load a pair of words or doublewords *)

(* Stores *)
| STR                            (* Store a word or doubleword *)
| STRB                           (* Store a byte *)
| STRH                           (* Store a halfword *)
| STP                            (* Store a pair of words or doublewords *)

(* Barriers *)
| CSDB                           (* Consumption of speculative data barrier *)
| DSB                            (* Data synchronization barrier, full system *)
| ISB.                           (* Instruction synchronization barrier *)

#[ export ]
Instance eqTC_armv8a_mnemonic : eqTypeC armv8a_mnemonic :=
  { ceqP := armv8a_mnemonic_eqb_OK }.

Canonical armv8a_mnemonic_eqType := @ceqT_eqType _ eqTC_armv8a_mnemonic.

Definition armv8a_mnemonics : seq armv8a_mnemonic :=
  [:: ADD; ADDS; ADC; ADCS; SUB; SUBS; SBC; SBCS; NEG
    ; MUL; MADD; MSUB; SDIV; UDIV
    ; UMULL; SMULL; UMADDL; SMADDL; UMULH; SMULH
    ; AND; ANDS; BIC; BICS; ORR; EOR; MVN
    ; ASR; LSL; LSR; ROR
    ; RBIT; REV; REV16; REV32; CLZ; CLS
    ; BFC; BFI; BFXIL; SBFX; UBFX; EXTR
    ; MOV; MOVN; MOVZ; MOVK; ADR
    ; SXTB; SXTH; SXTW; UXTB; UXTH; UXTW
    ; CMP; CMN; TST
    ; CSEL; CSINC; CSINV; CSNEG; CSET; CSETM
    ; LDR; LDRB; LDRH; LDRSB; LDRSH; LDRSW; LDP
    ; STR; STRB; STRH; STP
    ; CSDB; DSB; ISB
  ].

Lemma armv8a_mnemonic_fin_axiom : Finite.axiom armv8a_mnemonics.
Proof. by case. Qed.

#[ export ]
Instance finTC_armv8a_mnemonic : finTypeC armv8a_mnemonic :=
  {
    cenum := armv8a_mnemonics;
    cenumP := armv8a_mnemonic_fin_axiom;
  }.

Canonical armv8a_mnemonic_finType := @cfinT_finType _ finTC_armv8a_mnemonic.

(* Mnemonics whose last register operand can be optionally shifted. *)
Definition has_shift_mnemonics : seq armv8a_mnemonic :=
  [:: ADD; ADDS; SUB; SUBS; NEG
    ; AND; ANDS; BIC; BICS; ORR; EOR; MVN
    ; CMP; CMN; TST
  ].

(* The arithmetic instructions (ADD/ADDS/SUB/SUBS/NEG/CMP/CMN) only admit
   LSL, LSR and ASR on their shifted-register operand; ROR is reserved
   (C6.2.5 "ADD (shifted register)"). The logical instructions admit all
   four shifts (C6.2.14 "AND (shifted register)"). *)
Definition ror_shift_mnemonics : seq armv8a_mnemonic :=
  [:: AND; ANDS; BIC; BICS; ORR; EOR; MVN; TST ].

Definition shift_allowed (mn : armv8a_mnemonic) (sk : shift_kind) : bool :=
  if sk is SROR then mn \in ror_shift_mnemonics else true.

(* Mnemonics available in both the 32-bit (W) and 64-bit (X) forms; the
   remaining mnemonics are only valid with [opts_size = U64], except the
   barriers, which have no operand. *)
Definition sized_mnemonics : seq armv8a_mnemonic :=
  [:: ADD; ADDS; ADC; ADCS; SUB; SUBS; SBC; SBCS; NEG
    ; MUL; MADD; MSUB; SDIV; UDIV
    ; AND; ANDS; BIC; BICS; ORR; EOR; MVN
    ; ASR; LSL; LSR; ROR
    ; RBIT; REV; REV16; CLZ; CLS
    ; BFC; BFI; BFXIL; SBFX; UBFX; EXTR
    ; MOV; MOVN; MOVZ; MOVK
    ; SXTB; SXTH; UXTB; UXTH
    ; CMP; CMN; TST
    ; CSEL; CSINC; CSINV; CSNEG; CSET; CSETM
    ; LDR; LDRB; LDRH; LDRSB; LDRSH; LDP
    ; STR; STRB; STRH; STP
  ].

Definition wsize_uload_mn : seq (wsize * armv8a_mnemonic) :=
  [:: (U8, LDRB); (U16, LDRH); (U32, LDR); (U64, LDR) ].

Definition uload_mn_of_wsize (ws : wsize) : option armv8a_mnemonic :=
  xseq.assoc wsize_uload_mn ws.

Definition wsize_sload_mn : seq (wsize * armv8a_mnemonic) :=
  [:: (U8, LDRSB); (U16, LDRSH); (U32, LDRSW) ].

Definition sload_mn_of_wsize (ws : wsize) : option armv8a_mnemonic :=
  xseq.assoc wsize_sload_mn ws.

Definition wsize_of_sload_mn (mn : armv8a_mnemonic) : option wsize :=
  xseq.assoc ([seq (x.2, x.1) | x <- wsize_sload_mn]) mn.

(* Memory access width of narrow loads; [LDR] accesses at the operand
   size. *)
Definition wsize_of_narrow_load_mn (mn : armv8a_mnemonic) : option wsize :=
  match mn with
  | LDRB | LDRSB => Some U8
  | LDRH | LDRSH => Some U16
  | LDRSW => Some U32
  | _ => None
  end.

Definition wsize_store_mn : seq (wsize * armv8a_mnemonic) :=
  [:: (U8, STRB); (U16, STRH); (U32, STR); (U64, STR) ].

Definition store_mn_of_wsize (ws : wsize) : option armv8a_mnemonic :=
  xseq.assoc wsize_store_mn ws.

Definition wsize_of_narrow_store_mn (mn : armv8a_mnemonic) : option wsize :=
  match mn with
  | STRB => Some U8
  | STRH => Some U16
  | _ => None
  end.

Definition string_of_armv8a_mnemonic (mn : armv8a_mnemonic) : string :=
  match mn with
  | ADD => "ADD"
  | ADDS => "ADDS"
  | ADC => "ADC"
  | ADCS => "ADCS"
  | SUB => "SUB"
  | SUBS => "SUBS"
  | SBC => "SBC"
  | SBCS => "SBCS"
  | NEG => "NEG"
  | MUL => "MUL"
  | MADD => "MADD"
  | MSUB => "MSUB"
  | SDIV => "SDIV"
  | UDIV => "UDIV"
  | UMULL => "UMULL"
  | SMULL => "SMULL"
  | UMADDL => "UMADDL"
  | SMADDL => "SMADDL"
  | UMULH => "UMULH"
  | SMULH => "SMULH"
  | AND => "AND"
  | ANDS => "ANDS"
  | BIC => "BIC"
  | BICS => "BICS"
  | ORR => "ORR"
  | EOR => "EOR"
  | MVN => "MVN"
  | ASR => "ASR"
  | LSL => "LSL"
  | LSR => "LSR"
  | ROR => "ROR"
  | RBIT => "RBIT"
  | REV => "REV"
  | REV16 => "REV16"
  | REV32 => "REV32"
  | CLZ => "CLZ"
  | CLS => "CLS"
  | BFC => "BFC"
  | BFI => "BFI"
  | BFXIL => "BFXIL"
  | SBFX => "SBFX"
  | UBFX => "UBFX"
  | EXTR => "EXTR"
  | MOV => "MOV"
  | MOVN => "MOVN"
  | MOVZ => "MOVZ"
  | MOVK => "MOVK"
  | ADR => "ADR"
  | SXTB => "SXTB"
  | SXTH => "SXTH"
  | SXTW => "SXTW"
  | UXTB => "UXTB"
  | UXTH => "UXTH"
  | UXTW => "UXTW"
  | CMP => "CMP"
  | CMN => "CMN"
  | TST => "TST"
  | CSEL => "CSEL"
  | CSINC => "CSINC"
  | CSINV => "CSINV"
  | CSNEG => "CSNEG"
  | CSET => "CSET"
  | CSETM => "CSETM"
  | LDR => "LDR"
  | LDRB => "LDRB"
  | LDRH => "LDRH"
  | LDRSB => "LDRSB"
  | LDRSH => "LDRSH"
  | LDRSW => "LDRSW"
  | LDP => "LDP"
  | STR => "STR"
  | STRB => "STRB"
  | STRH => "STRH"
  | STP => "STP"
  | CSDB => "CSDB"
  | DSB => "DSB"
  | ISB => "ISB"
  end%string.


(* -------------------------------------------------------------------- *)
(* ARMv8-A Advanced SIMD (NEON) instruction mnemonics.
   They operate on the 128-bit SIMD&FP registers, as 64-bit or 128-bit
   vectors (the lane size and the vector size are arguments of
   [ARMv8A_vop]). Their constructors are prefixed with [V] to keep them
   apart from the scalar mnemonics; the assembly names are the
   architectural ones (see [string_of_armv8a_vmnemonic]), the intrinsic
   names keep the [V] prefix (see [armv8a_vmn_name]). *)

#[only(eqbOK)] derive
Variant armv8a_vmnemonic : Type :=
(* Moves, loads and stores *)
| VMOV                           (* Move vector *)
| VLDR                           (* Load a SIMD&FP register *)
| VSTR                           (* Store a SIMD&FP register *)

(* Bitwise *)
| VAND                           (* Bitwise AND *)
| VBIC                           (* Bitwise bit clear *)
| VORR                           (* Bitwise inclusive OR *)
| VORN                           (* Bitwise inclusive OR NOT *)
| VEOR                           (* Bitwise exclusive OR *)
| VNOT                           (* Bitwise NOT *)
| VBSL                           (* Bitwise select *)
| VBIT                           (* Bitwise insert if true *)
| VBIF                           (* Bitwise insert if false *)

(* Lane-wise integer arithmetic *)
| VADD                           (* Add *)
| VSUB                           (* Subtract *)
| VMUL                           (* Multiply *)
| VNEG                           (* Negate *)
| VABS                           (* Absolute value *)
| VSMAX                          (* Signed maximum *)
| VSMIN                          (* Signed minimum *)
| VUMAX                          (* Unsigned maximum *)
| VUMIN                          (* Unsigned minimum *)

(* Shifts by immediate *)
| VSHL                           (* Shift left *)
| VUSHR                          (* Unsigned shift right *)
| VSSHR                          (* Signed shift right *)
| VSLI                           (* Shift left and insert *)
| VSRI                           (* Shift right and insert *)
| VUSRA                          (* Unsigned shift right and accumulate *)
| VSSRA                          (* Signed shift right and accumulate *)

(* Shifts by register *)
| VUSHL                          (* Unsigned shift left (register) *)
| VSSHL                          (* Signed shift left (register) *)

(* Permutations *)
| VEXT                           (* Extract vector from pair of vectors *)
| VZIP1                          (* Zip vectors (primary) *)
| VZIP2                          (* Zip vectors (secondary) *)
| VUZP1                          (* Unzip vectors (primary) *)
| VUZP2                          (* Unzip vectors (secondary) *)
| VTRN1                          (* Transpose vectors (primary) *)
| VTRN2                          (* Transpose vectors (secondary) *)
| VREV16                         (* Reverse elements in 16-bit halfwords *)
| VREV32                         (* Reverse elements in 32-bit words *)
| VREV64                         (* Reverse elements in 64-bit doublewords *)
| VTBL                           (* Table vector lookup *)

(* Comparisons *)
| VCMEQ                          (* Compare bitwise equal *)
| VCMGT                          (* Compare signed greater than *)
| VCMGE                          (* Compare signed greater than or equal *)
| VCMHI                          (* Compare unsigned higher *)
| VCMHS                          (* Compare unsigned higher or same *)
| VCMTST                         (* Compare bitwise test bits nonzero *)

(* Copies between lanes and general registers *)
| VDUP                           (* Duplicate general register *)
| VDUPLANE                       (* Duplicate vector element *)
| VINS                           (* Insert general register *)
| VINSLANE                       (* Insert vector element *)
| VUMOV                          (* Unsigned move vector element *)
| VSMOV                          (* Signed move vector element *)

(* AES *)
| VAESE                          (* AES single round encryption *)
| VAESD                          (* AES single round decryption *)
| VAESMC                         (* AES mix columns *)
| VAESIMC                        (* AES inverse mix columns *)

(* Polynomial multiplication *)
| VPMULL                         (* Polynomial multiply long, low halves *)
| VPMULL2                        (* Polynomial multiply long, high halves *)

(* SHA-3 *)
| VEOR3                          (* Three-way exclusive OR *)
| VRAX1                          (* Rotate and exclusive OR *)
| VXAR                           (* Exclusive OR and rotate *)
| VBCAX                          (* Bit clear and exclusive OR *)

(* Multiply-accumulate *)
| VMLA                           (* Multiply-add to accumulator *)
| VMLS                           (* Multiply-subtract from accumulator *)

(* Saturating multiplications *)
| VSQDMULH                       (* Signed saturating doubling multiply
                                    returning high half *)
| VSQRDMULH                      (* Signed saturating rounding doubling
                                    multiply returning high half *)
| VSQRDMLAH                      (* Signed saturating rounding doubling
                                    multiply accumulate returning high
                                    half *)
| VSQRDMLSH.                     (* Signed saturating rounding doubling
                                    multiply subtract returning high
                                    half *)

#[ export ]
Instance eqTC_armv8a_vmnemonic : eqTypeC armv8a_vmnemonic :=
  { ceqP := armv8a_vmnemonic_eqb_OK }.

Canonical armv8a_vmnemonic_eqType := @ceqT_eqType _ eqTC_armv8a_vmnemonic.

Definition armv8a_vmnemonics : seq armv8a_vmnemonic :=
  [:: VMOV; VLDR; VSTR
    ; VAND; VBIC; VORR; VORN; VEOR; VNOT; VBSL; VBIT; VBIF
    ; VADD; VSUB; VMUL; VNEG; VABS; VSMAX; VSMIN; VUMAX; VUMIN
    ; VSHL; VUSHR; VSSHR; VSLI; VSRI; VUSRA; VSSRA
    ; VUSHL; VSSHL
    ; VEXT; VZIP1; VZIP2; VUZP1; VUZP2; VTRN1; VTRN2
    ; VREV16; VREV32; VREV64; VTBL
    ; VCMEQ; VCMGT; VCMGE; VCMHI; VCMHS; VCMTST
    ; VDUP; VDUPLANE; VINS; VINSLANE; VUMOV; VSMOV
    ; VAESE; VAESD; VAESMC; VAESIMC
    ; VPMULL; VPMULL2
    ; VEOR3; VRAX1; VXAR; VBCAX
    ; VMLA; VMLS
    ; VSQDMULH; VSQRDMULH; VSQRDMLAH; VSQRDMLSH
  ].

Lemma armv8a_vmnemonic_fin_axiom : Finite.axiom armv8a_vmnemonics.
Proof. by case. Qed.

#[ export ]
Instance finTC_armv8a_vmnemonic : finTypeC armv8a_vmnemonic :=
  {
    cenum := armv8a_vmnemonics;
    cenumP := armv8a_vmnemonic_fin_axiom;
  }.

Definition string_of_armv8a_vmnemonic (vmn : armv8a_vmnemonic) : string :=
  match vmn with
  | VMOV => "MOV"
  | VLDR => "LDR"
  | VSTR => "STR"
  | VAND => "AND"
  | VBIC => "BIC"
  | VORR => "ORR"
  | VORN => "ORN"
  | VEOR => "EOR"
  | VNOT => "NOT"
  | VBSL => "BSL"
  | VBIT => "BIT"
  | VBIF => "BIF"
  | VADD => "ADD"
  | VSUB => "SUB"
  | VMUL => "MUL"
  | VNEG => "NEG"
  | VABS => "ABS"
  | VSMAX => "SMAX"
  | VSMIN => "SMIN"
  | VUMAX => "UMAX"
  | VUMIN => "UMIN"
  | VSHL => "SHL"
  | VUSHR => "USHR"
  | VSSHR => "SSHR"
  | VSLI => "SLI"
  | VSRI => "SRI"
  | VUSRA => "USRA"
  | VSSRA => "SSRA"
  | VUSHL => "USHL"
  | VSSHL => "SSHL"
  | VEXT => "EXT"
  | VZIP1 => "ZIP1"
  | VZIP2 => "ZIP2"
  | VUZP1 => "UZP1"
  | VUZP2 => "UZP2"
  | VTRN1 => "TRN1"
  | VTRN2 => "TRN2"
  | VREV16 => "REV16"
  | VREV32 => "REV32"
  | VREV64 => "REV64"
  | VTBL => "TBL"
  | VCMEQ => "CMEQ"
  | VCMGT => "CMGT"
  | VCMGE => "CMGE"
  | VCMHI => "CMHI"
  | VCMHS => "CMHS"
  | VCMTST => "CMTST"
  | VDUP | VDUPLANE => "DUP"
  | VINS | VINSLANE => "INS"
  | VUMOV => "UMOV"
  | VSMOV => "SMOV"
  | VAESE => "AESE"
  | VAESD => "AESD"
  | VAESMC => "AESMC"
  | VAESIMC => "AESIMC"
  | VPMULL => "PMULL"
  | VPMULL2 => "PMULL2"
  | VEOR3 => "EOR3"
  | VRAX1 => "RAX1"
  | VXAR => "XAR"
  | VBCAX => "BCAX"
  | VMLA => "MLA"
  | VMLS => "MLS"
  | VSQDMULH => "SQDMULH"
  | VSQRDMULH => "SQRDMULH"
  | VSQRDMLAH => "SQRDMLAH"
  | VSQRDMLSH => "SQRDMLSH"
  end%string.

(* The Jasmin name of a vector mnemonic: the architectural one prefixed
   with [V] ([VMOV]), so that it is distinct from the scalar ones. The
   element forms of DUP and INS, whose source is a lane of a vector
   register, are named [VDUPLANE] and [VINSLANE], to keep them apart from
   the general-register forms [VDUP] and [VINS]. *)
Definition armv8a_vmn_name (vmn : armv8a_vmnemonic) : string :=
  match vmn with
  | VDUPLANE => "VDUPLANE"
  | VINSLANE => "VINSLANE"
  | _ => "V" ++ string_of_armv8a_vmnemonic vmn
  end%string.

(* The architecture extensions that the assembler must be told of for some
   Advanced SIMD instructions (with the directive [.arch_extension]), named
   as the assembler knows them: the base ARMv8-A instruction set does not
   include the cryptographic instructions, nor the rounding doubling
   multiply-accumulate instructions of ARMv8.1-A (FEAT_RDM). *)
Variant armv8a_extension :=
| EXT_aes                        (* AESE, AESD, AESMC, AESIMC, and PMULL
                                    and PMULL2 on 64-bit lanes *)
| EXT_sha3                       (* EOR3, RAX1, XAR, BCAX *)
| EXT_rdm.                       (* SQRDMLAH, SQRDMLSH *)

Definition string_of_armv8a_extension (ext : armv8a_extension) : string :=
  match ext with
  | EXT_aes => "aes"
  | EXT_sha3 => "sha3"
  | EXT_rdm => "rdm"
  end%string.

(* The extension that a vector mnemonic requires, if any. *)
Definition armv8a_vmn_extension (vmn : armv8a_vmnemonic)
  : option armv8a_extension :=
  match vmn with
  | VAESE | VAESD | VAESMC | VAESIMC
  | VPMULL | VPMULL2 => Some EXT_aes
  | VEOR3 | VRAX1 | VXAR | VBCAX => Some EXT_sha3
  | VSQRDMLAH | VSQRDMLSH => Some EXT_rdm
  | _ => None
  end.


(* -------------------------------------------------------------------- *)
(* ARMv8-A operators are pairs of mnemonics and options, or Advanced SIMD
   mnemonics with a lane size and a vector size, as the x86 vector
   instructions. *)

#[only(eqbOK)] derive
Variant armv8a_asm_op :=
| ARMv8A_op : armv8a_mnemonic -> armv8a_options -> armv8a_asm_op
| ARMv8A_vop : armv8a_vmnemonic -> velem -> wsize -> armv8a_asm_op.

#[ export ]
Instance eqTC_armv8a_asm_op : eqTypeC armv8a_asm_op :=
  { ceqP := armv8a_asm_op_eqb_OK }.

Canonical armv8a_asm_op_eqType := @ceqT_eqType _ eqTC_armv8a_asm_op.


(* -------------------------------------------------------------------- *)
(* Common semantic types. *)

Notation sflag := (lbool) (only parsing).
Notation snzcv := ([:: sflag; sflag; sflag; sflag ]) (only parsing).

Notation ty_nzcv := (sem_ltuple snzcv) (only parsing).
Notation ty_r := (sem_ltuple [:: lreg ]) (only parsing).
Notation ty_w ws := (sem_ltuple [:: lword ws ]) (only parsing).

Notation ty_nzcv_w ws := (sem_ltuple (snzcv ++ [:: lword ws ])) (only parsing).

(* Counterparts of the above for the total semantics: the flags are [bool]. *)
Notation ty_nzcv_t := (sem_ltuple_t snzcv) (only parsing).
Notation ty_w_t ws := (sem_ltuple_t [:: lword ws ]) (only parsing).
Notation ty_nzcv_w_t ws := (sem_ltuple_t (snzcv ++ [:: lword ws ])) (only parsing).


(* -------------------------------------------------------------------- *)
(* Common argument descriptions. *)

Definition ad_nzcv : seq arg_desc := map F [:: NF; ZF; CF; VF ].


(* -------------------------------------------------------------------- *)
(* Common flag definitions. *)

Definition NF_of_word (ws : wsize) (w : word ws) := msb w.
Definition ZF_of_word (ws : wsize) (w : word ws) := w == 0%w.

(* Compute the value of the flags for an arithmetic operation.
   For instance, for <+> a binary operation, this function should be called
   with
     res = w <+> w'
     res_unsigned = wunsigned w Z.<+> wunsigned w'
     res_signed = wsigned w Z.<+> wsigned w'
*)
Definition nzcv_of_aluop
  {ws : wsize}
  (res : word ws)     (* Actual result. *)
  (res_unsigned : Z)  (* Result with unsigned interpretation. *)
  (res_signed : Z)    (* Result with signed interpretation. *)
  : ty_nzcv :=
  (:: Some (NF_of_word res)                 (* NF *)
    , Some (ZF_of_word res)                 (* ZF *)
    , Some (wunsigned res != res_unsigned)  (* CF *)
    & Some (wsigned res != res_signed)      (* VF *)
  ).

(* Flags of A64 flag-setting logical instructions (ANDS, BICS, TST):
   PSTATE.<N,Z,C,V> = result<msb>:IsZeroBit(result):'00'. *)
Definition nzcv_w_of_aluop {ws : wsize} (w : word ws) (wun wsi : Z) :=
  merge_tuple (nzcv_of_aluop w wun wsi) (w : ty_w ws).

(* Total counterparts: every A64 flag is defined, so they only drop the
   [Some]. *)
Definition nzcv_of_aluop_t
  {ws : wsize} (res : word ws) (res_unsigned res_signed : Z) : ty_nzcv_t :=
  (:: NF_of_word res
    , ZF_of_word res
    , wunsigned res != res_unsigned
    & wsigned res != res_signed
  ).

Definition nzcv_of_logop_t {ws : wsize} (res : word ws) : ty_nzcv_t :=
  (:: NF_of_word res, ZF_of_word res, false & false).

Definition nzcv_w_of_aluop_t {ws : wsize} (w : word ws) (wun wsi : Z) : ty_nzcv_w_t ws :=
  merge_tuple (nzcv_of_aluop_t w wun wsi) (w : ty_w_t ws).

Definition nzcv_w_of_logop_t {ws : wsize} (w : word ws) : ty_nzcv_w_t ws :=
  merge_tuple (nzcv_of_logop_t w) (w : ty_w_t ws).


(* -------------------------------------------------------------------- *)
(* Shift transformations.
   Instruction descriptions are defined without optionally shifted registers.
   The following transformation adds a shift argument to an instruction
   and updates the semantics and the rest of the fields accordingly. *)

Definition mk_semi1_shifted
  {A} {ws : wsize} (sk : shift_kind) (semi : sem_lprod [:: lword ws ] (exec A)) :
  sem_lprod [:: lword ws; lword8 ] (exec A) :=
  fun wn shift_amount =>
    let sham := wunsigned shift_amount in
    semi (shift_op sk wn sham).

Definition mk_semi2_2_shifted
  {A} {o : ltype} {ws : wsize} (sk : shift_kind) (semi : sem_lprod [:: o; lword ws ] (exec A)) :
  sem_lprod [:: o; lword ws; lword8 ] (exec A) :=
  fun x wm shift_amount =>
    let sham := wunsigned shift_amount in
    semi x (shift_op sk wm sham).

(* Same, for a total semantics (no [exec] on the result). *)
Definition mk_semi1_shifted_t
  {A} {ws : wsize} (sk : shift_kind) (semi : sem_lprod [:: lword ws ] A) :
  sem_lprod [:: lword ws; lword8 ] A :=
  fun wn shift_amount =>
    let sham := wunsigned shift_amount in
    semi (shift_op sk wn sham).
Arguments mk_semi1_shifted_t {A ws} sk semi /.

Definition mk_semi2_2_shifted_t
  {A} {o : ltype} {ws : wsize} (sk : shift_kind) (semi : sem_lprod [:: o; lword ws ] A) :
  sem_lprod [:: o; lword ws; lword8 ] A :=
  fun x wm shift_amount =>
    let sham := wunsigned shift_amount in
    semi x (shift_op sk wm sham).
Arguments mk_semi2_2_shifted_t {A o ws} sk semi /.

#[ local ]
Lemma mk_shifted_eq_size {A B} {x y} {xs0 : seq A} {ys0 : seq B} {p} :
  (size xs0 == size ys0) && p
  -> (size (xs0 ++ [:: x ]) == size (ys0 ++ [:: y ])) && p.
Proof.
  move=> /andP [] /eqP H0 Hp.
  rewrite 2!size_cat H0.
  by apply/andP.
Qed.

(* Adding the shift amount at the end of the arguments does not change the
   safety and initialisation conditions, which only mention the earlier
   ones. *)
Lemma shifted_wf (idt : instr_desc_t) :
  [&& all (safety_cond_wt (map eval_ltype (id_tin idt ++ [:: lword8 ]))) (id_safe idt),
      all (safety_cond_wt (map eval_ltype (id_tin idt ++ [:: lword8 ]))) (id_init idt),
      ssrnat.eqn (size (id_init idt)) (size (id_tout idt))
    & ~~ is_ErrType (id_err idt)].
Proof.
  have /and4P [h0 h1 h2 h3] := id_wf idt.
  by rewrite map_cat (all_safety_cond_wt_cat _ h0) (all_safety_cond_wt_cat _ h1) h2 h3.
Qed.

(* On A64 a shifted operand exists only in the register form of an
   instruction (C6.2.5 "ADD (shifted register)" and friends). The immediate
   forms admit either no shift at all (logical instructions, whose bitmask
   immediate is checked by [CAimmC_armv8a_bitmask_imm]) or only
   [LSL #0]/[LSL #12], which is part of the immediate encoding itself and
   folded into [CAimmC_armv8a_arith_imm]. The shifted variant of an
   instruction therefore keeps only the register alternatives of the base
   instruction and appends the shift amount to those. *)
Definition args_kinds_no_imm (x : args_kinds) : bool :=
  ~~ has (has (fun k => if k is CAimm _ _ then true else false)) x.

Definition mk_shifted
  (ws : wsize) (sk : shift_kind) (mn : armv8a_mnemonic)
  (idt : instr_desc_t) semi_total'
  : instr_desc_t :=
  {|
    id_msb_flag := idt.(id_msb_flag);
    id_tin := (id_tin idt) ++ [:: lword8 ];
    id_in := (id_in idt) ++ [:: Ea (id_nargs idt) ];
    id_tout := id_tout idt;
    id_out := id_out idt;
    id_semi_total := semi_total';
    id_nargs := (id_nargs idt).+1;
    id_args_kinds :=
      map (fun x => x ++ [:: [:: CAimm (Some (CAimmC_armv8a_shift_amount ws)) U8] ])
        (filter args_kinds_no_imm (id_args_kinds idt));
    id_eq_size := mk_shifted_eq_size (id_eq_size idt);
    id_check_dest := id_check_dest idt;
    id_str_jas := id_str_jas idt;
    id_safe := id_safe idt;
    id_err := id_err idt;
    id_init := id_init idt;
    id_doit := id_doit idt;
    (* The shift amount is printed after the operands of the base
       instruction, with the name of the shift: [lsl #3]. *)
    id_pp_asm := pp_append_shift sk (id_nargs idt) (id_pp_asm idt);
    (* The descriptor itself rejects a shift kind that the instruction
       does not admit (ROR on the arithmetic class). *)
    id_valid := id_valid idt && shift_allowed mn sk;
    id_wf := shifted_wf idt;
  |}.

Arguments mk_shifted : clear implicits.


(* -------------------------------------------------------------------- *)
(* Printing. *)

(* Each argument is printed as a register of the width of the operand size:
   W for widths up to [U32], X for [U64]. The width only matters for
   register operands. *)
Definition pp_armv8a_op
  (mn : armv8a_mnemonic) (opts : armv8a_options) (args : seq asm_arg) : pp_asm_op :=
  {|
    pp_aop_name := string_of_armv8a_mnemonic mn;
    pp_aop_ext := PP_name;
    pp_aop_args := map (PPa_full (opts_size opts)) args;
  |}.

(* Same as [pp_armv8a_op] with an explicit width per argument, for the
   instructions whose operands are not all [opts_size]-wide (narrow loads
   and stores, 32-bit multiplies, extensions). *)
Definition pp_armv8a_op_szs
  (mn : armv8a_mnemonic) (szs : seq wsize) (args : seq asm_arg) : pp_asm_op :=
  {|
    pp_aop_name := string_of_armv8a_mnemonic mn;
    pp_aop_ext := PP_name;
    pp_aop_args := pp_fulls szs args;
  |}.

(* -------------------------------------------------------------------- *)
(* Instruction descriptions.
   Descriptions are parameterized by the options: the operand size [osz]
   selects the W or X form (W-form instructions clear the upper 32 bits of
   their destination registers, [MSB_CLEAR]), and data-processing
   instructions gain a shift operand with [mk_shifted] when [has_shift]
   is set.
   Each instruction's semantics ([*_semi], parametric in the operand size
   [ws] unless the instruction exists at a single size) is defined right
   before the description that uses it. *)

Section ARMV8A_INSTR.

Context
  (opts : armv8a_options).

Notation osz := (opts_size opts).

Let string_of_armv8a_mnemonic mn :=
  string_of_armv8a_mnemonic mn.

Notation osz_valid := ((osz == U32) || (osz == U64)) (only parsing).
Notation msbf := (if osz == U64 then MSB_MERGE else MSB_CLEAR) (only parsing).

(* Jasmin-source and EasyCrypt name of the operation: the mnemonics that
   exist in both the W and X forms are size-suffixed (ADD_32 / ADD_64, as
   on x86), matching the intrinsic parser ([armv8a_prim_string] below);
   fixed-size mnemonics keep their bare name. *)
Let armv8a_mn_str (mn : armv8a_mnemonic) : unit -> string :=
  if mn \in sized_mnemonics
  then pp_sz (string_of_armv8a_mnemonic mn) osz
  else pp_s (string_of_armv8a_mnemonic mn).

(* Argument kinds.
   Immediate operands are checked against the A64 encoding rules
   (armv8a_decl.v): [CAimmC_armv8a_arith_imm] (imm12, optionally shifted
   by 12) for the arithmetic class, [CAimmC_armv8a_bitmask_imm] for the
   logical class, [CAimmC_armv8a_mov_imm] for the MOV alias. Instructions
   without an immediate form (BIC, MVN, ...) only accept registers, which
   the [option] parameter of [ak_rr_or_imm]/[ak_rrr_or_imm] expresses
   with [None]. The immediate forms are only available without a shifted
   operand: [mk_shifted] drops them from the shifted variant. *)

Let ak_rr := ak_reg_reg.
Let ak_rrr := ak_reg_reg_reg.
Let ak_rrrr := ak_reg_reg_reg_reg.

Let ak_rr_or_imm (ick : option armv8a_caimm_cond) :=
  if ick is Some ic
  then ak_reg_reg ++ [:: [:: [:: CAreg ]; [:: CAimm (Some ic) osz ] ] ]
  else ak_reg_reg.

Let ak_rrr_or_imm (ick : option armv8a_caimm_cond) :=
  if ick is Some ic
  then ak_reg_reg_reg ++ [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm (Some ic) osz ] ] ]
  else ak_reg_reg_reg.

Let ak_rr_imm_shift :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm (Some (CAimmC_armv8a_shift_amount osz)) U8 ] ] ].

Let ak_r_imm16_shift :=
  [:: [:: [:: CAreg ]; [:: CAimm_sz U16 ]; [:: CAimm (Some (CAimmC_armv8a_halfword_shift osz)) U8 ] ] ].

Let ak_rrr_imm_shift :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAreg ]; [:: CAimm (Some (CAimmC_armv8a_shift_amount osz)) U8 ] ] ].

Let ak_rrr_cond :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAreg ]; [:: CAcond ] ] ].

Let ak_r_cond :=
  [:: [:: [:: CAreg ]; [:: CAcond ] ] ].

(* Bit-field instructions: the bit position is bounded by the operand size,
   the width is an 8-bit immediate. *)
Let ak_rr_lsb_width :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm (Some (CAimmC_armv8a_shift_amount osz)) U8 ]; [:: CAimm_sz U8 ] ] ].

Let ak_r_lsb_width :=
  [:: [:: [:: CAreg ]; [:: CAimm (Some (CAimmC_armv8a_shift_amount osz)) U8 ]; [:: CAimm_sz U8 ] ] ].

(* -------------------------------------------------------------------- *)
(* Arithmetic instructions. *)

(* A binary data-processing instruction without flag outputs, accepting
   an optionally shifted register or an immediate as its last operand. *)
(* [ick] is the immediate-encoding checker for the instruction's immediate
   form ([None] for instructions with no immediate form). *)
Definition mk_arith_instr mn (ick : option armv8a_caimm_cond)
  (semi : word osz -> word osz -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz ] in
  let x :=
    {|
      id_msb_flag := msbf;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := [:: lword osz ];
      id_out := [:: Ea 0 ];
      id_semi_total := semi;
      id_nargs := 3;
      id_args_kinds := ak_rrr_or_imm ick;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := armv8a_mn_str mn;
      id_safe := [::];
      id_err := ErrSemUndef;
      id_init := [:: IBool true ];
      id_doit := DOIT;
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_wf := refl_equal;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk mn x (mk_semi2_2_shifted_t sk (id_semi_total x))
  else x.

(* Same as [mk_arith_instr], with the NZCV flags as extra outputs. *)
Definition mk_ariths_instr mn (ick : option armv8a_caimm_cond)
  (semi_t : word osz -> word osz -> ty_nzcv_w_t osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz ] in
  let x :=
    {|
      id_msb_flag := msbf;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzcv ++ [:: lword osz ];
      id_out := ad_nzcv ++ [:: Ea 0 ];
      id_semi_total := semi_t;
      id_nargs := 3;
      id_args_kinds := ak_rrr_or_imm ick;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := armv8a_mn_str mn;
      id_safe := [::];
      id_err := ErrSemUndef;
      id_init := [:: IBool true; IBool true; IBool true; IBool true; IBool true ];
      id_doit := DOIT;
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_wf := refl_equal;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk mn x (mk_semi2_2_shifted_t sk (id_semi_total x))
  else x.

Arguments mk_ariths_instr : clear implicits.

Notation arith_imm := (Some CAimmC_armv8a_arith_imm) (only parsing).
Notation bitmask_imm := (Some CAimmC_armv8a_bitmask_imm) (only parsing).
Notation no_imm := (None : option armv8a_caimm_cond) (only parsing).

(* [C6.2.6 ADD (shifted register)] ARM DDI 0487 M.a, p. 1798
   Add optionally-shifted register  This instruction adds a register value and
   an optionally-shifted register value, and writes the result to the
   destination register.
   Syntax: ADD <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     bits(datasize) result;
     (result, -) = AddWithCarry(operand1, operand2, '0');
     X[d, datasize] = result;
*)
Definition armv8a_ADD_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  (wn + wm)%w.

Definition armv8a_ADD_instr : instr_desc_t :=
  mk_arith_instr ADD arith_imm armv8a_ADD_semi.
(* [C6.2.11 ADDS (shifted register)] ARM DDI 0487 M.a, p. 1807
   Add optionally-shifted register, setting flags  This instruction adds a
   register value and an optionally-shifted register value, and writes the
   result to the destination register. It updates the condition flags based on
   the result.  This instruction is used by the alias CMN (shifted register).
   Syntax: ADDS <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     bits(datasize) result;
     bits(4) nzcv;
     (result, nzcv) = AddWithCarry(operand1, operand2, '0');
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = nzcv;
*)

Definition armv8a_ADDS_semi_t {ws : wsize} (wn wm : word ws) : ty_nzcv_w_t ws :=
  nzcv_w_of_aluop_t
    (wn + wm)%w
    (wunsigned wn + wunsigned wm)%Z
    (wsigned wn + wsigned wm)%Z.

Definition armv8a_ADDS_instr : instr_desc_t :=
  mk_ariths_instr ADDS arith_imm armv8a_ADDS_semi_t.
(* [C6.2.457 SUB (shifted register)] ARM DDI 0487 M.a, p. 2785
   Subtract optionally-shifted register  This instruction subtracts an
   optionally-shifted register value from a register value, and writes the
   result to the destination register.  This instruction is used by the alias
   NEG (shifted register).
   Syntax: SUB <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = NOT(ShiftReg(m, shift_type, shift_amount, datasize));
     bits(datasize) result;
     (result, -) = AddWithCarry(operand1, operand2, '1');
     X[d, datasize] = result;
*)
Definition armv8a_SUB_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  (wn - wm)%w.

Definition armv8a_SUB_instr : instr_desc_t :=
  mk_arith_instr SUB arith_imm armv8a_SUB_semi.
(* [C6.2.464 SUBS (shifted register)] ARM DDI 0487 M.a, p. 2797
   Subtract optionally-shifted register, setting flags  This instruction
   subtracts an optionally-shifted register value from a register value, and
   writes the result to the destination register. It updates the condition
   flags based on the result.  This instruction is used by the aliases CMP
   (shifted register) and NEGS.
   Syntax: SUBS <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = NOT(ShiftReg(m, shift_type, shift_amount, datasize));
     bits(datasize) result;
     bits(4) nzcv;
     (result, nzcv) = AddWithCarry(operand1, operand2, '1');
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = nzcv;
*)

Definition armv8a_SUBS_semi_t {ws : wsize} (wn wm : word ws) : ty_nzcv_w_t ws :=
  let wmnot := wnot wm in
  nzcv_w_of_aluop_t
    (wn + wmnot + 1)%w
    (wunsigned wn + wunsigned wmnot + 1)%Z
    (wsigned wn + wsigned wmnot + 1)%Z.

Definition armv8a_SUBS_instr : instr_desc_t :=
  mk_ariths_instr SUBS arith_imm armv8a_SUBS_semi_t.

(* Add/subtract with carry (no shifted or immediate forms in A64). *)
Definition mk_carry_instr mn (semi : word osz -> word osz -> bool -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz; lbool ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; F CF ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_rrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

Definition mk_carrys_instr mn
  (semi_t : word osz -> word osz -> bool -> ty_nzcv_w_t osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz; lbool ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; F CF ];
    id_tout := snzcv ++ [:: lword osz ];
    id_out := ad_nzcv ++ [:: Ea 0 ];
    id_semi_total := semi_t;
    id_nargs := 3;
    id_args_kinds := ak_rrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true; IBool true; IBool true; IBool true; IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

Arguments mk_carrys_instr : clear implicits.

(* [C6.2.2 ADC] ARM DDI 0487 M.a, p. 1789
   Add with carry  This instruction adds two register values and the Carry flag
   value, and writes the result to the destination register.
   Syntax: ADC <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     bits(datasize) result;
     (result, -) = AddWithCarry(operand1, operand2, PSTATE.C);
     X[d, datasize] = result;
*)
Definition armv8a_ADC_semi {ws : wsize} (wn wm : word ws) (cf : bool) : ty_w ws :=
  let c := Z.b2z cf in
  (wn + wm + wrepr ws c)%w.

Definition armv8a_ADC_instr : instr_desc_t := mk_carry_instr ADC armv8a_ADC_semi.
(* [C6.2.3 ADCS] ARM DDI 0487 M.a, p. 1791
   Add with carry, setting flags  This instruction adds two register values and
   the Carry flag value, and writes the result to the destination register. It
   updates the condition flags based on the result.
   Syntax: ADCS <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     bits(datasize) result;
     bits(4) nzcv;
     (result, nzcv) = AddWithCarry(operand1, operand2, PSTATE.C);
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = nzcv;
*)

Definition armv8a_ADCS_semi_t {ws : wsize} (wn wm : word ws) (cf : bool) : ty_nzcv_w_t ws :=
  let c := Z.b2z cf in
  nzcv_w_of_aluop_t
    (wn + wm + wrepr ws c)%w
    (wunsigned wn + wunsigned wm + c)%Z
    (wsigned wn + wsigned wm + c)%Z.

Definition armv8a_ADCS_instr : instr_desc_t :=
  mk_carrys_instr ADCS armv8a_ADCS_semi_t.
(* [C6.2.351 SBC] ARM DDI 0487 M.a, p. 2548
   Subtract with carry  This instruction subtracts a register value and the
   value of NOT (Carry flag) from a register value, and writes the result to
   the destination register.  This instruction is used by the alias NGC.
   Syntax: SBC <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = NOT(X[m, datasize]);
     bits(datasize) result;
     (result, -) = AddWithCarry(operand1, operand2, PSTATE.C);
     X[d, datasize] = result;
*)
Definition armv8a_SBC_semi {ws : wsize} (wn wm : word ws) (cf : bool) : ty_w ws :=
  armv8a_ADC_semi wn (wnot wm) cf.

Definition armv8a_SBC_instr : instr_desc_t := mk_carry_instr SBC armv8a_SBC_semi.
(* [C6.2.352 SBCS] ARM DDI 0487 M.a, p. 2550
   Subtract with carry, setting flags  This instruction subtracts a register
   value and the value of NOT (Carry flag) from a register value, and writes
   the result to the destination register. It updates the condition flags based
   on the result.  This instruction is used by the alias NGCS.
   Syntax: SBCS <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = NOT(X[m, datasize]);
     bits(datasize) result;
     bits(4) nzcv;
     (result, nzcv) = AddWithCarry(operand1, operand2, PSTATE.C);
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = nzcv;
*)
Definition armv8a_SBCS_semi_t {ws : wsize} (wn wm : word ws) (cf : bool) : ty_nzcv_w_t ws :=
  armv8a_ADCS_semi_t wn (wnot wm) cf.

Definition armv8a_SBCS_instr : instr_desc_t :=
  mk_carrys_instr SBCS armv8a_SBCS_semi_t.
(* [C6.2.294 NEG (shifted register)] ARM DDI 0487 M.a, p. 2440
   Negate (shifted register)  This instruction negates an optionally-shifted
   register value, and writes the result to the destination register.  This is
   an alias of SUB (shifted register). This means:  • The encodings in this
   description are named to match the encodings of SUB (shifted register). •
   The description of SUB (shifted register) gives the operational pseudocode,
   any CONSTRAINED UNPREDICTABLE behavior, and any operational information for
   this instruction.
   Note: NEG is an alias of SUB (shifted register) with Rn = ZR; the SUB entry carries the operational pseudocode.
   Syntax: NEG <Xd>, <Xm>{, <shift> #<amount>}  ==  SUB <Xd>, XZR, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     The description of SUB (shifted register) gives the operational pseudocode for this instruction.
   Base instruction [C6.2.457 SUB (shifted register)] p. 2785, Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = NOT(ShiftReg(m, shift_type, shift_amount, datasize));
     bits(datasize) result;
     (result, -) = AddWithCarry(operand1, operand2, '1');
     X[d, datasize] = result;
*)
Definition armv8a_NEG_semi {ws : wsize} (wm : word ws) : ty_w ws :=
  (wnot wm + 1)%w.

Definition armv8a_NEG_instr : instr_desc_t :=
  let mn := NEG in
  let tin := [:: lword osz ] in
  let semi := armv8a_NEG_semi (ws := osz) in
  let x :=
    {|
      id_msb_flag := msbf;
      id_tin := tin;
      id_in := [:: Ea 1 ];
      id_tout := [:: lword osz ];
      id_out := [:: Ea 0 ];
      id_semi_total := semi;
      id_nargs := 2;
      id_args_kinds := ak_rr;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := armv8a_mn_str mn;
      id_safe := [::];
      id_err := ErrSemUndef;
      id_init := [:: IBool true ];
      id_doit := DOIT;
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_wf := refl_equal;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk mn x (mk_semi1_shifted_t sk (id_semi_total x))
  else x.

(* A three-register instruction without flags (MUL, SDIV, UDIV, ...).
   [valid] restricts the operand sizes the instruction exists at. *)
Definition mk_rrr_instr mn (doit_v : doit_t) (valid : bool)
  (semi : word osz -> word osz -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_rrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := doit_v;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := valid;
    id_wf := refl_equal;
  |}.

(* [C6.2.292 MUL] ARM DDI 0487 M.a, p. 2436
   Multiply  This instruction multiplies two register values and writes the
   result to the destination register.  This is an alias of MADD. This means:
   • The encodings in this description are named to match the encodings of
   MADD. • The description of MADD gives the operational pseudocode, any
   CONSTRAINED UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Note: MUL is an alias of MADD with Ra = ZR (see the MADD entry for the operational pseudocode).
   Syntax: MUL <Xd>, <Xn>, <Xm>  ==  MADD <Xd>, <Xn>, <Xm>, XZR
   Operation (ASL):
     The description of MADD gives the operational pseudocode for this instruction.
*)
Definition armv8a_MUL_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  (wn * wm)%w.

Definition armv8a_MUL_instr : instr_desc_t := mk_rrr_instr MUL DOIT osz_valid armv8a_MUL_semi.
(* [C6.2.356 SDIV] ARM DDI 0487 M.a, p. 2558
   Signed divide  This instruction divides the first signed source register
   value by the second signed source register value, and writes the result to
   the destination register. Dividing by zero writes the value zero to the
   destination register. The condition flags are not affected.
   Syntax: SDIV <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     constant integer dividend = SInt(operand1);
     constant integer divisor = SInt(operand2);
     integer result;
     if divisor == 0 then
         result = 0;
     elsif (dividend < 0) == (divisor < 0) then
         result = Abs(dividend) DIV Abs(divisor); // same signs - positive result
     else
         result = -(Abs(dividend) DIV Abs(divisor)); // different signs - negative result
     X[d, datasize] = result<datasize-1:0>;
*)
Definition armv8a_SDIV_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  wdivi wn wm.

Definition armv8a_SDIV_instr : instr_desc_t :=
  mk_rrr_instr SDIV NOT_DOIT (* Not DIT *) osz_valid armv8a_SDIV_semi.
(* [C6.2.489 UDIV] ARM DDI 0487 M.a, p. 2846
   Unsigned divide  This instruction divides the first unsigned source register
   value by the second unsigned source register value, and writes the result to
   the destination register. Dividing by zero writes the value zero to the
   destination register. The condition flags are not affected.
   Syntax: UDIV <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     constant integer dividend = UInt(operand1);
     constant integer divisor = UInt(operand2);
     integer result;
     if divisor == 0 then
         result = 0;
     else
         result = dividend DIV divisor;
     X[d, datasize] = result<datasize-1:0>;
*)
Definition armv8a_UDIV_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  wdiv wn wm.

Definition armv8a_UDIV_instr : instr_desc_t :=
  mk_rrr_instr UDIV NOT_DOIT (* Not DIT *) osz_valid armv8a_UDIV_semi.

(* [UMULH] ARM DDI 0487 M.a
   Unsigned multiply high  This instruction multiplies two 64-bit register
   values, and writes bits[127:64] of the 128-bit result to the 64-bit
   destination register.
   Syntax: UMULH <Xd>, <Xn>, <Xm>
   Operation (ASL, summarized):
     constant bits(64) operand1 = X[n, 64];
     constant bits(64) operand2 = X[m, 64];
     constant integer result = UInt(operand1) * UInt(operand2);
     X[d, 64] = result<127:64>;
*)
Definition armv8a_UMULH_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  wmulhu wn wm.

Definition armv8a_UMULH_instr : instr_desc_t :=
  mk_rrr_instr UMULH DOIT (osz == U64) armv8a_UMULH_semi.

(* [SMULH] ARM DDI 0487 M.a
   Signed multiply high  This instruction multiplies two 64-bit register
   values, and writes bits[127:64] of the 128-bit result to the 64-bit
   destination register.
   Syntax: SMULH <Xd>, <Xn>, <Xm>
   Operation (ASL, summarized):
     constant bits(64) operand1 = X[n, 64];
     constant bits(64) operand2 = X[m, 64];
     constant integer result = SInt(operand1) * SInt(operand2);
     X[d, 64] = result<127:64>;
*)
Definition armv8a_SMULH_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  wmulhs wn wm.

Definition armv8a_SMULH_instr : instr_desc_t :=
  mk_rrr_instr SMULH DOIT (osz == U64) armv8a_SMULH_semi.

(* Multiply-add and multiply-subtract. *)
Definition mk_madd_instr mn (semi : word osz -> word osz -> word osz -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz; lword osz ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 4;
    id_args_kinds := ak_rrrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

(* [C6.2.274 MADD] ARM DDI 0487 M.a, p. 2401
   Multiply-add  This instruction multiplies two register values, adds a third
   register value, and writes the result to the destination register.  This
   instruction is used by the alias MUL.
   Syntax: MADD <Xd>, <Xn>, <Xm>, <Xa>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     constant bits(datasize) operand3 = X[a, datasize];
     constant integer result = UInt(operand3) + (UInt(operand1) * UInt(operand2));
     X[d, datasize] = result<datasize-1:0>;
*)
Definition armv8a_MADD_semi {ws : wsize} (wn wm wa : word ws) : ty_w ws :=
  (wa + wn * wm)%w.

Definition armv8a_MADD_instr : instr_desc_t := mk_madd_instr MADD armv8a_MADD_semi.
(* [C6.2.290 MSUB] ARM DDI 0487 M.a, p. 2432
   Multiply-subtract  This instruction multiplies two register values,
   subtracts the product from a third register value, and writes the result to
   the destination register.  This instruction is used by the alias MNEG.
   Syntax: MSUB <Xd>, <Xn>, <Xm>, <Xa>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     constant bits(datasize) operand3 = X[a, datasize];
     constant integer result = UInt(operand3) - (UInt(operand1) * UInt(operand2));
     X[d, datasize] = result<datasize-1:0>;
*)
Definition armv8a_MSUB_semi {ws : wsize} (wn wm wa : word ws) : ty_w ws :=
  (wa - wn * wm)%w.

Definition armv8a_MSUB_instr : instr_desc_t := mk_madd_instr MSUB armv8a_MSUB_semi.

(* Long multiplies: the product of two 32-bit (W) registers is a 64-bit (X)
   register. These instructions only exist with an X destination. *)
Definition mk_mull_instr mn (semi : word U32 -> word U32 -> ty_r)
  : instr_desc_t :=
  let tin := [:: lword U32; lword U32 ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_rrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    (* [UMULL <Xd>, <Wn>, <Wm>] *)
    id_pp_asm := pp_armv8a_op_szs mn [:: U64; U32; U32 ];
    id_valid := osz == U64;
    id_wf := refl_equal;
  |}.

(* [C6.2.498 UMULL] ARM DDI 0487 M.a, p. 2862
   Unsigned multiply long  This instruction multiplies two 32-bit register
   values, and writes the result to the 64-bit destination register.  This is
   an alias of UMADDL. This means:  • The encodings in this description are
   named to match the encodings of UMADDL. • The description of UMADDL gives
   the operational pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any
   operational information for this instruction.
   Syntax: UMULL <Xd>, <Wn>, <Wm>  ==  UMADDL <Xd>, <Wn>, <Wm>, XZR
   Operation (ASL):
     The description of UMADDL gives the operational pseudocode for this instruction.
   Base instruction [C6.2.490 UMADDL] p. 2848, Operation (ASL):
     constant bits(32) operand1 = X[n, 32];
     constant bits(32) operand2 = X[m, 32];
     constant bits(64) operand3 = X[a, 64];
     constant integer result = UInt(operand3) + (UInt(operand1) * UInt(operand2));
     X[d, 64] = result<63:0>;
*)
Definition armv8a_UMULL_semi (wn wm : word U32) : ty_r :=
  (zero_extend U64 wn * zero_extend U64 wm)%w.

Definition armv8a_UMULL_instr : instr_desc_t := mk_mull_instr UMULL armv8a_UMULL_semi.
(* [C6.2.379 SMULL] ARM DDI 0487 M.a, p. 2616
   Signed multiply long  This instruction multiplies two 32-bit register
   values, and writes the result to the 64-bit destination register.  This is
   an alias of SMADDL. This means:  • The encodings in this description are
   named to match the encodings of SMADDL. • The description of SMADDL gives
   the operational pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any
   operational information for this instruction.
   Syntax: SMULL <Xd>, <Wn>, <Wm>  ==  SMADDL <Xd>, <Wn>, <Wm>, XZR
   Operation (ASL):
     The description of SMADDL gives the operational pseudocode for this instruction.
   Base instruction [C6.2.368 SMADDL] p. 2599, Operation (ASL):
     constant bits(32) operand1 = X[n, 32];
     constant bits(32) operand2 = X[m, 32];
     constant bits(64) operand3 = X[a, 64];
     constant integer result = SInt(operand3) + (SInt(operand1) * SInt(operand2));
     X[d, 64] = result<63:0>;
*)
Definition armv8a_SMULL_semi (wn wm : word U32) : ty_r :=
  (sign_extend U64 wn * sign_extend U64 wm)%w.

Definition armv8a_SMULL_instr : instr_desc_t := mk_mull_instr SMULL armv8a_SMULL_semi.

(* Long multiply-adds: the product of two 32-bit (W) registers is added to a
   64-bit (X) register. *)
Definition mk_maddl_instr mn (semi : word U32 -> word U32 -> word U64 -> ty_r)
  : instr_desc_t :=
  let tin := [:: lword U32; lword U32; lreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 4;
    id_args_kinds := ak_rrrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    (* [UMADDL <Xd>, <Wn>, <Wm>, <Xa>] *)
    id_pp_asm := pp_armv8a_op_szs mn [:: U64; U32; U32; U64 ];
    id_valid := osz == U64;
    id_wf := refl_equal;
  |}.

(* [C6.2.490 UMADDL] ARM DDI 0487 M.a, p. 2848
   Unsigned multiply-add long  This instruction multiplies two 32-bit register
   values, adds a 64-bit register value, and writes the result to the 64-bit
   destination register.  This instruction is used by the alias UMULL.
   Syntax: UMADDL <Xd>, <Wn>, <Wm>, <Xa>
   Operation (ASL):
     constant bits(32) operand1 = X[n, 32];
     constant bits(32) operand2 = X[m, 32];
     constant bits(64) operand3 = X[a, 64];
     constant integer result = UInt(operand3) + (UInt(operand1) * UInt(operand2));
     X[d, 64] = result<63:0>;
*)
Definition armv8a_UMADDL_semi (wn wm : word U32) (wa : word U64) : ty_r :=
  (wa + zero_extend U64 wn * zero_extend U64 wm)%w.

Definition armv8a_UMADDL_instr : instr_desc_t := mk_maddl_instr UMADDL armv8a_UMADDL_semi.
(* [C6.2.368 SMADDL] ARM DDI 0487 M.a, p. 2599
   Signed multiply-add long  This instruction multiplies two 32-bit register
   values, adds a 64-bit register value, and writes the result to the 64-bit
   destination register.  This instruction is used by the alias SMULL.
   Syntax: SMADDL <Xd>, <Wn>, <Wm>, <Xa>
   Operation (ASL):
     constant bits(32) operand1 = X[n, 32];
     constant bits(32) operand2 = X[m, 32];
     constant bits(64) operand3 = X[a, 64];
     constant integer result = SInt(operand3) + (SInt(operand1) * SInt(operand2));
     X[d, 64] = result<63:0>;
*)
(* Adding modulo 2^64 the unsigned or the signed interpretation of the
   64-bit operand gives the same low 64 bits. *)
Definition armv8a_SMADDL_semi (wn wm : word U32) (wa : word U64) : ty_r :=
  (wa + sign_extend U64 wn * sign_extend U64 wm)%w.

Definition armv8a_SMADDL_instr : instr_desc_t := mk_maddl_instr SMADDL armv8a_SMADDL_semi.

(* -------------------------------------------------------------------- *)
(* Bitwise instructions. *)

Definition armv8a_bitwise_semi
  {ws : wsize}
  (op0 op1 : word ws -> word ws)
  (op : word ws -> word ws -> word ws)
  (wn wm : word ws) :
  ty_w ws :=
  op (op0 wn) (op1 wm).

(* [C6.2.15 AND (shifted register)] ARM DDI 0487 M.a, p. 1813
   Bitwise AND (shifted register)  This instruction performs a bitwise AND of a
   register value and an optionally-shifted register value, and writes the
   result to the destination register.
   Syntax: AND <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     X[d, datasize] = operand1 AND operand2;
*)
Definition armv8a_AND_instr : instr_desc_t :=
  mk_arith_instr AND bitmask_imm (armv8a_bitwise_semi id id wand).

(* [C6.2.17 ANDS (shifted register)] ARM DDI 0487 M.a, p. 1817
   Bitwise AND (shifted register), setting flags  This instruction performs a
   bitwise AND of a register value and an optionally-shifted register value,
   and writes the result to the destination register. It updates the condition
   flags based on the result.  This instruction is used by the alias TST
   (shifted register).
   Syntax: ANDS <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     constant bits(datasize) result = operand1 AND operand2;
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = result<datasize-1>:IsZeroBit(result):'00';
*)
Definition armv8a_ANDS_semi_t {ws : wsize} (wn wm : word ws) : ty_nzcv_w_t ws :=
  nzcv_w_of_logop_t (wand wn wm).

Definition armv8a_ANDS_instr : instr_desc_t :=
  mk_ariths_instr ANDS bitmask_imm armv8a_ANDS_semi_t.

(* [C6.2.41 BIC (shifted register)] ARM DDI 0487 M.a, p. 1856
   Bitwise bit clear (shifted register)  This instruction performs a bitwise
   AND of a register value and the complement of an optionally-shifted register
   value, and writes the result to the destination register.
   Syntax: BIC <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     X[d, datasize] = operand1 AND NOT(operand2);
*)
(* BIC and BICS have no immediate form in A64 (an inverted bitmask
   immediate is an AND or ANDS immediate). *)
Definition armv8a_BIC_instr : instr_desc_t :=
  mk_arith_instr BIC no_imm (armv8a_bitwise_semi id wnot wand).

(* [C6.2.42 BICS (shifted register)] ARM DDI 0487 M.a, p. 1858
   Bitwise bit clear (shifted register), setting flags  This instruction
   performs a bitwise AND of a register value and the complement of an
   optionally-shifted register value, and writes the result to the destination
   register. It updates the condition flags based on the result.
   Syntax: BICS <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     constant bits(datasize) result = operand1 AND NOT(operand2);
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = result<datasize-1>:IsZeroBit(result):'00';
*)
Definition armv8a_BICS_semi_t {ws : wsize} (wn wm : word ws) : ty_nzcv_w_t ws :=
  nzcv_w_of_logop_t (wand wn (wnot wm)).

Definition armv8a_BICS_instr : instr_desc_t :=
  mk_ariths_instr BICS no_imm armv8a_BICS_semi_t.

(* [C6.2.301 ORR (shifted register)] ARM DDI 0487 M.a, p. 2453
   Bitwise OR (shifted register)  This instruction performs a bitwise
   (inclusive) OR of a register value and an optionally-shifted register value,
   and writes the result to the destination register.  This instruction is used
   by the alias MOV (register).
   Syntax: ORR <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     X[d, datasize] = operand1 OR operand2;
*)
Definition armv8a_ORR_instr : instr_desc_t :=
  mk_arith_instr ORR bitmask_imm (armv8a_bitwise_semi id id wor).

(* [C6.2.156 EOR (shifted register)] ARM DDI 0487 M.a, p. 2169
   Bitwise exclusive-OR (shifted register)  This instruction performs a bitwise
   exclusive-OR of a register value and an optionally-shifted register value,
   and writes the result to the destination register.
   Syntax: EOR <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     X[d, datasize] = operand1 EOR operand2;
*)
Definition armv8a_EOR_instr : instr_desc_t :=
  mk_arith_instr EOR bitmask_imm (armv8a_bitwise_semi id id wxor).

(* [C6.2.293 MVN] ARM DDI 0487 M.a, p. 2438
   Bitwise NOT  This instruction writes the bitwise inverse of a register value
   to the destination register.  This is an alias of ORN (shifted register).
   This means:  • The encodings in this description are named to match the
   encodings of ORN (shifted register). • The description of ORN (shifted
   register) gives the operational pseudocode, any CONSTRAINED UNPREDICTABLE
   behavior, and any operational information for this instruction.
   Syntax: MVN <Xd>, <Xm>{, <shift> #<amount>}  ==  ORN <Xd>, XZR, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     The description of ORN (shifted register) gives the operational pseudocode for this instruction.
*)
Definition armv8a_MVN_semi {ws : wsize} (wm : word ws) : ty_w ws :=
  wnot wm.

(* MVN is an alias of ORN (shifted register); it has no immediate form
   (an inverted immediate is a MOV with the complemented value). *)
Definition armv8a_MVN_instr : instr_desc_t :=
  let mn := MVN in
  let tin := [:: lword osz ] in
  let semi := armv8a_MVN_semi (ws := osz) in
  let x :=
    {|
      id_msb_flag := msbf;
      id_tin := tin;
      id_in := [:: Ea 1 ];
      id_tout := [:: lword osz ];
      id_out := [:: Ea 0 ];
      id_semi_total := semi;
      id_nargs := 2;
      id_args_kinds := ak_rr;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := armv8a_mn_str mn;
      id_safe := [::];
      id_err := ErrSemUndef;
      id_init := [:: IBool true ];
      id_doit := DOIT;
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_wf := refl_equal;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk mn x (mk_semi1_shifted_t sk (id_semi_total x))
  else x.

(* -------------------------------------------------------------------- *)
(* Shift instructions.
   The shift amount is the value of the second operand modulo the operand
   size; the immediate forms are restricted by the argument checker. Only
   the alias mnemonics (ASR, ...) are provided: they accept registers and
   immediates, subsuming the base variable forms (ASRV, ...), which accept
   only registers and are otherwise identical. *)

(* Shift semantics: the shift amount is the value of the last operand
   modulo the operand size in bits. *)
Definition armv8a_shift_semi
  {ws : wsize} (op : forall sz, word sz -> Z -> word sz)
  (wn : word ws) (wsham : word U8) : ty_w ws :=
  let sham := (wunsigned wsham mod wsize_bits ws)%Z in
  op ws wn sham.

Definition mk_shift_instr mn (op : forall sz, word sz -> Z -> word sz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword U8 ] in
  let semi := armv8a_shift_semi (ws := osz) op in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_rrr ++ ak_rr_imm_shift;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

(* [C6.2.19 ASR (register)] ARM DDI 0487 M.a, p. 1820
   Arithmetic shift right (register)  This instruction shifts a register value
   right by a variable number of bits, shifting in copies of its sign bit, and
   writes the result to the destination register. The value of the second
   source register modulo the register size in bits gives the number of bits by
   which the first source register is right-shifted.
   Syntax: ASR <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand2 = X[m, datasize];
     X[d, datasize] = ShiftReg(n, shift_type, UInt(operand2) MOD datasize, datasize);
*)
Definition armv8a_ASR_instr : instr_desc_t := mk_shift_instr ASR (@wsar).
(* [C6.2.268 LSL (register)] ARM DDI 0487 M.a, p. 2389
   Logical shift left (register)  This instruction shifts a register value left
   by a variable number of bits, shifting in zeros, and writes the result to
   the destination register. The value of the second source register modulo the
   register size in bits gives the number of bits by which the first source
   register is left-shifted.
   Syntax: LSL <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand2 = X[m, datasize];
     X[d, datasize] = ShiftReg(n, shift_type, UInt(operand2) MOD datasize, datasize);
*)
Definition armv8a_LSL_instr : instr_desc_t := mk_shift_instr LSL (@wshl).
(* [C6.2.271 LSR (register)] ARM DDI 0487 M.a, p. 2395
   Logical shift right (register)  This instruction shifts a register value
   right by a variable number of bits, shifting in zeros, and writes the result
   to the destination register. The value of the second source register modulo
   the register size in bits gives the number of bits by which the first source
   register is right-shifted.
   Syntax: LSR <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand2 = X[m, datasize];
     X[d, datasize] = ShiftReg(n, shift_type, UInt(operand2) MOD datasize, datasize);
*)
Definition armv8a_LSR_instr : instr_desc_t := mk_shift_instr LSR (@wshr).
(* [C6.2.347 ROR (register)] ARM DDI 0487 M.a, p. 2541
   Rotate right (register)  This instruction provides the value of the contents
   of a register rotated by a variable number of bits. The bits that are
   rotated off the right end are inserted into the vacated bit positions on the
   left. The value of the second source register modulo the register size in
   bits gives the number of bits by which the first source register is right-
   shifted.
   Syntax: ROR <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand2 = X[m, datasize];
     X[d, datasize] = ShiftReg(n, shift_type, UInt(operand2) MOD datasize, datasize);
*)
Definition armv8a_ROR_instr : instr_desc_t := mk_shift_instr ROR (@wror).

(* -------------------------------------------------------------------- *)
(* Bit field instructions. *)

(* [C6.2.160 EXTR] ARM DDI 0487 M.a, p. 2174
   Extract register  This instruction extracts a register from a pair of
   registers.  This instruction is used by the alias ROR (immediate).
   Syntax: EXTR <Xd>, <Xn>, <Xm>, #<lsb>
   Operation (ASL):
     bits(datasize) result;
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     constant bits(2*datasize) concat = operand1:operand2;
     result = concat<(lsb+datasize)-1:lsb>;
     X[d, datasize] = result;
*)
(* The argument checker bounds [lsb] by the operand size; the low [lsb]
   bits of [operand1] form the top of the result. *)
Definition armv8a_EXTR_semi {ws : wsize} (wn wm : word ws) (wlsb : word U8) : ty_w ws :=
  let bits := wsize_bits ws in
  let l := (wunsigned wlsb mod bits)%Z in
  if (l =? 0)%Z
  then wm
  else wor (wshr wm l) (wshl wn (bits - l)).

Definition armv8a_EXTR_instr : instr_desc_t :=
  let mn := EXTR in
  let tin := [:: lword osz; lword osz; lword U8 ] in
  let semi := armv8a_EXTR_semi (ws := osz) in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 4;
    id_args_kinds := ak_rrr_imm_shift;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

(* The bitfield aliases take the bit position [lsb] and the width of the
   field as 8-bit immediates. The field must lie within the register: the
   argument checker bounds [lsb] by the operand size, and the safety
   conditions [id_safe] state [1 <= width] and [lsb + width <= datasize];
   the semantics is undefined otherwise. *)

(* [C6.2.37 BFC] ARM DDI 0487 M.a, p. 1848
   Bitfield clear  This instruction sets a bitfield of <width> bits at bit
   position <lsb> of the destination register to zero, leaving the other
   destination bits unchanged.  This is an alias of BFM. This means:  • The
   encodings in this description are named to match the encodings of BFM. • The
   description of BFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: BFC <Xd>, #<lsb>, #<width>  ==  BFM <Xd>, XZR, #(-<lsb> MOD 64), #(<width>-1)
   Operation (ASL):
     The description of BFM gives the operational pseudocode for this instruction.
   Base instruction [C6.2.39 BFM] p. 1852, Operation (ASL):
     constant bits(datasize) dst = X[d, datasize];
     constant bits(datasize) src = X[n, datasize];
     // Perform bitfield move on low bits
     constant bits(datasize) bot = (dst AND NOT(wmask)) OR (ROR(src, r) AND wmask);
     // Combine extension bits and result bits
     X[d, datasize] = (dst AND NOT(tmask)) OR (bot AND tmask);
*)
Definition armv8a_BFC_semi (x : word osz) (lsb width : word U8) : ty_w osz :=
  let lsbit := wunsigned lsb in
  let nbits := wunsigned width in
  let msbit := (lsbit + nbits - 1)%Z in
  let mk i :=
    if [&& Z.to_nat lsbit <=? i & i <=? Z.to_nat msbit ]
    then false
    else wbit_n x i
  in
  winit osz mk.

Definition armv8a_BFC_semi_sc :=
  [:: sc_uge U8 1%Z 2; sc_uadd_le U8 2 1 (wsize_bits osz) ].

Definition armv8a_BFC_instr : instr_desc_t :=
  let mn := BFC in
  {|
    id_msb_flag := msbf;
    id_tin := [:: lword osz; lword8; lword8 ];
    id_in := [:: Ea 0; Ea 1; Ea 2 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := armv8a_BFC_semi;
    id_nargs := 3;
    id_args_kinds := ak_r_lsb_width;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := armv8a_BFC_semi_sc;
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

(* [C6.2.38 BFI] ARM DDI 0487 M.a, p. 1850
   Bitfield insert  This instruction copies a bitfield of <width> bits from the
   least significant bits of the source register to bit position <lsb> of the
   destination register, leaving the other destination bits unchanged.  This is
   an alias of BFM. This means:  • The encodings in this description are named
   to match the encodings of BFM. • The description of BFM gives the
   operational pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any
   operational information for this instruction.
   Syntax: BFI <Xd>, <Xn>, #<lsb>, #<width>  ==  BFM <Xd>, <Xn>, #(-<lsb> MOD 64), #(<width>-1)
   Operation (ASL):
     The description of BFM gives the operational pseudocode for this instruction.
   Base instruction [C6.2.39 BFM] p. 1852, Operation (ASL):
     constant bits(datasize) dst = X[d, datasize];
     constant bits(datasize) src = X[n, datasize];
     // Perform bitfield move on low bits
     constant bits(datasize) bot = (dst AND NOT(wmask)) OR (ROR(src, r) AND wmask);
     // Combine extension bits and result bits
     X[d, datasize] = (dst AND NOT(tmask)) OR (bot AND tmask);
*)
Definition armv8a_BFI_semi (x y : word osz) (lsb width : word U8) : ty_w osz :=
  let lsbit := wunsigned lsb in
  let nbits := wunsigned width in
  let msbit := (lsbit + nbits - 1)%Z in
  let mk i :=
    if [&& Z.to_nat lsbit <=? i & i <=? Z.to_nat msbit ]
    then wbit_n y (i - Z.to_nat lsbit)
    else wbit_n x i
  in
  winit osz mk.

Definition armv8a_BFI_semi_sc :=
  [:: sc_uge U8 1%Z 3; sc_uadd_le U8 3 2 (wsize_bits osz) ].

Definition armv8a_BFI_instr : instr_desc_t :=
  let mn := BFI in
  {|
    id_msb_flag := msbf;
    id_tin := [:: lword osz; lword osz; lword8; lword8 ];
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := armv8a_BFI_semi;
    id_nargs := 4;
    id_args_kinds := ak_rr_lsb_width;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := armv8a_BFI_semi_sc;
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

(* [C6.2.40 BFXIL] ARM DDI 0487 M.a, p. 1854
   Bitfield extract and insert at low end  This instruction copies a bitfield
   of <width> bits starting from bit position <lsb> in the source register to
   the least significant bits of the destination register, leaving the other
   destination bits unchanged.  This is an alias of BFM. This means:  • The
   encodings in this description are named to match the encodings of BFM. • The
   description of BFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: BFXIL <Xd>, <Xn>, #<lsb>, #<width>  ==  BFM <Xd>, <Xn>, #<lsb>, #(<lsb>+<width>-1)
   Operation (ASL):
     The description of BFM gives the operational pseudocode for this instruction.
   Base instruction [C6.2.39 BFM] p. 1852, Operation (ASL):
     constant bits(datasize) dst = X[d, datasize];
     constant bits(datasize) src = X[n, datasize];
     // Perform bitfield move on low bits
     constant bits(datasize) bot = (dst AND NOT(wmask)) OR (ROR(src, r) AND wmask);
     // Combine extension bits and result bits
     X[d, datasize] = (dst AND NOT(tmask)) OR (bot AND tmask);
*)
Definition armv8a_BFXIL_semi (x y : word osz) (lsb width : word U8) : ty_w osz :=
  let lsbit := wunsigned lsb in
  let nbits := wunsigned width in
  let mk i :=
    if (i <? Z.to_nat nbits)%nat
    then wbit_n y (i + Z.to_nat lsbit)
    else wbit_n x i
  in
  winit osz mk.

(* The same bounds as BFI. *)
Definition armv8a_BFXIL_semi_sc := armv8a_BFI_semi_sc.

Definition armv8a_BFXIL_instr : instr_desc_t :=
  let mn := BFXIL in
  {|
    id_msb_flag := msbf;
    id_tin := [:: lword osz; lword osz; lword8; lword8 ];
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := armv8a_BFXIL_semi;
    id_nargs := 4;
    id_args_kinds := ak_rr_lsb_width;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := armv8a_BFXIL_semi_sc;
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

(* Bitfield extraction (SBFX, UBFX): the field is moved to the top of the
   register by a left shift, then to the bottom by a right shift, which is
   arithmetic for SBFX (sign extension) and logical for UBFX (zero
   extension). The argument checker bounds [lsb] by the operand size. *)
Definition armv8a_bitfield_extract_semi
  (shr : word osz -> Z -> word osz) (wn : word osz) (wlsb wwidth : word U8)
  : ty_w osz :=
  let bits := wsize_bits osz in
  let lsb := wunsigned wlsb in
  let width := wunsigned wwidth in
  shr (wshl wn (bits - width - lsb)%Z) (bits - width)%Z.

Definition armv8a_bitfield_extract_semi_sc :=
  [:: sc_uge U8 1%Z 2; sc_uadd_le U8 2 1 (wsize_bits osz) ].

Definition mk_bfx_instr mn (shr : word osz -> Z -> word osz) : instr_desc_t :=
  {|
    id_msb_flag := msbf;
    id_tin := [:: lword osz; lword8; lword8 ];
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := armv8a_bitfield_extract_semi shr;
    id_nargs := 4;
    id_args_kinds := ak_rr_lsb_width;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := armv8a_bitfield_extract_semi_sc;
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

(* [C6.2.355 SBFX] ARM DDI 0487 M.a, p. 2556
   Signed bitfield extract  This instruction copies a bitfield of <width> bits
   starting from bit position <lsb> in the source register to the least
   significant bits of the destination register, and sets destination bits
   above the bitfield to a copy of the most significant bit of the bitfield.
   This is an alias of SBFM. This means:  • The encodings in this description
   are named to match the encodings of SBFM. • The description of SBFM gives
   the operational pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any
   operational information for this instruction.
   Syntax: SBFX <Xd>, <Xn>, #<lsb>, #<width>  ==  SBFM <Xd>, <Xn>, #<lsb>, #(<lsb>+<width>-1)
   Operation (ASL):
     The description of SBFM gives the operational pseudocode for this instruction.
   Base instruction [C6.2.354 SBFM] p. 2554, Operation (ASL):
     constant bits(datasize) src = X[n, datasize];
     // Perform bitfield move on low bits
     constant bits(datasize) bot = ROR(src, r) AND wmask;
     constant bits(datasize) top = Replicate(src<s>, datasize);
     // Combine extension bits and result bits
     X[d, datasize] = (top AND NOT(tmask)) OR (bot AND tmask);
*)
Definition armv8a_SBFX_instr : instr_desc_t := mk_bfx_instr SBFX (wsar (sz := osz)).
(* [C6.2.487 UBFX] ARM DDI 0487 M.a, p. 2843
   Unsigned bitfield extract  This instruction copies a bitfield of <width>
   bits starting from bit position <lsb> in the source register to the least
   significant bits of the destination register, and sets destination bits
   above the bitfield to zero.  This is an alias of UBFM. This means:  • The
   encodings in this description are named to match the encodings of UBFM. •
   The description of UBFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: UBFX <Xd>, <Xn>, #<lsb>, #<width>  ==  UBFM <Xd>, <Xn>, #<lsb>, #(<lsb>+<width>-1)
   Operation (ASL):
     The description of UBFM gives the operational pseudocode for this instruction.
   Base instruction [C6.2.486 UBFM] p. 2841, Operation (ASL):
     constant bits(datasize) src = X[n, datasize];
     // Perform bitfield move on low bits
     constant bits(datasize) bot = ROR(src, r) AND wmask;
     // Combine extension bits and result bits
     X[d, datasize] = bot AND tmask;
*)
Definition armv8a_UBFX_instr : instr_desc_t := mk_bfx_instr UBFX (wshr (sz := osz)).


(* -------------------------------------------------------------------- *)
(* Moves. *)

(* [C6.2.281 MOV (register)] ARM DDI 0487 M.a, p. 2413
   Move register value  This instruction copies the value in a source register
   to the destination register.  This is an alias of ORR (shifted register).
   This means:  • The encodings in this description are named to match the
   encodings of ORR (shifted register). • The description of ORR (shifted
   register) gives the operational pseudocode, any CONSTRAINED UNPREDICTABLE
   behavior, and any operational information for this instruction.
   Syntax: MOV <Xd>, <Xm>  ==  ORR <Xd>, XZR, <Xm>
   Operation (ASL):
     The description of ORR (shifted register) gives the operational pseudocode for this instruction.
*)
Definition armv8a_MOV_semi {ws : wsize} (wn : word ws) : ty_w ws :=
  wn.

Definition armv8a_MOV_instr : instr_desc_t :=
  let mn := MOV in
  let tin := [:: lword osz ] in
  let semi := armv8a_MOV_semi (ws := osz) in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds :=
      ak_reg_reg ++ [:: [:: [:: CAreg ]; [:: CAimm (Some CAimmC_armv8a_mov_imm) osz ] ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

Definition mk_movw_instr mn (semi : word U16 -> word U8 -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword U16; lword U8 ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_r_imm16_shift;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    (* The halfword shift is printed as [LSL #<sh>], and dropped when it is
       zero. *)
    id_pp_asm :=
      pp_op_shapes (string_of_armv8a_mnemonic mn)
        [:: pp_full osz; pp_full U16; pp_shift SLSL ];
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

(* [C6.2.284 MOVZ] ARM DDI 0487 M.a, p. 2418
   Move wide with zero  This instruction moves an optionally-shifted 16-bit
   immediate value to a register.  This instruction is used by the alias MOV
   (wide immediate).
   Syntax: MOVZ <Xd>, #<imm>{, LSL #<shift>}
   Operation (ASL):
     bits(datasize) result = Zeros(datasize);
     result<pos+15:pos> = imm;
     X[d, datasize] = result;
*)
Definition armv8a_MOVZ_semi {ws : wsize} (imm : word U16) (wsh : word U8) : ty_w ws :=
  wshl (zero_extend ws imm) (wunsigned wsh).

Definition armv8a_MOVZ_instr : instr_desc_t :=
  mk_movw_instr MOVZ (armv8a_MOVZ_semi (ws := osz)).

(* [C6.2.283 MOVN] ARM DDI 0487 M.a, p. 2416
   Move wide with NOT  This instruction moves the inverse of an optionally-
   shifted 16-bit immediate value to a register.  This instruction is used by
   the alias MOV (inverted wide immediate).
   Syntax: MOVN <Xd>, #<imm>{, LSL #<shift>}
   Operation (ASL):
     bits(datasize) result = Zeros(datasize);
     result<pos+15:pos> = imm;
     X[d, datasize] = NOT(result);
*)
Definition armv8a_MOVN_semi {ws : wsize} (imm : word U16) (wsh : word U8) : ty_w ws :=
  wnot (wshl (zero_extend ws imm) (wunsigned wsh)).

Definition armv8a_MOVN_instr : instr_desc_t :=
  mk_movw_instr MOVN (armv8a_MOVN_semi (ws := osz)).

(* [C6.2.282 MOVK] ARM DDI 0487 M.a, p. 2415
   Move wide with keep  This instruction moves an optionally-shifted 16-bit
   immediate value into a register, keeping other bits unchanged.
   Syntax: MOVK <Xd>, #<imm>{, LSL #<shift>}
   Operation (ASL):
     bits(datasize) result = X[d, datasize];
     result<pos+15:pos> = imm;
     X[d, datasize] = result;
*)
Definition armv8a_MOVK_semi {ws : wsize} (old : word ws) (imm : word U16) (wsh : word U8) : ty_w ws :=
  let sh := wunsigned wsh in
  let mask := wshl (zero_extend ws (wrepr U16 (-1))) sh in
  wor (wshl (zero_extend ws imm) sh) (wand old (wnot mask)).

Definition armv8a_MOVK_instr : instr_desc_t :=
  let mn := MOVK in
  let tin := [:: lword osz; lword U16; lword U8 ] in
  let semi := armv8a_MOVK_semi (ws := osz) in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1; Ea 2 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_r_imm16_shift;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm :=
      pp_op_shapes (string_of_armv8a_mnemonic mn)
        [:: pp_full osz; pp_full U16; pp_shift SLSL ];
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.


(* -------------------------------------------------------------------- *)
(* Extensions.
   [in_ws] is the width of the extracted low bits; the result is extended
   to the operand size. SXTW and UXTW only exist in the X form. *)

Definition armv8a_extend_semi
  {ws : wsize} (sign : bool) (ws' : wsize) (wn : word ws) : word ws' :=
  let f := if sign then sign_extend else zero_extend in
  (f ws' ws wn).

Definition mk_extend_instr mn (in_ws : wsize) (sign : bool) (valid : bool)
  : instr_desc_t :=
  let tin := [:: lword in_ws ] in
  let semi := armv8a_extend_semi (ws := in_ws) sign osz in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    (* [SXTB <Xd>, <Wn>] / [UXTB <Wd>, <Wn>]: the source is always a W
       register, and so is the destination of the zero-extensions. *)
    id_pp_asm := pp_armv8a_op_szs mn [:: (if sign then osz else U32); U32 ];
    id_valid := valid;
    id_wf := refl_equal;
  |}.

(* [C6.2.12 ADR] ARM DDI 0487 M.a, p. 1809
   Form PC-relative address  This instruction adds an immediate value to the PC
   value to form a PC-relative address, and writes the result to the
   destination register.
   Syntax: ADR <Xd>, <label>
   Operation (ASL):
     X[d, 64] = PC64 + imm;
*)
Definition armv8a_ADR_semi (wn : word U64) : ty_r :=
  wn.

Definition armv8a_ADR_instr : instr_desc_t :=
  let mn := ADR in
  let tin := [:: lreg ] in
  let semi := armv8a_ADR_semi in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ec 1 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := NOT_DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz == U64;
    id_wf := refl_equal;
  |}.

(* [C6.2.471 SXTB] ARM DDI 0487 M.a, p. 2812
   Signed extend byte  This instruction extracts an 8-bit value from a
   register, sign-extends it to the size of the register, and writes the result
   to the destination register.  This is an alias of SBFM. This means:  • The
   encodings in this description are named to match the encodings of SBFM. •
   The description of SBFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: SXTB <Xd>, <Wn>  ==  SBFM <Xd>, <Xn>, #0, #7
   Operation (ASL):
     The description of SBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_SXTB_instr : instr_desc_t := mk_extend_instr SXTB U8 true osz_valid.
(* [C6.2.472 SXTH] ARM DDI 0487 M.a, p. 2813
   Sign extend halfword  This instruction extracts a 16-bit value, sign-extends
   it to the size of the register, and writes the result to the destination
   register.  This is an alias of SBFM. This means:  • The encodings in this
   description are named to match the encodings of SBFM. • The description of
   SBFM gives the operational pseudocode, any CONSTRAINED UNPREDICTABLE
   behavior, and any operational information for this instruction.
   Syntax: SXTH <Xd>, <Wn>  ==  SBFM <Xd>, <Xn>, #0, #15
   Operation (ASL):
     The description of SBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_SXTH_instr : instr_desc_t := mk_extend_instr SXTH U16 true osz_valid.
(* [C6.2.473 SXTW] ARM DDI 0487 M.a, p. 2814
   Sign extend word  This instruction sign-extends a word to the size of the
   register, and writes the result to the destination register.  This is an
   alias of SBFM. This means:  • The encodings in this description are named to
   match the encodings of SBFM. • The description of SBFM gives the operational
   pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any operational
   information for this instruction.
   Syntax: SXTW <Xd>, <Wn>  ==  SBFM <Xd>, <Xn>, #0, #31
   Operation (ASL):
     The description of SBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_SXTW_instr : instr_desc_t := mk_extend_instr SXTW U32 true (osz == U64).
(* [C6.2.499 UXTB] ARM DDI 0487 M.a, p. 2863
   Unsigned extend byte  This instruction extracts an 8-bit value from a
   register, zero-extends it to the size of the register, and writes the result
   to the destination register.  This is an alias of UBFM. This means:  • The
   encodings in this description are named to match the encodings of UBFM. •
   The description of UBFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: UXTB <Wd>, <Wn>  ==  UBFM <Wd>, <Wn>, #0, #7
   Operation (ASL):
     The description of UBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_UXTB_instr : instr_desc_t := mk_extend_instr UXTB U8 false osz_valid.
(* [C6.2.500 UXTH] ARM DDI 0487 M.a, p. 2864
   Unsigned extend halfword  This instruction extracts a 16-bit value from a
   register, zero-extends it to the size of the register, and writes the result
   to the destination register.  This is an alias of UBFM. This means:  • The
   encodings in this description are named to match the encodings of UBFM. •
   The description of UBFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: UXTH <Wd>, <Wn>  ==  UBFM <Wd>, <Wn>, #0, #15
   Operation (ASL):
     The description of UBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_UXTH_instr : instr_desc_t := mk_extend_instr UXTH U16 false osz_valid.
(* [C6.2.281 MOV (register)] ARM DDI 0487 M.a, p. 2413
   Move register value  This instruction copies the value in a source register
   to the destination register.  This is an alias of ORR (shifted register).
   This means:  • The encodings in this description are named to match the
   encodings of ORR (shifted register). • The description of ORR (shifted
   register) gives the operational pseudocode, any CONSTRAINED UNPREDICTABLE
   behavior, and any operational information for this instruction.
   Note: The ARM ARM defines no UXTW entry: UXTW #0 is equivalent to a 32-bit register MOV (alias of ORR (shifted register)), whose 32-bit result is zero-extended to 64 bits; the MOV (register) entry is recorded here in its place.
   Syntax: MOV <Xd>, <Xm>  ==  ORR <Xd>, XZR, <Xm>
   Operation (ASL):
     The description of ORR (shifted register) gives the operational pseudocode for this instruction.
*)
Definition armv8a_UXTW_instr : instr_desc_t := mk_extend_instr UXTW U32 false (osz == U64).

(* -------------------------------------------------------------------- *)
(* Bit-manipulation instructions. *)

(* A two-register instruction without flags nor shifted operand.
   [valid] restricts the operand sizes the instruction exists at. *)
Definition mk_rr_instr mn (doit_v : doit_t) (valid : bool)
  (semi : word osz -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := ak_rr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := doit_v;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := valid;
    id_wf := refl_equal;
  |}.

(* [RBIT] ARM DDI 0487 M.a
   Reverse bits  This instruction reverses the bit order in a register.
   Syntax: RBIT <Xd>, <Xn>
   Operation (ASL, summarized):
     constant bits(datasize) operand = X[n, datasize];
     bits(datasize) result;
     for i = 0 to datasize-1
         result<datasize-1-i> = operand<i>;
     X[d, datasize] = result;
*)
Definition armv8a_RBIT_semi {ws : wsize} (wn : word ws) : ty_w ws :=
  wbitrev wn.

Definition armv8a_RBIT_instr : instr_desc_t :=
  mk_rr_instr RBIT DOIT osz_valid (armv8a_RBIT_semi (ws := osz)).

(* [CLZ] ARM DDI 0487 M.a
   Count leading zeros  This instruction counts the number of consecutive
   binary zero bits, starting from the most significant bit in the source
   register, and places the count in the destination register.
   Syntax: CLZ <Xd>, <Xn>
   Operation (ASL, summarized):
     constant integer result = CountLeadingZeroBits(X[n, datasize]);
     X[d, datasize] = result<datasize-1:0>;
*)
Definition armv8a_CLZ_semi {ws : wsize} (wn : word ws) : ty_w ws :=
  leading_zero wn.

Definition armv8a_CLZ_instr : instr_desc_t :=
  mk_rr_instr CLZ DOIT osz_valid (armv8a_CLZ_semi (ws := osz)).

(* [C6.2.90 CLS] ARM DDI 0487 M.a, p. 1939
   Count leading sign bits  This instruction counts the number of leading bits
   of the source register that have the same value as the most significant bit
   of the register, and writes the result to the destination register. This
   count does not include the most significant bit of the source register.
   Syntax: CLS <Xd>, <Xn>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant integer result = CountLeadingSignBits(operand1);
     X[d, datasize] = result<datasize-1:0>;
*)
(* CountLeadingSignBits(x) = CountLeadingZeroBits(x<msb:1> EOR x<msb-1:0>):
   the (N-1)-bit word [x<msb:1> EOR x<msb-1:0>] is computed as the N-bit
   word [(x >> 1) EOR x] with its top bit cleared, whose leading-zero
   count is one more than that of the (N-1)-bit word. *)
Definition armv8a_CLS_semi {ws : wsize} (wn : word ws) : ty_w ws :=
  let t := wand (wxor (wshr wn 1) wn) (wrepr ws (2 ^ (wsize_bits ws - 1) - 1)) in
  (leading_zero t - 1)%w.

Definition armv8a_CLS_instr : instr_desc_t :=
  mk_rr_instr CLS DOIT osz_valid (armv8a_CLS_semi (ws := osz)).

(* [C6.2.341 REV] ARM DDI 0487 M.a, p. 2532
   Reverse bytes  This instruction reverses the byte order in a register.  This
   instruction is used by the pseudo-instruction REV64.
   Syntax: REV <Xd>, <Xn>
   Operation (ASL):
     constant bits(datasize) operand = X[n, datasize];
     bits(datasize) result;
     constant integer containers = datasize DIV container_size;
     for c = 0 to containers-1
         constant bits(container_size) container = Elem[operand, c, container_size];
         Elem[result, c, container_size] = Reverse(container, 8);
     X[d, datasize] = result;
*)
(* The container is the whole register ([container_size = datasize]). *)
Definition armv8a_REV_semi {ws : wsize} (wn : word ws) : ty_w ws :=
  wbswap wn.

Definition armv8a_REV_instr : instr_desc_t :=
  mk_rr_instr REV DOIT osz_valid (armv8a_REV_semi (ws := osz)).

(* [C6.2.342 REV16] ARM DDI 0487 M.a, p. 2534
   Reverse bytes in 16-bit halfwords  This instruction reverses the byte order
   in each 16-bit halfword of a register.
   Syntax: REV16 <Xd>, <Xn>
   Operation (ASL):
     constant bits(datasize) operand = X[n, datasize];
     bits(datasize) result;
     constant integer containers = datasize DIV container_size;
     for c = 0 to containers-1
         constant bits(container_size) container = Elem[operand, c, container_size];
         Elem[result, c, container_size] = Reverse(container, 8);
     X[d, datasize] = result;
*)
Definition armv8a_REV16_semi {ws : wsize} (wn : word ws) : ty_w ws :=
  lift1_vec U16 (@wbswap U16) ws wn.

Definition armv8a_REV16_instr : instr_desc_t :=
  mk_rr_instr REV16 DOIT osz_valid (armv8a_REV16_semi (ws := osz)).

(* [C6.2.343 REV32] ARM DDI 0487 M.a, p. 2536
   Reverse bytes in 32-bit words  This instruction reverses the byte order in
   each 32-bit word of a register.
   Syntax: REV32 <Xd>, <Xn>
   Operation (ASL):
     constant bits(datasize) operand = X[n, datasize];
     bits(datasize) result;
     constant integer containers = datasize DIV container_size;
     for c = 0 to containers-1
         constant bits(container_size) container = Elem[operand, c, container_size];
         Elem[result, c, container_size] = Reverse(container, 8);
     X[d, datasize] = result;
*)
(* REV32 only exists in the X form: on a W register it is REV. *)
Definition armv8a_REV32_semi {ws : wsize} (wn : word ws) : ty_w ws :=
  lift1_vec U32 (@wbswap U32) ws wn.

Definition armv8a_REV32_instr : instr_desc_t :=
  mk_rr_instr REV32 DOIT (osz == U64) (armv8a_REV32_semi (ws := osz)).

(* -------------------------------------------------------------------- *)
(* Comparisons. *)

Definition mk_cmp_instr mn (ick : option armv8a_caimm_cond)
  (semi_t : word osz -> word osz -> ty_nzcv_t)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz ] in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 0; Ea 1 ];
      id_tout := snzcv;
      id_out := ad_nzcv;
      id_semi_total := semi_t;
      id_nargs := 2;
      id_args_kinds := ak_rr_or_imm ick;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := armv8a_mn_str mn;
      id_safe := [::];
      id_err := ErrSemUndef;
      id_init := [:: IBool true; IBool true; IBool true; IBool true ];
      id_doit := DOIT;
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_wf := refl_equal;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk mn x (mk_semi2_2_shifted_t sk (id_semi_total x))
  else x.

Arguments mk_cmp_instr : clear implicits.

(* [C6.2.97 CMP (shifted register)] ARM DDI 0487 M.a, p. 1953
   Compare (shifted register)  This instruction subtracts an optionally-shifted
   register value from a register value. It updates the condition flags based
   on the result, and discards the result.  This is an alias of SUBS (shifted
   register). This means:  • The encodings in this description are named to
   match the encodings of SUBS (shifted register). • The description of SUBS
   (shifted register) gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: CMP <Wn>, <Wm>{, <shift> #<amount>}  ==  CMP <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     The description of SUBS (shifted register) gives the operational pseudocode for this instruction.
*)

Definition armv8a_CMP_semi_t {ws : wsize} (wn wm : word ws) : ty_nzcv_t :=
  let wmnot := wnot wm in
  nzcv_of_aluop_t
    (wn + wmnot + 1)%w
    (wunsigned wn + wunsigned wmnot + 1)%Z
    (wsigned wn + wsigned wmnot + 1)%Z.

Definition armv8a_CMP_instr : instr_desc_t :=
  mk_cmp_instr CMP arith_imm armv8a_CMP_semi_t.
(* [C6.2.94 CMN (shifted register)] ARM DDI 0487 M.a, p. 1946
   Compare negative (shifted register)  This instruction adds a register value
   and an optionally-shifted register value. It updates the condition flags
   based on the result, and discards the result.  This is an alias of ADDS
   (shifted register). This means:  • The encodings in this description are
   named to match the encodings of ADDS (shifted register). • The description
   of ADDS (shifted register) gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: CMN <Wn>, <Wm>{, <shift> #<amount>}  ==  CMN <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     The description of ADDS (shifted register) gives the operational pseudocode for this instruction.
   Base instruction [C6.2.11 ADDS (shifted register)] p. 1807, Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     bits(datasize) result;
     bits(4) nzcv;
     (result, nzcv) = AddWithCarry(operand1, operand2, '0');
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = nzcv;
*)
Definition armv8a_CMN_semi_t {ws : wsize} (wn wm : word ws) : ty_nzcv_t :=
  nzcv_of_aluop_t
    (wn + wm)%w
    (wunsigned wn + wunsigned wm)%Z
    (wsigned wn + wsigned wm)%Z.

Definition armv8a_CMN_instr : instr_desc_t :=
  mk_cmp_instr CMN arith_imm armv8a_CMN_semi_t.
(* [C6.2.484 TST (shifted register)] ARM DDI 0487 M.a, p. 2837
   Test (shifted register)  This instruction performs a bitwise AND operation
   on a register value and an optionally-shifted register value. It updates the
   condition flags based on the result, and discards the result.  This is an
   alias of ANDS (shifted register). This means:  • The encodings in this
   description are named to match the encodings of ANDS (shifted register). •
   The description of ANDS (shifted register) gives the operational pseudocode,
   any CONSTRAINED UNPREDICTABLE behavior, and any operational information for
   this instruction.
   Syntax: TST <Wn>, <Wm>{, <shift> #<amount>}  ==  TST <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     The description of ANDS (shifted register) gives the operational pseudocode for this instruction.
*)

Definition armv8a_TST_semi_t {ws : wsize} (wn wm : word ws) : ty_nzcv_t :=
  nzcv_of_logop_t (wand wn wm).

Definition armv8a_TST_instr : instr_desc_t :=
  mk_cmp_instr TST bitmask_imm armv8a_TST_semi_t.

(* -------------------------------------------------------------------- *)
(* Conditional selection.
   The condition is a first-class operand (the [CAcond] argument kind),
   evaluated by [arm_eval_cond] on the NZCV flags and passed to the
   semantics as a boolean. *)

Definition mk_csel_instr mn (semi : word osz -> word osz -> bool -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz; lbool ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 4;
    id_args_kinds := ak_rrr_cond;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

(* [C6.2.138 CSEL] ARM DDI 0487 M.a, p. 2138
   Conditional select  This instruction writes the value of the first source
   register to the destination register if the condition is TRUE. If the
   condition is FALSE, it writes the value of the second source register to the
   destination register.
   Syntax: CSEL <Xd>, <Xn>, <Xm>, <cond>
   Operation (ASL):
     bits(datasize) result;
     if ConditionHolds(condition) then
         result = X[n, datasize];
     else
         result = X[m, datasize];
     X[d, datasize] = result;
*)
Definition armv8a_CSEL_semi {ws : wsize} (wn wm : word ws) (b : bool) : ty_w ws :=
  if b then wn else wm.

Definition armv8a_CSEL_instr := mk_csel_instr CSEL (armv8a_CSEL_semi (ws := osz)).

(* [C6.2.141 CSINC] ARM DDI 0487 M.a, p. 2144
   Conditional select increment  This instruction returns, in the destination
   register, the value of the first source register if the condition is TRUE,
   and otherwise returns the value of the second source register incremented by
   1.  This instruction is used by the aliases CINC and CSET.
   Syntax: CSINC <Xd>, <Xn>, <Xm>, <cond>
   Operation (ASL):
     bits(datasize) result;
     if ConditionHolds(condition) then
         result = X[n, datasize];
     else
         result = X[m, datasize] + 1;
     X[d, datasize] = result;
*)
Definition armv8a_CSINC_semi {ws : wsize} (wn wm : word ws) (b : bool) : ty_w ws :=
  if b then wn else (wm + 1)%w.

Definition armv8a_CSINC_instr := mk_csel_instr CSINC (armv8a_CSINC_semi (ws := osz)).

(* [C6.2.142 CSINV] ARM DDI 0487 M.a, p. 2146
   Conditional select invert  This instruction returns, in the destination
   register, the value of the first source register if the condition is TRUE,
   and otherwise returns the bitwise inversion value of the second source
   register.  This instruction is used by the aliases CINV and CSETM.
   Syntax: CSINV <Xd>, <Xn>, <Xm>, <cond>
   Operation (ASL):
     bits(datasize) result;
     if ConditionHolds(condition) then
         result = X[n, datasize];
     else
         result = NOT(X[m, datasize]);
     X[d, datasize] = result;
*)
Definition armv8a_CSINV_semi {ws : wsize} (wn wm : word ws) (b : bool) : ty_w ws :=
  if b then wn else wnot wm.

Definition armv8a_CSINV_instr := mk_csel_instr CSINV (armv8a_CSINV_semi (ws := osz)).

(* [C6.2.143 CSNEG] ARM DDI 0487 M.a, p. 2148
   Conditional select negation  This instruction returns, in the destination
   register, the value of the first source register if the condition is TRUE,
   and otherwise returns the negated value of the second source register.  This
   instruction is used by the alias CNEG.
   Syntax: CSNEG <Xd>, <Xn>, <Xm>, <cond>
   Operation (ASL):
     bits(datasize) result;
     if ConditionHolds(condition) then
         result = X[n, datasize];
     else
         result = NOT(X[m, datasize]) + 1;
     X[d, datasize] = result;
*)
Definition armv8a_CSNEG_semi {ws : wsize} (wn wm : word ws) (b : bool) : ty_w ws :=
  if b then wn else (wnot wm + 1)%w.

Definition armv8a_CSNEG_instr := mk_csel_instr CSNEG (armv8a_CSNEG_semi (ws := osz)).

(* The conditional set aliases take only a destination and a condition.
   The condition operand is the one written in the alias: the assembler
   encodes its inverse in the base instruction, whose source registers are
   the zero register. *)
Definition mk_cset_instr mn (semi : bool -> ty_w osz) : instr_desc_t :=
  let tin := [:: lbool ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := ak_r_cond;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

(* [C6.2.139 CSET] ARM DDI 0487 M.a, p. 2140
   Conditional set  This instruction sets the destination register to 1 if the
   condition is TRUE, and otherwise sets it to 0.  This is an alias of CSINC.
   This means:  • The encodings in this description are named to match the
   encodings of CSINC. • The description of CSINC gives the operational
   pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any operational
   information for this instruction.
   Syntax: CSET <Xd>, <invcond>  ==  CSINC <Xd>, XZR, XZR, <cond>
   Operation (ASL):
     The description of CSINC gives the operational pseudocode for this instruction.
   Base instruction [C6.2.141 CSINC] p. 2144, Operation (ASL):
     bits(datasize) result;
     if ConditionHolds(condition) then
         result = X[n, datasize];
     else
         result = X[m, datasize] + 1;
     X[d, datasize] = result;
*)
Definition armv8a_CSET_semi {ws : wsize} (b : bool) : ty_w ws :=
  if b then 1%w else 0%w.

Definition armv8a_CSET_instr := mk_cset_instr CSET (armv8a_CSET_semi (ws := osz)).

(* [C6.2.140 CSETM] ARM DDI 0487 M.a, p. 2142
   Conditional set mask  This instruction sets all bits of the destination
   register to 1 if the condition is TRUE, and otherwise sets all bits to 0.
   This is an alias of CSINV. This means:  • The encodings in this description
   are named to match the encodings of CSINV. • The description of CSINV gives
   the operational pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any
   operational information for this instruction.
   Syntax: CSETM <Xd>, <invcond>  ==  CSINV <Xd>, XZR, XZR, <cond>
   Operation (ASL):
     The description of CSINV gives the operational pseudocode for this instruction.
   Base instruction [C6.2.142 CSINV] p. 2146, Operation (ASL):
     bits(datasize) result;
     if ConditionHolds(condition) then
         result = X[n, datasize];
     else
         result = NOT(X[m, datasize]);
     X[d, datasize] = result;
*)
Definition armv8a_CSETM_semi {ws : wsize} (b : bool) : ty_w ws :=
  if b then wrepr ws (-1) else 0%w.

Definition armv8a_CSETM_instr := mk_cset_instr CSETM (armv8a_CSETM_semi (ws := osz)).

(* -------------------------------------------------------------------- *)
(* Loads and stores.
   The memory access itself is performed by the framework ([eval_asm_arg]
   reads or writes memory for address arguments); the instruction semantics
   only sign- or zero-extends the transferred value. [LDR] and [STR] access
   memory at the operand size; the narrow loads and stores have their
   access width in the mnemonic. *)

(* [C6.2.217 LDR (register)] ARM DDI 0487 M.a, p. 2275
   Load register (register)  This instruction calculates an address from a base
   register value and an offset register value, loads a word from memory, and
   writes it to a register. The offset register value can optionally be shifted
   and extended. For information about addressing modes, see Load/Store
   addressing modes.
   Syntax: LDR <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Syntax: LDR <Xt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(datasize) data = Mem[address, datasize DIV 8, accdesc];
     X[t, regsize] = ZeroExtend(data, regsize);
*)
Definition armv8a_load_instr mn : instr_desc_t :=
  let wacc :=
    if wsize_of_narrow_load_mn mn is Some ws'
    then ws'
    else osz
  in
  let tin := [:: lword wacc ] in
  let semi := armv8a_extend_semi (ws := wacc) (isSome (wsize_of_sload_mn mn)) osz in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Eu 1 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    (* The transferred register of the zero-extending narrow loads is
       always a W register ([LDRB <Wt>, ...]); the sign-extending loads
       name it at the operand size ([LDRSB <Wt>|<Xt>, ...]). *)
    id_pp_asm :=
      pp_armv8a_op_szs mn
        [:: (match mn with LDRB | LDRH => U32 | _ => osz end); osz ];
    id_valid := osz_valid && (if mn is LDRSW then osz == U64 else true);
    id_wf := refl_equal;
  |}.

(* [C6.2.220 LDRB (register)] ARM DDI 0487 M.a, p. 2283
   Load register byte (register)  This instruction calculates an address from a
   base register value and an offset register value, loads a byte from memory,
   zero-extends it, and writes it to a register. For information about
   addressing modes, see Load/Store addressing modes.
   Syntax: LDRB <Wt>, [<Xn|SP>, (<Wm>|<Xm>), <extend> {<amount>}]
   Syntax: LDRB <Wt>, [<Xn|SP>, <Xm>{, LSL <amount>}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(8) data = Mem[address, 1, accdesc];
     X[t, 32] = ZeroExtend(data, 32);
*)

(* [C6.2.222 LDRH (register)] ARM DDI 0487 M.a, p. 2288
   Load register halfword (register)  This instruction calculates an address
   from a base register value and an offset register value, loads a halfword
   from memory, zero-extends it, and writes it to a register. For information
   about addressing modes, see Load/Store addressing modes.
   Syntax: LDRH <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(16) data = Mem[address, 2, accdesc];
     X[t, 32] = ZeroExtend(data, 32);
*)

(* [C6.2.224 LDRSB (register)] ARM DDI 0487 M.a, p. 2293
   Load register signed byte (register)  This instruction calculates an address
   from a base register value and an offset register value, loads a byte from
   memory, sign-extends it, and writes it to a register. For information about
   addressing modes, see Load/Store addressing modes.
   Syntax: LDRSB <Wt>, [<Xn|SP>, (<Wm>|<Xm>), <extend> {<amount>}]
   Syntax: LDRSB <Wt>, [<Xn|SP>, <Xm>{, LSL <amount>}]
   Syntax: LDRSB <Xt>, [<Xn|SP>, (<Wm>|<Xm>), <extend> {<amount>}]
   Syntax: LDRSB <Xt>, [<Xn|SP>, <Xm>{, LSL <amount>}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(8) data = Mem[address, 1, accdesc];
     X[t, regsize] = SignExtend(data, regsize);
*)

(* [C6.2.226 LDRSH (register)] ARM DDI 0487 M.a, p. 2298
   Load register signed halfword (register)  This instruction calculates an
   address from a base register value and an offset register value, loads a
   halfword from memory, sign-extends it, and writes it to a register. For
   information about addressing modes, see Load/Store addressing modes.
   Syntax: LDRSH <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Syntax: LDRSH <Xt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(16) data = Mem[address, 2, accdesc];
     X[t, regsize] = SignExtend(data, regsize);
*)

(* [C6.2.229 LDRSW (register)] ARM DDI 0487 M.a, p. 2304
   Load register signed word (register)  This instruction calculates an address
   from a base register value and an offset register value, loads a word from
   memory, sign-extends it to form a 64-bit value, and writes it to a register.
   The offset register value can be shifted left by 0 or 2 bits. For
   information about addressing modes, see Load/Store addressing modes.
   Syntax: LDRSW <Xt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(32) data = Mem[address, 4, accdesc];
     X[t, 64] = SignExtend(data, 64);
*)

(* [C6.2.415 STR (register)] ARM DDI 0487 M.a, p. 2693
   Store register (register)  This instruction calculates an address from a
   base register value and an offset register value, and stores a 32-bit word
   or a 64-bit doubleword to the calculated address, from a register. For
   information about addressing modes, see Load/Store addressing modes.  The
   instruction uses an offset addressing mode, that calculates the address used
   for the memory access from a base register value and an offset register
   value. The offset can be optionally shifted and extended.
   Syntax: STR <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Syntax: STR <Xt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_STORE, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     Mem[address, datasize DIV 8, accdesc] = X[t, datasize];
*)
Definition armv8a_store_instr mn : instr_desc_t :=
  let wacc :=
    if wsize_of_narrow_store_mn mn is Some ws'
    then ws'
    else osz
  in
  let tin := [:: lword wacc ] in
  let semi := armv8a_extend_semi (ws := wacc) false wacc in
  {|
    id_msb_flag := MSB_MERGE;
    (* The input should be an [osz] word and be zero_extended to the output
       size, but this is implicit in Jasmin semantics. *)
    id_tin := tin;
    id_in := [:: Ea 0 ];
    id_tout := [:: lword wacc ];
    id_out := [:: Eu 1 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    (* The transferred register of the narrow stores is always a W
       register ([STRB <Wt>, ...]). *)
    id_pp_asm :=
      pp_armv8a_op_szs mn
        [:: (match mn with STRB | STRH => U32 | _ => osz end); osz ];
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

(* [C6.2.417 STRB (register)] ARM DDI 0487 M.a, p. 2699
   Store register byte (register)  This instruction calculates an address from
   a base register value and an offset register value, and stores a byte from a
   32-bit register to the calculated address. For information about addressing
   modes, see Load/Store addressing modes.  The instruction uses an offset
   addressing mode, that calculates the address used for the memory access from
   a base register value and an offset register value. The offset can be
   optionally shifted and extended.
   Syntax: STRB <Wt>, [<Xn|SP>, (<Wm>|<Xm>), <extend> {<amount>}]
   Syntax: STRB <Wt>, [<Xn|SP>, <Xm>{, LSL <amount>}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_STORE, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     Mem[address, 1, accdesc] = X[t, 8];
*)

(* [C6.2.419 STRH (register)] ARM DDI 0487 M.a, p. 2704
   Store register halfword (register)  This instruction calculates an address
   from a base register value and an offset register value, and stores a
   halfword from a 32-bit register to the calculated address. For information
   about addressing modes, see Load/Store addressing modes.  The instruction
   uses an offset addressing mode, that calculates the address used for the
   memory access from a base register value and an offset register value. The
   offset can be optionally shifted and extended.
   Syntax: STRH <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_STORE, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     Mem[address, 2, accdesc] = X[t, 16];
*)

(* -------------------------------------------------------------------- *)
(* Load and store pair, signed offset form.
   The two registers are transferred through a single memory argument of
   twice the register size ([wsize_pair]). Jasmin memory is little endian,
   so the low half of that argument is the word at the lower address, which
   the first register receives (or provides). The address must satisfy
   [CAmemC_armv8a_pair]: a base register and a scaled 7-bit displacement.
   The pre-index and post-index (writeback) forms are not modelled. *)

Definition wsize_pair (ws : wsize) : wsize := if ws == U32 then U64 else U128.

(* Global addresses are not allowed: [lower_glob_load] first computes the
   address of a global into a register ([armv8a_is_load]). *)
Let ak_reg_reg_pair :=
  [:: [:: [:: CAreg ]; [:: CAreg ];
          [:: CAmem false (Some (CAmemC_armv8a_pair osz)) ] ] ].

(* [C6.2.214 LDP] ARM DDI 0487 M.d
   Load pair of registers. Signed offset form:
   Syntax: LDP <Wt1>, <Wt2>, [<Xn|SP>{, #<imm>}]
   Syntax: LDP <Xt1>, <Xt2>, [<Xn|SP>{, #<imm>}]
   <imm> is "a multiple of 4 in the range -256 to 252" (W) or "a multiple
   of 8 in the range -512 to 504" (X), "encoded in the "imm7" field".
   Operation (ASL, excerpt):
     let data : bits(2*datasize) = Mem{2*datasize}(address, accdesc);
     ...
     else
         data1 = data[(datasize-1):0];
         data2 = data[(2*datasize-1):datasize];
     end;
     X{datasize}(t) = data1;
     X{datasize}(t2) = data2;
   If t == t2, the behavior is CONSTRAINED UNPREDICTABLE (K1.2.17.7). The
   two destinations are written by the same instruction, so register
   allocation gives them distinct registers.
*)
Definition armv8a_LDP_semi {ws : wsize} (w : word (wsize_pair ws))
  : sem_ltuple [:: lword ws; lword ws ] :=
  (zero_extend ws w, zero_extend ws (wshr w (wsize_bits ws))).

Definition armv8a_LDP_instr : instr_desc_t :=
  let tin := [:: lword (wsize_pair osz) ] in
  let semi := armv8a_LDP_semi (ws := osz) in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Eu 2 ];
    id_tout := [:: lword osz; lword osz ];
    id_out := [:: Ea 0; Ea 1 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_pair;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str LDP;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true; IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op_szs LDP [:: osz; osz; osz ];
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

(* [C6.2.414 STP] ARM DDI 0487 M.d
   Store pair of registers. Signed offset form:
   Syntax: STP <Wt1>, <Wt2>, [<Xn|SP>{, #<imm>}]
   Syntax: STP <Xt1>, <Xt2>, [<Xn|SP>{, #<imm>}]
   <imm> has the same range as for LDP.
   Operation (ASL, excerpt, without the writeback cases):
     data1 = X{datasize}(t);
     data2 = X{datasize}(t2);
     let data : bits(2*datasize) = (if BigEndian(accdesc.acctype) then data1::data2
                                                                 else data2::data1);
     Mem{2 * datasize}(address, accdesc) = data;
*)
Definition armv8a_STP_semi {ws : wsize} (w1 w2 : word ws)
  : sem_ltuple [:: lword (wsize_pair ws) ] :=
  make_vec (wsize_pair ws) [:: w1; w2 ].

Definition armv8a_STP_instr : instr_desc_t :=
  let tin := [:: lword osz; lword osz ] in
  let semi := armv8a_STP_semi (ws := osz) in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1 ];
    id_tout := [:: lword (wsize_pair osz) ];
    id_out := [:: Eu 2 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := ak_reg_reg_pair;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str STP;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_op_szs STP [:: osz; osz; osz ];
    id_valid := osz_valid;
    id_wf := refl_equal;
  |}.

(* -------------------------------------------------------------------- *)
(* Barriers.
   They only constrain speculative execution and the order in which memory
   accesses are observed, which the semantics does not model: in the
   sequential semantics they have no effect, like the x86 fences. *)

(* [DSB] is printed in its full system form [DSB SY]. Its mnemonic string
   stays [DSB], as it is also the intrinsic and EasyCrypt name. *)
Definition pp_barrier (mn : armv8a_mnemonic) (_ : seq asm_arg) : pp_asm_op :=
  {|
    pp_aop_name := if mn is DSB then "DSB SY" else string_of_armv8a_mnemonic mn;
    pp_aop_ext := PP_name;
    pp_aop_args := [::];
  |}.

Definition mk_barrier_instr mn : instr_desc_t :=
  let semi : sem_ltuple [::] := tt in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := [::];
    id_in := [::];
    id_tout := [::];
    id_out := [::];
    id_semi_total := semi;
    id_nargs := 0;
    id_args_kinds := [:: [::] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_mn_str mn;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [::];
    id_doit := NOT_DOIT; (* Not DIT *)
    id_pp_asm := pp_barrier mn;
    id_valid := true;
    id_wf := refl_equal;
  |}.

(* [CSDB] ARM DDI 0487 M.a
   Consumption of speculative data barrier  Instructions after the barrier,
   other than branches, are not speculatively executed using the results of
   data value predictions, or of condition flag predictions of instructions
   other than conditional branches, of earlier instructions that are not
   architecturally resolved. Control flow speculation is still allowed.
   Syntax: CSDB
*)
Definition armv8a_CSDB_instr : instr_desc_t := mk_barrier_instr CSDB.

(* [DSB] ARM DDI 0487 M.a
   Data synchronization barrier  The memory accesses before the barrier
   complete before it completes, and the instructions after it do not alter
   any state of the system until then. Only the full system form is
   provided.
   Syntax: DSB SY
*)
Definition armv8a_DSB_instr : instr_desc_t := mk_barrier_instr DSB.

(* [ISB] ARM DDI 0487 M.a
   Instruction synchronization barrier  The instructions after the barrier
   are fetched after it completes.
   Syntax: ISB
*)
Definition armv8a_ISB_instr : instr_desc_t := mk_barrier_instr ISB.

(* -------------------------------------------------------------------- *)
(* Description of instructions. *)

Definition mn_desc (mn : armv8a_mnemonic) : instr_desc_t :=
  match mn with
  | ADD => armv8a_ADD_instr
  | ADDS => armv8a_ADDS_instr
  | ADC => armv8a_ADC_instr
  | ADCS => armv8a_ADCS_instr
  | SUB => armv8a_SUB_instr
  | SUBS => armv8a_SUBS_instr
  | SBC => armv8a_SBC_instr
  | SBCS => armv8a_SBCS_instr
  | NEG => armv8a_NEG_instr
  | MUL => armv8a_MUL_instr
  | MADD => armv8a_MADD_instr
  | MSUB => armv8a_MSUB_instr
  | SDIV => armv8a_SDIV_instr
  | UDIV => armv8a_UDIV_instr
  | UMULL => armv8a_UMULL_instr
  | SMULL => armv8a_SMULL_instr
  | UMADDL => armv8a_UMADDL_instr
  | SMADDL => armv8a_SMADDL_instr
  | UMULH => armv8a_UMULH_instr
  | SMULH => armv8a_SMULH_instr
  | AND => armv8a_AND_instr
  | ANDS => armv8a_ANDS_instr
  | BIC => armv8a_BIC_instr
  | BICS => armv8a_BICS_instr
  | ORR => armv8a_ORR_instr
  | EOR => armv8a_EOR_instr
  | MVN => armv8a_MVN_instr
  | ASR => armv8a_ASR_instr
  | LSL => armv8a_LSL_instr
  | LSR => armv8a_LSR_instr
  | ROR => armv8a_ROR_instr
  | RBIT => armv8a_RBIT_instr
  | REV => armv8a_REV_instr
  | REV16 => armv8a_REV16_instr
  | REV32 => armv8a_REV32_instr
  | CLZ => armv8a_CLZ_instr
  | CLS => armv8a_CLS_instr
  | BFC => armv8a_BFC_instr
  | BFI => armv8a_BFI_instr
  | BFXIL => armv8a_BFXIL_instr
  | SBFX => armv8a_SBFX_instr
  | UBFX => armv8a_UBFX_instr
  | EXTR => armv8a_EXTR_instr
  | MOV => armv8a_MOV_instr
  | MOVN => armv8a_MOVN_instr
  | MOVZ => armv8a_MOVZ_instr
  | MOVK => armv8a_MOVK_instr
  | ADR => armv8a_ADR_instr
  | SXTB => armv8a_SXTB_instr
  | SXTH => armv8a_SXTH_instr
  | SXTW => armv8a_SXTW_instr
  | UXTB => armv8a_UXTB_instr
  | UXTH => armv8a_UXTH_instr
  | UXTW => armv8a_UXTW_instr
  | CMP => armv8a_CMP_instr
  | CMN => armv8a_CMN_instr
  | TST => armv8a_TST_instr
  | CSEL => armv8a_CSEL_instr
  | CSINC => armv8a_CSINC_instr
  | CSINV => armv8a_CSINV_instr
  | CSNEG => armv8a_CSNEG_instr
  | CSET => armv8a_CSET_instr
  | CSETM => armv8a_CSETM_instr
  | LDR => armv8a_load_instr LDR
  | LDRB => armv8a_load_instr LDRB
  | LDRH => armv8a_load_instr LDRH
  | LDRSB => armv8a_load_instr LDRSB
  | LDRSH => armv8a_load_instr LDRSH
  | LDRSW => armv8a_load_instr LDRSW
  | LDP => armv8a_LDP_instr
  | STR => armv8a_store_instr STR
  | STRB => armv8a_store_instr STRB
  | STRH => armv8a_store_instr STRH
  | STP => armv8a_STP_instr
  | CSDB => armv8a_CSDB_instr
  | DSB => armv8a_DSB_instr
  | ISB => armv8a_ISB_instr
  end.

End ARMV8A_INSTR.

Arguments armv8a_extend_semi {ws} sign ws' wn /.

(* -------------------------------------------------------------------- *)
(* Advanced SIMD (NEON) instruction descriptions.
   They are parameterised by the arrangement of the vector: its lane size
   and its size, 64 bits (the low half of the register) or 128 bits (the
   whole register). An instruction on a 64-bit vector zeroes the upper 64
   bits of its destination register, hence [MSB_CLEAR]: a 64-bit result
   zero-extended to 128 bits (in the source, [(128u)#VAND_64(a, b)]) is the
   whole register. The assembly printer shows the arrangement of the vector
   registers ([v0.4s], [v0.2d], ...), which the shape [pp_vec ve sz]
   requests. Bitwise operations do not depend on the arrangement; they have
   byte lanes only, [v0.8b] or [v0.16b]. Loads and stores name the register
   through its 128-bit scalar view ([q0]), which [pp_full] requests.
   The operations of the moves, loads, stores and bitwise instructions below
   are written after the pseudocode of the ARM Architecture Reference
   Manual; those of the other instructions are quoted from its
   machine-readable version (the A64 ISA XML). *)

(* The valid arrangements of a mnemonic, as pairs of a lane size and a
   vector size; the first one is the default of its intrinsic. The
   lane-wise operations have every arrangement that the architecture allows:
   1D is reserved, MUL, SMAX, SMIN, UMAX, UMIN, REV64, MLA and MLS have no
   64-bit lanes, REV32 has 8- and 16-bit lanes and REV16 8-bit lanes only.
   EXT and TBL operate on bytes. INS, UMOV and SMOV address a lane of a whole
   register, hence have 128-bit vectors only; UMOV and SMOV move a lane to
   a general register, W for 8-, 16- and 32-bit lanes and X for 64-bit
   ones, and SMOV, which is taken in its X form only, has no 64-bit lanes.
   AESE, AESD, AESMC and AESIMC operate on a whole register, as bytes.
   PMULL and PMULL2 are taken in their 64-bit polynomial form only, which
   multiplies a lane of 64 bits of each source into the whole destination
   register. EOR3 and BCAX operate on a whole register, as bytes, RAX1 and
   XAR on 64-bit lanes of a whole register. SQDMULH, SQRDMULH, SQRDMLAH and
   SQRDMLSH have 16- and 32-bit lanes only. *)
Definition armv8a_vmn_shapes (vmn : armv8a_vmnemonic) : seq (velem * wsize) :=
  match vmn with
  | VMOV | VLDR | VSTR => [:: (VE8, U128) ]
  | VAND | VBIC | VORR | VORN | VEOR | VNOT | VBSL | VBIT | VBIF
  | VEXT | VTBL | VREV16 =>
      [:: (VE8, U128); (VE8, U64) ]
  | VADD | VSUB | VNEG | VABS
  | VSHL | VUSHR | VSSHR | VSLI | VSRI | VUSRA | VSSRA
  | VUSHL | VSSHL
  | VZIP1 | VZIP2 | VUZP1 | VUZP2 | VTRN1 | VTRN2
  | VCMEQ | VCMGT | VCMGE | VCMHI | VCMHS | VCMTST
  | VDUP | VDUPLANE =>
      [:: (VE8, U128); (VE16, U128); (VE32, U128); (VE64, U128)
        ; (VE8, U64); (VE16, U64); (VE32, U64) ]
  | VINS | VINSLANE | VUMOV =>
      [:: (VE8, U128); (VE16, U128); (VE32, U128); (VE64, U128) ]
  | VSMOV => [:: (VE8, U128); (VE16, U128); (VE32, U128) ]
  | VAESE | VAESD | VAESMC | VAESIMC
  | VPMULL | VPMULL2
  | VEOR3 | VBCAX => [:: (VE8, U128) ]
  | VRAX1 | VXAR => [:: (VE64, U128) ]
  | VMUL | VSMAX | VSMIN | VUMAX | VUMIN | VREV64 | VMLA | VMLS =>
      [:: (VE8, U128); (VE16, U128); (VE32, U128)
        ; (VE8, U64); (VE16, U64); (VE32, U64) ]
  | VREV32 => [:: (VE8, U128); (VE16, U128); (VE8, U64); (VE16, U64) ]
  | VSQDMULH | VSQRDMULH | VSQRDMLAH | VSQRDMLSH =>
      [:: (VE16, U128); (VE32, U128); (VE16, U64); (VE32, U64) ]
  end.

(* Whether [ve] lanes in a vector of [sz] bits is a valid arrangement of
   [vmn] (lane sizes are compared as word sizes). *)
Definition armv8a_vop_valid
  (vmn : armv8a_vmnemonic) (ve : velem) (sz : wsize) : bool :=
  has
    (fun s : velem * wsize => (wsize_of_velem ve == s.1) && (sz == s.2))
    (armv8a_vmn_shapes vmn).

(* The operations whose result depends on the lane size. *)
Definition armv8a_vmn_lanewise (vmn : armv8a_vmnemonic) : bool :=
  match vmn with
  | VADD | VSUB | VMUL | VNEG | VABS | VSMAX | VSMIN | VUMAX | VUMIN
  | VSHL | VUSHR | VSSHR | VSLI | VSRI | VUSRA | VSSRA
  | VUSHL | VSSHL
  | VZIP1 | VZIP2 | VUZP1 | VUZP2 | VTRN1 | VTRN2
  | VREV16 | VREV32 | VREV64
  | VCMEQ | VCMGT | VCMGE | VCMHI | VCMHS | VCMTST
  | VDUP | VDUPLANE | VINS | VINSLANE | VUMOV | VSMOV
  | VRAX1 | VXAR
  | VMLA | VMLS
  | VSQDMULH | VSQRDMULH | VSQRDMLAH | VSQRDMLSH => true
  | VMOV | VLDR | VSTR
  | VAND | VBIC | VORR | VORN | VEOR | VNOT | VBSL | VBIT | VBIF
  | VEXT | VTBL
  | VAESE | VAESD | VAESMC | VAESIMC
  | VPMULL | VPMULL2
  | VEOR3 | VBCAX => false
  end.

(* A vector instruction whose operands are printed with the given shapes. *)
Definition pp_armv8a_vop
  (vmn : armv8a_vmnemonic) (shapes : seq pp_shape) : asm_args -> pp_asm_op :=
  pp_op_shapes (string_of_armv8a_vmnemonic vmn) shapes.

(* Jasmin-source and EasyCrypt name of a vector operation, as the x86
   vector instructions: suffixed with the vector size (VMOV_128, as
   VPAND_128) or, for a lane-wise one, with the lanes (as VPADD_4u32). *)
Definition armv8a_vmn_str
  (vmn : armv8a_vmnemonic) (ve : velem) (sz : wsize) : unit -> string :=
  if armv8a_vmn_lanewise vmn
  then pp_ve_sz (armv8a_vmn_name vmn) ve sz
  else pp_sz (armv8a_vmn_name vmn) sz.

Notation ak_v := [:: CAxmm ] (only parsing).

(* A vector instruction [vmn Vd, Vn] or [vmn Vd, Vn, Vm] computing a
   function of its source registers. *)
Definition mk_vunop_instr vmn (ve : velem) {sz} (doit_v : doit_t)
  (semi : word sz -> ty_w sz) : instr_desc_t :=
  let tin := [:: lword sz ] in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: lword sz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := [:: [:: ak_v; ak_v ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str vmn ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := doit_v;
    id_pp_asm := pp_armv8a_vop vmn [:: pp_vec ve sz; pp_vec ve sz ];
    id_valid := armv8a_vop_valid vmn ve sz;
    id_wf := refl_equal;
  |}.

Definition mk_vbinop_instr vmn (ve : velem) {sz} (doit_v : doit_t)
  (semi : word sz -> word sz -> ty_w sz)
  : instr_desc_t :=
  let tin := [:: lword sz; lword sz ] in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword sz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := [:: [:: ak_v; ak_v; ak_v ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str vmn ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := doit_v;
    id_pp_asm := pp_armv8a_vop vmn [:: pp_vec ve sz; pp_vec ve sz; pp_vec ve sz ];
    id_valid := armv8a_vop_valid vmn ve sz;
    id_wf := refl_equal;
  |}.

(* A vector instruction [vmn Vd, Vn] that also reads its destination
   register: the first source is [Vd] itself. *)
Definition mk_vunop_acc_instr vmn (ve : velem) {sz} (doit_v : doit_t)
  (semi : word sz -> word sz -> ty_w sz) : instr_desc_t :=
  let tin := [:: lword sz; lword sz ] in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1 ];
    id_tout := [:: lword sz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := [:: [:: ak_v; ak_v ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str vmn ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := doit_v;
    id_pp_asm := pp_armv8a_vop vmn [:: pp_vec ve sz; pp_vec ve sz ];
    id_valid := armv8a_vop_valid vmn ve sz;
    id_wf := refl_equal;
  |}.

(* A vector instruction [vmn Vd, Vn, Vm] that also reads its destination
   register: the first source is [Vd] itself. *)
Definition mk_vbinop_acc_instr vmn (ve : velem) {sz} (doit_v : doit_t)
  (semi : word sz -> word sz -> word sz -> ty_w sz) : instr_desc_t :=
  let tin := [:: lword sz; lword sz; lword sz ] in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1; Ea 2 ];
    id_tout := [:: lword sz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := [:: [:: ak_v; ak_v; ak_v ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str vmn ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := doit_v;
    id_pp_asm := pp_armv8a_vop vmn [:: pp_vec ve sz; pp_vec ve sz; pp_vec ve sz ];
    id_valid := armv8a_vop_valid vmn ve sz;
    id_wf := refl_equal;
  |}.

(* A vector shift by immediate [vmn Vd, Vn, #shift]. The amount is an 8-bit
   immediate whose range depends on the lane size and on the direction
   ([rshift]): see [check_vshift_amount]. *)
Definition ak_vshift (ve : velem) (rshift : bool) : arg_kinds :=
  [:: CAimm (Some (CAimmC_armv8a_vshift_amount ve rshift)) U8 ].

Definition mk_vshift_instr vmn (ve : velem) (rshift : bool) {sz}
  (doit_v : doit_t) (semi : word sz -> word U8 -> ty_w sz) : instr_desc_t :=
  let tin := [:: lword sz; lword8 ] in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword sz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := [:: [:: ak_v; ak_v; ak_vshift ve rshift ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str vmn ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := doit_v;
    id_pp_asm := pp_armv8a_vop vmn [:: pp_vec ve sz; pp_vec ve sz; pp_full U8 ];
    id_valid := armv8a_vop_valid vmn ve sz;
    id_wf := refl_equal;
  |}.

(* A vector shift by immediate [vmn Vd, Vn, #shift] that also reads its
   destination register: the first source is [Vd] itself. *)
Definition mk_vshift_acc_instr vmn (ve : velem) (rshift : bool) {sz}
  (doit_v : doit_t) (semi : word sz -> word sz -> word U8 -> ty_w sz)
  : instr_desc_t :=
  let tin := [:: lword sz; lword sz; lword8 ] in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1; Ea 2 ];
    id_tout := [:: lword sz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := [:: [:: ak_v; ak_v; ak_vshift ve rshift ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str vmn ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := doit_v;
    id_pp_asm := pp_armv8a_vop vmn [:: pp_vec ve sz; pp_vec ve sz; pp_full U8 ];
    id_valid := armv8a_vop_valid vmn ve sz;
    id_wf := refl_equal;
  |}.

(* [MOV (vector)] ARM DDI 0487 M.a, C7.2
   Move vector. This is an alias of ORR (vector, register) with the same
   source register twice.
   Syntax: MOV <Vd>.<T>, <Vn>.<T>  ==  ORR <Vd>.<T>, <Vn>.<T>, <Vn>.<T>
   Operation (after the ASL of ORR (vector, register)):
     constant bits(datasize) operand1 = V[n, datasize];
     constant bits(datasize) operand2 = V[m, datasize];
     V[d, datasize] = operand1 OR operand2;
*)
Definition armv8a_VMOV_semi sz (wn : word sz) : ty_w sz :=
  wn.

Definition armv8a_VMOV_instr (ve : velem) sz : instr_desc_t :=
  mk_vunop_instr VMOV ve DOIT (@armv8a_VMOV_semi sz).

(* [LDR (immediate, SIMD&FP)] ARM DDI 0487 M.a, C7.2
   Load SIMD&FP register (immediate offset). The Q form loads 128 bits.
   Syntax: LDR <Qt>, [<Xn|SP>{, #<pimm>}]
   Operation (after the ASL):
     constant bits(datasize) data = Mem[address, datasize DIV 8, accdesc];
     V[t, datasize] = data;
*)
Definition armv8a_VLDR_instr (ve : velem) sz : instr_desc_t :=
  let tin := [:: lword sz ] in
  let semi := @armv8a_VMOV_semi sz in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Eu 1 ];
    id_tout := [:: lword sz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := [:: [:: ak_v; [:: CAmem true None ] ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str VLDR ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_vop VLDR [:: pp_full sz; pp_full U64 ];
    id_valid := armv8a_vop_valid VLDR ve sz;
    id_wf := refl_equal;
  |}.

(* [STR (immediate, SIMD&FP)] ARM DDI 0487 M.a, C7.2
   Store SIMD&FP register (immediate offset). The Q form stores 128 bits.
   Syntax: STR <Qt>, [<Xn|SP>{, #<pimm>}]
   Operation (after the ASL):
     Mem[address, datasize DIV 8, accdesc] = V[t, datasize];
*)
Definition armv8a_VSTR_instr (ve : velem) sz : instr_desc_t :=
  let tin := [:: lword sz ] in
  let semi := @armv8a_VMOV_semi sz in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 0 ];
    id_tout := [:: lword sz ];
    id_out := [:: Eu 1 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := [:: [:: ak_v; [:: CAmem true None ] ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str VSTR ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_vop VSTR [:: pp_full sz; pp_full U64 ];
    id_valid := armv8a_vop_valid VSTR ve sz;
    id_wf := refl_equal;
  |}.

(* [AND (vector)] ARM DDI 0487 M.a, C7.2
   Bitwise AND (vector).
   Syntax: AND <Vd>.<T>, <Vn>.<T>, <Vm>.<T>
   Operation (after the ASL):
     constant bits(datasize) operand1 = V[n, datasize];
     constant bits(datasize) operand2 = V[m, datasize];
     V[d, datasize] = operand1 AND operand2;
*)
Definition armv8a_VAND_semi sz (wn wm : word sz) : ty_w sz :=
  wand wn wm.

Definition armv8a_VAND_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VAND ve DOIT (@armv8a_VAND_semi sz).

(* [BIC (vector, register)] ARM DDI 0487 M.a, C7.2
   Bitwise bit clear (vector, register).
   Syntax: BIC <Vd>.<T>, <Vn>.<T>, <Vm>.<T>
   Operation (after the ASL):
     constant bits(datasize) operand1 = V[n, datasize];
     constant bits(datasize) operand2 = NOT(V[m, datasize]);
     V[d, datasize] = operand1 AND operand2;
*)
Definition armv8a_VBIC_semi sz (wn wm : word sz) : ty_w sz :=
  wandn wm wn.

Definition armv8a_VBIC_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VBIC ve DOIT (@armv8a_VBIC_semi sz).

(* [ORR (vector, register)] ARM DDI 0487 M.a, C7.2
   Bitwise inclusive OR (vector, register).
   Syntax: ORR <Vd>.<T>, <Vn>.<T>, <Vm>.<T>
   Operation (after the ASL):
     constant bits(datasize) operand1 = V[n, datasize];
     constant bits(datasize) operand2 = V[m, datasize];
     V[d, datasize] = operand1 OR operand2;
*)
Definition armv8a_VORR_semi sz (wn wm : word sz) : ty_w sz :=
  wor wn wm.

Definition armv8a_VORR_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VORR ve DOIT (@armv8a_VORR_semi sz).

(* [ORN (vector)] ARM DDI 0487 M.a, C7.2
   Bitwise inclusive OR NOT (vector).
   Syntax: ORN <Vd>.<T>, <Vn>.<T>, <Vm>.<T>
   Operation (after the ASL):
     constant bits(datasize) operand1 = V[n, datasize];
     constant bits(datasize) operand2 = NOT(V[m, datasize]);
     V[d, datasize] = operand1 OR operand2;
*)
Definition armv8a_VORN_semi sz (wn wm : word sz) : ty_w sz :=
  wor wn (wnot wm).

Definition armv8a_VORN_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VORN ve DOIT (@armv8a_VORN_semi sz).

(* [EOR (vector)] ARM DDI 0487 M.a, C7.2
   Bitwise exclusive OR (vector).
   Syntax: EOR <Vd>.<T>, <Vn>.<T>, <Vm>.<T>
   Operation (after the ASL):
     constant bits(datasize) operand1 = V[m, datasize];
     constant bits(datasize) operand2 = V[n, datasize];
     V[d, datasize] = operand1 EOR operand2;
*)
Definition armv8a_VEOR_semi sz (wn wm : word sz) : ty_w sz :=
  wxor wn wm.

Definition armv8a_VEOR_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VEOR ve DOIT (@armv8a_VEOR_semi sz).

(* [NOT] ARM DDI 0487 M.a, C7.2
   Bitwise NOT (vector). This instruction is used by the alias MVN.
   Syntax: NOT <Vd>.<T>, <Vn>.<T>
   Operation (after the ASL, per element, which amounts to the whole vector):
     element = Elem[operand, e, esize];
     Elem[result, e, esize] = NOT(element);
*)
Definition armv8a_VNOT_semi sz (wn : word sz) : ty_w sz :=
  wnot wn.

Definition armv8a_VNOT_instr (ve : velem) sz : instr_desc_t :=
  mk_vunop_instr VNOT ve DOIT (@armv8a_VNOT_semi sz).

(* BSL, BIT and BIF insert the bits of [Vn] into a result that otherwise
   takes the bits of another register, as selected by a mask: [Vd] for
   BSL, [Vm] for BIT and its complement for BIF.

   [BSL] ARM DDI 0487 M.a, C7.2
   Bitwise select.
   Syntax: BSL <Vd>.<T>, <Vn>.<T>, <Vm>.<T>
   Operation (after the ASL):
     constant bits(datasize) operand1 = V[d, datasize];
     constant bits(datasize) operand2 = V[n, datasize];
     constant bits(datasize) operand3 = V[m, datasize];
     V[d, datasize] = operand3 EOR ((operand3 EOR operand2) AND operand1);

   [BIT] ARM DDI 0487 M.a, C7.2
   Bitwise insert if true.
   Syntax: BIT <Vd>.<T>, <Vn>.<T>, <Vm>.<T>
   Operation (after the ASL):
     constant bits(datasize) operand1 = V[d, datasize];
     constant bits(datasize) operand2 = V[n, datasize];
     constant bits(datasize) operand3 = V[m, datasize];
     V[d, datasize] = operand1 EOR ((operand1 EOR operand2) AND operand3);

   [BIF] ARM DDI 0487 M.a, C7.2
   Bitwise insert if false.
   Syntax: BIF <Vd>.<T>, <Vn>.<T>, <Vm>.<T>
   Operation (after the ASL):
     constant bits(datasize) operand1 = V[d, datasize];
     constant bits(datasize) operand2 = V[n, datasize];
     constant bits(datasize) operand3 = V[m, datasize];
     V[d, datasize] = operand1 EOR ((operand1 EOR operand2) AND NOT(operand3));
*)
Definition armv8a_VBSL_semi sz (wd wn wm : word sz) : ty_w sz :=
  wxor wm (wand (wxor wm wn) wd).

Definition armv8a_VBSL_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_acc_instr VBSL ve DOIT (@armv8a_VBSL_semi sz).

Definition armv8a_VBIT_semi sz (wd wn wm : word sz) : ty_w sz :=
  wxor wd (wand (wxor wd wn) wm).

Definition armv8a_VBIT_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_acc_instr VBIT ve DOIT (@armv8a_VBIT_semi sz).

Definition armv8a_VBIF_semi sz (wd wn wm : word sz) : ty_w sz :=
  wxor wd (wand (wxor wd wn) (wnot wm)).

Definition armv8a_VBIF_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_acc_instr VBIF ve DOIT (@armv8a_VBIF_semi sz).

(* The lane-wise operations below read and write vectors of [elements]
   lanes of [esize] bits: [ve] is [esize] and [sz] is [datasize].

   [ADD (vector)] ARM DDI 0487 M.a, C7.2
   Add (vector).
   Syntax: ADD <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [SUB (vector)] ARM DDI 0487 M.a, C7.2
   Subtract (vector).
   Syntax: SUB <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   <T> is 8B, 16B, 4H, 8H, 2S, 4S or 2D (1D is reserved).
   Operation, where [sub_op] is FALSE for ADD and TRUE for SUB:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand1 = V[n, datasize];
     bits(datasize) operand2 = V[m, datasize];
     bits(datasize) result;
     bits(esize) element1;
     bits(esize) element2;

     for e = 0 to elements-1
         element1 = Elem[operand1, e, esize];
         element2 = Elem[operand2, e, esize];
         if sub_op then
             Elem[result, e, esize] = element1 - element2;
         else
             Elem[result, e, esize] = element1 + element2;

     V[d, datasize] = result;
*)
Definition armv8a_VADD_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  lift2_vec ve +%w sz wn wm.

Definition armv8a_VADD_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VADD ve DOIT (@armv8a_VADD_semi ve sz).

Definition armv8a_VSUB_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  lift2_vec ve (fun x y => x - y)%w sz wn wm.

Definition armv8a_VSUB_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VSUB ve DOIT (@armv8a_VSUB_semi ve sz).

(* [MUL (vector)] ARM DDI 0487 M.a, C7.2
   Multiply (vector).
   Syntax: MUL <Vd>.<T>, <Vn>.<T>, <Vm>.<T>
   <T> is 8B, 16B, 4H, 8H, 2S or 4S (64-bit lanes are reserved).
   Operation, where [poly] is FALSE (TRUE is PMUL):
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand1 = V[n, datasize];
     bits(datasize) operand2 = V[m, datasize];
     bits(datasize) result;
     bits(esize) element1;
     bits(esize) element2;
     bits(esize) product;

     for e = 0 to elements-1
         element1 = Elem[operand1, e, esize];
         element2 = Elem[operand2, e, esize];
         if poly then
             product = PolynomialMult(element1, element2)<esize-1:0>;
         else
             product = (UInt(element1) * UInt(element2))<esize-1:0>;
         Elem[result, e, esize] = product;

     V[d, datasize] = result;
*)
Definition armv8a_VMUL_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  lift2_vec ve *%w sz wn wm.

Definition armv8a_VMUL_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VMUL ve DOIT (@armv8a_VMUL_semi ve sz).

(* [NEG (vector)] ARM DDI 0487 M.a, C7.2
   Negate (vector).
   Syntax: NEG <Vd>.<T>, <Vn>.<T>

   [ABS] ARM DDI 0487 M.a, C7.2
   Absolute value (vector).
   Syntax: ABS <Vd>.<T>, <Vn>.<T>

   <T> is 8B, 16B, 4H, 8H, 2S, 4S or 2D (1D is reserved).
   Operation, where [neg] is TRUE for NEG and FALSE for ABS:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand = V[n, datasize];
     bits(datasize) result;
     integer element;

     for e = 0 to elements-1
         element = SInt(Elem[operand, e, esize]);
         if neg then
             element = -element;
         else
             element = Abs(element);
         Elem[result, e, esize] = element<esize-1:0>;

     V[d, datasize] = result;
*)
Definition armv8a_VNEG_semi (ve : velem) sz (wn : word sz) : ty_w sz :=
  lift1_vec ve (fun x => wrepr ve (- wsigned x)) sz wn.

Definition armv8a_VNEG_instr (ve : velem) sz : instr_desc_t :=
  mk_vunop_instr VNEG ve DOIT (@armv8a_VNEG_semi ve sz).

Definition armv8a_VABS_semi (ve : velem) sz (wn : word sz) : ty_w sz :=
  wabs ve wn.

Definition armv8a_VABS_instr (ve : velem) sz : instr_desc_t :=
  mk_vunop_instr VABS ve DOIT (@armv8a_VABS_semi ve sz).

(* [SMAX] ARM DDI 0487 M.a, C7.2
   Signed Maximum (vector).
   Syntax: SMAX <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [SMIN] ARM DDI 0487 M.a, C7.2
   Signed Minimum (vector).
   Syntax: SMIN <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [UMAX] ARM DDI 0487 M.a, C7.2
   Unsigned Maximum (vector).
   Syntax: UMAX <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [UMIN] ARM DDI 0487 M.a, C7.2
   Unsigned Minimum (vector).
   Syntax: UMIN <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   <T> is 8B, 16B, 4H, 8H, 2S or 4S (64-bit lanes are reserved).
   Operation, where [unsigned] is TRUE for UMAX and UMIN, and [minimum] is
   TRUE for SMIN and UMIN:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand1 = V[n, datasize];
     bits(datasize) operand2 = V[m, datasize];
     bits(datasize) result;
     integer element1;
     integer element2;
     integer maxmin;

     for e = 0 to elements-1
         element1 = Int(Elem[operand1, e, esize], unsigned);
         element2 = Int(Elem[operand2, e, esize], unsigned);
         maxmin = if minimum then Min(element1, element2) else Max(element1, element2);
         Elem[result, e, esize] = maxmin<esize-1:0>;

     V[d, datasize] = result;
*)
Definition armv8a_VSMAX_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  wmax Signed ve wn wm.

Definition armv8a_VSMAX_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VSMAX ve DOIT (@armv8a_VSMAX_semi ve sz).

Definition armv8a_VSMIN_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  wmin Signed ve wn wm.

Definition armv8a_VSMIN_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VSMIN ve DOIT (@armv8a_VSMIN_semi ve sz).

Definition armv8a_VUMAX_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  wmax Unsigned ve wn wm.

Definition armv8a_VUMAX_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VUMAX ve DOIT (@armv8a_VUMAX_semi ve sz).

Definition armv8a_VUMIN_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  wmin Unsigned ve wn wm.

Definition armv8a_VUMIN_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VUMIN ve DOIT (@armv8a_VUMIN_semi ve sz).

(* The shifts by immediate below have every arrangement of the lane-wise
   operations (1D is reserved). The amount [shift] of a left shift (SHL,
   SLI) is in 0..esize-1, that of a right shift (USHR, SSHR, SRI, USRA,
   SSRA) in 1..esize; [CAimmC_armv8a_vshift_amount] checks it. A right
   shift by [esize] gives zero (USHR) or the sign of the lane (SSHR), which
   [wshr] and [wsar] also give.

   [SHL] ARM DDI 0487 M.a, C7.2
   Shift left (immediate).
   Syntax: SHL <Vd>.<T>, <Vn>.<T>, #<shift>
   Decode: integer shift = UInt(immh:immb) - esize;
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand  = V[n, datasize];
     bits(datasize) result;

     for e = 0 to elements-1
         Elem[result, e, esize] = LSL(Elem[operand, e, esize], shift);

     V[d, datasize] = result;
*)
Definition armv8a_VSHL_semi (ve : velem) sz (wn : word sz) (shift : word U8)
  : ty_w sz :=
  lift1_vec ve (fun x => wshl x (wunsigned shift)) sz wn.

Definition armv8a_VSHL_instr (ve : velem) sz : instr_desc_t :=
  mk_vshift_instr VSHL ve false DOIT (@armv8a_VSHL_semi ve sz).

(* [USHR] ARM DDI 0487 M.a, C7.2
   Unsigned shift right (immediate).
   Syntax: USHR <Vd>.<T>, <Vn>.<T>, #<shift>

   [SSHR] ARM DDI 0487 M.a, C7.2
   Signed shift right (immediate).
   Syntax: SSHR <Vd>.<T>, <Vn>.<T>, #<shift>

   [USRA] ARM DDI 0487 M.a, C7.2
   Unsigned shift right and accumulate (immediate).
   Syntax: USRA <Vd>.<T>, <Vn>.<T>, #<shift>

   [SSRA] ARM DDI 0487 M.a, C7.2
   Signed shift right and accumulate (immediate).
   Syntax: SSRA <Vd>.<T>, <Vn>.<T>, #<shift>

   Decode: integer shift = (esize * 2) - UInt(immh:immb);
           boolean unsigned = (U == '1');
           boolean round = (o1 == '1');
           boolean accumulate = (o0 == '1');
   where [unsigned] is TRUE for USHR and USRA, [round] is FALSE (TRUE is
   URSHR, SRSHR, URSRA and SRSRA), and [accumulate] is TRUE for USRA and
   SSRA.
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand  = V[n, datasize];
     bits(datasize) operand2;
     bits(datasize) result;
     integer round_const = if round then (1 << (shift - 1)) else 0;
     integer element;

     operand2 = if accumulate then V[d, datasize] else Zeros(datasize);
     for e = 0 to elements-1
         element = (Int(Elem[operand, e, esize], unsigned) + round_const) >> shift;
         Elem[result, e, esize] = Elem[operand2, e, esize] + element<esize-1:0>;

     V[d, datasize] = result;
*)
Definition armv8a_VUSHR_semi (ve : velem) sz (wn : word sz) (shift : word U8)
  : ty_w sz :=
  lift1_vec ve (fun x => wshr x (wunsigned shift)) sz wn.

Definition armv8a_VUSHR_instr (ve : velem) sz : instr_desc_t :=
  mk_vshift_instr VUSHR ve true DOIT (@armv8a_VUSHR_semi ve sz).

Definition armv8a_VSSHR_semi (ve : velem) sz (wn : word sz) (shift : word U8)
  : ty_w sz :=
  lift1_vec ve (fun x => wsar x (wunsigned shift)) sz wn.

Definition armv8a_VSSHR_instr (ve : velem) sz : instr_desc_t :=
  mk_vshift_instr VSSHR ve true DOIT (@armv8a_VSSHR_semi ve sz).

Definition armv8a_VUSRA_semi
  (ve : velem) sz (wd wn : word sz) (shift : word U8) : ty_w sz :=
  lift2_vec ve (fun d x => d + wshr x (wunsigned shift))%w sz wd wn.

Definition armv8a_VUSRA_instr (ve : velem) sz : instr_desc_t :=
  mk_vshift_acc_instr VUSRA ve true DOIT (@armv8a_VUSRA_semi ve sz).

Definition armv8a_VSSRA_semi
  (ve : velem) sz (wd wn : word sz) (shift : word U8) : ty_w sz :=
  lift2_vec ve (fun d x => d + wsar x (wunsigned shift))%w sz wd wn.

Definition armv8a_VSSRA_instr (ve : velem) sz : instr_desc_t :=
  mk_vshift_acc_instr VSSRA ve true DOIT (@armv8a_VSSRA_semi ve sz).

(* SLI and SRI keep the bits of each lane of the destination that the
   shifted lane does not cover: the [shift] low bits for SLI, the [shift]
   high bits for SRI (the whole lane for SRI #esize).

   [SLI] ARM DDI 0487 M.a, C7.2
   Shift left and insert (immediate).
   Syntax: SLI <Vd>.<T>, <Vn>.<T>, #<shift>
   Decode: integer shift = UInt(immh:immb) - esize;
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand  = V[n, datasize];
     bits(datasize) operand2 = V[d, datasize];
     bits(datasize) result;
     bits(esize) mask = LSL(Ones(esize), shift);
     bits(esize) shifted;

     for e = 0 to elements-1
         shifted = LSL(Elem[operand, e, esize], shift);
         Elem[result, e, esize] = (Elem[operand2, e, esize] AND NOT(mask)) OR shifted;
     V[d, datasize] = result;

   [SRI] ARM DDI 0487 M.a, C7.2
   Shift right and insert (immediate).
   Syntax: SRI <Vd>.<T>, <Vn>.<T>, #<shift>
   Decode: integer shift = (esize * 2) - UInt(immh:immb);
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand  = V[n, datasize];
     bits(datasize) operand2 = V[d, datasize];
     bits(datasize) result;
     bits(esize) mask = LSR(Ones(esize), shift);
     bits(esize) shifted;

     for e = 0 to elements-1
         shifted = LSR(Elem[operand, e, esize], shift);
         Elem[result, e, esize] = (Elem[operand2, e, esize] AND NOT(mask)) OR shifted;
     V[d, datasize] = result;
*)
Definition armv8a_VSLI_semi
  (ve : velem) sz (wd wn : word sz) (shift : word U8) : ty_w sz :=
  let sh := wunsigned shift in
  lift2_vec ve (fun d x => wor (wandn (wshl (wrepr _ (-1)) sh) d) (wshl x sh)) sz wd wn.

Definition armv8a_VSLI_instr (ve : velem) sz : instr_desc_t :=
  mk_vshift_acc_instr VSLI ve false DOIT (@armv8a_VSLI_semi ve sz).

Definition armv8a_VSRI_semi
  (ve : velem) sz (wd wn : word sz) (shift : word U8) : ty_w sz :=
  let sh := wunsigned shift in
  lift2_vec ve (fun d x => wor (wandn (wshr (wrepr _ (-1)) sh) d) (wshr x sh)) sz wd wn.

Definition armv8a_VSRI_instr (ve : velem) sz : instr_desc_t :=
  mk_vshift_acc_instr VSRI ve true DOIT (@armv8a_VSRI_semi ve sz).

(* [USHL] ARM DDI 0487 M.a, C7.2
   Unsigned shift left (register).
   Syntax: USHL <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [SSHL] ARM DDI 0487 M.a, C7.2
   Signed shift left (register).
   Syntax: SSHL <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   <T> is 8B, 16B, 4H, 8H, 2S, 4S or 2D (1D is reserved).
   Decode: boolean unsigned = (U == '1');
           boolean rounding = (R == '1');
           boolean saturating = (S == '1');
   where [unsigned] is TRUE for USHL, and [rounding] and [saturating] are
   FALSE (TRUE is URSHL, SRSHL, UQSHL, SQSHL, UQRSHL and SQRSHL).
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand1 = V[n, datasize];
     bits(datasize) operand2 = V[m, datasize];
     bits(datasize) result;

     boolean sat;

     for e = 0 to elements-1
         integer element = Int(Elem[operand1, e, esize], unsigned);
         integer shift = SInt(Elem[operand2, e, esize]<7:0>);
         if shift >= 0 then // left shift
             element = element << shift;
         else               // right shift
             shift = -shift;
             if rounding then
                 element = (element + (1 << (shift - 1))) >> shift;
             else
                 element = element >> shift;

         if saturating then
             (Elem[result, e, esize], sat) = SatQ(element, esize, unsigned);
             if sat then FPSR.QC = '1';
         else
             Elem[result, e, esize] = element<esize-1:0>;

     V[d, datasize] = result;

   Each lane of [Vn] is shifted by the signed low byte of the same lane of
   [Vm], in -128..127: to the left if it is nonnegative, to the right
   otherwise. The low [esize] bits of a left shift do not depend on the
   signedness of the element, and are zero for a shift by [esize] or more,
   as [wshl] gives. A right shift by [esize] or more gives zero (USHL) or
   the sign of the lane (SSHL), as [wshr] and [wsar] give. *)
Definition armv8a_vshl_reg
  (shr : forall ws, word ws -> Z -> word ws) {ve : velem} (x y : word ve)
  : word ve :=
  let shift := wsigned (zero_extend U8 y) in
  if (0 <=? shift)%Z then wshl x shift else shr ve x (- shift)%Z.

Definition armv8a_VUSHL_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  lift2_vec ve (armv8a_vshl_reg (@wshr)) sz wn wm.

Definition armv8a_VUSHL_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VUSHL ve DOIT (@armv8a_VUSHL_semi ve sz).

Definition armv8a_VSSHL_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  lift2_vec ve (armv8a_vshl_reg (@wsar)) sz wn wm.

Definition armv8a_VSSHL_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VSSHL ve DOIT (@armv8a_VSSHL_semi ve sz).

(* [EXT] ARM DDI 0487 M.a, C7.2
   Extract vector from pair of vectors.
   Syntax: EXT <Vd>.<T>, <Vn>.<T>, <Vm>.<T>, #<index>
   <T> is 8B or 16B; <index> is 0..7 for 8B and 0..15 for 16B, which
   [CAimmC_armv8a_vext_index] checks.
   Decode: integer position = UInt(imm4) << 3;
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) hi = V[m, datasize];
     bits(datasize) lo = V[n, datasize];
     bits(datasize*2) concat = hi : lo;

     V[d, datasize] = concat<(position+datasize)-1:position>;

   The bytes of [concat] from [index] on, of which [make_vec] keeps the
   [datasize] low bits. *)
Definition armv8a_VEXT_semi sz (wn wm : word sz) (index : word U8) : ty_w sz :=
  make_vec sz
    (drop (Z.to_nat (wunsigned index)) (split_vec U8 wn ++ split_vec U8 wm)).

Definition armv8a_VEXT_instr (ve : velem) sz : instr_desc_t :=
  let tin := [:: lword sz; lword sz; lword8 ] in
  let semi := @armv8a_VEXT_semi sz in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword sz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 4;
    id_args_kinds :=
      [:: [:: ak_v; ak_v; ak_v
            ; [:: CAimm (Some (CAimmC_armv8a_vext_index sz)) U8 ] ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str VEXT ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_vop VEXT [:: pp_vec ve sz; pp_vec ve sz; pp_vec ve sz; pp_full U8 ];
    id_valid := armv8a_vop_valid VEXT ve sz;
    id_wf := refl_equal;
  |}.

(* ZIP, UZP and TRN pick lanes from the two halves of a list of lanes
   [s] ([armv8a_vlanes_half]), or from its even or odd positions
   ([armv8a_vlanes_parity]): the first ones if [part] is false, the second
   ones if it is true. *)
Definition armv8a_vlanes_half (part : bool) {ve : wsize} (s : seq (word ve))
  : seq (word ve) :=
  let pairs := (size s)./2 in
  if part then drop pairs s else take pairs s.

Definition armv8a_vlanes_parity (part : bool) {ve : wsize} (s : seq (word ve))
  : seq (word ve) :=
  [seq nth 0%w s (2 * p + part) | p <- iota 0 (size s)./2 ].

(* [ZIP1] ARM DDI 0487 M.a, C7.2
   Zip vectors (primary).
   Syntax: ZIP1 <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [ZIP2] ARM DDI 0487 M.a, C7.2
   Zip vectors (secondary).
   Syntax: ZIP2 <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   <T> is 8B, 16B, 4H, 8H, 2S, 4S or 2D (1D is reserved).
   Decode: integer part = UInt(op);
           integer pairs = elements DIV 2;
   where [part] is 0 for ZIP1 and 1 for ZIP2.
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand1 = V[n, datasize];
     bits(datasize) operand2 = V[m, datasize];
     bits(datasize) result;

     integer base = part * pairs;

     for p = 0 to pairs-1
         Elem[result, 2*p+0, esize] = Elem[operand1, base+p, esize];
         Elem[result, 2*p+1, esize] = Elem[operand2, base+p, esize];

     V[d, datasize] = result;

   The lanes of the low (ZIP1) or high (ZIP2) halves of the sources,
   interleaved. *)
Definition armv8a_vzip (part : bool) (ve : velem) sz (wn wm : word sz)
  : word sz :=
  make_vec sz
    (interleave
       (armv8a_vlanes_half part (split_vec ve wn))
       (armv8a_vlanes_half part (split_vec ve wm))).

Definition armv8a_VZIP1_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  armv8a_vzip false ve wn wm.

Definition armv8a_VZIP1_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VZIP1 ve DOIT (@armv8a_VZIP1_semi ve sz).

Definition armv8a_VZIP2_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  armv8a_vzip true ve wn wm.

Definition armv8a_VZIP2_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VZIP2 ve DOIT (@armv8a_VZIP2_semi ve sz).

(* [UZP1] ARM DDI 0487 M.a, C7.2
   Unzip vectors (primary).
   Syntax: UZP1 <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [UZP2] ARM DDI 0487 M.a, C7.2
   Unzip vectors (secondary).
   Syntax: UZP2 <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   <T> is 8B, 16B, 4H, 8H, 2S, 4S or 2D (1D is reserved).
   Decode: integer part = UInt(op);
   where [part] is 0 for UZP1 and 1 for UZP2.
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operandl = V[n, datasize];
     bits(datasize) operandh = V[m, datasize];
     bits(datasize) result;

     bits(datasize*2) zipped = operandh:operandl;
     for e = 0 to elements-1
         Elem[result, e, esize] = Elem[zipped, 2*e+part, esize];

     V[d, datasize] = result;

   The even (UZP1) or odd (UZP2) lanes of the concatenation of the
   sources. *)
Definition armv8a_vuzp (part : bool) (ve : velem) sz (wn wm : word sz)
  : word sz :=
  make_vec sz (armv8a_vlanes_parity part (split_vec ve wn ++ split_vec ve wm)).

Definition armv8a_VUZP1_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  armv8a_vuzp false ve wn wm.

Definition armv8a_VUZP1_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VUZP1 ve DOIT (@armv8a_VUZP1_semi ve sz).

Definition armv8a_VUZP2_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  armv8a_vuzp true ve wn wm.

Definition armv8a_VUZP2_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VUZP2 ve DOIT (@armv8a_VUZP2_semi ve sz).

(* [TRN1] ARM DDI 0487 M.a, C7.2
   Transpose vectors (primary).
   Syntax: TRN1 <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [TRN2] ARM DDI 0487 M.a, C7.2
   Transpose vectors (secondary).
   Syntax: TRN2 <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   <T> is 8B, 16B, 4H, 8H, 2S, 4S or 2D (1D is reserved).
   Decode: integer part = UInt(op);
           integer pairs = elements DIV 2;
   where [part] is 0 for TRN1 and 1 for TRN2.
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand1 = V[n, datasize];
     bits(datasize) operand2 = V[m, datasize];
     bits(datasize) result;

     for p = 0 to pairs-1
         Elem[result, 2*p+0, esize] = Elem[operand1, 2*p+part, esize];
         Elem[result, 2*p+1, esize] = Elem[operand2, 2*p+part, esize];

     V[d, datasize] = result;

   The even (TRN1) or odd (TRN2) lanes of the sources, interleaved. *)
Definition armv8a_vtrn (part : bool) (ve : velem) sz (wn wm : word sz)
  : word sz :=
  make_vec sz
    (interleave
       (armv8a_vlanes_parity part (split_vec ve wn))
       (armv8a_vlanes_parity part (split_vec ve wm))).

Definition armv8a_VTRN1_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  armv8a_vtrn false ve wn wm.

Definition armv8a_VTRN1_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VTRN1 ve DOIT (@armv8a_VTRN1_semi ve sz).

Definition armv8a_VTRN2_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  armv8a_vtrn true ve wn wm.

Definition armv8a_VTRN2_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VTRN2 ve DOIT (@armv8a_VTRN2_semi ve sz).

(* [REV16 (vector)] ARM DDI 0487 M.a, C7.2
   Reverse elements in 16-bit halfwords (vector).
   Syntax: REV16 <Vd>.<T>, <Vn>.<T>
   <T> is 8B or 16B.

   [REV32 (vector)] ARM DDI 0487 M.a, C7.2
   Reverse elements in 32-bit words (vector).
   Syntax: REV32 <Vd>.<T>, <Vn>.<T>
   <T> is 8B, 16B, 4H or 8H.

   [REV64] ARM DDI 0487 M.a, C7.2
   Reverse elements in 64-bit doublewords (vector).
   Syntax: REV64 <Vd>.<T>, <Vn>.<T>
   <T> is 8B, 16B, 4H, 8H, 2S or 4S.

   Decode: integer container_size;
           case op of
               when '10' container_size = 16;
               when '01' container_size = 32;
               when '00' container_size = 64;

           integer containers = datasize DIV container_size;
           integer elements_per_container = container_size DIV esize;
   where [container_size] is 16 for REV16, 32 for REV32 and 64 for REV64.
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand = V[n, datasize];
     bits(datasize) result;
     integer element = 0;
     integer rev_element;
     for c = 0 to containers-1
         rev_element = (element + elements_per_container) - 1;
         for e = 0 to elements_per_container-1
             Elem[result, rev_element, esize] = Elem[operand, element, esize];
             element = element + 1;
             rev_element = rev_element - 1;

     V[d, datasize] = result;

   The lanes of each container, in reverse order (for byte lanes, [wbswap]
   on each container). *)
Definition armv8a_vrev (container : wsize) (ve : velem) sz (wn : word sz)
  : word sz :=
  lift1_vec container (fun c => make_vec container (rev (split_vec ve c))) sz wn.

Definition armv8a_VREV16_semi (ve : velem) sz (wn : word sz) : ty_w sz :=
  armv8a_vrev U16 ve wn.

Definition armv8a_VREV16_instr (ve : velem) sz : instr_desc_t :=
  mk_vunop_instr VREV16 ve DOIT (@armv8a_VREV16_semi ve sz).

Definition armv8a_VREV32_semi (ve : velem) sz (wn : word sz) : ty_w sz :=
  armv8a_vrev U32 ve wn.

Definition armv8a_VREV32_instr (ve : velem) sz : instr_desc_t :=
  mk_vunop_instr VREV32 ve DOIT (@armv8a_VREV32_semi ve sz).

Definition armv8a_VREV64_semi (ve : velem) sz (wn : word sz) : ty_w sz :=
  armv8a_vrev U64 ve wn.

Definition armv8a_VREV64_instr (ve : velem) sz : instr_desc_t :=
  mk_vunop_instr VREV64 ve DOIT (@armv8a_VREV64_semi ve sz).

(* [TBL] ARM DDI 0487 M.a, C7.2
   Table vector lookup, single register table variant: the table is the
   128-bit register [Vn], the indices and the result have <Ta>.
   Syntax: TBL <Vd>.<Ta>, { <Vn>.16B }, <Vm>.<Ta>
   <Ta> is 8B or 16B.
   Decode: integer elements = datasize DIV 8;
           integer regs = UInt(len) + 1;
           boolean is_tbl = (op == '0');
   where [regs] is 1 (2, 3 and 4 are the multiple register table variants)
   and [is_tbl] is TRUE (FALSE is TBX).
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) indices = V[m, datasize];
     bits(128*regs) table = Zeros(128*regs);
     bits(datasize) result;
     integer index;

     // Create table from registers
     for i = 0 to regs - 1
         table<128*i+127:128*i> = V[n, 128];
         n = (n + 1) MOD 32;

     result = if is_tbl then Zeros(datasize) else V[d, datasize];
     for i = 0 to elements - 1
         index = UInt(Elem[indices, i, 8]);
         if index < 16 * regs then
             Elem[result, i, 8] = Elem[table, index, 8];

     V[d, datasize] = result;

   An index out of the table (16 or more) gives a zero byte. *)
Definition armv8a_vtbl1 (table : seq u8) (index : u8) : u8 :=
  let i := wunsigned index in
  if (i <? 16)%Z then nth 0%w table (Z.to_nat i) else 0%w.

Definition armv8a_VTBL_semi sz (table : word U128) (indices : word sz)
  : ty_w sz :=
  make_vec sz (map (armv8a_vtbl1 (split_vec U8 table)) (split_vec U8 indices)).

(* The table register is printed as a list, with its 128-bit arrangement,
   [{ v1.16b }], whatever the size of the indices. *)
Definition armv8a_VTBL_instr (ve : velem) sz : instr_desc_t :=
  let tin := [:: lword U128; lword sz ] in
  let semi := @armv8a_VTBL_semi sz in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword sz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := [:: [:: ak_v; ak_v; ak_v ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str VTBL ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_vop VTBL [:: pp_vec ve sz; pp_reglist U8 U128; pp_vec ve sz ];
    id_valid := armv8a_vop_valid VTBL ve sz;
    id_wf := refl_equal;
  |}.

(* The comparisons below set each lane of the result to all ones if the
   test on the lanes of the sources passes, to zero otherwise, as [wpcmps1]
   (signed) and [armv8a_vcmpu1] (unsigned).

   [CMEQ (register)] ARM DDI 0487 M.a, C7.2
   Compare bitwise equal (vector).
   Syntax: CMEQ <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [CMTST] ARM DDI 0487 M.a, C7.2
   Compare bitwise test bits nonzero (vector).
   Syntax: CMTST <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   <T> is 8B, 16B, 4H, 8H, 2S, 4S or 2D (1D is reserved).
   Decode: boolean and_test = (U == '0');
   where [and_test] is FALSE for CMEQ and TRUE for CMTST.
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand1 = V[n, datasize];
     bits(datasize) operand2 = V[m, datasize];
     bits(datasize) result;
     bits(esize) element1;
     bits(esize) element2;
     boolean test_passed;

     for e = 0 to elements-1
         element1 = Elem[operand1, e, esize];
         element2 = Elem[operand2, e, esize];
         if and_test then
             test_passed = !IsZero(element1 AND element2);
         else
             test_passed = (element1 == element2);
         Elem[result, e, esize] = if test_passed then Ones(esize) else Zeros(esize);

     V[d, datasize] = result;

   CMTST is the complement of the lane-wise comparison with zero of the
   bitwise AND of the sources. *)
Definition armv8a_VCMEQ_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  wpcmpeq ve wn wm.

Definition armv8a_VCMEQ_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VCMEQ ve DOIT (@armv8a_VCMEQ_semi ve sz).

Definition armv8a_VCMTST_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  wnot (wpcmpeq ve (wand wn wm) 0%w).

Definition armv8a_VCMTST_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VCMTST ve DOIT (@armv8a_VCMTST_semi ve sz).

(* [CMGT (register)] ARM DDI 0487 M.a, C7.2
   Compare signed greater than (vector).
   Syntax: CMGT <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [CMGE (register)] ARM DDI 0487 M.a, C7.2
   Compare signed greater than or equal (vector).
   Syntax: CMGE <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [CMHI (register)] ARM DDI 0487 M.a, C7.2
   Compare unsigned higher (vector).
   Syntax: CMHI <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [CMHS (register)] ARM DDI 0487 M.a, C7.2
   Compare unsigned higher or same (vector).
   Syntax: CMHS <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   <T> is 8B, 16B, 4H, 8H, 2S, 4S or 2D (1D is reserved).
   Decode: boolean unsigned = (U == '1');
           boolean cmp_eq = (eq == '1');
   where [unsigned] is TRUE for CMHI and CMHS, and [cmp_eq] is TRUE for
   CMGE and CMHS.
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand1 = V[n, datasize];
     bits(datasize) operand2 = V[m, datasize];
     bits(datasize) result;
     integer element1;
     integer element2;
     boolean test_passed;

     for e = 0 to elements-1
         element1 = Int(Elem[operand1, e, esize], unsigned);
         element2 = Int(Elem[operand2, e, esize], unsigned);
         test_passed = if cmp_eq then element1 >= element2 else element1 > element2;
         Elem[result, e, esize] = if test_passed then Ones(esize) else Zeros(esize);

     V[d, datasize] = result;
*)
Definition armv8a_vcmpu1 (cmp : Z -> Z -> bool) {ve : wsize} (x y : word ve)
  : word ve :=
  if cmp (wunsigned x) (wunsigned y) then wrepr ve (-1) else 0%w.

Definition armv8a_VCMGT_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  wpcmpgt ve wn wm.

Definition armv8a_VCMGT_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VCMGT ve DOIT (@armv8a_VCMGT_semi ve sz).

Definition armv8a_VCMGE_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  lift2_vec ve (wpcmps1 Z.geb) sz wn wm.

Definition armv8a_VCMGE_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VCMGE ve DOIT (@armv8a_VCMGE_semi ve sz).

Definition armv8a_VCMHI_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  lift2_vec ve (armv8a_vcmpu1 Z.gtb) sz wn wm.

Definition armv8a_VCMHI_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VCMHI ve DOIT (@armv8a_VCMHI_semi ve sz).

Definition armv8a_VCMHS_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  lift2_vec ve (armv8a_vcmpu1 Z.geb) sz wn wm.

Definition armv8a_VCMHS_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VCMHS ve DOIT (@armv8a_VCMHS_semi ve sz).

(* The copies below move lanes between vector registers and general
   registers. An index is an 8-bit immediate that addresses a lane of a
   whole 128-bit register, whatever the size of the vector: see
   [check_lane_index]. The assembly printer shows the register of such a
   lane as an element followed by the index ([v1.s[2]]), and not the index
   as an operand of its own. In the arguments, as in the assembly, each
   index follows the register it refers to, and the shape [pp_lane] takes
   both. A general register is W for lanes up to 32 bits, X for 64-bit
   lanes; its value is the lane, which the intrinsics take and return at the
   size of the lane.

   [Elem[operand, index, esize]], the lane [index] of [operand]. *)
Definition armv8a_velem (ve : velem) (v : u128) (index : u8) : word ve :=
  nth (0%w : word ve) (split_vec ve v) (Z.to_nat (wunsigned index)).

Definition ak_lane (ve : velem) : arg_kinds :=
  [:: CAimm (Some (CAimmC_armv8a_lane_index ve)) U8 ].

Definition armv8a_gpr_size (ve : velem) : wsize :=
  if ve is VE64 then U64 else U32.

(* [DUP (general)] ARM DDI 0487 M.a, C7.2
   Duplicate general-purpose register to vector.
   Syntax: DUP <Vd>.<T>, <R><n>
   <T> is 8B, 16B, 4H, 8H, 2S, 4S or 2D (1D is reserved); <R> is W, or X
   for 2D.
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(esize) element = X[n, esize];
     bits(datasize) result;

     for e = 0 to elements-1
         Elem[result, e, esize] = element;
     V[d, datasize] = result;
*)
Definition armv8a_VDUP_semi (ve : velem) sz (wn : word ve) : ty_w sz :=
  wpbroadcast sz wn.

Definition armv8a_VDUP_instr (ve : velem) sz : instr_desc_t :=
  let tin := [:: lword ve ] in
  let semi := @armv8a_VDUP_semi ve sz in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: lword sz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 2;
    id_args_kinds := [:: [:: ak_v; [:: CAreg ] ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str VDUP ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_vop VDUP [:: pp_vec ve sz; pp_full (armv8a_gpr_size ve) ];
    id_valid := armv8a_vop_valid VDUP ve sz;
    id_wf := refl_equal;
  |}.

(* [DUP (element)] ARM DDI 0487 M.a, C7.2
   Duplicate vector element to vector.
   Syntax: DUP <Vd>.<T>, <Vn>.<Ts>[<index>]
   <T> is 8B, 16B, 4H, 8H, 2S, 4S or 2D (1D is reserved); <Ts> is B, H, S
   or D, and <index> is 0..15, 0..7, 0..3 or 0..1 respectively.
   Decode: integer idxdsize = if imm5<4> == '1' then 128 else 64;
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(idxdsize) operand = V[n, idxdsize];
     bits(datasize) result;
     bits(esize) element;

     element = Elem[operand, index, esize];
     for e = 0 to elements-1
         Elem[result, e, esize] = element;
     V[d, datasize] = result;

   The index selects a lane of the whole source register: [idxdsize] is 64
   exactly when that lane is in its low half. *)
Definition armv8a_VDUPLANE_semi (ve : velem) sz (wn : word U128) (index : word U8)
  : ty_w sz :=
  wpbroadcast sz (armv8a_velem ve wn index).

Definition armv8a_VDUPLANE_instr (ve : velem) sz : instr_desc_t :=
  let tin := [:: lword U128; lword8 ] in
  let semi := @armv8a_VDUPLANE_semi ve sz in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword sz ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := [:: [:: ak_v; ak_v; ak_lane ve ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str VDUPLANE ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_vop VDUPLANE [:: pp_vec ve sz; pp_lane ve ];
    id_valid := armv8a_vop_valid VDUPLANE ve sz;
    id_wf := refl_equal;
  |}.

(* [INS (general)] ARM DDI 0487 M.a, C7.2
   Insert vector element from general-purpose register.
   Syntax: INS <Vd>.<Ts>[<index>], <R><n>
   <Ts> is B, H, S or D, and <index> is 0..15, 0..7, 0..3 or 0..1
   respectively; <R> is W, or X for D.
   Decode: integer datasize = 128;
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(esize) element = X[n, esize];
     bits(datasize) result;

     result = V[d, datasize];
     Elem[result, index, esize] = element;
     V[d, datasize] = result;

   The intrinsic takes the destination, whose other lanes are kept, the
   index, which follows the register it refers to, and the general
   register. *)
Definition armv8a_VINS_semi (ve : velem) (wd : word U128) (index : word U8)
  (wn : word ve) : ty_w U128 :=
  wpinsr wd wn index.

Definition armv8a_VINS_instr (ve : velem) sz : instr_desc_t :=
  let tin := [:: lword U128; lword8; lword ve ] in
  let semi := @armv8a_VINS_semi ve in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1; Ea 2 ];
    id_tout := [:: lword U128 ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := [:: [:: ak_v; ak_lane ve; [:: CAreg ] ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str VINS ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_vop VINS [:: pp_lane ve; pp_full (armv8a_gpr_size ve) ];
    id_valid := armv8a_vop_valid VINS ve sz;
    id_wf := refl_equal;
  |}.

(* [INS (element)] ARM DDI 0487 M.a, C7.2
   Insert vector element from another vector element.
   Syntax: INS <Vd>.<Ts>[<index1>], <Vn>.<Ts>[<index2>]
   <Ts> is B, H, S or D, and each index is 0..15, 0..7, 0..3 or 0..1
   respectively.
   Decode: integer dst_index = UInt(imm5<4:size+1>);
           integer src_index = UInt(imm4<3:size>);
           integer idxdsize = if imm4<3> == '1' then 128 else 64;
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(idxdsize) operand = V[n, idxdsize];
     bits(128) result;

     result = V[d, 128];
     Elem[result, dst_index, esize] = Elem[operand, src_index, esize];
     V[d, 128] = result;

   The intrinsic takes the destination, whose other lanes are kept, [index1],
   the source and [index2]: each index follows the register it refers to. *)
Definition armv8a_VINSLANE_semi (ve : velem) (wd : word U128)
  (dst_index : word U8) (wn : word U128) (src_index : word U8) : ty_w U128 :=
  wpinsr wd (armv8a_velem ve wn src_index) dst_index.

Definition armv8a_VINSLANE_instr (ve : velem) sz : instr_desc_t :=
  let tin := [:: lword U128; lword8; lword U128; lword8 ] in
  let semi := @armv8a_VINSLANE_semi ve in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword U128 ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 4;
    id_args_kinds := [:: [:: ak_v; ak_lane ve; ak_v; ak_lane ve ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str VINSLANE ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_vop VINSLANE [:: pp_lane ve; pp_lane ve ];
    id_valid := armv8a_vop_valid VINSLANE ve sz;
    id_wf := refl_equal;
  |}.

(* [UMOV] ARM DDI 0487 M.a, C7.2
   Unsigned move vector element to general-purpose register.
   Syntax: UMOV <Wd>, <Vn>.<Ts>[<index>]
   Syntax: UMOV <Xd>, <Vn>.<Ts>[<index>]
   <Ts> is B, H or S for the 32-bit variant, with <index> 0..15, 0..7 or
   0..3 respectively, and D for the 64-bit one, with <index> 0..1.
   Decode: integer idxdsize = if imm5<4> == '1' then 128 else 64;
           integer datasize = if Q == '1' then 64 else 32;
   Operation:
     if index == 0 then
         CheckFPEnabled64();
     else
         CheckFPAdvSIMDEnabled64();
     bits(idxdsize) operand = V[n, idxdsize];

     X[d, datasize] = ZeroExtend(Elem[operand, index, esize], datasize);

   The result is the lane; the zero extension to the register is that of
   [MSB_CLEAR]: [(64u)#VUMOV_8u16(v, 5)]. *)
Definition armv8a_VUMOV_semi (ve : velem) (wn : word U128) (index : word U8)
  : ty_w ve :=
  armv8a_velem ve wn index.

Definition armv8a_VUMOV_instr (ve : velem) sz : instr_desc_t :=
  let tin := [:: lword U128; lword8 ] in
  let semi := @armv8a_VUMOV_semi ve in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword ve ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := [:: [:: [:: CAreg ]; ak_v; ak_lane ve ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str VUMOV ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_vop VUMOV [:: pp_full (armv8a_gpr_size ve); pp_lane ve ];
    id_valid := armv8a_vop_valid VUMOV ve sz;
    id_wf := refl_equal;
  |}.

(* [SMOV] ARM DDI 0487 M.a, C7.2
   Signed move vector element to general-purpose register, 64-bit variant.
   Syntax: SMOV <Xd>, <Vn>.<Ts>[<index>]
   <Ts> is B, H or S, and <index> is 0..15, 0..7 or 0..3 respectively.
   Decode: integer idxdsize = if imm5<4> == '1' then 128 else 64;
           integer datasize = if Q == '1' then 64 else 32;
   where Q is '1' (the 32-bit variant, SMOV <Wd>, is left out).
   Operation:
     if index == 0 then
         CheckFPEnabled64();
     else
         CheckFPAdvSIMDEnabled64();
     bits(idxdsize) operand = V[n, idxdsize];

     X[d, datasize] = SignExtend(Elem[operand, index, esize], datasize);
*)
Definition armv8a_VSMOV_semi (ve : velem) (wn : word U128) (index : word U8)
  : ty_w U64 :=
  sign_extend U64 (armv8a_velem ve wn index).

Definition armv8a_VSMOV_instr (ve : velem) sz : instr_desc_t :=
  let tin := [:: lword U128; lword8 ] in
  let semi := @armv8a_VSMOV_semi ve in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword U64 ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := [:: [:: [:: CAreg ]; ak_v; ak_lane ve ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str VSMOV ve sz;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm := pp_armv8a_vop VSMOV [:: pp_full U64; pp_lane ve ];
    id_valid := armv8a_vop_valid VSMOV ve sz;
    id_wf := refl_equal;
  |}.

(* The AES instructions operate on the 128-bit state of AES, as the x86
   ones, with the building blocks of waes.v: the state is the register, its
   bytes in increasing order of significance. AESE and AESD compute the
   first half of a round: they add the round key and apply ShiftRows and
   SubBytes, or their inverses; AESMC and AESIMC compute MixColumns and
   its inverse. So [AESMC(AESE(s, k0))] XOR [k1] is the x86
   [AESENC(s XOR k0, k1)]. AESE and AESD read their destination, which is
   the first argument of their intrinsic. They have the single arrangement
   16B, and their descriptions are those of 128-bit vectors of bytes.

   [AESE] ARM DDI 0487 M.a, C7.2
   AES single round encryption.
   Syntax: AESE <Vd>.16B, <Vn>.16B
   Decode: boolean decrypt = (D == '1');
   where D is '0'.
   Operation:
     AArch64.CheckFPAdvSIMDEnabled();

     bits(128) operand1 = V[d, 128];
     bits(128) operand2 = V[n, 128];
     bits(128) result;
     result = operand1 EOR operand2;
     if decrypt then
         result = AESInvSubBytes(AESInvShiftRows(result));
     else
         result = AESSubBytes(AESShiftRows(result));

     V[d, 128] = result;

   [AESD] ARM DDI 0487 M.a, C7.2
   AES single round decryption.
   Syntax: AESD <Vd>.16B, <Vn>.16B
   Decode and operation: those of AESE, where D is '1'.
*)
Definition armv8a_VAESE_semi (wd wn : word U128) : ty_w U128 :=
  SubBytes (ShiftRows (wxor wd wn)).

Definition armv8a_VAESE_instr : instr_desc_t :=
  mk_vunop_acc_instr VAESE VE8 DOIT armv8a_VAESE_semi.

Definition armv8a_VAESD_semi (wd wn : word U128) : ty_w U128 :=
  InvSubBytes (InvShiftRows (wxor wd wn)).

Definition armv8a_VAESD_instr : instr_desc_t :=
  mk_vunop_acc_instr VAESD VE8 DOIT armv8a_VAESD_semi.

(* [AESMC] ARM DDI 0487 M.a, C7.2
   AES mix columns.
   Syntax: AESMC <Vd>.16B, <Vn>.16B
   Decode: boolean decrypt = (D == '1');
   where D is '0'.
   Operation:
     AArch64.CheckFPAdvSIMDEnabled();

     bits(128) operand = V[n, 128];
     bits(128) result;
     if decrypt then
         result = AESInvMixColumns(operand);
     else
         result = AESMixColumns(operand);
     V[d, 128] = result;

   [AESIMC] ARM DDI 0487 M.a, C7.2
   AES inverse mix columns.
   Syntax: AESIMC <Vd>.16B, <Vn>.16B
   Decode and operation: those of AESMC, where D is '1'.
*)
Definition armv8a_VAESMC_semi (wn : word U128) : ty_w U128 :=
  MixColumns wn.

Definition armv8a_VAESMC_instr : instr_desc_t :=
  mk_vunop_instr VAESMC VE8 DOIT armv8a_VAESMC_semi.

Definition armv8a_VAESIMC_semi (wn : word U128) : ty_w U128 :=
  InvMixColumns wn.

Definition armv8a_VAESIMC_instr : instr_desc_t :=
  mk_vunop_instr VAESIMC VE8 DOIT armv8a_VAESIMC_semi.

(* [PMULL, PMULL2] ARM DDI 0487 M.a, C7.2
   Polynomial multiply long.
   Syntax: PMULL{2} <Vd>.<Ta>, <Vn>.<Tb>, <Vm>.<Tb>
   <Ta> is 8H or 1Q, <Tb> is 8B or 1D (PMULL), 16B or 2D (PMULL2); only the
   1Q form, with 1D or 2D sources, is described here.
   Decode:
     if size == '01' || size == '10' then UNDEFINED;
     if size == '11' && !HaveBit128PMULLExt() then UNDEFINED;
     integer esize = 8 << UInt(size);
     integer datasize = 64;
     integer part = UInt(Q);
     integer elements = datasize DIV esize;
   where size is '11', hence a single element of 64 bits, and Q is '0' for
   PMULL, '1' for PMULL2.
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize)   operand1 = Vpart[n, part, datasize];
     bits(datasize)   operand2 = Vpart[m, part, datasize];
     bits(2*datasize) result;
     bits(esize) element1;
     bits(esize) element2;

     for e = 0 to elements-1
         element1 = Elem[operand1, e, esize];
         element2 = Elem[operand2, e, esize];
         Elem[result, e, 2*esize] = PolynomialMult(element1, element2);

     V[d, 2*datasize] = result;

   [Vpart[n, part, 64]] is the low (part 0) or high (part 1) half of the
   register. The sources of PMULL are the low halves, [u64] values in V
   registers, printed [v1.1d], and those of PMULL2 are whole registers,
   printed [v1.2d]; the destination is printed [v0.1q].

   [PolynomialMult(op1, op2)] (shared pseudocode), the carry-less product
   of two polynomials over GF(2):
     func PolynomialMult{M, N}(op1 : bits(M), op2 : bits(N)) => bits(M+N)
     begin
         var result : bits(N + M) = Zeros{M+N};
         let extended_op2 : bits(N + M) = ZeroExtend{M+N}(op2);
         for i=0 to M-1 do
             if op1[i] == '1' then
                 result = result XOR LSL(extended_op2, i);
             end;
         end;
         return result;
     end;
*)
Definition armv8a_polynomial_mult (op1 op2 : u64) : u128 :=
  let extended_op2 := zero_extend U128 op2 in
  foldl
    (fun result i =>
       if wbit_n op1 i then wxor result (wshl extended_op2 (Z.of_nat i))
       else result)
    0%w (iota 0 64).

Definition armv8a_VPMULL_semi (wn wm : word U64) : ty_w U128 :=
  armv8a_polynomial_mult wn wm.

(* [Vpart[n, 1, 64]], the high half of a register. *)
Definition armv8a_vpart_high (w : u128) : u64 :=
  nth (0%w : u64) (split_vec U64 w) 1.

Definition armv8a_VPMULL2_semi (wn wm : word U128) : ty_w U128 :=
  armv8a_polynomial_mult (armv8a_vpart_high wn) (armv8a_vpart_high wm).

(* A polynomial multiplication [vmn Vd.1Q, Vn.<Tb>, Vm.<Tb>] of 64-bit lanes
   of sources of [sz] bits. *)
Definition mk_vpmull_instr vmn {sz} (semi : word sz -> word sz -> ty_w U128)
  : instr_desc_t :=
  let tin := [:: lword sz; lword sz ] in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword U128 ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 3;
    id_args_kinds := [:: [:: ak_v; ak_v; ak_v ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str vmn VE8 U128;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm :=
      pp_armv8a_vop vmn [:: pp_vec U128 U128; pp_vec U64 sz; pp_vec U64 sz ];
    id_valid := armv8a_vop_valid vmn VE8 U128;
    id_wf := refl_equal;
  |}.

Definition armv8a_VPMULL_instr : instr_desc_t :=
  mk_vpmull_instr VPMULL armv8a_VPMULL_semi.

Definition armv8a_VPMULL2_instr : instr_desc_t :=
  mk_vpmull_instr VPMULL2 armv8a_VPMULL2_semi.

(* EOR3, RAX1, XAR and BCAX compute the steps of the Keccak-f permutation
   of SHA-3 on 128-bit registers, as bytes (EOR3, BCAX) or as two 64-bit
   lanes (RAX1, XAR). They have a single arrangement, and their
   descriptions are those of 128-bit vectors. *)

(* A vector instruction [vmn Vd, Vn, Vm, Va] computing a function of its
   three 128-bit source registers. *)
Definition mk_vternop_instr vmn (semi : u128 -> u128 -> u128 -> ty_w U128)
  : instr_desc_t :=
  let tin := [:: lword U128; lword U128; lword U128 ] in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword U128 ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 4;
    id_args_kinds := [:: [:: ak_v; ak_v; ak_v; ak_v ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str vmn VE8 U128;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm :=
      pp_armv8a_vop vmn
        [:: pp_vec VE8 U128; pp_vec VE8 U128; pp_vec VE8 U128; pp_vec VE8 U128 ];
    id_valid := armv8a_vop_valid vmn VE8 U128;
    id_wf := refl_equal;
  |}.

(* [EOR3] ARM DDI 0487 M.a, C7.2
   Three-way exclusive-OR.
   Syntax: EOR3 <Vd>.16B, <Vn>.16B, <Vm>.16B, <Va>.16B
   Operation:
     AArch64.CheckFPAdvSIMDEnabled();

     bits(128) Vm = V[m, 128];
     bits(128) Vn = V[n, 128];
     bits(128) Va = V[a, 128];
     V[d, 128] = Vn EOR Vm EOR Va;

   [BCAX] ARM DDI 0487 M.a, C7.2
   Bit clear and exclusive-OR.
   Syntax: BCAX <Vd>.16B, <Vn>.16B, <Vm>.16B, <Va>.16B
   Operation:
     AArch64.CheckFPAdvSIMDEnabled();

     bits(128) Vm = V[m, 128];
     bits(128) Vn = V[n, 128];
     bits(128) Va = V[a, 128];
     V[d, 128] = Vn EOR (Vm AND NOT(Va));
*)
Definition armv8a_VEOR3_semi (wn wm wa : u128) : ty_w U128 :=
  wxor (wxor wn wm) wa.

Definition armv8a_VEOR3_instr : instr_desc_t :=
  mk_vternop_instr VEOR3 armv8a_VEOR3_semi.

Definition armv8a_VBCAX_semi (wn wm wa : u128) : ty_w U128 :=
  wxor wn (wand wm (wnot wa)).

Definition armv8a_VBCAX_instr : instr_desc_t :=
  mk_vternop_instr VBCAX armv8a_VBCAX_semi.

(* [RAX1] ARM DDI 0487 M.a, C7.2
   Rotate and exclusive-OR.
   Syntax: RAX1 <Vd>.2D, <Vn>.2D, <Vm>.2D
   Operation:
     AArch64.CheckFPAdvSIMDEnabled();

     bits(128) Vm = V[m, 128];
     bits(128) Vn = V[n, 128];
     V[d, 128] = Vn EOR (ROL(Vm<127:64>,1):ROL(Vm<63:0>, 1));
*)
Definition armv8a_VRAX1_semi (wn wm : u128) : ty_w U128 :=
  wxor wn (lift1_vec U64 (fun x => wrol x 1) U128 wm).

Definition armv8a_VRAX1_instr : instr_desc_t :=
  mk_vbinop_instr VRAX1 VE64 DOIT armv8a_VRAX1_semi.

(* [XAR] ARM DDI 0487 M.a, C7.2
   Exclusive-OR and rotate.
   Syntax: XAR <Vd>.2D, <Vn>.2D, <Vm>.2D, #<imm6>
   <imm6> is the rotation amount, 0..63.
   Operation:
     AArch64.CheckFPAdvSIMDEnabled();

     bits(128) Vm = V[m, 128];
     bits(128) Vn = V[n, 128];
     bits(128) tmp;
     tmp = Vn EOR Vm;
     V[d, 128] = ROR(tmp<127:64>, UInt(imm6)):ROR(tmp<63:0>, UInt(imm6));

   The amount is an 8-bit immediate in 0..63, as that of a 64-bit scalar
   shift: see [check_shift_amount]. *)
Definition armv8a_VXAR_semi (wn wm : u128) (imm : u8) : ty_w U128 :=
  lift1_vec U64 (fun x => wror x (wunsigned imm)) U128 (wxor wn wm).

Definition armv8a_VXAR_instr : instr_desc_t :=
  let tin := [:: lword U128; lword U128; lword8 ] in
  let semi := armv8a_VXAR_semi in
  {|
    id_msb_flag := MSB_CLEAR;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword U128 ];
    id_out := [:: Ea 0 ];
    id_semi_total := semi;
    id_nargs := 4;
    id_args_kinds :=
      [:: [:: ak_v; ak_v; ak_v
            ; [:: CAimm (Some (CAimmC_armv8a_shift_amount U64)) U8 ] ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := armv8a_vmn_str VXAR VE64 U128;
    id_safe := [::];
    id_err := ErrSemUndef;
    id_init := [:: IBool true ];
    id_doit := DOIT;
    id_pp_asm :=
      pp_armv8a_vop VXAR
        [:: pp_vec VE64 U128; pp_vec VE64 U128; pp_vec VE64 U128; pp_full U8 ];
    id_valid := armv8a_vop_valid VXAR VE64 U128;
    id_wf := refl_equal;
  |}.

(* [MLA (vector)] ARM DDI 0487 M.a, C7.2
   Multiply-add to accumulator (vector).
   Syntax: MLA <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [MLS (vector)] ARM DDI 0487 M.a, C7.2
   Multiply-subtract from accumulator (vector).
   Syntax: MLS <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   <T> is 8B, 16B, 4H, 8H, 2S or 4S (64-bit lanes are reserved).
   Operation, where [sub_op] is FALSE for MLA and TRUE for MLS:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand1 = V[n, datasize];
     bits(datasize) operand2 = V[m, datasize];
     bits(datasize) operand3 = V[d, datasize];
     bits(datasize) result;
     bits(esize) element1;
     bits(esize) element2;
     bits(esize) product;

     for e = 0 to elements-1
         element1 = Elem[operand1, e, esize];
         element2 = Elem[operand2, e, esize];
         product = (UInt(element1) * UInt(element2))<esize-1:0>;
         if sub_op then
             Elem[result, e, esize] = Elem[operand3, e, esize] - product;
         else
             Elem[result, e, esize] = Elem[operand3, e, esize] + product;

     V[d, datasize] = result;

   The product is that of MUL, which the destination, the first argument,
   accumulates as ADD or SUB would. *)
Definition armv8a_VMLA_semi (ve : velem) sz (wd wn wm : word sz) : ty_w sz :=
  armv8a_VADD_semi ve wd (armv8a_VMUL_semi ve wn wm).

Definition armv8a_VMLA_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_acc_instr VMLA ve DOIT (@armv8a_VMLA_semi ve sz).

Definition armv8a_VMLS_semi (ve : velem) sz (wd wn wm : word sz) : ty_w sz :=
  armv8a_VSUB_semi ve wd (armv8a_VMUL_semi ve wn wm).

Definition armv8a_VMLS_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_acc_instr VMLS ve DOIT (@armv8a_VMLS_semi ve sz).

(* The saturating multiplications below compute on the signed values of the
   lanes, as integers, and saturate their result to the signed range of the
   lane: SignedSatQ(i, esize) of the pseudocode is
   [wrepr_saturated_signed esize i]. Its second result, which records a
   saturation in the flag FPSR.QC, is not modelled: FPSR is not part of the
   Jasmin state. [>>] is an arithmetic shift of an integer, rounding towards
   minus infinity, as [Z.shiftr].

   [SQDMULH (vector)] ARM DDI 0487 M.a, C7.2
   Signed saturating doubling multiply returning high half.
   Syntax: SQDMULH <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [SQRDMULH (vector)] ARM DDI 0487 M.a, C7.2
   Signed saturating rounding doubling multiply returning high half.
   Syntax: SQRDMULH <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   <T> is 4H, 8H, 2S or 4S (8- and 64-bit lanes are reserved).
   Operation, where [rounding] is FALSE for SQDMULH and TRUE for SQRDMULH:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand1 = V[n, datasize];
     bits(datasize) operand2 = V[m, datasize];
     bits(datasize) result;
     integer round_const = if rounding then 1 << (esize - 1) else 0;
     integer element1;
     integer element2;
     integer product;
     boolean sat;

     for e = 0 to elements-1
         element1 = SInt(Elem[operand1, e, esize]);
         element2 = SInt(Elem[operand2, e, esize]);
         product = (2 * element1 * element2) + round_const;
         (Elem[result, e, esize], sat) = SignedSatQ(product >> esize, esize);
         if sat then FPSR.QC = '1';

     V[d, datasize] = result;

   Only the product of two lanes that are both the least signed value,
   [-2^(esize-1)], saturates. *)
Definition armv8a_sqdmulh (esize : wsize) (rounding : bool) (x y : word esize)
  : word esize :=
  (let esz := wsize_bits esize in
   let round_const := if rounding then Z.shiftl 1 (esz - 1) else 0 in
   let product := 2 * wsigned x * wsigned y + round_const in
   wrepr_saturated_signed esize (Z.shiftr product esz))%Z.

Definition armv8a_VSQDMULH_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  lift2_vec ve (@armv8a_sqdmulh ve false) sz wn wm.

Definition armv8a_VSQDMULH_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VSQDMULH ve DOIT (@armv8a_VSQDMULH_semi ve sz).

Definition armv8a_VSQRDMULH_semi (ve : velem) sz (wn wm : word sz) : ty_w sz :=
  lift2_vec ve (@armv8a_sqdmulh ve true) sz wn wm.

Definition armv8a_VSQRDMULH_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_instr VSQRDMULH ve DOIT (@armv8a_VSQRDMULH_semi ve sz).

(* [SQRDMLAH (vector)] ARM DDI 0487 M.a, C7.2
   Signed saturating rounding doubling multiply accumulate returning high
   half.
   Syntax: SQRDMLAH <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   [SQRDMLSH (vector)] ARM DDI 0487 M.a, C7.2
   Signed saturating rounding doubling multiply subtract returning high
   half.
   Syntax: SQRDMLSH <Vd>.<T>, <Vn>.<T>, <Vm>.<T>

   <T> is 4H, 8H, 2S or 4S (8- and 64-bit lanes are reserved).
   Decode: if !HaveQRDMLAHExt() then UNDEFINED;
           boolean rounding = TRUE;
           boolean sub_op = (S == '1');
   where [sub_op] is FALSE for SQRDMLAH and TRUE for SQRDMLSH.
   Operation:
     CheckFPAdvSIMDEnabled64();
     bits(datasize) operand1 = V[n, datasize];
     bits(datasize) operand2 = V[m, datasize];
     bits(datasize) operand3 = V[d, datasize];
     bits(datasize) result;
     integer rounding_const = if rounding then 1 << (esize - 1) else 0;
     integer element1;
     integer element2;
     integer element3;
     integer product;
     integer accum;
     boolean sat;

     for e = 0 to elements-1
         element1 = SInt(Elem[operand1, e, esize]);
         element2 = SInt(Elem[operand2, e, esize]);
         element3 = SInt(Elem[operand3, e, esize]);
         if sub_op then
             accum = ((element3 << esize) - 2 * (element1 * element2) + rounding_const);
         else
             accum = ((element3 << esize) + 2 * (element1 * element2) + rounding_const);
         (Elem[result, e, esize], sat) = SignedSatQ(accum >> esize, esize);
         if sat then FPSR.QC = '1';

     V[d, datasize] = result;

   The accumulation is done on the whole product, before the rounding and
   the saturation: SQRDMLAH is not SQRDMULH followed by a saturating
   addition. HaveQRDMLAHExt() is FEAT_RDM, which the assembler must be told
   of ([EXT_rdm]). *)
Definition armv8a_sqrdmlah (esize : wsize) (sub_op : bool) (d x y : word esize)
  : word esize :=
  (let esz := wsize_bits esize in
   let rounding_const := Z.shiftl 1 (esz - 1) in
   let element3 := wsigned d in
   let product := 2 * (wsigned x * wsigned y) in
   let accum :=
     if sub_op
     then Z.shiftl element3 esz - product + rounding_const
     else Z.shiftl element3 esz + product + rounding_const
   in
   wrepr_saturated_signed esize (Z.shiftr accum esz))%Z.

Definition armv8a_VSQRDMLAH_semi (ve : velem) sz (wd wn wm : word sz)
  : ty_w sz :=
  make_vec sz
    (map3 (@armv8a_sqrdmlah ve false)
       (split_vec ve wd) (split_vec ve wn) (split_vec ve wm)).

Definition armv8a_VSQRDMLAH_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_acc_instr VSQRDMLAH ve DOIT (@armv8a_VSQRDMLAH_semi ve sz).

Definition armv8a_VSQRDMLSH_semi (ve : velem) sz (wd wn wm : word sz)
  : ty_w sz :=
  make_vec sz
    (map3 (@armv8a_sqrdmlah ve true)
       (split_vec ve wd) (split_vec ve wn) (split_vec ve wm)).

(* SQRDMLSH is not in the list of data-independent-timing instructions
   (ARM DDI 0487, DIT), which has SQRDMLAH only. *)
Definition armv8a_VSQRDMLSH_instr (ve : velem) sz : instr_desc_t :=
  mk_vbinop_acc_instr VSQRDMLSH ve NOT_DOIT (@armv8a_VSQRDMLSH_semi ve sz).

Definition vmn_desc (ve : velem) (sz : wsize) (vmn : armv8a_vmnemonic)
  : instr_desc_t :=
  match vmn with
  | VMOV => armv8a_VMOV_instr ve sz
  | VLDR => armv8a_VLDR_instr ve sz
  | VSTR => armv8a_VSTR_instr ve sz
  | VAND => armv8a_VAND_instr ve sz
  | VBIC => armv8a_VBIC_instr ve sz
  | VORR => armv8a_VORR_instr ve sz
  | VORN => armv8a_VORN_instr ve sz
  | VEOR => armv8a_VEOR_instr ve sz
  | VNOT => armv8a_VNOT_instr ve sz
  | VBSL => armv8a_VBSL_instr ve sz
  | VBIT => armv8a_VBIT_instr ve sz
  | VBIF => armv8a_VBIF_instr ve sz
  | VADD => armv8a_VADD_instr ve sz
  | VSUB => armv8a_VSUB_instr ve sz
  | VMUL => armv8a_VMUL_instr ve sz
  | VNEG => armv8a_VNEG_instr ve sz
  | VABS => armv8a_VABS_instr ve sz
  | VSMAX => armv8a_VSMAX_instr ve sz
  | VSMIN => armv8a_VSMIN_instr ve sz
  | VUMAX => armv8a_VUMAX_instr ve sz
  | VUMIN => armv8a_VUMIN_instr ve sz
  | VSHL => armv8a_VSHL_instr ve sz
  | VUSHR => armv8a_VUSHR_instr ve sz
  | VSSHR => armv8a_VSSHR_instr ve sz
  | VSLI => armv8a_VSLI_instr ve sz
  | VSRI => armv8a_VSRI_instr ve sz
  | VUSRA => armv8a_VUSRA_instr ve sz
  | VSSRA => armv8a_VSSRA_instr ve sz
  | VUSHL => armv8a_VUSHL_instr ve sz
  | VSSHL => armv8a_VSSHL_instr ve sz
  | VEXT => armv8a_VEXT_instr ve sz
  | VZIP1 => armv8a_VZIP1_instr ve sz
  | VZIP2 => armv8a_VZIP2_instr ve sz
  | VUZP1 => armv8a_VUZP1_instr ve sz
  | VUZP2 => armv8a_VUZP2_instr ve sz
  | VTRN1 => armv8a_VTRN1_instr ve sz
  | VTRN2 => armv8a_VTRN2_instr ve sz
  | VREV16 => armv8a_VREV16_instr ve sz
  | VREV32 => armv8a_VREV32_instr ve sz
  | VREV64 => armv8a_VREV64_instr ve sz
  | VTBL => armv8a_VTBL_instr ve sz
  | VCMEQ => armv8a_VCMEQ_instr ve sz
  | VCMGT => armv8a_VCMGT_instr ve sz
  | VCMGE => armv8a_VCMGE_instr ve sz
  | VCMHI => armv8a_VCMHI_instr ve sz
  | VCMHS => armv8a_VCMHS_instr ve sz
  | VCMTST => armv8a_VCMTST_instr ve sz
  | VDUP => armv8a_VDUP_instr ve sz
  | VDUPLANE => armv8a_VDUPLANE_instr ve sz
  | VINS => armv8a_VINS_instr ve sz
  | VINSLANE => armv8a_VINSLANE_instr ve sz
  | VUMOV => armv8a_VUMOV_instr ve sz
  | VSMOV => armv8a_VSMOV_instr ve sz
  | VAESE => armv8a_VAESE_instr
  | VAESD => armv8a_VAESD_instr
  | VAESMC => armv8a_VAESMC_instr
  | VAESIMC => armv8a_VAESIMC_instr
  | VPMULL => armv8a_VPMULL_instr
  | VPMULL2 => armv8a_VPMULL2_instr
  | VEOR3 => armv8a_VEOR3_instr
  | VRAX1 => armv8a_VRAX1_instr
  | VXAR => armv8a_VXAR_instr
  | VBCAX => armv8a_VBCAX_instr
  | VMLA => armv8a_VMLA_instr ve sz
  | VMLS => armv8a_VMLS_instr ve sz
  | VSQDMULH => armv8a_VSQDMULH_instr ve sz
  | VSQRDMULH => armv8a_VSQRDMULH_instr ve sz
  | VSQRDMLAH => armv8a_VSQRDMLAH_instr ve sz
  | VSQRDMLSH => armv8a_VSQRDMLSH_instr ve sz
  end.


(* -------------------------------------------------------------------- *)

Definition armv8a_instr_desc (o : armv8a_asm_op) : instr_desc_t :=
  match o with
  | ARMv8A_op mn opts => mn_desc opts mn
  | ARMv8A_vop vmn ve sz => vmn_desc ve sz vmn
  end.

(* Size-suffixed intrinsic parsing: [#ADD] is the X (64-bit) form and
   [#ADD_32] the W form. Fixed-size mnemonics take no suffix. *)
Definition armv8a_prim_sized (mn : armv8a_mnemonic) : prim_constructor armv8a_asm_op :=
  PrimX86
    [:: PVp U64; PVp U32 ]
    (fun s =>
       if s is PVp sz
       then Some (ARMv8A_op mn (opts_at sz))
       else None).

(* Vector intrinsics are suffixed, as the x86 ones, with the vector size
   ([#VMOV_128]) or, for the lane-wise operations, with the lanes (as
   [#VPADD_4u32]). Only the valid arrangements are accepted. *)
Definition armv8a_prim_vector (vmn : armv8a_vmnemonic) : prim_constructor armv8a_asm_op :=
  let suffix '(ve, sz) :=
    if armv8a_vmn_lanewise vmn then PVv ve sz else PVp sz
  in
  PrimX86
    (map suffix (armv8a_vmn_shapes vmn))
    (fun s =>
       match s with
       | PVp sz => Some (ARMv8A_vop vmn VE8 sz)
       | PVv ve sz => Some (ARMv8A_vop vmn ve sz)
       | _ => None
       end).

Definition armv8a_prim_string : seq (string * prim_constructor armv8a_asm_op) :=
  map
    (fun mn =>
       (string_of_armv8a_mnemonic mn,
        if mn \in sized_mnemonics
        then armv8a_prim_sized mn
        else primM (ARMv8A_op mn default_opts)))
    cenum
  ++ map (fun vmn => (armv8a_vmn_name vmn, armv8a_prim_vector vmn)) cenum.

#[ export ]
Instance armv8a_op_decl : asm_op_decl armv8a_asm_op :=
  {|
    instr_desc_op := armv8a_instr_desc;
    prim_string := armv8a_prim_string;
  |}.

Definition armv8a_prog := @asm_prog _ _ _ _ _ _ _ armv8a_op_decl.
