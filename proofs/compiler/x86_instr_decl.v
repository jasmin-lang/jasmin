From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype tuple.
From mathcomp Require Import ssralg word word_ssrZ.
Require Import utils strings word waes sha256 sem_type global oseq sopn.
Import Utf8 Relation_Operators ZArith.

Require Export arch_decl.
Require Import x86_decl.

(* -------------------------------------------------------------------- *)

#[only(eqbOK)] derive
Variant x86_op : Type :=
  (* Data transfert *)
| MOV    of wsize              (* copy *)
| MOVSX  of wsize & wsize      (* sign-extend *)
| MOVZX  of wsize & wsize      (* zero-extend *)
| CMOVcc of wsize              (* conditional copy *)
| XCHG   of wsize              (* exchanges the contents of two operands *)

  (* Arithmetic *)
| ADD    of wsize                  (* add unsigned / signed *)
| SUB    of wsize                  (* sub unsigned / signed *)
| MUL    of wsize                  (* mul unsigned *)
| IMUL   of wsize                             (* mul signed with truncation *)
| IMULr  of wsize   (* oprd * oprd *)         (* mul signed with truncation *)
| IMULri of wsize   (* oprd * oprd * imm *)   (* mul signed with truncation *)

| DIV    of wsize                        (* div unsigned *)
| IDIV   of wsize                        (* div   signed *)
| CQO    of wsize                               (* CWD CDQ CQO: allows sign extention in many words *)
| ADC    of wsize                 (* add with carry *)
| SBB    of wsize                 (* sub with borrow *)

| NEG	   of wsize 	                      (* negation *)

| INC    of wsize                         (* increment *)
| DEC    of wsize                         (* decrement *)

| LZCNT  of wsize             (* number of leading zero *)
| TZCNT  of wsize             (* number of trailing zero *)

  (* Flag *)
| SETcc                           (* Set byte on condition *)
| BT     of wsize                  (* Bit test, sets result to CF *)
| CLC                          (* Clear CF *)
| STC                          (* Set CF *)

  (* Pointer arithmetic *)
| LEA    of wsize              (* Load Effective Address *)

  (* Comparison *)
| TEST   of wsize                  (* Bit-wise logical and CMP *)
| CMP    of wsize                  (* Signed sub CMP *)


  (* Bitwise logical instruction *)
| AND    of wsize  (* bit-wise and *)
| ANDN   of wsize  (* bit-wise andn *)
| OR     of wsize  (* bit-wise or  *)
| XOR    of wsize  (* bit-wise xor *)
| NOT    of wsize  (* bit-wise not *)

  (* Bit shifts *)
| ROR    of wsize    (* rotation / right *)
| ROL    of wsize    (* rotation / left  *)
| RCR    of wsize    (* rotation / right with carry *)
| RCL    of wsize    (* rotation / left  with carry *)
| SHL    of wsize    (* unsigned / left  *)
| SHR    of wsize    (* unsigned / right *)
| SAL    of wsize    (*   signed / left; synonym of SHL *)
| SAR    of wsize    (*   signed / right *)
| SHLD   of wsize    (* unsigned (double) / left *)
| SHRD   of wsize    (* unsigned (double) / right *)

| RORX of wsize (* rotate right w/o affecting flags *)
| SARX of wsize (* arithmetic shift right w/o affecting flags *)
| SHRX of wsize (* logical shift right w/o affecting flags *)
| SHLX of wsize (* logical shift left w/o affecting flags *)

| MULX_lo_hi of wsize  (* mul unsigned, doesn't affect arithmetic flags *)
| ADCX    of wsize  (* add with carry flag, only writes carry flag *)
| ADOX    of wsize  (* add with overflow flag, only writes overflow flag *)

| BSWAP  of wsize                     (* byte swap *)
| POPCNT of wsize    (* Count bits set to 1 *)
| BTR    of wsize    (* bit test and reset *)
| BTS    of wsize    (* bit test and set *)

| PEXT   of wsize    (* parallel bits extract *)
| PDEP   of wsize    (* parallel bits deposit *)

  (* MMX instructions *)
| MOVX  of wsize
| POR
| PADD of velem & wsize (* parallel addition *)

  (* SSE instructions *)
| MOVD     of wsize (* MOVD/MOVQ to wide registers *)
| MOVV     of wsize (* MOVD/MOVQ from wide registers *)
| VMOV     of wsize
| VMOVDQA  of wsize
| VMOVDQU  `(wsize)
| VPMOVSX of velem & wsize & velem & wsize (* parallel sign-extension: sizes are source, source, target, target *)
| VPMOVZX of velem & wsize & velem & wsize (* parallel zero-extension: sizes are source, source, target, target *)
| VPAND    `(wsize)
| VPANDN   `(wsize)
| VPOR     `(wsize)
| VPXOR    `(wsize)
| VPADD    `(velem) `(wsize)
| VPSUB    `(velem) `(wsize)
| VPAVG of velem & wsize
| VPMULL   `(velem) `(wsize)
| VPMULH   of wsize   (* signed multiplication of 16-bits*)
| VPMULHU  of wsize
| VPMULHRS of wsize (* Packed Multiply High with Round and Scale *)
| VPMUL    `(wsize)
| VPMULU   `(wsize)
| VPEXTR   of wsize
| VPINSR   of velem
| VPSLL    `(velem) `(wsize)
| VPSRL    `(velem) `(wsize)
| VPSRA    `(velem) `(wsize)
| VPSLLV   `(velem) `(wsize)
| VPSRLV   `(velem) `(wsize)
| VPSLLDQ  `(wsize)
| VPSRLDQ  `(wsize)
| VPSHUFB  `(wsize)
| VPSHUFD  `(wsize)
| VPSHUFHW `(wsize)
| VPSHUFLW `(wsize)
| VPBLEND  `(velem) `(wsize)
| BLENDV of velem & wsize (* vpblendvb, vblendvps, vblendvpd *)
| VPACKUS  `(velem) `(wsize)
| VPACKSS  `(velem) `(wsize)
| VSHUFPS  `(wsize)
| VPBROADCAST of velem & wsize
| VMOVSHDUP of wsize (* Replicate 32-bit (“single”) high values *)
| VMOVSLDUP of wsize (* Replicate 32-bit (“single”) low values *)
| VPALIGNR  `(wsize)
| VBROADCASTI128
| VPUNPCKH `(velem) `(wsize)
| VPUNPCKL `(velem) `(wsize)
| VEXTRACTI128
| VINSERTI128
| VPERM2I128
| VPERMD
| VPERMQ
| VPMOVMSKB of wsize & wsize (* source size (U128/256) & dest. size (U32/64) *)
| MOVEMASK of velem & wsize
| VPCMPEQ of velem & wsize
| VPCMPGT of velem & wsize
| VPSIGN of velem & wsize
| VPMADDUBSW of wsize
| VPMADDWD of wsize
| VMOVLPD   (* Store low 64-bits from XMM register *)
| VMOVHPD   (* Store high 64-bits from XMM register *)
| VPMINU of velem & wsize
| VPMINS of velem & wsize
| VPMAXU of velem & wsize
| VPMAXS of velem & wsize
| VPABS of velem & wsize
| VPTEST `(wsize)

(* Cache *)
| CLFLUSH
| PREFETCHT0
| PREFETCHT1
| PREFETCHT2
| PREFETCHNTA

(* Fences *)
| LFENCE
| MFENCE
| SFENCE

(* Monitoring *)
| RDTSC   of wsize
| RDTSCP  of wsize

(* AES instructions *)
| AESDEC
| VAESDEC of wsize
| AESDECLAST
| VAESDECLAST of wsize
| AESENC
| VAESENC of wsize
| AESENCLAST
| VAESENCLAST of wsize
| AESIMC
| VAESIMC
| AESKEYGENASSIST
| VAESKEYGENASSIST

(* PCLMULQDQ instructions *)
| PCLMULQDQ
| VPCLMULQDQ of wsize

(* SHA instructions *)
| SHA256RNDS2
| SHA256MSG1
| SHA256MSG2
.

HB.instance Definition _ := hasDecEq.Build x86_op x86_op_eqb_OK.

(* ----------------------------------------------------------------------------- *)
Definition b_ty             := [:: sbool].
Definition b4_ty            := [:: sbool; sbool; sbool; sbool].
Definition b5_ty            := [:: sbool; sbool; sbool; sbool; sbool].

Definition bw_ty    sz      := [:: sbool; sword sz].
Definition bw2_ty   sz      := [:: sbool; sword sz; sword sz].
Definition b2w_ty   sz      := [:: sbool; sbool; sword sz].
Definition b4w_ty   sz      := [:: sbool; sbool; sbool; sbool; sword sz].
Definition b5w_ty   sz      := [:: sbool; sbool; sbool; sbool; sbool; sword sz].
Definition b5w2_ty  sz      := [:: sbool; sbool; sbool; sbool; sbool; sword sz; sword sz].

Definition w_ty     sz      := [:: sword sz].
Definition w2_ty    sz sz'  := [:: sword sz; sword sz'].
Definition w3_ty    sz      := [:: sword sz; sword sz; sword sz].
Definition w8_ty            := [:: sword8].
Definition w128_ty          := [:: sword128].
Definition w256_ty          := [:: sword256].

Definition w2b_ty   sz sz'  := [:: sword sz; sword sz'; sbool].
Definition ww8_ty   sz      := [:: sword sz; sword8].
Definition ww8b_ty   sz     := [:: sword sz; sword8; sbool].
Definition w2w8_ty   sz     := [:: sword sz; sword sz; sword8].
Definition w128w8_ty        := [:: sword128; sword8].
Definition w128ww8_ty sz    := [:: sword128; sword sz; sword8].
Definition w256w8_ty        := [:: sword256; sword8].
Definition w256w128w8_ty    := [:: sword256; sword128; sword8].
Definition w256x2w8_ty      := [:: sword256; sword256; sword8].

(* ----------------------------------------------------------------------------- *)

Definition SF_of_word sz (w : word sz) :=
  msb w.

Definition PF_of_word sz (w : word sz) : bool :=
  foldl xorb true [seq wbit_n w i | i <- iota 0 8].

Definition ZF_of_word sz (w : word sz) :=
  w == 0%R.

(* -------------------------------------------------------------------- *)
  (*  OF; CF; SF;    PF;    ZF  *)
Definition rflags_of_bwop sz (w : word sz) : (sem_tuple b5_ty) :=
  (*  OF;  CF;    SF;           PF;           ZF  *)
  (:: Some false, Some false, Some (SF_of_word w), Some (PF_of_word w) & Some (ZF_of_word w)).

(* -------------------------------------------------------------------- *)
(*  OF; CF ;SF; PF; ZF  *)
Definition rflags_of_aluop sz (w : word sz) (vu vs : Z) : (sem_tuple b5_ty) :=
  (*  OF;             CF;                SF;           PF;           ZF  *)
  (:: Some (wsigned  w != vs), Some (wunsigned w != vu), Some (SF_of_word w), Some (PF_of_word w) & Some (ZF_of_word w )).

(* -------------------------------------------------------------------- *)
Definition rflags_of_mul (ov : bool) : (sem_tuple b5_ty) :=
  (*  OF; CF; SF;    PF;    ZF  *)
  (:: Some ov, Some ov, None, None & None).

(* -------------------------------------------------------------------- *)

Definition rflags_of_div : (sem_tuple b5_ty):=
  (*  OF;    CF;    SF;    PF;    ZF  *)
  (:: None, None, None, None & None).

(* -------------------------------------------------------------------- *)

Definition rflags_of_andn sz (w: word sz) : (sem_tuple b5_ty) :=
  (* OF ; CF ; SF ; PF ; ZF *)
  (:: Some false , Some false , Some (SF_of_word w) , None & Some (ZF_of_word w) ).

(* -------------------------------------------------------------------- *)

Definition rflags_None_w {sz} w : (sem_tuple (b5w_ty sz)):=
  (*  OF;    CF;    SF;    PF;    ZF  *)
  (:: None, None, None, None, None & w).


(* -------------------------------------------------------------------- *)
(*  OF; SF; PF; ZF  *)
Definition rflags_of_aluop_nocf sz (w : word sz) (vs : Z) : (sem_tuple b4_ty) :=
  (*  OF                 SF          ; PF          ; ZF          ] *)
  (:: Some (wsigned   w != vs), Some (SF_of_word w), Some (PF_of_word w) & Some (ZF_of_word w)).

Definition flags_w {l1} (bs: ltuple l1) {sz} (w: word sz):=
  (merge_tuple bs (w : sem_tuple (w_ty sz))).

Definition flags_w2 {l1} (bs: ltuple l1) {sz} w :=
  (merge_tuple bs (w : sem_tuple (w2_ty sz sz))).

Definition rflags_of_aluop_w sz (w : word sz) (vu vs : Z) :=
  flags_w (rflags_of_aluop w vu vs) w.

Definition rflags_of_aluop_nocf_w sz (w : word sz) (vs : Z) :=
  flags_w (rflags_of_aluop_nocf w vs) w.

Definition rflags_of_bwop_w sz (w : word sz) :=
  flags_w (rflags_of_bwop w) w.

(* -------------------------------------------------------------------- *)
Section PRIM_RANGE.

Context {A: Type}.

Let prim_range range (f: wsize → A) : prim_constructor A :=
  PrimX86 (map PVp range)
        (fun s => if s is PVp sz then Some (f sz) else None).

Definition prim_8_64 := prim_range [:: U64; U32; U16; U8 ].
Definition prim_16_64 := prim_range [:: U64; U32; U16 ].
Definition prim_32_64 := prim_range [:: U64; U32 ].
Definition prim_128_256 := prim_range [:: U128; U256 ].

Let prim_movxx range (f: wsize → wsize → x86_op) :=
  PrimX86 range
        (fun s => if s is PVx szo szi then Some (f szo szi) else None).

Definition prim_movsx := prim_movxx [:: PVx U16 U8; PVx U32 U8; PVx U64 U8; PVx U16 U16; PVx U32 U16; PVx U64 U16; PVx U32 U32; PVx U64 U32 ].

Definition prim_movzx := prim_movxx [:: PVx U16 U8; PVx U32 U8; PVx U64 U8; PVx U32 U16; PVx U64 U16 ].

Definition prim_vv (f: velem → wsize → velem → wsize → x86_op) : prim_constructor x86_op :=
  PrimX86
    [:: PVvv VE8 U64 VE16 U128
     ; PVvv VE8 U32 VE32 U128
     ; PVvv VE8 U16 VE64 U128
     ; PVvv VE16 U64 VE32 U128
     ; PVvv VE16 U32 VE64 U128
     ; PVvv VE32 U64 VE64 U128
     ; PVvv VE8 U128 VE16 U256
     ; PVvv VE8 U64 VE32 U256
     ; PVvv VE8 U32 VE64 U256
     ; PVvv VE16 U128 VE32 U256
     ; PVvv VE16 U64 VE64 U256
     ; PVvv VE32 U128 VE64 U256
    ]
    (fun s => if s is PVvv ve sz ve' sz' then Some (f ve sz ve' sz') else None).

Definition primV_range range (f: velem → wsize → x86_op) : prim_constructor x86_op :=
  PrimX86 range
    (fun s => if s is PVv ve sz then Some (f ve sz) else None).

Definition primV := primV_range [seq PVv ve sz | ve <- [:: VE8; VE16; VE32; VE64 ], sz <- [:: U128; U256 ]].
Definition primV_8_16 := primV_range [seq PVv ve sz | ve <- [:: VE8; VE16 ], sz <- [:: U128; U256 ]].
Definition primV_8_32 := primV_range [seq PVv ve sz | ve <- [:: VE8; VE16; VE32 ], sz <- [:: U128; U256 ]].
Definition primV_16 := primV_range [seq PVv VE16 sz | sz <- [:: U128; U256 ]].
Definition primV_16_32 := primV_range [seq PVv ve sz | ve <- [:: VE16; VE32 ], sz <- [:: U128; U256 ]].
Definition primV_16_64 := primV_range [seq PVv ve sz | ve <- [:: VE16; VE32; VE64 ], sz <- [:: U128; U256 ]].
Definition primV_128 := primV_range [seq PVv ve U128 | ve <- [:: VE8; VE16; VE32; VE64 ]].

Definition primMMX := primV_range [seq PVv ve sz | ve <- [:: VE8; VE16; VE32; VE64 ], sz <- [:: U64; U128 ]].

Definition primSV_8_32 (f: signedness → velem → wsize → x86_op) : prim_constructor x86_op :=
  PrimX86
    [seq pv sz | pv <- [seq PVsv sg ve | sg <- [:: Signed; Unsigned], ve <- [:: VE8; VE16; VE32 ] ], sz <- [:: U128; U256 ] ]
    (fun s => if s is PVsv sg ve sz then Some (f sg ve sz) else None).

Definition primX (f: wsize → wsize → x86_op) : prim_constructor x86_op :=
  PrimX86 [seq PVx ssz dsz | ssz <- [:: U128; U256 ], dsz <- [:: U64; U32 ] ]
    (fun s => if s is PVx ssz dsz then Some (f ssz dsz) else None).

End PRIM_RANGE.

(* -------------------------------------------------------------------- *)

Notation "'tpl' A" := (sem_tuple A) (at level 200, only parsing).

Notation "'ex_tpl' A" := (exec (sem_tuple A)) (at level 200, only parsing).

Definition implicit_flags      := map F [::OF; CF; SF; PF; ZF].
Definition implicit_flags_noCF := map F [::OF; SF; PF; ZF].

Definition iCF := F CF.

(* -------------------------------------------------------------------- *)

Definition reg_msb_flag (sz : wsize) :=
  if (sz <= U16)%CMP then MSB_MERGE
  else MSB_CLEAR.

Notation mk_instr str_jas tin tout ain aout msb semi args_kinds nargs safe_cond valid pp_asm safe_wf semi_errty semi_safe :=
 {|
  id_valid      := valid;
  id_msb_flag   := msb;
  id_tin        := tin;
  id_in         := ain;
  id_tout       := tout;
  id_out        := aout;
  id_semi       := semi;
  id_nargs      := nargs;
  id_args_kinds := args_kinds;
  id_eq_size    := refl_equal;
  id_tin_narr   := refl_equal;
  id_tout_narr  := refl_equal;
  id_check_dest := refl_equal;
  id_str_jas    := str_jas;
  id_safe       := safe_cond;
  id_pp_asm     := pp_asm;
  id_safe_wf    := safe_wf;
  id_semi_errty := semi_errty;
  id_semi_safe  := semi_safe;
|}.

(* Can only be use for safe instruction *)
Notation mk_instr_safe str_jas tin tout ain aout msb semi args_kinds nargs valid pp_asm :=
  (mk_instr str_jas tin tout ain aout msb (sem_prod_ok tin semi) args_kinds nargs [::] valid pp_asm
    refl_equal
    (fun _ => (@sem_prod_ok_error _ tin semi ErrType))
    (fun _ => (@values.sem_prod_ok_safe _ tin semi)))
  (only parsing).

(* Can only be use for safe instruction *)
Notation mk_instr_pp name tin tout ain aout msb semi check nargs prc pp_asm :=
  (mk_instr_safe (pp_s name%string) tin tout ain aout msb semi check nargs true pp_asm,
   (name%string, prc)) (only parsing).

(* Can only be use for safe instruction *)
Notation mk_instr_w_w name semi ain aout nargs check prc valid pp_asm :=
 ((fun sz =>
  mk_instr_safe (pp_sz name sz) (w_ty sz) (w_ty sz) ain aout (reg_msb_flag sz) (semi sz) (check sz) nargs (valid sz) (pp_asm sz)), (name%string,prc)) (only parsing).

Notation mk_instr_w_w'_10 name sign semi check prc valid pp_asm :=
 ((fun szo szi =>
  mk_instr_safe (pp_sz_sz name sign szo szi) (w_ty szi) (w_ty szo) [:: Eu 1] [:: Eu 0] (reg_msb_flag szo) (semi szi szo) (check szi szo) 2 (valid szi szo) (pp_asm szi szo)), (name%string,prc)) (only parsing).

Notation mk_instr_bw2_w_0211 name semi check prc valid pp_asm :=
 ((fun sz =>
  mk_instr_safe (pp_sz name sz) (bw2_ty sz) (w_ty sz) [:: Ea 0; Eu 2; Ea 1] [:: Ea 1] (reg_msb_flag sz) (semi sz) (check sz) 3 (valid sz) (pp_asm sz)), (name%string, prc))  (only parsing).

Notation mk_instr_w_b5w name semi ain aout nargs check prc valid pp_asm :=
 ((fun sz =>
  mk_instr_safe (pp_sz name sz) (w_ty sz) (b5w_ty sz) ain (implicit_flags ++ aout) (reg_msb_flag sz) (semi sz) (check sz) nargs (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w_b4w_00 name semi check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (w_ty sz) (b4w_ty sz) [:: Eu 0] (implicit_flags_noCF ++ [:: Eu 0]) (reg_msb_flag sz) (semi sz) (check sz) 1 (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2_b name semi ain aout nargs check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (w2_ty sz sz) (b_ty) ain aout (reg_msb_flag sz) (semi sz) (check sz) nargs (valid sz)(pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2_b5 name semi ain nargs check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (w2_ty sz sz) (b5_ty) ain implicit_flags (reg_msb_flag sz) (semi sz) (check sz) nargs (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2_b5w name semi ain aout nargs check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (w2_ty sz sz) (b5w_ty sz) ain (implicit_flags ++ aout) (reg_msb_flag sz) (semi sz) (check sz) nargs (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2_b5w_010 name semi check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (w2_ty sz sz) (b5w_ty sz) [:: Eu 0; Eu 1] (implicit_flags ++ [:: Eu 0]) (reg_msb_flag sz) (semi sz) (check sz) 2 (valid sz) (pp_asm sz)), (name%string,prc)) (only parsing).

Notation mk_instr_w2b_b5w_010 name semi check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (w2b_ty sz sz) (b5w_ty sz) ([:: Eu 0; Eu 1] ++ [::iCF]) (implicit_flags ++ [:: Eu 0]) (reg_msb_flag sz) (semi sz) (check sz) 2 (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2_bw name semi check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (w2_ty sz sz) (bw_ty sz) [:: Ea 0; Eu 1] [::F CF; Ea 0] MSB_MERGE (semi sz) (check sz) 2 (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2b_bw name semi flag check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (w2b_ty sz sz) (bw_ty sz) ([:: Ea 0; Eu 1] ++ [::F flag]) ([::F flag; Ea 0]) (reg_msb_flag sz) (semi sz) (check sz) 2 (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2_b5w2 name semi ain aout nargs check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (w2_ty sz sz) (b5w2_ty sz) ain (implicit_flags ++ aout) (reg_msb_flag sz) (semi sz) (check sz) nargs (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_division sg name semi check prc valid pp_asm semi_errty semi_safe := ((fun sz =>
  mk_instr (pp_sz name sz) (w3_ty sz) (b5w2_ty sz) [:: R RDX; R RAX; Eu 0]  (implicit_flags ++ [:: R RAX; R RDX]) (reg_msb_flag sz) (semi sz) (check sz) 1 [::X86Division sz sg] (valid sz) (pp_asm sz) refl_equal (semi_errty sz) (semi_safe sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2_w_120 name semi check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (w2_ty sz sz) (w_ty sz) [:: Ea 1 ; Eu 2] [:: Ea 0] MSB_CLEAR (semi sz) (check sz) 3 (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_ww8_w_120 name semi check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (ww8_ty sz) (w_ty sz) [:: Eu 1 ; Ea 2] [:: Ea 0] (reg_msb_flag sz) (semi sz) (check sz) 3 (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_ww8_b2w_0c0 name semi check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (ww8_ty sz) (b2w_ty sz) [:: Eu 0; Ef 1 RCX] [::F OF; F CF; Eu 0] (reg_msb_flag sz) (semi sz) (check sz) 2 (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_ww8b_b2w_0c0 name semi check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (ww8b_ty sz) (b2w_ty sz) [:: Eu 0; Ef 1 RCX; F CF] [::F OF; F CF; Eu 0] (reg_msb_flag sz) (semi sz) (check sz) 2 (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_ww8_b5w_0c0 name semi check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (ww8_ty sz) (b5w_ty sz) [:: Eu 0; Ef 1 RCX] (implicit_flags ++ [:: Eu 0]) (reg_msb_flag sz) (semi sz) (check sz) 2 (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2w8_b5w_01c0 name semi check safe_cond prc valid pp_asm safe_wf semi_errty semi_safe := ((fun sz =>
  mk_instr (pp_sz name sz) (w2w8_ty sz) (b5w_ty sz) [:: Eu 0; Ea 1; Ef 2 RCX] (implicit_flags ++ [:: Eu 0]) (reg_msb_flag sz) (semi sz) (check sz) 3 (safe_cond sz) (valid sz) (pp_asm sz) (safe_wf sz) (semi_errty sz) (semi_safe sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2w8_w_1230 name semi check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (w2w8_ty sz) (w_ty sz) [:: Ea 1 ; Eu 2 ; Ea 3] [:: Ea 0] (reg_msb_flag sz) (semi sz) (check sz) 4 (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_ve_instr_w2w8_w_1230 name semi check prc valid pp_asm := ((fun (ve:velem) sz =>
  mk_instr_safe (pp_ve_sz name ve sz) (w2w8_ty sz) (w_ty sz) [:: Ea 1 ; Eu 2 ; Ea 3] [:: Ea 0] (reg_msb_flag sz) (semi ve sz) (check sz) 4 (valid ve sz) (pp_asm ve sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w_w128_10 name msb semi check prc valid pp_asm := ((fun sz =>
  mk_instr_safe (pp_sz name sz) (w_ty sz) (w128_ty) [:: Eu 1] [:: Eu 0] msb (semi sz) (check sz) 2 (valid sz) (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_ve_instr_w_w_10 name semi check prc valid pp_asm := ((fun (ve:velem) sz =>
  mk_instr_safe (pp_ve_sz name ve sz) (w_ty _) (w_ty sz) [:: Eu 1] [:: Ea 0] (reg_msb_flag sz) (semi ve sz) (check sz) 2 (valid ve sz) (pp_asm ve sz)), (name%string,prc))  (only parsing).

Notation mk_ve_instr_w2_w_120 name semi check prc valid pp_asm := ((fun (ve:velem) sz =>
  mk_instr_safe (pp_ve_sz name ve sz) (w2_ty sz sz) (w_ty sz) [:: Ea 1 ; Eu 2] [:: Ea 0] MSB_CLEAR (semi ve sz) (check sz) 3 (valid ve sz) (pp_asm ve sz)), (name%string,prc))  (only parsing).

Notation mk_ve_instr_ww128_w_120 name semi check prc valid pp_asm := ((fun ve sz =>
  mk_instr_safe (pp_ve_sz name ve sz) (w2_ty sz U128) (w_ty sz) [:: Ea 1 ; Eu 2] [:: Ea 0] (reg_msb_flag sz) (semi ve sz) (check sz) 3 (valid ve sz) (pp_asm ve sz)), (name%string,prc))  (only parsing).

Definition max_32 (sz:wsize) := if (sz <= U32)%CMP then sz else U32.

Definition map_sz (sz:wsize) (a:asm_args) := List.map (fun a => (sz,a)) a.

Definition pp_name name sz args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_name;
     pp_aop_args := map_sz sz args; |}.

Definition pp_name_ty name (ws:seq wsize) args :=
 {| pp_aop_name := name;
    pp_aop_ext  := PP_name;
    pp_aop_args := zip ws args; |}.

Definition pp_iname name sz args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_iname sz;
     pp_aop_args := map_sz sz args; |}.

Definition pp_viname_long name ve sz args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_viname ve true;
     pp_aop_args := map_sz sz args; |}.

Definition pp_viname name ve sz args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_viname ve false;
     pp_aop_args := map_sz sz args; |}.

Definition pp_viname_ww_128 name ve sz args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_viname ve false;
     pp_aop_args := zip [:: sz; sz; U128 ] args; |}.

Definition pp_iname_w_8 name sz args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_iname sz;
     pp_aop_args := zip [::sz; U8] args; |}.

Definition pp_iname_ww_8 name sz args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_iname sz;
     pp_aop_args := zip [::sz;sz; U8] args; |}.

Definition get_ct args :=
  match args with
  | a :: args => (PP_ct a, args)
  | _         => (PP_error, args)
  end.

Definition pp_ct name sz args :=
  let (ext, args) := get_ct args in
  {| pp_aop_name := name;
     pp_aop_ext  := ext;
     pp_aop_args := map_sz sz args; |}.

Definition pp_cqo sz (args: asm_args) :=
  let (name, ext) :=
      match sz with
      | U16 => ("cwd"%string, PP_name)
      | U32 => ("cdq"%string, PP_name)
      | U64 => ("cqo"%string, PP_name)
      | _   => ("CQO"%string, PP_error)
      end in
  {| pp_aop_name := name;
     pp_aop_ext  := ext;
     pp_aop_args := map_sz sz [::]; |}.

Definition c := [::CAcond].
Definition r := [:: CAreg].
Definition rx := [:: CAregx].
Definition m b := [:: CAmem b].
Definition i sz := [:: CAimm CAimmC_none sz].
Definition rm b := [:: CAreg; CAmem b].
Definition rxm b := [:: CAregx; CAmem b].

Definition rmi sz := [:: CAreg; CAmem true; CAimm CAimmC_none sz].
Definition ri  sz := [:: CAreg; CAimm CAimmC_none sz].

Definition m_r := [:: m false; r].
Definition r_rm_false := [:: r; rm false].

Definition r_rm := [:: r; rm true].
Definition r_rmi sz := [:: r; rmi sz].
Definition m_ri sz := [:: m false; ri sz].

Definition xmm := [:: CAxmm ].
Definition xmmm b := [:: CAxmm; CAmem b].
Definition xmmmi sz := [:: CAxmm; CAmem true; CAimm CAimmC_none sz].

Definition xmm_xmmm := [::xmm; xmmm true].
Definition xmmm_xmm := [::xmmm false; xmm].
Definition xmm_xmm_xmmm := [::xmm; xmm; xmmm true].
Definition xmm_xmm_xmmmi sz := [::xmm; xmm; xmmmi sz].

Definition x86_MOV sz (x: word sz) : word sz := x.

Definition check_mov sz := [:: r_rmi sz; m_ri (max_32 sz)].

Definition Ox86_MOV_instr               :=
  mk_instr_w_w "MOV" x86_MOV [:: Eu 1] [:: Eu 0] 2
               check_mov (prim_8_64 MOV) size_8_64 (pp_iname "mov").

Definition check_movx (sz:wsize) := [:: [:: rx; rm true]; [:: rm true; rx]].

Definition pp_movd name sz args :=
 pp_name_ty (if sz == U64 then (name ++ "q")%string else (name ++ "d")%string)
            match args with
            | [:: XReg _ ; Reg _ ] => [:: U128 ; sz ]
            | [:: Reg _ ; XReg _ ] => [:: sz ; U128 ]
            | _ => [:: sz ; sz ]
            end
            args.

Definition x86_MOVX sz (x: word sz) : word sz := x.

Definition Ox86_MOVX_instr               :=
  mk_instr_w_w "MOVX" x86_MOVX [:: Eu 1] [:: Eu 0] 2
               check_movx (prim_32_64 MOVX) size_32_64 (pp_movd "mov").

Definition check_por : i_args_kinds := [:: [:: rx; rxm true ] ].

Definition x86_POR (v1 v2: wreg) : wreg := wor v1 v2.

Definition Ox86_POR_instr :=
  let desc :=
    mk_instr_safe
      (pp_s "POR")
      (w2_ty U64 U64)
      (w_ty U64)
      [:: Eu 0; Eu 1 ]
      [:: Eu 0 ]
      MSB_MERGE
      x86_POR
      check_por
      2
      true
      (pp_name "por" U64)
  in
  (desc, ("POR"%string, primM POR)).

Definition check_padd : i_args_kinds := [:: [:: rx; rxm true ]; [:: xmm; xmmm true ] ].

Definition Ox86_PADD_instr :=
  let padd := "PADD"%string in
  (λ (ve: velem) (sz: wsize),
    mk_instr_safe (pp_ve_sz padd ve sz) (w2_ty sz sz) (w_ty sz) [:: Eu 0; Eu 1 ] [:: Eu 0 ] MSB_CLEAR
      (lift2_vec ve +%R sz) check_padd 2 (size_64_128 sz) (pp_viname "padd" ve sz),
   (padd, primMMX PADD)).

Definition check_movsx (_ _:wsize) := [:: r_rm ].

Definition pp_movsx szs szd args :=
  let ext := if (szd == szs) || (szd == U64) && (szs == U32) then "xd"%string else "x"%string in
  {| pp_aop_name := "movs";
     pp_aop_ext  := PP_iname2 ext szs szd;
     pp_aop_args := zip [::szd; szs] args; |}.

Definition size_MOVSX szi szo :=
  match szi with
  | U8 | U16 => size_16_64 szo
  | U32 => size_32_64 szo
  | _ => false
  end.

Definition x86_MOVSX szi szo (x: word szi) : tpl (w_ty szo) :=
  sign_extend szo x.

Definition Ox86_MOVSX_instr             :=
  mk_instr_w_w'_10 "MOVSX" true x86_MOVSX check_movsx (prim_movsx MOVSX) size_MOVSX pp_movsx.

Definition pp_movzx szs szd args :=
  {| pp_aop_name := "movz";
     pp_aop_ext  := PP_iname2 "x" szs szd;
     pp_aop_args := zip [::szd; szs] args; |}.

Definition size_MOVZX szi szo :=
  match szi with
  | U8 => size_16_64 szo
  | U16 => size_32_64 szo
  | _ => false
  end.

Definition x86_MOVZX szi szo (x: word szi) : tpl (w_ty szo) :=
  zero_extend szo x.

Definition Ox86_MOVZX_instr             :=
  mk_instr_w_w'_10 "MOVZX" false x86_MOVZX check_movsx (prim_movzx MOVZX) size_MOVZX pp_movzx.

Definition check_xchg := [:: m_r; r_rm].

Definition x86_XCHG sz (v1 v2: word sz) : tpl (w2_ty sz sz) :=
  (v2, v1).

Definition Ox86_XCHG_instr :=
  let name := "XCHG"%string in
  ( (fun sz => mk_instr_safe (pp_sz name sz) (w2_ty sz sz) (w2_ty sz sz) [:: Eu 0; Eu 1] [:: Eu 0; Eu 1] (reg_msb_flag sz) (@x86_XCHG sz) check_xchg 2 (size_8_64 sz) (pp_name "xchg" sz)), (name, primP XCHG)).

Definition c_r_rm := [:: c; r; rm true].

Definition x86_CMOVcc sz (b:bool) (w2 w3: word sz) : tpl (w_ty sz) :=
  if b then w2 else w3.

Definition Ox86_CMOVcc_instr            :=
  mk_instr_bw2_w_0211 "CMOVcc" x86_CMOVcc (fun sz => [::c_r_rm]) (prim_16_64 CMOVcc) size_16_64 (pp_ct "cmov").

Definition check_add sz := [:: m_ri (max_32 sz); r_rmi (max_32 sz)].

Definition x86_ADD sz (v1 v2 : word sz) : tpl (b5w_ty sz) :=
  rflags_of_aluop_w
    (v1 + v2)%R
    (wunsigned v1 + wunsigned v2)%Z
    (wsigned   v1 + wsigned   v2)%Z.

Definition Ox86_ADD_instr  :=
  mk_instr_w2_b5w_010 "ADD" x86_ADD check_add (prim_8_64 ADD) size_8_64 (pp_iname "add").

Definition x86_SUB sz (v1 v2 : word sz) : tpl (b5w_ty sz) :=
  rflags_of_aluop_w
    (v1 - v2)%R
    (wunsigned v1 - wunsigned v2)%Z
    (wsigned   v1 - wsigned   v2)%Z.

Definition Ox86_SUB_instr :=
  mk_instr_w2_b5w_010 "SUB" x86_SUB check_add (prim_8_64 SUB) size_8_64 (pp_iname "sub").

Definition check_mul (_:wsize) := [:: [::rm true]].

Definition x86_MUL sz (v1 v2: word sz) : tpl (b5w2_ty sz) :=
  let lo := (v1 * v2)%R in
  let hi := wmulhu v1 v2 in
  let ov := wdwordu hi lo in
  let ov := (ov >? wbase sz - 1)%Z in
  flags_w2 (rflags_of_mul ov) (:: hi & lo).

Definition Ox86_MUL_instr :=
  mk_instr_w2_b5w2 "MUL"  x86_MUL [:: R RAX; Eu 0] [:: R RDX; R RAX] 1
    check_mul (prim_16_64 MUL) size_16_64 (pp_iname "mul").

Definition x86_IMUL_overflow sz (hi lo: word sz) : bool :=
  let ov := wdwords hi lo in
  (ov <? wmin_signed sz)%Z || (ov >? wmax_signed sz)%Z.

Definition x86_IMUL sz (v1 v2: word sz) : tpl (b5w2_ty sz) :=
  let lo := (v1 * v2)%R in
  let hi := wmulhs v1 v2 in
  let ov := x86_IMUL_overflow hi lo in
  flags_w2 (rflags_of_mul ov) (:: hi & lo).

Definition Ox86_IMUL_instr :=
  mk_instr_w2_b5w2 "IMUL" x86_IMUL [:: R RAX; Eu 0] [:: R RDX; R RAX] 1
    check_mul (prim_16_64 IMUL) size_16_64 (pp_iname "imul") .

Definition x86_IMULt sz (v1 v2: word sz) : tpl (b5w_ty sz) :=
  let lo := (v1 * v2)%R in
  let hi := wmulhs v1 v2 in
  let ov := x86_IMUL_overflow hi lo in
  flags_w (rflags_of_mul ov) lo.

Definition Ox86_IMULr_instr             :=
  mk_instr_w2_b5w_010 "IMULr" x86_IMULt
    (fun _ => [::r_rm]) (prim_16_64 IMULr) size_16_64 (pp_iname "imul").

Definition Ox86_IMULri_instr :=
  mk_instr_w2_b5w "IMULri" x86_IMULt [:: Eu 1; Eu 2] [:: Eu 0] 3
  (fun sz => [:: [::r; rm true; i (max_32 sz)]]) (prim_16_64 IMULri) size_16_64 (pp_iname "imul").

Definition x86_DIV sz (hi lo dv: word sz) : ex_tpl (b5w2_ty sz) :=
  let dd := wdwordu hi lo in
  let dv := wunsigned dv in
  let q  := (dd  /  dv)%Z in
  let r  := (dd mod dv)%Z in
  let ov := (q >? wmax_unsigned sz)%Z in

  if (dv == 0)%Z || ov then Error ErrArith else
  ok (flags_w2 (rflags_of_div) (:: (wrepr sz q) & (wrepr sz r))).

Lemma Ox86_DIV_errty (ws : wsize) :
  sem_forall (λ r : result error (sem_tuple (b5w2_ty ws)), r ≠ Error ErrType) (w3_ty ws) (x86_DIV (sz:=ws)).
Proof. by move=> hi lo dv; rewrite /x86_DIV; case: ifP. Qed.

Lemma Ox86_DIV_safe (ws : wsize) :
  values.interp_safe_cond_ty (tin := w3_ty ws)
  [:: X86Division ws Unsigned] (x86_DIV (sz:=ws)).
Proof.
  move=> hi lo dv /= h; have {h} /= /(_ hi lo dv) := List.Forall_inv h.
  rewrite !truncate_word_u /x86_DIV /= => /(_ erefl) /negP/negPf ->; eauto.
Qed.

Definition Ox86_DIV_instr :=
  mk_instr_division Unsigned "DIV" x86_DIV check_mul (prim_16_64 DIV) size_16_64 (pp_iname "div")
    (fun ws _ => @Ox86_DIV_errty ws) (fun ws _ => @Ox86_DIV_safe ws).

Definition x86_IDIV sz (hi lo dv: word sz) : ex_tpl (b5w2_ty sz) :=
  let dd := wdwords hi lo in
  let dv := wsigned dv in
  let q  := (Z.quot dd dv)%Z in
  let r  := (Z.rem  dd dv)%Z in
  let ov := (q <? wmin_signed sz)%Z || (q >? wmax_signed sz)%Z in

  if (dv == 0)%Z || ov then Error ErrArith else
  ok (flags_w2 (rflags_of_div) (:: (wrepr sz q) & (wrepr sz r))).

Lemma Ox86_IDIV_errty (ws : wsize) :
  sem_forall (λ r : result error (sem_tuple (b5w2_ty ws)), r ≠ Error ErrType) (w3_ty ws) (x86_IDIV (sz:=ws)).
Proof. by move=> hi lo dv; rewrite /x86_IDIV; case: ifP. Qed.

Lemma Ox86_IDIV_safe (ws : wsize) :
  values.interp_safe_cond_ty (tin := w3_ty ws)
  [:: X86Division ws Signed] (x86_IDIV (sz:=ws)).
Proof.
  move=> hi lo dv /= h; have {h} /= /(_ hi lo dv) := List.Forall_inv h.
  rewrite !truncate_word_u /x86_IDIV /= => /(_ erefl) /negP/negPf ->; eauto.
Qed.

Definition Ox86_IDIV_instr :=
  mk_instr_division Signed "IDIV" x86_IDIV check_mul (prim_16_64 IDIV) size_16_64 (pp_iname "idiv")
    (fun ws _ => @Ox86_IDIV_errty ws) (fun ws _ => @Ox86_IDIV_safe ws).

Definition x86_CQO sz (w:word sz) : word sz :=
  (if msb w then -1 else 0)%R.

Definition Ox86_CQO_instr :=
  mk_instr_w_w "CQO" x86_CQO [:: R RAX] [:: R RDX] 0 (fun _ => [:: [::]]) (prim_16_64 CQO) size_16_64 pp_cqo.

Definition add_carry sz (x y c: Z) : word sz :=
  wrepr sz (x + y + c).

Definition x86_ADC sz (v1 v2 : word sz) (c: bool) : tpl (b5w_ty sz) :=
  let c := Z.b2z c in
  rflags_of_aluop_w
    (add_carry sz (wunsigned v1) (wunsigned v2) c)
    (wunsigned v1 + wunsigned v2 + c)%Z
    (wsigned   v1 + wsigned   v2 + c)%Z.

Definition Ox86_ADC_instr :=
  mk_instr_w2b_b5w_010 "ADC" x86_ADC check_add (prim_8_64 ADC) size_8_64 (pp_iname "adc").

Definition sub_borrow sz (x y c: Z) : word sz :=
  wrepr sz (x - y - c).

Definition x86_SBB sz (v1 v2 : word sz) (c:bool) : tpl (b5w_ty sz) :=
  let c := Z.b2z c in
  rflags_of_aluop_w
    (sub_borrow sz (wunsigned v1) (wunsigned v2) c)
    (wunsigned v1 - (wunsigned v2 + c))%Z
    (wsigned   v1 - (wsigned   v2 + c))%Z.

Definition Ox86_SBB_instr               :=
  mk_instr_w2b_b5w_010 "SBB" x86_SBB check_add (prim_8_64 SBB) size_8_64 (pp_iname "sbb").

Definition check_adcx (_:wsize) := [:: r_rm].

Definition x86_ADCX sz (v1 v2: word sz) (c:bool) : tpl (bw_ty sz) :=
  let (c,w) := waddcarry v1 v2 c in
  (Some c, w).

Definition Ox86_ADCX_instr :=
  mk_instr_w2b_bw "ADCX" x86_ADCX CF check_adcx (prim_32_64 ADCX) size_32_64 (pp_iname "adcx").

Definition Ox86_ADOX_instr :=
  mk_instr_w2b_bw "ADOX" x86_ADCX OF check_adcx (prim_32_64 ADOX) size_32_64 (pp_iname "adox").

Definition check_mulx := [:: [::r;r;rm true]].

Definition x86_MULX_lo_hi sz (v1 v2: word sz) : tpl (w2_ty sz sz) :=
  let: (hi, lo) := wumul v1 v2 in
  (lo, hi).

Definition Ox86_MULX_lo_hi_instr :=
  let name := "MULX_lo_hi"%string in
   ((fun (sz:wsize) =>
     mk_instr_safe (pp_sz name sz) (w2_ty sz sz) (w2_ty sz sz)
         [::R RDX; Eu 2] [:: Eu 1; Eu 0] (* lo, hi *) (reg_msb_flag sz)
         (@x86_MULX_lo_hi sz) check_mulx 3 (size_32_64 sz) (pp_iname "mulx" sz)),
    (name, prim_32_64 MULX_lo_hi)).

Definition check_neg (_:wsize) := [::[::rm false]].

Definition x86_NEG sz (w: word sz) : tpl (b5w_ty sz) :=
  let vs := (- wsigned w)%Z in
  let v := (- w)%R in
  flags_w
  ((:: Some (wsigned   v != vs), Some ((w != 0)%R), Some (SF_of_word v), Some (PF_of_word v) & Some (ZF_of_word v)) : sem_tuple b5_ty)
  v.

Definition Ox86_NEG_instr               :=
  mk_instr_w_b5w "NEG" x86_NEG [:: Eu 0] [:: Eu 0] 1 check_neg (prim_8_64 NEG) size_8_64 (pp_iname "neg").

Definition x86_INC sz (w: word sz) : tpl (b4w_ty sz) :=
  rflags_of_aluop_nocf_w
    (w + 1)
    (wsigned w + 1)%Z.

Definition Ox86_INC_instr               :=
  mk_instr_w_b4w_00 "INC" x86_INC check_neg (prim_8_64 INC) size_8_64 (pp_iname "inc").

Definition x86_DEC sz (w: word sz) : tpl (b4w_ty sz) :=
  rflags_of_aluop_nocf_w
    (w - 1)
    (wsigned w - 1)%Z.

Definition Ox86_DEC_instr :=
  mk_instr_w_b4w_00 "DEC" x86_DEC check_neg (prim_8_64 DEC) size_8_64 (pp_iname "dec").

Definition x86_LZCNT sz (w: word sz) : tpl (b5w_ty sz) :=
   let v := leading_zero w in
   flags_w
        (*  OF;     CF;                  SF;   PF;    ZF  *)
         ((:: None, Some (ZF_of_word w), None, None & Some (ZF_of_word v)) : sem_tuple b5_ty) v.

Definition Ox86_LZCNT_instr               :=
  mk_instr_w_b5w "LZCNT" x86_LZCNT [:: Eu 1] [:: Eu 0] 2 (fun _ => [::r_rm]) (prim_16_64 LZCNT) size_16_64 (pp_iname "lzcnt").

Definition x86_TZCNT sz (w: word sz) : tpl (b5w_ty sz) :=
  let v := trailing_zero w in
  flags_w
    (*  OF;     CF;                  SF;   PF;    ZF  *)
    ((:: None, Some (ZF_of_word w), None, None & Some (ZF_of_word v)) : sem_tuple b5_ty) v.

Definition Ox86_TZCNT_instr               :=
  mk_instr_w_b5w "TZCNT" x86_TZCNT [:: Eu 1] [:: Eu 0] 2 (fun _ => [::r_rm]) (prim_16_64 TZCNT) size_16_64 (pp_iname "tzcnt").


Definition check_setcc := [:: [::c; rm false]].

Definition x86_SETcc (b:bool) : tpl (w_ty U8) := wrepr U8 (Z.b2z b).

Definition Ox86_SETcc_instr             :=
  mk_instr_pp "SETcc" b_ty w8_ty [:: Eu 0] [:: Eu 1] (reg_msb_flag U8) x86_SETcc check_setcc 2 (primM SETcc) (pp_ct "set" U8).

Definition check_bt of wsize := [:: [:: r; ri U8 ]].

Definition x86_BT sz (x y: word sz) : tpl (b_ty) :=
  Some (wbit x y).

Definition Ox86_BT_instr                :=
  mk_instr_w2_b "BT" x86_BT [:: Eu 0; Eu 1] [:: F CF] 2 check_bt (prim_16_64 BT) size_16_64 (pp_iname "bt").

(* -------------------------------------------------------------------- *)

Definition x86_CLC : tpl b_ty := Some false.

Definition Ox86_CLC_instr :=
  mk_instr_pp "CLC" [::] b_ty [::] [:: F CF ] MSB_CLEAR x86_CLC [:: [::]] 0 (primM CLC) (pp_name "clc" U8).

Definition x86_STC : tpl b_ty := Some true.

Definition Ox86_STC_instr :=
  mk_instr_pp "STC" [::] b_ty [::] [:: F CF ] MSB_CLEAR x86_STC [:: [::]] 0 (primM STC) (pp_name "stc" U8).

(* -------------------------------------------------------------------- *)
Definition check_lea (_:wsize) := [:: [::r; m true]].

Definition x86_LEA sz (addr: word sz) : tpl (w_ty sz) := addr.

Definition Ox86_LEA_instr :=
  mk_instr_w_w "LEA" x86_LEA [:: Ec 1] [:: Eu 0] 2 check_lea (prim_16_64 LEA) size_16_64 (pp_iname "lea").

Definition check_test (sz:wsize) := [:: [::rm false; ri (max_32 sz)]].

Definition x86_TEST sz (x y: word sz) : tpl  b5_ty :=
  rflags_of_bwop (wand x y).

Definition Ox86_TEST_instr              :=
  mk_instr_w2_b5 "TEST" x86_TEST [:: Eu 0; Eu 1] 2 check_test (prim_8_64 TEST) size_8_64 (pp_iname "test").

Definition check_cmp (sz:wsize) := [:: [::rm false; ri (max_32 sz)]; r_rm].

Definition x86_CMP sz (x y: word sz) : tpl b5_ty :=
  rflags_of_aluop (x - y)
       (wunsigned x - wunsigned y)%Z (wsigned x - wsigned y)%Z.

Definition Ox86_CMP_instr :=
  mk_instr_w2_b5 "CMP" x86_CMP [:: Eu 0; Eu 1] 2 check_cmp (prim_8_64 CMP) size_8_64 (pp_iname "cmp").

Definition x86_AND sz (v1 v2: word sz) : tpl (b5w_ty sz) :=
  rflags_of_bwop_w (wand v1 v2).

Definition Ox86_AND_instr :=
  mk_instr_w2_b5w_010 "AND" x86_AND check_cmp (prim_8_64 AND) size_8_64 (pp_iname "and").

Definition x86_OR sz (v1 v2: word sz) : tpl (b5w_ty sz) :=
  rflags_of_bwop_w (wor v1 v2).

Definition Ox86_OR_instr                :=
  mk_instr_w2_b5w_010 "OR" x86_OR check_cmp (prim_8_64 OR) size_8_64 (pp_iname "or").

Definition x86_XOR sz (v1 v2: word sz) : tpl (b5w_ty sz) :=
  rflags_of_bwop_w (wxor v1 v2).

Definition Ox86_XOR_instr               :=
  mk_instr_w2_b5w_010 "XOR" x86_XOR check_cmp (prim_8_64 XOR) size_8_64 (pp_iname "xor").

Definition check_andn (_:wsize) := [:: [:: r; r; rm true]].

Definition x86_ANDN sz (v1 v2: word sz) : tpl (b5w_ty sz) :=
  let w := wandn v1 v2 in
  flags_w (rflags_of_andn w) (w).

Definition Ox86_ANDN_instr              :=
  mk_instr_w2_b5w "ANDN" x86_ANDN [:: Eu 1; Eu 2] [:: Eu 0] 3
  check_andn (prim_32_64 ANDN) size_32_64 (pp_iname "andn").

Definition x86_NOT sz (v: word sz)  : tpl (w_ty sz) := wnot v.

Definition Ox86_NOT_instr               :=
  mk_instr_w_w "NOT" x86_NOT [:: Eu 0] [:: Eu 0] 1 check_neg (prim_8_64 NOT) size_8_64 (pp_iname "not").

Definition check_ror (_:wsize):= [::[::rm false; ri U8]].
Definition x86_shift_mask (s:wsize) : u8 :=
  match s with
  | U8 | U16 | U32 => wrepr U8 31
  | U64  => wrepr U8 63
  | U128 => wrepr U8 127
  | U256 => wrepr U8 255
  end%Z.

Definition x86_ROR sz (v: word sz) (i: u8) : tpl (b2w_ty sz) :=
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    (:: None , None & v)
  else
    let r := wror v (wunsigned i) in
    let CF := msb r in
    let OF := if i == 1%R then Some (CF != msb v) else None in
    (:: OF , Some CF & r).

Definition Ox86_ROR_instr               :=
  mk_instr_ww8_b2w_0c0 "ROR" x86_ROR check_ror (prim_8_64 ROR) size_8_64 (pp_iname_w_8 "ror").

Definition x86_ROL sz (v: word sz) (i: u8) : tpl (b2w_ty sz) :=
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    (:: None , None & v)
  else
    let r := wrol v (wunsigned i) in
    let CF := lsb r in
    let OF := if i == 1%R then Some (msb r != CF) else None in
    (:: OF, Some CF & r ).

Definition Ox86_ROL_instr :=
  mk_instr_ww8_b2w_0c0 "ROL" x86_ROL check_ror (prim_8_64 ROL) size_8_64 (pp_iname_w_8 "rol").

Definition x86_rotate_with_carry (sz: wsize)
  (rot: word.word.word sz.+1 → nat → word.word.word sz.+1)
  (ovf: word sz → bool → bool)
  (v: word sz) (i: u8) (cf: bool)
  : tpl (b2w_ty sz) :=
  let i := wand i (x86_shift_mask sz) in
  let i :=
    match sz with
    | U8 => Z.modulo (wunsigned i) 9
    | U16 => Z.modulo (wunsigned i) 17
    | _  => wunsigned i
    end in
  let r := mathcomp.word.word.t2w [tuple of cf::mathcomp.word.word.w2t v] in
  let r := rot r (Z.to_nat i) in
  let r := mathcomp.word.word.w2t r in
  let CF := head false r in
  let r : word sz := mathcomp.word.word.t2w [tuple of behead r] in
  let OF := if i == 1%R then Some (ovf r CF) else None in
  (:: OF, Some CF & r ).

Definition x86_RCR sz (v: word sz) (i: u8) (cf:bool) : tpl (b2w_ty sz) :=
  @x86_rotate_with_carry sz (@mathcomp.word.word.rotr _) (λ _ _, msb v != cf) v i cf.

Definition Ox86_RCR_instr :=
  mk_instr_ww8b_b2w_0c0 "RCR" x86_RCR check_ror (prim_8_64 RCR) size_8_64 (pp_iname_w_8 "rcr").

Definition x86_RCL sz (v: word sz) (i: u8) (cf:bool) : tpl (b2w_ty sz) :=
  @x86_rotate_with_carry sz (@mathcomp.word.word.rotl _) (λ r c, msb r != c) v i cf.

Definition Ox86_RCL_instr :=
  mk_instr_ww8b_b2w_0c0 "RCL" x86_RCL check_ror (prim_8_64 RCL) size_8_64 (pp_iname_w_8 "rcl").

Definition rflags_OF {s} sz (i:word s) (r:word sz) rc OF : tpl (b5w_ty sz) :=
  let OF := if i == 1%R then Some OF else None in
  let CF := Some rc in
  let SF := Some (SF_of_word r) in
  let PF := Some (PF_of_word r) in
  let ZF := Some (ZF_of_word r) in
  (:: OF, CF, SF, PF, ZF & r).

Definition x86_SHL sz (v: word sz) (i: u8) : tpl (b5w_ty sz) :=
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    rflags_None_w v
  else
    let rc := msb (wshl v (wunsigned i - 1)) in
    let r  := wshl v (wunsigned i) in
    rflags_OF i r rc (msb r (+) rc).

Definition Ox86_SHL_instr :=
  mk_instr_ww8_b5w_0c0 "SHL" x86_SHL check_ror (prim_8_64 SHL) size_8_64 (pp_iname_w_8 "shl").

Definition x86_SHR sz (v: word sz) (i: u8) : tpl (b5w_ty sz) :=
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    rflags_None_w v
  else
    let rc := lsb (wshr v (wunsigned i - 1)) in
    let r  := wshr v (wunsigned i) in
    rflags_OF i r rc (msb v).

Definition Ox86_SHR_instr :=
  mk_instr_ww8_b5w_0c0 "SHR" x86_SHR check_ror (prim_8_64 SHR) size_8_64 (pp_iname_w_8 "shr").

Definition Ox86_SAL_instr :=
  mk_instr_ww8_b5w_0c0 "SAL" x86_SHL check_ror (prim_8_64 SAL) size_8_64 (pp_iname_w_8 "sal").

Definition x86_SAR sz (v: word sz) (i: u8) : tpl (b5w_ty sz) :=
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    rflags_None_w v
  else
    let rc := lsb (wsar v (wunsigned i - 1)) in
    let r  := wsar v (wunsigned i) in
    rflags_OF i r rc false.

Definition Ox86_SAR_instr :=
  mk_instr_ww8_b5w_0c0 "SAR" x86_SAR check_ror (prim_8_64 SAR) size_8_64 (pp_iname_w_8 "sar").

Definition check_shld (_:wsize):= [::[::rm false; r; ri U8]].

Definition safe_shxd sz : seq safe_cond :=
  match sz with
  | U16 => [:: InRangeMod32 U8 0 16 2 ]
  | _ => [::]
  end.

Definition x86_SHLD sz (v1 v2: word sz) (i: u8) : ex_tpl (b5w_ty sz) :=
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (rflags_None_w v1)
  else
    let j := (wsize_bits sz - wunsigned i)%Z in
    if (j <? 0)%Z then Error ErrArith else
    let rc := msb (wshl v1 (wunsigned i - 1)) in
    let r1 := wshl v1 (wunsigned i) in
    let r2 := wshr v2 j in
    let r  := wor r1 r2 in
    ok (rflags_OF i r rc (msb r (+) rc)).

Lemma x86_SHLD_errtyp (ws : wsize) :
  sem_forall (λ r : result error (sem_tuple (b5w_ty ws)), r ≠ Error ErrType) (w2w8_ty ws) (x86_SHLD (sz:=ws)).
Proof. by move=> v1 v2 i; rewrite /x86_SHLD; case: ifP => // _; case: ifP. Qed.

Lemma x86_shift_maskE  ws :
  x86_shift_mask ws = wrepr U8 (2 ^ Z.of_nat (match ws with U256 => 8 | U128 => 7 | U64 => 6 | _ => 5 end) - 1).
Proof. by case: ws. Qed.

Lemma safe_shxdP ws (v1 v2 : sem_t (sword ws)) (i : sem_t sword8) :
  size_16_64 ws ->
  List.Forall (values.interp_safe_cond (values.list_ltuple (sem_prod_tuple (w2w8_ty ws) v1 v2 i)))
        (safe_shxd ws) ->
  ~ (wsize_bits ws - wunsigned (wand i (x86_shift_mask ws)) < 0)%Z.
Proof.
Opaque Z.sub.
  case: ws v1 v2 => v1 v2 // _ h; rewrite x86_shift_maskE wand_modulo.
  + by have /= {h} := List.Forall_inv h; rewrite truncate_word_u => /(_ _ erefl) hi;
        (have -> : (Z.pow_pos 2 5 = 32)%Z by done); rewrite /wsize_bits /= => h; Lia.lia.
  + have -> : (2 ^ Z.of_nat 5 = 32)%Z by done.
    rewrite /wsize_bits /=; have := Z.mod_pos_bound (wunsigned i) 32 erefl; Lia.nia.
  + have -> : (2 ^ Z.of_nat 6 = 64)%Z by done.
    rewrite /wsize_bits /=; have := Z.mod_pos_bound (wunsigned i) 64 erefl; Lia.nia.
Transparent Z.sub.
Qed.

Lemma safe_wf_shxdP ws : all (λ sc : safe_cond, values.sc_needed_args sc <= size (w2w8_ty ws)) (safe_shxd ws).
Proof. by case: ws. Qed.

Lemma x86_SHLD_safe (ws : wsize) :
  size_16_64 ws -> values.interp_safe_cond_ty (tin:= w2w8_ty ws) (safe_shxd ws) (x86_SHLD (sz:=ws)).
Proof.
  move=> hsz v1 v2 i; rewrite /x86_SHLD.
  case: ifPn => hws h; first eauto.
  case: ZltP; last eauto.
  by move=> /(safe_shxdP hsz h).
Qed.

Definition Ox86_SHLD_instr :=
  mk_instr_w2w8_b5w_01c0 "SHLD" x86_SHLD check_shld safe_shxd (prim_16_64 SHLD) size_16_64 (pp_iname_ww_8 "shld")
   safe_wf_shxdP (fun ws _ => @x86_SHLD_errtyp ws) x86_SHLD_safe.

Definition x86_SHRD sz (v1 v2: word sz) (i: u8) : ex_tpl (b5w_ty sz) :=
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (rflags_None_w v1)
  else
    let j := (wsize_bits sz - wunsigned i)%Z in
    if (j <? 0)%Z then Error ErrArith else
    let rc := lsb (wshr v1 (wunsigned i - 1)) in
    let r1 := wshr v1 (wunsigned i) in
    let r2 := wshl v2 j in
    let r  := wor r1 r2 in
    ok (rflags_OF i r rc (msb r (+) msb v1)).

Lemma x86_SHRD_errtyp (ws : wsize) :
  sem_forall (λ r : result error (sem_tuple (b5w_ty ws)), r ≠ Error ErrType) (w2w8_ty ws) (x86_SHRD (sz:=ws)).
Proof. by move=> v1 v2 i; rewrite /x86_SHRD; case: ifP => // _; case: ifP. Qed.

Lemma x86_SHRD_safe (ws : wsize) :
  size_16_64 ws ->
  values.interp_safe_cond_ty (tin:= w2w8_ty ws) (safe_shxd ws) (x86_SHRD (sz:=ws)).
Proof.
  move=> hsz v1 v2 i; rewrite /safe_shxd /x86_SHRD.
  case: ifPn => hws h; first eauto.
  case: ZltP; last eauto.
  by move=> /(safe_shxdP hsz h).
Qed.

Definition Ox86_SHRD_instr :=
  mk_instr_w2w8_b5w_01c0 "SHRD" x86_SHRD check_shld safe_shxd (prim_16_64 SHRD) size_16_64 (pp_iname_ww_8 "shrd")
   safe_wf_shxdP (fun ws _ => @x86_SHRD_errtyp ws) x86_SHRD_safe.

Definition check_rorx of wsize := [::[::r ; rm true; i U8]].

Definition x86_RORX sz (v: word sz) (i: u8) : word sz :=
  let i := wand i (x86_shift_mask sz) in
  wror v (wunsigned i).

Definition Ox86_RORX_instr :=
  mk_instr_ww8_w_120 "RORX" x86_RORX check_rorx (prim_32_64 RORX) size_32_64 (pp_name "rorx").

Definition x86_bmi_shift sz (op: word sz → Z → word sz) (v i: word sz) : word sz :=
  let i := Z.land (wunsigned i) (wunsigned (x86_shift_mask sz)) in
  op v i.

Definition check_sarx of wsize := [::[::r ; rm true; r]].

Definition x86_SARX sz := x86_bmi_shift (@wsar sz).

Definition Ox86_SARX_instr :=
  mk_instr_w2_w_120 "SARX" x86_SARX check_sarx (prim_32_64 SARX) size_32_64 (pp_name "sarx").

Definition x86_SHRX sz := x86_bmi_shift (@wshr sz).

Definition Ox86_SHRX_instr :=
  mk_instr_w2_w_120 "SHRX" x86_SHRX check_sarx (prim_32_64 SHRX) size_32_64 (pp_name "shrx").

Definition x86_SHLX sz := x86_bmi_shift (@wshl sz).

Definition Ox86_SHLX_instr :=
  mk_instr_w2_w_120 "SHLX" x86_SHLX check_sarx (prim_32_64 SHLX) size_32_64 (pp_name "shlx").

Definition x86_BSWAP sz (v: word sz) : tpl (w_ty sz) := wbswap v.

Definition Ox86_BSWAP_instr :=
  mk_instr_w_w "BSWAP" x86_BSWAP [:: Eu 0] [:: Eu 0] 1 (fun _ => [:: [::r]]) (prim_32_64 BSWAP) size_32_64 (pp_iname "bswap").

Definition x86_POPCNT sz (v: word sz): tpl (b5w_ty sz) :=
  let r := popcnt  v in
  (:: Some false, Some false, Some false, Some false, Some (ZF_of_word v) & r).

Definition Ox86_POPCNT_instr :=
  mk_instr_w_b5w "POPCNT" x86_POPCNT [:: Eu 1] [:: Eu 0] 2 (fun _ => [::r_rm]) (prim_16_64 POPCNT) size_16_64 (pp_name "popcnt").

Definition x86_BTX op sz (x y: word sz) : tpl (bw_ty sz) :=
  let bit := (wunsigned y mod wsize_bits sz)%Z in
  (:: Some (wbit_n x (Z.to_nat bit)) & op sz (wrepr sz (2 ^ bit)) x).

Definition Ox86_BTR_instr :=
  mk_instr_w2_bw "BTR" (x86_BTX wandn) check_bt (prim_16_64 BTR) size_16_64 (pp_iname "btr").

Definition Ox86_BTS_instr :=
  mk_instr_w2_bw "BTS" (x86_BTX (@wor)) check_bt (prim_16_64 BTS) size_16_64 (pp_iname "bts").

Definition x86_PEXT sz (v1 v2: word sz): tpl (w_ty sz) :=
  @pextr sz v1 v2.

Definition Ox86_PEXT_instr :=
  mk_instr_w2_w_120 "PEXT" x86_PEXT (fun _ => [:: [:: r; r; rm true]]) (prim_32_64 PEXT) size_32_64 (pp_name "pext").

Definition x86_PDEP sz (v1 v2: word sz): tpl (w_ty sz) :=
  @pdep sz v1 v2.

Definition Ox86_PDEP_instr :=
  mk_instr_w2_w_120 "PDEP" x86_PDEP (fun _ => [:: [:: r; r; rm true]]) (prim_32_64 PDEP) size_32_64 (pp_name "pdep").

(* Vectorized instruction *)

Definition check_movd (_:wsize) := [:: [::xmm; rm true]].
Definition x86_MOVD sz (v: word sz) : tpl (w_ty U128) :=
  zero_extend U128 v.

Definition Ox86_MOVD_instr :=
  mk_instr_w_w128_10 "MOVD" MSB_MERGE x86_MOVD check_movd (prim_32_64 MOVD) size_32_64 (pp_movd "mov").

Definition Ox86_MOVV_instr :=
  mk_instr_w_w "MOVV" x86_MOVX [:: Eu 1 ] [:: Eu 0 ] 2 (λ _, [:: [:: rm false; xmm ] ]) (prim_32_64 MOVV) size_32_64 (pp_movd "mov").

Definition Ox86_VMOV_instr :=
  mk_instr_w_w128_10 "VMOV" MSB_CLEAR x86_MOVD check_movd (prim_32_64 VMOV) size_32_64 (pp_movd "vmov").

Definition check_vmovdq (_:wsize) := [:: xmm_xmmm; xmmm_xmm].

Definition x86_VMOVDQ sz (v: word sz) : tpl (w_ty sz) := v.

Definition Ox86_VMOVDQA_instr :=
  mk_instr_w_w "VMOVDQA" x86_VMOVDQ [:: Ea 1] [:: Ea 0] 2 check_vmovdq (prim_128_256 VMOVDQA) size_128_256 (pp_name "vmovdqa").

Definition Ox86_VMOVDQU_instr :=
  mk_instr_w_w "VMOVDQU" x86_VMOVDQ [:: Eu 1] [:: Eu 0] 2 check_vmovdq (prim_128_256 VMOVDQU) size_128_256 (pp_name "vmovdqu").

Definition pp_vpmovx name ve sz ve' sz' args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_viname2 ve ve';
     pp_aop_args := zip [:: sz' ; sz ] args; |}.

(* How many elements of size ve in a vector of size ws *)
Definition vector_size (ve: velem) (ws: wsize) : option Z :=
  let: (q, r) := Z.div_eucl (wsize_size ws) (wsize_size ve) in
  if r == 0%Z then Some q else None.

Definition check_vector_length (ve : velem) (sz : wsize) (ve' : velem) (sz' : wsize) :=
  match vector_size ve sz, vector_size ve' sz' with
  | Some i, Some j => i == j
  | _, _ => false
  end.

Definition x86_VPMOVSX (ve: velem) (sz: wsize) (ve': velem) (sz': wsize) (w: word sz) : word sz' :=
  lift1_vec' (@sign_extend ve' ve) sz' w.

Definition Ox86_VPMOVSX_instr :=
  let name := "VPMOVSX"%string in
  (λ ve sz ve' sz',
   mk_instr_safe (pp_ve_sz_ve_sz name ve sz ve' sz') [:: sword sz ] [:: sword sz' ] [:: Eu 1 ] [:: Eu 0 ]
            MSB_CLEAR (@x86_VPMOVSX ve sz ve' sz') [:: [:: xmm ; xmmm true]] 2
                      (size_128_256 sz' && check_vector_length ve sz ve' sz') (pp_vpmovx "vpmovsx" ve sz ve' sz'),
   (name, prim_vv VPMOVSX)
   ).

Definition x86_VPMOVZX (ve: velem) (sz: wsize) (ve': velem) (sz': wsize) (w: word sz) : word sz' :=
  lift1_vec' (@zero_extend ve' ve) sz' w.

Definition Ox86_VPMOVZX_instr :=
  let name := "VPMOVZX"%string in
  (λ ve sz ve' sz',
   mk_instr_safe (pp_ve_sz_ve_sz name ve sz ve' sz') [:: sword sz ] [:: sword sz' ] [:: Eu 1 ] [:: Eu 0 ]
            MSB_CLEAR (@x86_VPMOVZX ve sz ve' sz') [:: [:: xmm ; xmmm true]] 2
                      (size_128_256 sz' && check_vector_length ve sz ve' sz') (pp_vpmovx "vpmovzx" ve sz ve' sz'),
   (name, prim_vv VPMOVZX)
   ).

Definition check_xmm_xmm_xmmm (_:wsize) := [:: xmm_xmm_xmmm].

Definition x86_VPAND sz := @wand sz.

Definition Ox86_VPAND_instr  := mk_instr_w2_w_120    "VPAND"   x86_VPAND  check_xmm_xmm_xmmm (prim_128_256 VPAND) size_128_256 (pp_name "vpand").

Definition x86_VPANDN sz := @wandn sz.

Definition Ox86_VPANDN_instr := mk_instr_w2_w_120    "VPANDN"  x86_VPANDN check_xmm_xmm_xmmm (prim_128_256 VPANDN) size_128_256 (pp_name "vpandn").

Definition x86_VPOR sz := @wor sz.

Definition Ox86_VPOR_instr   := mk_instr_w2_w_120    "VPOR"    x86_VPOR   check_xmm_xmm_xmmm (prim_128_256 VPOR) size_128_256 (pp_name "vpor").

Definition x86_VPXOR sz := @wxor sz.

Definition Ox86_VPXOR_instr  := mk_instr_w2_w_120    "VPXOR"   x86_VPXOR  check_xmm_xmm_xmmm (prim_128_256 VPXOR) size_128_256 (pp_name "vpxor").

Definition x86_VPADD (ve: velem) sz := lift2_vec ve +%R sz.

Definition Ox86_VPADD_instr  := mk_ve_instr_w2_w_120 "VPADD"   x86_VPADD  check_xmm_xmm_xmmm (primV VPADD) (fun ve sz => size_128_256 sz) (pp_viname "vpadd").

Definition x86_VPSUB (ve: velem) sz :=
  lift2_vec ve (fun x y => x - y)%R sz.

Definition Ox86_VPSUB_instr  := mk_ve_instr_w2_w_120 "VPSUB"   x86_VPSUB  check_xmm_xmm_xmmm (primV VPSUB) (fun ve sz => size_128_256 sz) (pp_viname "vpsub").

Definition x86_VPAVG (ve: velem) (sz: wsize) v1 v2 :=
  let avg x y := wrepr ve ((wunsigned x + wunsigned y + 1) / 2) in
  lift2_vec ve avg sz v1 v2.

Definition Ox86_VPAVG_instr := mk_ve_instr_w2_w_120 "VPAVG" x86_VPAVG check_xmm_xmm_xmmm (primV_8_16 VPAVG)
(fun (ve:velem) sz => size_8_16 ve && size_128_256 sz) (pp_viname "vpavg").

Definition x86_VPMULL (ve: velem) sz v1 v2 :=
  lift2_vec ve *%R sz v1 v2.

Definition Ox86_VPMULL_instr := mk_ve_instr_w2_w_120 "VPMULL" x86_VPMULL check_xmm_xmm_xmmm (primV_16_32 VPMULL)
(fun (ve:velem) sz => size_16_32 ve && size_128_256 sz)  (pp_viname "vpmull").

Definition x86_VPMUL sz := @wpmul sz.

Definition Ox86_VPMUL_instr  := ((fun sz => mk_instr_safe (pp_sz "VPMUL" sz) (w2_ty sz sz) (w_ty sz) [:: Eu 1 ; Eu 2] [:: Eu 0] MSB_CLEAR (@x86_VPMUL sz) (check_xmm_xmm_xmmm sz) 3 (size_128_256 sz) (pp_name "vpmuldq" sz)), ("VPMUL"%string, (prim_128_256 VPMUL))).

Definition x86_VPMULU sz := @wpmulu sz.

Definition Ox86_VPMULU_instr := ((fun sz => mk_instr_safe (pp_sz "VPMULU" sz) (w2_ty sz sz) (w_ty sz) [:: Eu 1 ; Eu 2] [:: Eu 0] MSB_CLEAR (@x86_VPMULU sz) (check_xmm_xmm_xmmm sz) 3 (size_128_256 sz) (pp_name "vpmuludq" sz)), ("VPMULU"%string, (prim_128_256 VPMULU))).

Notation mk_instr_vpmulh name semi prc asm_name :=
  ((λ sz,
     mk_instr_safe (pp_ve_sz name VE16 sz) (w2_ty sz sz) (w_ty sz) [:: Eu 1 ; Eu 2 ] [:: Eu 0] (reg_msb_flag sz) (semi sz) (check_xmm_xmm_xmmm sz) 3 (size_128_256 sz) (pp_viname asm_name VE16 sz)), (name%string, primV_16 (λ _, prc)))  (only parsing).

Definition x86_VPMULH sz v1 v2 :=
  lift2_vec U16 (@wmulhs U16) sz v1 v2.

Definition Ox86_VPMULH_instr := mk_instr_vpmulh "VPMULH" x86_VPMULH VPMULH "vpmulh".

Definition x86_VPMULHU sz v1 v2 :=
  lift2_vec U16 (@wmulhu U16) sz v1 v2.

Definition Ox86_VPMULHU_instr := mk_instr_vpmulh "VPMULHU" x86_VPMULHU VPMULHU "vpmulhu".

Definition x86_VPMULHRS sz v1 v2 :=
  lift2_vec U16 (@wmulhrs U16) sz v1 v2.

Definition Ox86_VPMULHRS_instr := mk_instr_vpmulh "VPMULHRS" x86_VPMULHRS VPMULHRS "vpmulhrs".

Definition check_vpextr (_:wsize) :=  [:: [:: rm false; xmm; i U8] ].

Definition pp_viname_t name ve (ts:seq wsize) args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_viname ve false;
     pp_aop_args := zip ts args; |}.

Definition x86_nelem_mask (sze szc:wsize) : u8 :=
  wrepr U8 (two_power_nat (wsize_log2 szc - wsize_log2 sze) - 1).

Definition x86_VPEXTR (ve: wsize) (v: u128) (i: u8) : tpl (w_ty ve) :=
  let i := wand i (x86_nelem_mask ve U128) in
  nth (0%R: word ve) (split_vec ve v) (Z.to_nat (wunsigned i)).

Definition Ox86_VPEXTR_instr :=
  ((fun sz =>
      let ve := match sz with U8 => VE8 | U16 => VE16 | U32 => VE32 | _ => VE64 end in
      mk_instr_safe (pp_sz "VPEXTR" sz) w128w8_ty (w_ty sz) [:: Eu 1 ; Eu 2] [:: Eu 0]
               MSB_CLEAR (@x86_VPEXTR sz) (check_vpextr sz) 3 (size_8_64 sz)
               (pp_viname_t "vpextr" ve [:: if sz==U32 then U32 else U64; U128; U8])),
   ("VPEXTR"%string, (prim_8_64 VPEXTR))).

Definition pp_vpinsr ve args :=
  let rs := match ve with VE8 | VE16 | VE32 => U32 | VE64 => U64 end in
  {| pp_aop_name := "vpinsr";
     pp_aop_ext  := PP_viname ve false;
     pp_aop_args := zip [::U128; U128; rs; U8] args; |}.

Definition check_vpinsr (_:wsize) :=  [:: [:: xmm; xmm; rm true; i U8] ].

Definition x86_VPINSR (ve: velem) (v1: u128) (v2: word ve) (i: u8) : tpl (w_ty U128) :=
  let i := wand i (x86_nelem_mask ve U128) in
  wpinsr v1 v2 i.

Arguments x86_VPINSR : clear implicits.

Definition Ox86_VPINSR_instr  :=
  ((fun (ve:velem) =>
      mk_instr_safe (pp_ve_sz "VPINSR" ve U128) (w128ww8_ty ve) w128_ty [:: Eu 1 ; Eu 2 ; Eu 3] [:: Eu 0] MSB_CLEAR (x86_VPINSR ve)
                               (check_vpinsr ve) 4 true (pp_vpinsr ve)),
   ("VPINSR"%string, primV_128 (λ ve _, VPINSR ve))).

Definition check_xmm_xmm_imm8 (_:wsize) := [:: [:: xmm; xmm; i U8]].

Definition x86_u128_shift sz' sz (op: word sz' → Z → word sz')
  (v: word sz) (c: word U128) : tpl (w_ty sz) :=
  lift1_vec sz' (λ v, op v (wunsigned c)) sz v.

Arguments x86_u128_shift : clear implicits.

Definition check_xmm_xmm_xmmmi of wsize := [:: xmm_xmm_xmmmi U8 ].

Definition x86_VPSLL (ve: velem) sz := x86_u128_shift ve sz (@wshl _).

Definition Ox86_VPSLL_instr :=
  mk_ve_instr_ww128_w_120 "VPSLL" x86_VPSLL check_xmm_xmm_xmmmi (primV_16_64 VPSLL)
  (fun (ve:velem)  sz => size_16_64 ve && size_128_256 sz) (pp_viname_ww_128 "vpsll").

Definition x86_VPSRL (ve: velem) sz := x86_u128_shift ve sz (@wshr _).

Definition Ox86_VPSRL_instr :=
  mk_ve_instr_ww128_w_120 "VPSRL" x86_VPSRL check_xmm_xmm_xmmmi (primV_16_64 VPSRL)
  (fun (ve:velem) sz => size_16_64 ve && size_128_256 sz) (pp_viname_ww_128 "vpsrl").

Definition x86_VPSRA (ve: velem) sz := x86_u128_shift ve sz (@wsar _).

Definition Ox86_VPSRA_instr :=
  mk_ve_instr_ww128_w_120 "VPSRA" x86_VPSRA check_xmm_xmm_xmmmi (primV_16_32 VPSRA)
  (fun (ve:velem) sz => size_16_32 ve && size_128_256 sz) (pp_viname_ww_128 "vpsra").

Definition x86_u128_shift_variable ve sz op v1 v2 : tpl (w_ty sz) :=
  lift2_vec ve (λ v1 v2, op v1 (Z.min (wunsigned v2) (wsize_bits ve))) sz v1 v2.

Arguments x86_u128_shift_variable : clear implicits.

Definition x86_VPSLLV ve sz := x86_u128_shift_variable ve sz (@wshl _).

Definition Ox86_VPSLLV_instr :=
  mk_ve_instr_w2_w_120 "VPSLLV" x86_VPSLLV check_xmm_xmm_xmmm (primV_16_64 VPSLLV)
  (fun (ve:velem)  sz => size_16_64 ve && size_128_256 sz) (pp_viname "vpsllv").

Definition x86_VPSRLV ve sz := x86_u128_shift_variable ve sz (@wshr _).

Definition Ox86_VPSRLV_instr :=
  mk_ve_instr_w2_w_120 "VPSRLV" x86_VPSRLV check_xmm_xmm_xmmm (primV_16_64 VPSRLV)
  (fun (ve:velem) sz => size_16_64 ve && size_128_256 sz) (pp_viname "vpsrlv").

Definition x86_vpsxldq sz op (v1: word sz) (v2: u8) : tpl (w_ty sz) :=
  op v1 v2.

Definition x86_VPSLLDQ sz := x86_vpsxldq (@wpslldq sz).

Definition Ox86_VPSLLDQ_instr :=
  mk_instr_ww8_w_120 "VPSLLDQ" x86_VPSLLDQ check_xmm_xmm_imm8 (prim_128_256 VPSLLDQ) size_128_256 (pp_name "vpslldq").

Definition x86_VPSRLDQ sz := x86_vpsxldq (@wpsrldq sz).

Definition Ox86_VPSRLDQ_instr :=
  mk_instr_ww8_w_120 "VPSRLDQ" x86_VPSRLDQ check_xmm_xmm_imm8 (prim_128_256 VPSRLDQ) size_128_256 (pp_name "vpsrldq").

Definition x86_VPSHUFB sz := lift2_vec U128 (@wpshufb U128) sz.

Definition Ox86_VPSHUFB_instr :=
  mk_instr_w2_w_120 "VPSHUFB" x86_VPSHUFB check_xmm_xmm_xmmm (prim_128_256 VPSHUFB) size_128_256 (pp_name "vpshufb").

Definition check_xmm_xmmm_imm8 (_:wsize) := [:: [:: xmm; xmmm true; i U8]].

Definition x86_vpshuf sz (op: word sz → Z → word sz) (v1: word sz) (v2: u8) : tpl (w_ty sz) :=
  op v1 (wunsigned v2).

Arguments x86_vpshuf : clear implicits.

Definition x86_VPSHUFHW sz := x86_vpshuf sz (@wpshufhw _).

Definition Ox86_VPSHUFHW_instr          :=
  mk_instr_ww8_w_120 "VPSHUFHW" x86_VPSHUFHW check_xmm_xmmm_imm8 (prim_128_256 VPSHUFHW) size_128_256 (pp_name "vpshufhw").

Definition x86_VPSHUFLW sz := x86_vpshuf sz (@wpshuflw _).

Definition Ox86_VPSHUFLW_instr :=
  mk_instr_ww8_w_120 "VPSHUFLW" x86_VPSHUFLW check_xmm_xmmm_imm8 (prim_128_256 VPSHUFLW) size_128_256 (pp_name "vpshuflw").

Definition x86_VPSHUFD sz := x86_vpshuf sz (@wpshufd _).

Definition Ox86_VPSHUFD_instr :=
  mk_instr_ww8_w_120 "VPSHUFD" x86_VPSHUFD check_xmm_xmmm_imm8 (prim_128_256 VPSHUFD) size_128_256 (pp_name "vpshufd").

Definition x86_VPUNPCKH ve sz := @wpunpckh sz ve.

Definition Ox86_VPUNPCKH_instr :=
  mk_ve_instr_w2_w_120 "VPUNPCKH" x86_VPUNPCKH check_xmm_xmm_xmmm (primV VPUNPCKH) (fun ve sz => size_128_256 sz) (pp_viname_long "vpunpckh").

Definition x86_VPUNPCKL ve sz := @wpunpckl sz ve.

Definition Ox86_VPUNPCKL_instr :=
  mk_ve_instr_w2_w_120 "VPUNPCKL" x86_VPUNPCKL check_xmm_xmm_xmmm (primV VPUNPCKL) (fun ve sz => size_128_256 sz) (pp_viname_long "vpunpckl").

Definition check_xmm_xmm_xmmm_imm8 (_:wsize) := [:: [:: xmm; xmm; xmmm true; i U8]].

Definition wpblendw (m : u8) (w1 w2 : word U128) :=
  let v1 := split_vec U16 w1 in
  let v2 := split_vec U16 w2 in
  let b := split_vec 1 m in
  let r := map3 (λ (b0 : (mathcomp.word.word.word 1 : ringType)) (v3 v4 : mathcomp.word.word.word U16), if b0 == 1%R then v4 else v3) b v1 v2 in
  make_vec U128 r.

Definition x86_VPBLEND ve sz (v1 v2: word sz) (m: u8) : tpl (w_ty sz) :=
  if ve == U32 then wpblendd v1 v2 m
  else lift2_vec U128 (wpblendw m) sz v1 v2.

Definition Ox86_VPBLEND_instr :=
  mk_ve_instr_w2w8_w_1230 "VPBLEND" (@x86_VPBLEND) check_xmm_xmm_xmmm_imm8 (primV_16_32 VPBLEND)
  (fun ve sz => size_16_32 ve && size_128_256 sz) (pp_viname "vpblend").

Definition check_xmm_xmm_xmmm_xmm (_:wsize) := [:: [:: xmm; xmm; xmmm true; xmm]].

Definition x86_BLENDV ve sz (x y m: word sz) : tpl (w_ty sz) :=
  blendv ve x y m.

Definition Ox86_BLENDV_instr :=
  (fun ve sz => mk_instr_safe
                  (pp_ve_sz "BLENDV" ve sz) (w3_ty sz) (w_ty sz) [:: Ea 1; Eu 2; Ea 3] [:: Ea 0] MSB_CLEAR
                  (@x86_BLENDV ve sz) (check_xmm_xmm_xmmm_xmm sz) 4 (size_128_256 sz)
                  (pp_name match ve with
                     | VE8 => "vpblendvb"
                     | VE32 => "vblendvps"
                     | VE64 => "vblendvpd"
                     | _ => "<assert false>"
                     end sz),
     ("BLENDV"%string, primV_range [seq PVv ve sz | ve <- [:: VE8; VE32; VE64 ], sz <- [:: U128; U256 ]] BLENDV)
  ).

Definition SaturatedSignedToUnsigned (sz1 sz2:wsize) (w:word sz1) : word sz2 :=
  let i1 := wsigned w in
  let i2 := cmp_max 0%Z (cmp_min i1 (wmax_unsigned sz2)) in
  wrepr sz2 i2.

Definition SaturatedSignedToSigned (sz1 sz2:wsize) (w:word sz1) : word sz2 :=
  let i1 := wsigned w in
  let i2 := cmp_max (wmin_signed sz2) (cmp_min i1 (wmax_signed sz2)) in
  wrepr sz2 i2.

Definition vpack2 (sz1 sz2 sz:wsize) (op:word sz1 -> word sz2) (w1 w2:word sz) : word sz :=
  make_vec sz (map op (split_vec sz1 w1) ++ map op (split_vec sz1 w2)).

Definition x86_VPACKUS ve sz (v1 v2:word sz) : tpl (w_ty sz) :=
  let doit sz (v1 v2:word sz) :=
      if ve == U32 then vpack2 (@SaturatedSignedToUnsigned U32 U16) v1 v2
      else vpack2 (@SaturatedSignedToUnsigned U16 U8) v1 v2 in
  if sz == U128 then doit sz v1 v2
  else lift2_vec U128 (doit U128) sz v1 v2.

Definition Ox86_VPACKUS_instr :=
 mk_ve_instr_w2_w_120 "VPACKUS" x86_VPACKUS check_xmm_xmm_xmmm (primV_16_32 VPACKUS)
   (fun ve sz => size_16_32 ve && size_128_256 sz)
   (fun (ve:velem) => pp_name (if U16 == ve then "vpackuswb"%string else "vpackusdw"%string)).

Definition x86_VPACKSS ve sz (v1 v2:word sz) : tpl (w_ty sz) :=
  let doit sz (v1 v2:word sz) :=
      if ve == U32 then vpack2 (@SaturatedSignedToSigned U32 U16) v1 v2
      else vpack2 (@SaturatedSignedToSigned U16 U8) v1 v2 in
  if sz == U128 then doit sz v1 v2
  else lift2_vec U128 (doit U128) sz v1 v2.

Definition Ox86_VPACKSS_instr :=
 mk_ve_instr_w2_w_120 "VPACKSS" x86_VPACKSS check_xmm_xmm_xmmm (primV_16_32 VPACKSS)
   (fun ve sz => size_16_32 ve && size_128_256 sz)
   (fun (ve:velem) => pp_name (if U16 == ve then "vpacksswb"%string else "vpackssdw"%string)).

Definition wshufps_128 (o : u8) (s1 s2: u128) :=
  @make_vec U32 U128 [:: wpshufd1 s1 o 0; wpshufd1 s1 o 1; wpshufd1 s2 o 2; wpshufd1 s2 o 3].

Definition x86_VSHUFPS sz s1 s2 o : tpl (w_ty sz) :=
  lift2_vec U128 (wshufps_128 o) sz s1 s2.

Definition Ox86_VSHUFPS_instr :=
  mk_instr_w2w8_w_1230 "VSHUFPS" (@x86_VSHUFPS) check_xmm_xmm_xmmm_imm8 (prim_128_256 VSHUFPS)
      size_128_256
      (pp_name "vshufps").

Definition pp_vpbroadcast ve sz args :=
  {| pp_aop_name := "vpbroadcast";
     pp_aop_ext  := PP_viname ve false;
     pp_aop_args := zip [::sz; wsize_of_velem ve] args; |}.

Definition check_xmm_xmmm (_:wsize) := [:: [:: xmm; xmmm true]].

Definition x86_VPBROADCAST ve sz (v: word ve) : tpl (w_ty sz) :=
  wpbroadcast sz v.

Definition Ox86_VPBROADCAST_instr       :=
  mk_ve_instr_w_w_10 "VPBROADCAST" x86_VPBROADCAST check_xmm_xmmm (primV VPBROADCAST)
  (fun ve sz => size_128_256 sz) pp_vpbroadcast.

Definition x86_VMOVSHDUP sz (v: word sz) : tpl (w_ty sz) :=
  wdup_hi VE32 v.

Definition Ox86_VMOVSHDUP_instr :=
  mk_instr_w_w "VMOVSHDUP" x86_VMOVSHDUP [:: Eu 1 ] [:: Eu 0 ] 2 check_xmm_xmmm (prim_128_256 VMOVSHDUP)
  size_128_256 (pp_name "vmovshdup").

Definition x86_VMOVSLDUP sz (v: word sz) : tpl (w_ty sz) :=
  wdup_lo VE32 v.

Definition Ox86_VMOVSLDUP_instr :=
  mk_instr_w_w "VMOVSLDUP" x86_VMOVSLDUP [:: Eu 1 ] [:: Eu 0 ] 2 check_xmm_xmmm (prim_128_256 VMOVSLDUP)
  size_128_256 (pp_name "vmovsldup").

Definition x86_VPALIGNR128 (m:u8) (v1 v2: word U128) : word U128 :=
  let v := make_vec U256 [::v2;v1] in
  let v' := wshr v (wunsigned m * 8) in
  @nth (word U128) 0%R (split_vec U128 v') 0.

Definition x86_VPALIGNR sz (v1 v2: word sz) (m:u8) : tpl (w_ty sz) :=
  lift2_vec U128 (x86_VPALIGNR128 m) sz v1 v2.

Definition Ox86_VPALIGNR_instr :=
  ((fun sz =>
     mk_instr_safe (pp_sz "VPALIGNR" sz) (w2w8_ty sz) (w_ty sz) [:: Eu 1 ; Eu 2 ; Eu 3] [:: Eu 0] MSB_CLEAR
      (@x86_VPALIGNR sz) (check_xmm_xmm_xmmm_imm8 sz) 4 (size_128_256 sz) (pp_name "vpalignr" sz)), ("VPALIGNR"%string, prim_128_256 VPALIGNR)).

(* 256 *)

Definition Ox86_VBROADCASTI128_instr    :=
  (mk_instr_safe (pp_s "VPBROADCAST_2u128") w128_ty w256_ty [:: Eu 1] [:: Eu 0] MSB_CLEAR (x86_VPBROADCAST U256)
            ([:: [::xmm; m true]]) 2 true (pp_name_ty "vbroadcasti128" [::U256; U128]),
   ("VPBROADCAST_2u128"%string, (primM VBROADCASTI128))).

Definition check_xmmm_xmm_imm8 (_:wsize) := [:: [:: xmmm false; xmm; i U8]].

Definition x86_VEXTRACTI128 (v: u256) (i: u8) : tpl (w_ty U128) :=
  let r := if lsb i then wshr v (Z.of_nat U128) else v in
  zero_extend U128 r.

Definition Ox86_VEXTRACTI128_instr :=
  mk_instr_pp "VEXTRACTI128" w256w8_ty w128_ty [:: Eu 1; Eu 2] [:: Eu 0] MSB_CLEAR x86_VEXTRACTI128
              (check_xmmm_xmm_imm8 U256) 3 (primM VEXTRACTI128) (pp_name_ty "vextracti128" [::U128; U256; U8]).

Definition x86_VINSERTI128 (v1: u256) (v2: u128) (m: u8) : tpl (w_ty U256) :=
  winserti128 v1 v2 m.

Definition Ox86_VINSERTI128_instr :=
  mk_instr_pp "VINSERTI128" w256w128w8_ty w256_ty [:: Eu 1; Eu 2; Eu 3] [:: Eu 0] MSB_CLEAR x86_VINSERTI128
              (check_xmm_xmm_xmmm_imm8 U256) 4 (primM VINSERTI128) (pp_name_ty "vinserti128" [::U256;U256; U128; U8]).

Definition x86_VPERM2I128 (v1 v2: u256) (m: u8) : tpl (w_ty U256) :=
  wperm2i128 v1 v2 m.

Definition Ox86_VPERM2I128_instr :=
  mk_instr_pp "VPERM2I128" w256x2w8_ty w256_ty [:: Eu 1; Eu 2; Eu 3] [:: Eu 0] MSB_CLEAR x86_VPERM2I128
              (check_xmm_xmm_xmmm_imm8 U256) 4 (primM VPERM2I128) (pp_name_ty "vperm2i128" [::U256;U256;U256;U8]).

Definition x86_VPERMD (v1 v2: u256): tpl w256_ty :=
  wpermd v1 v2.

Definition Ox86_VPERMD_instr :=
  mk_instr_pp "VPERMD" (w2_ty U256 U256) w256_ty [:: Eu 1; Eu 2] [:: Eu 0] MSB_CLEAR x86_VPERMD
       (check_xmm_xmm_xmmm U256) 3 (primM VPERMD) (pp_name "vpermd" U256).

Definition x86_VPERMQ (v: u256) (m: u8) : tpl (w_ty U256) :=
  wpermq v m.

Definition Ox86_VPERMQ_instr :=
  mk_instr_pp "VPERMQ" w256w8_ty w256_ty [:: Eu 1; Eu 2] [:: Eu 0] MSB_CLEAR x86_VPERMQ
              (check_xmm_xmmm_imm8 U256) 3 (primM VPERMQ) (pp_name_ty "vpermq" [::U256;U256;U8]).

(* TODO: remove *)
Definition x86_VPMOVMSKB ssz dsz (v : word ssz): tpl (w_ty dsz) :=
  zero_extend dsz (movemask VE8 v).

(* TODO: remove *)
Definition Ox86_PMOVMSKB_instr :=
  (fun ssz dsz => mk_instr_safe
    (pp_sz_sz "VPMOVMSKB"%string false ssz dsz) (* Jasmin name *)
    (w_ty ssz) (* args type *)
    (w_ty dsz) (* result type *)
    [:: Eu 1 ] (* args *)
    [:: Eu 0 ]  (* results *)
    MSB_CLEAR (* clear MostSignificantBits *)
    (@x86_VPMOVMSKB ssz dsz) (* semantics *)
    [:: [:: r ; xmm ] ] (* arg checks *)
    2 (* nargs *)
    (size_32_64 dsz && size_128_256 ssz)
    (pp_name_ty "vpmovmskb" [:: dsz; ssz]) (* asm pprinter *)
  , ("VPMOVMSKB"%string, primX VPMOVMSKB) (* jasmin concrete syntax *)
  ).

Definition Ox86_MOVEMASK_instr :=
  (fun (ve: velem) sz =>
     mk_instr_safe (pp_ve_sz "MOVEMASK" ve sz) (w_ty sz) (w_ty U32) [:: Eu 1 ] [:: Eu 0 ] MSB_CLEAR
       (@movemask ve sz) [:: [:: r ; xmm ] ] 2 (((ve : wsize) \in [:: U8; U32; U64 ]) && size_128_256 sz)
       (pp_name_ty match ve with
          | VE8 => "vpmovmskb"
          | VE32 => "vmovmskps"
          | VE64 => "vmovmskpd"
          | _ => "<assert false>"
          end [:: U32; sz ]),
     ("MOVEMASK"%string, primV_range [seq PVv ve sz | ve <- [:: VE8; VE32; VE64 ], sz <- [:: U128; U256 ]] MOVEMASK)
  ).

Definition x86_VPCMPEQ (ve: velem) sz (v1 v2: word sz): tpl(w_ty sz) :=
  wpcmpeq ve v1 v2.

Definition Ox86_VPCMPEQ_instr :=
  (fun (ve: velem) sz => mk_instr_safe
                  (pp_ve_sz "VPCMPEQ"%string ve sz)
                  (w2_ty sz sz)
                  (w_ty sz)
                  [:: Eu 1; Eu 2]
                  [:: Eu 0]
                  MSB_CLEAR
                  (@x86_VPCMPEQ ve sz)
                  (check_xmm_xmm_xmmm sz)
                  3
                  (size_8_64 ve && size_128_256 sz)
                  (pp_viname "vpcmpeq" ve sz)
                ,("VPCMPEQ"%string, primV VPCMPEQ)
  ).

Definition x86_VPCMPGT (ve: velem) sz (v1 v2: word sz): tpl(w_ty sz) :=
  wpcmpgt ve v1 v2.

Definition Ox86_VPCMPGT_instr :=
  (fun (ve: velem) sz => mk_instr_safe
                  (pp_ve_sz "VPCMPGT"%string ve sz)
                  (w2_ty sz sz)
                  (w_ty sz)
                  [:: Eu 1; Eu 2]
                  [:: Eu 0]
                  MSB_CLEAR
                  (@x86_VPCMPGT ve sz)
                  (check_xmm_xmm_xmmm sz)
                  3
                  (size_8_64 ve && size_128_256 sz)
                  (pp_viname "vpcmpgt" ve sz)
                ,("VPCMPGT"%string, primV VPCMPGT)
  ).

Definition x86_VPSIGN (ve: velem) sz (v1 v2: word sz) : tpl (w_ty sz) :=
  lift2_vec ve (λ x m, match wsigned m with Zpos _ => x | Z0 => 0%R | Zneg _ => (- x)%R end) sz v1 v2.

Definition Ox86_VPSIGN_instr :=
  (fun (ve: velem) sz => mk_instr_safe
                  (pp_ve_sz "VPSIGN"%string ve sz)
                  (w2_ty sz sz)
                  (w_ty sz)
                  [:: Ea 1; Eu 2]
                  [:: Ea 0]
                  MSB_CLEAR
                  (@x86_VPSIGN ve sz)
                  (check_xmm_xmm_xmmm sz)
                  3
                  (size_8_32 ve && size_128_256 sz)
                  (pp_viname "vpsign" ve sz)
                ,("VPSIGN"%string, primV_8_32 VPSIGN)
  ).

Definition x86_VPMADDUBSW sz (v v1: word sz) : tpl (w_ty sz) :=
  wpmaddubsw v v1.

Definition Ox86_VPMADDUBSW_instr :=
  (fun sz => mk_instr_safe
                (pp_sz "VPMADDUBSW"%string sz)
                (w2_ty sz sz)
                (w_ty sz)
                [:: Eu 1; Eu 2]
                [:: Eu 0 ]
                MSB_CLEAR
                (@x86_VPMADDUBSW sz)
                (check_xmm_xmm_xmmm sz)
                3
                (size_128_256 sz)
                (pp_name_ty "vpmaddubsw" [:: sz; sz; sz])
             ,("VPMADDUBSW"%string, prim_128_256 VPMADDUBSW)
  ).

Definition x86_VPMADDWD sz (v v1: word sz) : tpl (w_ty sz) :=
  wpmaddwd v v1.

Definition Ox86_VPMADDWD_instr :=
  (fun sz => mk_instr_safe
                (pp_sz "VPMADDWD"%string sz)
                (w2_ty sz sz)
                (w_ty sz)
                [:: Eu 1; Eu 2]
                [:: Eu 0 ]
                MSB_CLEAR
                (@x86_VPMADDWD sz)
                (check_xmm_xmm_xmmm sz)
                3
                (size_128_256 sz)
                (pp_name_ty "vpmaddwd" [:: sz; sz; sz])
             ,("VPMADDWD"%string, prim_128_256 VPMADDWD)
  ).

Definition check_movpd := [:: [::m false; xmm]].

Definition x86_VMOVLPD (v: u128): tpl (w_ty U64) :=
  zero_extend U64 v.

Definition Ox86_VMOVLPD_instr :=
  mk_instr_pp "VMOVLPD" (w_ty U128) (w_ty U64) [:: Eu 1] [:: Eu 0] MSB_CLEAR x86_VMOVLPD check_movpd 2 (primM VMOVLPD) (pp_name_ty "vmovlpd" [::U64; U128]).

Definition x86_VMOVHPD (v: u128): tpl (w_ty U64) :=
  zero_extend U64 (wshr v 64).

Definition Ox86_VMOVHPD_instr :=
  mk_instr_pp "VMOVHPD" (w_ty U128) (w_ty U64) [:: Eu 1] [:: Eu 0] MSB_CLEAR x86_VMOVHPD check_movpd 2 (primM VMOVHPD) (pp_name_ty "vmovhpd" [::U64;U128]).

Definition x86_VPMINS (ve: velem) sz (x y : word sz) : tpl (w_ty sz) :=
  wmin Signed ve x y.

Definition Ox86_VPMINS_instr  :=
  mk_ve_instr_w2_w_120 "VPMINS" x86_VPMINS check_xmm_xmm_xmmm (primV_8_32 VPMINS)
  (fun ve sz => size_8_32 ve && size_128_256 sz) (pp_viname "vpmins").

Definition x86_VPMINU (ve: velem) sz (x y : word sz) : tpl (w_ty sz) :=
  wmin Unsigned ve x y.

Definition Ox86_VPMINU_instr  :=
  mk_ve_instr_w2_w_120 "VPMINU" x86_VPMINU check_xmm_xmm_xmmm (primV_8_32 VPMINU)
  (fun ve sz => size_8_32 ve && size_128_256 sz) (pp_viname "vpminu").

Definition x86_VPMAXS (ve: velem) sz (x y : word sz) : tpl (w_ty sz) :=
  wmax Signed ve x y.

Definition Ox86_VPMAXS_instr  :=
  mk_ve_instr_w2_w_120 "VPMAXS" x86_VPMAXS check_xmm_xmm_xmmm (primV_8_32 VPMAXS)
  (fun ve sz => size_8_32 ve && size_128_256 sz)
  (pp_viname "vpmaxs").

Definition x86_VPMAXU (ve: velem) sz (x y : word sz) : tpl (w_ty sz) :=
  wmax Unsigned ve x y.

Definition Ox86_VPMAXU_instr  :=
  mk_ve_instr_w2_w_120 "VPMAXU" x86_VPMAXU check_xmm_xmm_xmmm (primV_8_32 VPMAXU)
  (fun ve sz => size_8_32 ve && size_128_256 sz)
  (pp_viname "vpmaxu").

Definition x86_VPABS (ve: velem) sz (x : word sz) : tpl (w_ty sz) :=
  wabs ve x.

Definition Ox86_VPABS_instr  :=
  mk_ve_instr_w_w_10 "VPABS" x86_VPABS check_xmm_xmmm (primV_8_32 VPABS)
    (fun ve sz => size_8_32 ve && size_128_256 sz)
    (pp_viname "vpabs").

Definition check_vptest (_:wsize) := [:: xmm_xmmm].

Definition x86_VPTEST sz (x y: word sz) : tpl b5_ty :=
  (:: Some false, Some (wandn x y == 0%R), Some false, Some false & Some (ZF_of_word (wand x y))).

Definition Ox86_VPTEST_instr :=
  (fun sz => mk_instr_safe
               (pp_sz "VPTEST" sz) (w2_ty sz sz) (b5_ty) [:: Eu 0; Eu 1] implicit_flags MSB_MERGE
               (@x86_VPTEST sz) (check_vptest sz) 2
               (size_128_256 sz)
               (pp_name "vptest" sz), ("VPTEST"%string, prim_128_256 VPTEST)).

(* Monitoring instructions.
   These instructions are declared for the convenience of the programmer.
   Nothing can be proved about programs that use these instructions;
   in particular the correctness theorem does not apply to programs using them. *)

Lemma ErrSemUndef_errty l:
  sem_forall (λ r : result error (sem_tuple l), r ≠ Error ErrType) [::] (Error ErrSemUndef).
Proof. done. Qed.

Lemma ErrSemUndef_safe l:
  values.interp_safe_cond_ty (tin := [::])
  [:: ScFalse] (@Error _ (sem_tuple l) ErrSemUndef).
Proof. by move=> h; have := List.Forall_inv h. Qed.

Definition Ox86_RDTSC_instr :=
  (fun sz => mk_instr
              (pp_sz "RDTSC"%string sz) (* Jasmin name *)
              nil (* args type *)
              (w2_ty sz sz) (* result type *)
              nil (* args *)
              [:: R RDX; R RAX] (* results *)
              MSB_CLEAR (* clear MostSignificantBits *)
              (Error ErrSemUndef) (* No semantics *)
              [:: [::]]
              0 (* nargs *)
              [:: ScFalse]
              (size_32_64 sz)
              (pp_name_ty "rdtsc" [:: sz; sz]) (* asm pretty-print*)
              refl_equal
              (fun _ => @ErrSemUndef_errty (w2_ty sz sz))
              (fun _ => @ErrSemUndef_safe (w2_ty sz sz))
   ,("RDTSC"%string, prim_32_64 RDTSC) (* jasmin concrete syntax *)
  ).

Definition Ox86_RDTSCP_instr :=
  (fun sz => mk_instr
              (pp_sz "RDTSCP"%string sz) (* Jasmin name *)
              nil (* args type *)
              (w3_ty sz) (* result type *)
              nil (* args *)
              [:: R RDX; R RAX; R RCX] (* results *)
              MSB_CLEAR (* clear MostSignificantBits *)
              (Error ErrSemUndef) (* No semantics *)
              [:: [::]] (* arg checks *)
              0 (* nargs *)
              [:: ScFalse]
              (size_32_64 sz)
              (pp_name_ty "rdtscp" [:: sz; sz; sz]) (* asm pprinter *)
              refl_equal
              (fun _ => @ErrSemUndef_errty (w3_ty sz))
              (fun _ => @ErrSemUndef_safe (w3_ty sz))
   ,("RDTSCP"%string, prim_32_64 RDTSCP) (* jasmin concrete syntax *)
  ).

(* Fences & cache-related instructions *)
Definition Ox86_CLFLUSH_instr :=
  mk_instr_pp "CLFLUSH" [:: sword Uptr ] [::] [:: Ec 0 ] [::] MSB_CLEAR (λ _, tt) [:: [:: m true ] ] 1 (primM CLFLUSH) (pp_name "clflush" U8).

Definition Ox86_PREFETCHT0_instr :=
  mk_instr_pp "PREFETCHT0" [:: sword Uptr ] [::] [:: Ec 0 ] [::] MSB_CLEAR (λ _, tt) [:: [:: m true ] ] 1 (primM PREFETCHT0) (pp_name "prefetcht0" U8).
Definition Ox86_PREFETCHT1_instr :=
  mk_instr_pp "PREFETCHT1" [:: sword Uptr ] [::] [:: Ec 0 ] [::] MSB_CLEAR (λ _, tt) [:: [:: m true ] ] 1 (primM PREFETCHT1) (pp_name "prefetcht1" U8).
Definition Ox86_PREFETCHT2_instr :=
  mk_instr_pp "PREFETCHT2" [:: sword Uptr ] [::] [:: Ec 0 ] [::] MSB_CLEAR (λ _, tt) [:: [:: m true ] ] 1 (primM PREFETCHT2) (pp_name "prefetcht2" U8).
Definition Ox86_PREFETCHNTA_instr :=
  mk_instr_pp "PREFETCHNTA" [:: sword Uptr ] [::] [:: Ec 0 ] [::] MSB_CLEAR (λ _, tt) [:: [:: m true ] ] 1 (primM PREFETCHNTA) (pp_name "prefetchnta" U8).

Definition Ox86_LFENCE_instr :=
  mk_instr_pp "LFENCE" [::] [::] [::] [::] MSB_CLEAR tt [:: [::] ] 0 (primM LFENCE) (pp_name "lfence" U8).
Definition Ox86_MFENCE_instr :=
  mk_instr_pp "MFENCE" [::] [::] [::] [::] MSB_CLEAR tt [:: [::] ] 0 (primM MFENCE) (pp_name "mfence" U8).
Definition Ox86_SFENCE_instr :=
  mk_instr_pp "SFENCE" [::] [::] [::] [::] MSB_CLEAR tt [:: [::] ] 0 (primM SFENCE) (pp_name "sfence" U8).

(* AES instructions *)
Definition x86_AESDEC          (v1 v2 : u128)           : tpl (w_ty U128) := wAESDEC          v1 v2.
Definition x86_AESDECLAST      (v1 v2 : u128)           : tpl (w_ty U128) := wAESDECLAST      v1 v2.
Definition x86_AESENC          (v1 v2 : u128)           : tpl (w_ty U128) := wAESENC          v1 v2.
Definition x86_AESENCLAST      (v1 v2 : u128)           : tpl (w_ty U128) := wAESENCLAST      v1 v2.
Definition x86_AESIMC          (v1    : u128)           : tpl (w_ty U128) := wAESIMC          v1.
Definition x86_AESKEYGENASSIST (v1    : u128) (v2 : u8) : tpl (w_ty U128) := wAESKEYGENASSIST v1 v2.

Definition mk_instr_aes2 jname aname (constr:x86_op) x86_sem msb_flag :=
  mk_instr_pp jname (w2_ty U128 U128) (w_ty U128) [:: Eu 0; Eu 1] [:: Eu 0] msb_flag x86_sem
         (check_xmm_xmmm U128) 2 (primM constr) (pp_name_ty aname [::U128;U128]).

Definition mk_instr_aes3 jname aname (constr: wsize → x86_op) x86_sem :=
  (λ sz, mk_instr_safe (pp_sz jname sz) (w2_ty sz sz) (w_ty sz) [:: Eu 1; Eu 2]
           [:: Eu 0] MSB_CLEAR
           (lift2_vec U128 x86_sem sz)
           (check_xmm_xmm_xmmm sz) 3
           (size_128_256 sz)
           (pp_name_ty aname [:: sz; sz; sz ]),
   (jname%string, prim_128_256 constr)).

Definition Ox86_AESDEC_instr :=
  mk_instr_aes2 "AESDEC" "aesdec" AESDEC x86_AESDEC MSB_MERGE.

Definition Ox86_VAESDEC_instr :=
  mk_instr_aes3 "VAESDEC" "vaesdec" VAESDEC wAESDEC.

Definition Ox86_AESDECLAST_instr :=
  mk_instr_aes2 "AESDECLAST" "aesdeclast" AESDECLAST x86_AESDECLAST MSB_MERGE.

Definition Ox86_VAESDECLAST_instr :=
  mk_instr_aes3 "VAESDECLAST" "vaesdeclast" VAESDECLAST wAESDECLAST.

Definition Ox86_AESENC_instr :=
  mk_instr_aes2 "AESENC" "aesenc" AESENC x86_AESENC MSB_MERGE.

Definition Ox86_VAESENC_instr :=
  mk_instr_aes3 "VAESENC" "vaesenc" VAESENC wAESENC.

Definition Ox86_AESENCLAST_instr :=
  mk_instr_aes2 "AESENCLAST" "aesenclast" AESENCLAST x86_AESENCLAST MSB_MERGE.

Definition Ox86_VAESENCLAST_instr :=
  mk_instr_aes3 "VAESENCLAST" "vaesenclast" VAESENCLAST wAESENCLAST.

Definition Ox86_AESIMC_instr :=
  mk_instr_pp "AESIMC" (w_ty U128) (w_ty U128) [:: Eu 1] [:: Eu 0] MSB_MERGE x86_AESIMC
         (check_xmm_xmmm U128) 2 (primM AESIMC) (pp_name_ty "aesimc" [::U128;U128]).

Definition Ox86_VAESIMC_instr :=
  mk_instr_pp "VAESIMC" (w_ty U128) (w_ty U128) [:: Eu 1] [:: Eu 0] MSB_CLEAR x86_AESIMC
         (check_xmm_xmmm U128) 2 (primM VAESIMC) (pp_name_ty "vaesimc" [::U128;U128]).

Definition Ox86_AESKEYGENASSIST_instr :=
  mk_instr_pp "AESKEYGENASSIST" (w2_ty U128 U8) (w_ty U128) [:: Eu 1; Eu 2] [:: Eu 0]
    MSB_MERGE x86_AESKEYGENASSIST
   (check_xmm_xmmm_imm8 U128) 3 (primM AESKEYGENASSIST)
   (pp_name_ty "aeskeygenassist" [::U128;U128;U8]).

Definition Ox86_VAESKEYGENASSIST_instr :=
  mk_instr_pp "VAESKEYGENASSIST" (w2_ty U128 U8) (w_ty U128) [:: Eu 1; Eu 2] [:: Eu 0]
    MSB_CLEAR x86_AESKEYGENASSIST
   (check_xmm_xmmm_imm8 U128) 3 (primM VAESKEYGENASSIST)
   (pp_name_ty "vaeskeygenassist" [::U128;U128;U8]).

(* PCLMULDQD instructions *)
(* --------------------------------------------------------------------------------------
Instruction:		PCLMULQDQ xmm1, xmm2/m128, imm8
CPUID feature flag:	PCLMULQDQ
Description:		Carry-less multiplication of one quadword of xmm1 by one quadword
			of xmm2/m128, stores the 128-bit result in xmm1. The immediate is
			used to determine which quadwords of xmm1 and xmm2/m128 should be
			used.
Instruction:		VPCLMULQDQ xmm1, xmm2, xmm3/m128, imm8
CPUID feature flag:	PCLMULQDQ AVX
Description:		Carry-less multiplication of one quadword of xmm2 by one quadword
			of xmm3/m128, stores the 128-bit result in xmm1. The immediate is
			used to determine which quadwords of xmm2 and xmm3/m128 should be
			used.
Instruction:		VPCLMULQDQ ymm1, ymm2, ymm3/m256, imm8
CPUID feature flag:	VPCLMULQDQ
Description:		Carry-less multiplication of one quadword of ymm2 by one quadword
			of ymm3/m256, stores the 128-bit result in ymm1. The immediate is
			used to determine which quadwords of ymm2 and ymm3/m256 should be
			used.                                                            *)

Definition wclmulq (x1 x2: u64): word U128 :=
 let x := zero_extend U128 x1 in
 foldr (fun k r => wxor (if wbit_n x2 k then wshl x (Z.of_nat k) else 0%R) r) 0%R (iota 0 64).

Definition wVPCLMULDQD sz (w1 w2: word sz) (k: u8): word sz :=
 let get1 (w: u128) := @nth u64 0%R (split_vec U64 w) (wbit_n k 0) in
 let get2 (w: u128) := @nth u64 0%R (split_vec U64 w) (wbit_n k 4) in
 let f (w1 w2: u128) := wclmulq (get1 w1) (get2 w2) in
 make_vec sz (map2 f (split_vec U128 w1) (split_vec U128 w2)).

Definition x86_VPCLMULQDQ sz (v1 v2: word sz) (k: u8): tpl (w_ty sz) :=
 wVPCLMULDQD v1 v2 k.

Definition Ox86_PCLMULQDQ_instr :=
  mk_instr_pp "PCLMULQDQ" [:: sword U128; sword U128; sword U8] (w_ty U128)
    [:: Eu 0; Eu 1; Eu 2] [:: Eu 0] MSB_CLEAR (@x86_VPCLMULQDQ U128)
    (check_xmm_xmmm_imm8 U128) 3 (primM PCLMULQDQ)
    (pp_name_ty "pclmulqdq" [::U128;U128;U8]).

Definition Ox86_VPCLMULQDQ_instr :=
 (fun sz =>
   mk_instr_safe (pp_sz "VPCLMULQDQ"%string sz) [:: sword sz; sword sz; sword U8] (w_ty sz)
       [:: Eu 1; Eu 2; Eu 3] [:: Eu 0] MSB_CLEAR (@x86_VPCLMULQDQ sz)
       (check_xmm_xmm_xmmm_imm8 sz) 4 (size_128_256 sz) (pp_name "vpclmulqdq" sz)
 , ("VPCLMULQDQ"%string, prim_128_256 VPCLMULQDQ)).

(* -------------------------------------------------------------------------------------- *)
(* SHA instructions *)
Definition Ox86_SHA256RNDS2_instr :=
  mk_instr_pp "SHA256RNDS2" (w3_ty U128) (w_ty U128)
    [:: Eu 0; Eu 1; ADExplicit (AK_mem Unaligned) 2 (ACR_vector XMM0)]
    [:: Eu 0] MSB_MERGE sha256rnds2
    [:: [:: xmm; xmmm true; xmm ]] 3 (primM SHA256RNDS2) (pp_name_ty "sha256rnds2" [:: U128; U128; U128 ]).

Definition Ox86_SHA256MSG1_instr :=
  mk_instr_pp "SHA256MSG1" (w2_ty U128 U128) (w_ty U128) [:: Eu 0; Eu 1] [:: Eu 0] MSB_MERGE sha256msg1
    (check_xmm_xmmm U128) 2 (primM SHA256MSG1) (pp_name_ty "sha256msg1" [::U128;U128]).

Definition Ox86_SHA256MSG2_instr :=
  mk_instr_pp "SHA256MSG2" (w2_ty U128 U128) (w_ty U128) [:: Eu 0; Eu 1] [:: Eu 0] MSB_MERGE sha256msg2
         (check_xmm_xmmm U128) 2 (primM SHA256MSG2) (pp_name_ty "sha256msg2" [::U128;U128]).

(* -------------------------------------------------------------------------------------- *)

Definition x86_instr_desc o : instr_desc_t :=
  match o with
  | MOV sz             => Ox86_MOV_instr.1 sz
  | MOVSX sz sz'       => Ox86_MOVSX_instr.1 sz sz'
  | MOVZX sz sz'       => Ox86_MOVZX_instr.1 sz sz'
  | CMOVcc sz          => Ox86_CMOVcc_instr.1 sz
  | XCHG sz            => Ox86_XCHG_instr.1 sz
  | BSWAP sz           => Ox86_BSWAP_instr.1 sz
  | POPCNT sz          => Ox86_POPCNT_instr.1 sz
  | BTR sz             => Ox86_BTR_instr.1 sz
  | BTS sz             => Ox86_BTS_instr.1 sz
  | PEXT sz            => Ox86_PEXT_instr.1 sz
  | PDEP sz            => Ox86_PDEP_instr.1 sz
  | CQO sz             => Ox86_CQO_instr.1 sz
  | ADD sz             => Ox86_ADD_instr.1 sz
  | SUB sz             => Ox86_SUB_instr.1 sz
  | MUL sz             => Ox86_MUL_instr.1 sz
  | IMUL sz            => Ox86_IMUL_instr.1 sz
  | IMULr sz           => Ox86_IMULr_instr.1 sz
  | IMULri sz          => Ox86_IMULri_instr.1 sz
  | DIV sz             => Ox86_DIV_instr.1 sz
  | IDIV sz            => Ox86_IDIV_instr.1 sz
  | ADC sz             => Ox86_ADC_instr.1 sz
  | ADCX sz            => Ox86_ADCX_instr.1 sz
  | ADOX sz            => Ox86_ADOX_instr.1 sz
  | MULX_lo_hi sz      => Ox86_MULX_lo_hi_instr.1 sz
  | SBB sz             => Ox86_SBB_instr.1 sz
  | NEG sz             => Ox86_NEG_instr.1 sz
  | INC sz             => Ox86_INC_instr.1 sz
  | DEC sz             => Ox86_DEC_instr.1 sz
  | LZCNT sz           => Ox86_LZCNT_instr.1 sz
  | TZCNT sz           => Ox86_TZCNT_instr.1 sz
  | SETcc              => Ox86_SETcc_instr.1
  | BT sz              => Ox86_BT_instr.1 sz
  | CLC                => Ox86_CLC_instr.1
  | STC                => Ox86_STC_instr.1
  | LEA sz             => Ox86_LEA_instr.1 sz
  | TEST sz            => Ox86_TEST_instr.1 sz
  | CMP sz             => Ox86_CMP_instr.1 sz
  | AND sz             => Ox86_AND_instr.1 sz
  | ANDN sz            => Ox86_ANDN_instr.1 sz
  | OR sz              => Ox86_OR_instr.1 sz
  | XOR sz             => Ox86_XOR_instr.1 sz
  | NOT sz             => Ox86_NOT_instr.1 sz
  | ROL sz             => Ox86_ROL_instr.1 sz
  | ROR sz             => Ox86_ROR_instr.1 sz
  | RCL sz             => Ox86_RCL_instr.1 sz
  | RCR sz             => Ox86_RCR_instr.1 sz
  | SHL sz             => Ox86_SHL_instr.1 sz
  | SHR sz             => Ox86_SHR_instr.1 sz
  | SAR sz             => Ox86_SAR_instr.1 sz
  | SAL sz             => Ox86_SAL_instr.1 sz
  | SHLD sz            => Ox86_SHLD_instr.1 sz
  | SHRD sz            => Ox86_SHRD_instr.1 sz
  | RORX sz            => Ox86_RORX_instr.1 sz
  | SARX sz            => Ox86_SARX_instr.1 sz
  | SHRX sz            => Ox86_SHRX_instr.1 sz
  | SHLX sz            => Ox86_SHLX_instr.1 sz
  | MOVX sz            => Ox86_MOVX_instr.1 sz
  | POR                => Ox86_POR_instr.1
  | PADD ve sz         => Ox86_PADD_instr.1 ve sz
  | MOVD sz            => Ox86_MOVD_instr.1 sz
  | MOVV sz            => Ox86_MOVV_instr.1 sz
  | VMOV sz            => Ox86_VMOV_instr.1 sz
  | VPINSR sz          => Ox86_VPINSR_instr.1 sz
  | VEXTRACTI128       => Ox86_VEXTRACTI128_instr.1
  | VMOVDQA sz         => Ox86_VMOVDQA_instr.1 sz
  | VMOVDQU sz         => Ox86_VMOVDQU_instr.1 sz
  | VPMOVSX ve sz ve' sz' => Ox86_VPMOVSX_instr.1 ve sz ve' sz'
  | VPMOVZX ve sz ve' sz' => Ox86_VPMOVZX_instr.1 ve sz ve' sz'
  | VPAND sz           => Ox86_VPAND_instr.1 sz
  | VPANDN sz          => Ox86_VPANDN_instr.1 sz
  | VPOR sz            => Ox86_VPOR_instr.1 sz
  | VPXOR sz           => Ox86_VPXOR_instr.1 sz
  | VPADD sz sz'       => Ox86_VPADD_instr.1 sz sz'
  | VPSUB sz sz'       => Ox86_VPSUB_instr.1 sz sz'
  | VPAVG sz sz'       => Ox86_VPAVG_instr.1 sz sz'
  | VPMULL sz sz'      => Ox86_VPMULL_instr.1 sz sz'
  | VPMUL sz           => Ox86_VPMUL_instr.1 sz
  | VPMULU sz          => Ox86_VPMULU_instr.1 sz
  | VPMULH sz          => Ox86_VPMULH_instr.1 sz
  | VPMULHU sz         => Ox86_VPMULHU_instr.1 sz
  | VPMULHRS sz        => Ox86_VPMULHRS_instr.1 sz
  | VPSLL sz sz'       => Ox86_VPSLL_instr.1 sz sz'
  | VPSRL sz sz'       => Ox86_VPSRL_instr.1 sz sz'
  | VPSRA sz sz'       => Ox86_VPSRA_instr.1 sz sz'
  | VPSLLV sz sz'      => Ox86_VPSLLV_instr.1 sz sz'
  | VPSRLV sz sz'      => Ox86_VPSRLV_instr.1 sz sz'
  | VPSLLDQ sz         => Ox86_VPSLLDQ_instr.1 sz
  | VPSRLDQ sz         => Ox86_VPSRLDQ_instr.1 sz
  | VPSHUFB sz         => Ox86_VPSHUFB_instr.1 sz
  | VPSHUFHW sz        => Ox86_VPSHUFHW_instr.1 sz
  | VPSHUFLW sz        => Ox86_VPSHUFLW_instr.1 sz
  | VPSHUFD sz         => Ox86_VPSHUFD_instr.1 sz
  | VSHUFPS sz         => Ox86_VSHUFPS_instr.1 sz
  | VPUNPCKH sz sz'    => Ox86_VPUNPCKH_instr.1 sz sz'
  | VPUNPCKL sz sz'    => Ox86_VPUNPCKL_instr.1 sz sz'
  | VPBLEND ve sz      => Ox86_VPBLEND_instr.1 ve sz
  | BLENDV ve sz       => Ox86_BLENDV_instr.1 ve sz
  | VPACKUS ve sz      => Ox86_VPACKUS_instr.1 ve sz
  | VPACKSS ve sz      => Ox86_VPACKSS_instr.1 ve sz
  | VPBROADCAST sz sz' => Ox86_VPBROADCAST_instr.1 sz sz'
  | VMOVSHDUP sz       => Ox86_VMOVSHDUP_instr.1 sz
  | VMOVSLDUP sz       => Ox86_VMOVSLDUP_instr.1 sz
  | VPALIGNR sz        => Ox86_VPALIGNR_instr.1 sz
  | VBROADCASTI128     => Ox86_VBROADCASTI128_instr.1
  | VPERM2I128         => Ox86_VPERM2I128_instr.1
  | VPERMD             => Ox86_VPERMD_instr.1
  | VPERMQ             => Ox86_VPERMQ_instr.1
  | VINSERTI128        => Ox86_VINSERTI128_instr.1
  | VPEXTR ve          => Ox86_VPEXTR_instr.1 ve
  | VPMOVMSKB sz sz'   => Ox86_PMOVMSKB_instr.1 sz sz'
  | MOVEMASK ve sz     => Ox86_MOVEMASK_instr.1 ve sz
  | VPCMPEQ ve sz      => Ox86_VPCMPEQ_instr.1 ve sz
  | VPCMPGT ve sz      => Ox86_VPCMPGT_instr.1 ve sz
  | VPSIGN ve sz       => Ox86_VPSIGN_instr.1 ve sz
  | VPMADDUBSW sz      => Ox86_VPMADDUBSW_instr.1 sz
  | VPMADDWD sz        => Ox86_VPMADDWD_instr.1 sz
  | VMOVLPD            => Ox86_VMOVLPD_instr.1
  | VMOVHPD            => Ox86_VMOVHPD_instr.1
  | VPMINU ve sz       => Ox86_VPMINU_instr.1 ve sz
  | VPMINS ve sz       => Ox86_VPMINS_instr.1 ve sz
  | VPMAXU ve sz       => Ox86_VPMAXU_instr.1 ve sz
  | VPMAXS ve sz       => Ox86_VPMAXS_instr.1 ve sz
  | VPABS ve sz        => Ox86_VPABS_instr.1 ve sz
  | VPTEST sz          => Ox86_VPTEST_instr.1 sz
  | CLFLUSH            => Ox86_CLFLUSH_instr.1
  | PREFETCHT0         => Ox86_PREFETCHT0_instr.1
  | PREFETCHT1         => Ox86_PREFETCHT1_instr.1
  | PREFETCHT2         => Ox86_PREFETCHT2_instr.1
  | PREFETCHNTA        => Ox86_PREFETCHNTA_instr.1
  | LFENCE             => Ox86_LFENCE_instr.1
  | MFENCE             => Ox86_MFENCE_instr.1
  | SFENCE             => Ox86_SFENCE_instr.1
  | RDTSC sz           => Ox86_RDTSC_instr.1 sz
  | RDTSCP sz          => Ox86_RDTSCP_instr.1 sz
  | AESDEC             => Ox86_AESDEC_instr.1
  | VAESDEC sz         => Ox86_VAESDEC_instr.1 sz
  | AESDECLAST         => Ox86_AESDECLAST_instr.1
  | VAESDECLAST sz     => Ox86_VAESDECLAST_instr.1 sz
  | AESENC             => Ox86_AESENC_instr.1
  | VAESENC sz         => Ox86_VAESENC_instr.1 sz
  | AESENCLAST         => Ox86_AESENCLAST_instr.1
  | VAESENCLAST sz     => Ox86_VAESENCLAST_instr.1 sz
  | AESIMC             => Ox86_AESIMC_instr.1
  | VAESIMC            => Ox86_VAESIMC_instr.1
  | AESKEYGENASSIST    => Ox86_AESKEYGENASSIST_instr.1
  | VAESKEYGENASSIST   => Ox86_VAESKEYGENASSIST_instr.1
  | PCLMULQDQ          => Ox86_PCLMULQDQ_instr.1
  | VPCLMULQDQ sz      => Ox86_VPCLMULQDQ_instr.1 sz
  | SHA256RNDS2        => Ox86_SHA256RNDS2_instr.1
  | SHA256MSG1         => Ox86_SHA256MSG1_instr.1
  | SHA256MSG2         => Ox86_SHA256MSG2_instr.1
  end.

(* -------------------------------------------------------------------- *)

Definition x86_prim_string :=
 [::
   Ox86_MOV_instr.2;
   Ox86_MOVSX_instr.2;
   Ox86_MOVZX_instr.2;
   Ox86_CMOVcc_instr.2;
   Ox86_XCHG_instr.2;
   Ox86_BSWAP_instr.2;
   Ox86_POPCNT_instr.2;
   Ox86_BTR_instr.2;
   Ox86_BTS_instr.2;
   Ox86_PEXT_instr.2;
   Ox86_PDEP_instr.2;
   Ox86_CQO_instr.2;
   Ox86_ADD_instr.2;
   Ox86_SUB_instr.2;
   Ox86_MUL_instr.2;
   Ox86_IMUL_instr.2;
   Ox86_IMULr_instr.2;
   Ox86_IMULri_instr.2;
   Ox86_DIV_instr.2;
   Ox86_IDIV_instr.2;
   Ox86_ADC_instr.2;
   Ox86_ADCX_instr.2;
   Ox86_ADOX_instr.2;
   Ox86_MULX_lo_hi_instr.2;
   Ox86_SBB_instr.2;
   Ox86_NEG_instr.2;
   Ox86_INC_instr.2;
   Ox86_DEC_instr.2;
   Ox86_LZCNT_instr.2;
   Ox86_TZCNT_instr.2;
   Ox86_SETcc_instr.2;
   Ox86_BT_instr.2;
   Ox86_CLC_instr.2;
   Ox86_STC_instr.2;
   Ox86_LEA_instr.2;
   Ox86_TEST_instr.2;
   Ox86_CMP_instr.2;
   Ox86_AND_instr.2;
   Ox86_ANDN_instr.2;
   Ox86_OR_instr.2;
   Ox86_XOR_instr.2;
   Ox86_NOT_instr.2;
   Ox86_ROL_instr.2;
   Ox86_ROR_instr.2;
   Ox86_RCL_instr.2;
   Ox86_RCR_instr.2;
   Ox86_SHL_instr.2;
   Ox86_SHR_instr.2;
   Ox86_SAR_instr.2;
   Ox86_SAL_instr.2;
   Ox86_SHLD_instr.2;
   Ox86_SHRD_instr.2;
   Ox86_RORX_instr.2;
   Ox86_SARX_instr.2;
   Ox86_SHRX_instr.2;
   Ox86_SHLX_instr.2;
   Ox86_MOVX_instr.2;
   Ox86_POR_instr.2;
   Ox86_PADD_instr.2;
   Ox86_MOVD_instr.2;
   Ox86_MOVV_instr.2;
   Ox86_VMOV_instr.2;
   Ox86_VPMOVSX_instr.2;
   Ox86_VPMOVZX_instr.2;
   Ox86_VPINSR_instr.2;
   Ox86_VEXTRACTI128_instr.2;
   Ox86_VMOVDQA_instr.2;
   Ox86_VMOVDQU_instr.2;
   Ox86_VPAND_instr.2;
   Ox86_VPANDN_instr.2;
   Ox86_VPOR_instr.2;
   Ox86_VPXOR_instr.2;
   Ox86_VPADD_instr.2;
   Ox86_VPSUB_instr.2;
   Ox86_VPAVG_instr.2;
   Ox86_VPMULL_instr.2;
   Ox86_VPMUL_instr.2;
   Ox86_VPMULU_instr.2;
   Ox86_VPMULH_instr.2;
   Ox86_VPMULHU_instr.2;
   Ox86_VPMULHRS_instr.2;
   Ox86_VPSLL_instr.2;
   Ox86_VPSRL_instr.2;
   Ox86_VPSRA_instr.2;
   Ox86_VPSLLV_instr.2;
   Ox86_VPSRLV_instr.2;
   Ox86_VPSLLDQ_instr.2;
   Ox86_VPSRLDQ_instr.2;
   Ox86_VPSHUFB_instr.2;
   Ox86_VPSHUFHW_instr.2;
   Ox86_VPSHUFLW_instr.2;
   Ox86_VPSHUFD_instr.2;
   Ox86_VSHUFPS_instr.2;
   Ox86_VPUNPCKH_instr.2;
   Ox86_VPUNPCKL_instr.2;
   Ox86_VPBLEND_instr.2;
   Ox86_BLENDV_instr.2;
   Ox86_VPACKUS_instr.2;
   Ox86_VPACKSS_instr.2;
   Ox86_VPBROADCAST_instr.2;
   Ox86_VMOVSHDUP_instr.2;
   Ox86_VMOVSLDUP_instr.2;
   Ox86_VPALIGNR_instr.2;
   Ox86_VBROADCASTI128_instr.2;
   Ox86_VPERM2I128_instr.2;
   Ox86_VPERMD_instr.2;
   Ox86_VPERMQ_instr.2;
   Ox86_VINSERTI128_instr.2;
   Ox86_VPEXTR_instr.2;
   Ox86_PMOVMSKB_instr.2;
   Ox86_MOVEMASK_instr.2;
   Ox86_VPCMPEQ_instr.2;
   Ox86_VPCMPGT_instr.2;
   Ox86_VPSIGN_instr.2;
   Ox86_VPMADDUBSW_instr.2;
   Ox86_VPMADDWD_instr.2;
   Ox86_VMOVLPD_instr.2;
   Ox86_VMOVHPD_instr.2;
   Ox86_VPMINU_instr.2;
   Ox86_VPMINS_instr.2;
   Ox86_VPMAXU_instr.2;
   Ox86_VPMAXS_instr.2;
   Ox86_VPABS_instr.2;
   Ox86_VPTEST_instr.2;
   Ox86_CLFLUSH_instr.2;
   Ox86_PREFETCHT0_instr.2;
   Ox86_PREFETCHT1_instr.2;
   Ox86_PREFETCHT2_instr.2;
   Ox86_PREFETCHNTA_instr.2;
   Ox86_LFENCE_instr.2;
   Ox86_MFENCE_instr.2;
   Ox86_SFENCE_instr.2;
   Ox86_RDTSC_instr.2;
   Ox86_RDTSCP_instr.2;
   Ox86_AESDEC_instr.2;
   Ox86_VAESDEC_instr.2;
   Ox86_AESDECLAST_instr.2;
   Ox86_VAESDECLAST_instr.2;
   Ox86_AESENC_instr.2;
   Ox86_VAESENC_instr.2;
   Ox86_AESENCLAST_instr.2;
   Ox86_VAESENCLAST_instr.2;
   Ox86_AESIMC_instr.2;
   Ox86_VAESIMC_instr.2;
   Ox86_AESKEYGENASSIST_instr.2;
   Ox86_VAESKEYGENASSIST_instr.2;
   Ox86_PCLMULQDQ_instr.2;
   Ox86_VPCLMULQDQ_instr.2;
   Ox86_SHA256RNDS2_instr.2;
   Ox86_SHA256MSG1_instr.2;
   Ox86_SHA256MSG2_instr.2;
   ("VPMAX"%string,
     primSV_8_32 (fun signedness ve sz =>
              if signedness is Signed then VPMAXS ve sz else VPMAXU ve sz));
   ("VPMIN"%string,
     primSV_8_32 (fun signedness ve sz =>
              if signedness is Signed then VPMINS ve sz else VPMINU ve sz))
 ].

#[global]
Instance eqC_x86_op : eqTypeC x86_op :=
  { ceqP := x86_op_eqb_OK }.

#[global]
Instance x86_op_decl : asm_op_decl x86_op := {
   instr_desc_op  := x86_instr_desc;
   prim_string    := x86_prim_string;
}.

Definition x86_prog := @asm_prog register _ _ _ _ _ _ x86_op_decl.
