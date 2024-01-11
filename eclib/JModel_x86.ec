(* -------------------------------------------------------------------- *)
require import AllCore BitEncoding IntDiv SmtMap Ring List StdOrder Bool.
(*---*) import CoreMap Map Ring.IntID IntOrder .
require export JModel_common JArray JWord_array Jslh JMemory AES.


(* ------------------------------------------------------------------- *)

(* Semantics for expressions *)
abbrev [-printing] (\vshr8u128)  (w1:W128.t) (w2:W8.t) = VPSRL_16u8 w1 w2.
abbrev [-printing] (\vshr16u128) (w1:W128.t) (w2:W8.t) = VPSRL_8u16 w1 w2.
abbrev [-printing] (\vshr32u128) (w1:W128.t) (w2:W8.t) = VPSRL_4u32 w1 w2.
abbrev [-printing] (\vshr64u128) (w1:W128.t) (w2:W8.t) = VPSRL_2u64 w1 w2.

abbrev [-printing] (\vshl8u128)  (w1:W128.t) (w2:W8.t) = VPSLL_16u8 w1 w2.
abbrev [-printing] (\vshl16u128) (w1:W128.t) (w2:W8.t) = VPSLL_8u16 w1 w2.
abbrev [-printing] (\vshl32u128) (w1:W128.t) (w2:W8.t) = VPSLL_4u32 w1 w2.
abbrev [-printing] (\vshl64u128) (w1:W128.t) (w2:W8.t) = VPSLL_2u64 w1 w2.

abbrev [-printing] (\vsar8u128)  (w1:W128.t) (w2:W8.t) = VPSRA_16u8 w1 w2.
abbrev [-printing] (\vsar16u128) (w1:W128.t) (w2:W8.t) = VPSRA_8u16 w1 w2.
abbrev [-printing] (\vsar32u128) (w1:W128.t) (w2:W8.t) = VPSRA_4u32 w1 w2.
abbrev [-printing] (\vsar64u128) (w1:W128.t) (w2:W8.t) = VPSRA_2u64 w1 w2.

abbrev [-printing] (\vadd8u128)  (w1 w2:W128.t) = VPADD_16u8 w1 w2.
abbrev [-printing] (\vadd16u128) (w1 w2:W128.t) = VPADD_8u16 w1 w2.
abbrev [-printing] (\vadd32u128) (w1 w2:W128.t) = VPADD_4u32 w1 w2.
abbrev [-printing] (\vadd64u128) (w1 w2:W128.t) = VPADD_2u64 w1 w2.

abbrev [-printing] (\vsub8u128)  (w1 w2:W128.t) = VPSUB_16u8 w1 w2.
abbrev [-printing] (\vsub16u128) (w1 w2:W128.t) = VPSUB_8u16 w1 w2.
abbrev [-printing] (\vsub32u128) (w1 w2:W128.t) = VPSUB_4u32 w1 w2.
abbrev [-printing] (\vsub64u128) (w1 w2:W128.t) = VPSUB_2u64 w1 w2.

abbrev [-printing] (\vmul8u128)  (w1 w2:W128.t) = VPMULL_16u8 w1 w2.
abbrev [-printing] (\vmul16u128) (w1 w2:W128.t) = VPMULL_8u16 w1 w2.
abbrev [-printing] (\vmul32u128) (w1 w2:W128.t) = VPMULL_4u32 w1 w2.
abbrev [-printing] (\vmul64u128) (w1 w2:W128.t) = VPMULL_2u64 w1 w2.

abbrev [-printing] (\vshr8u256)  (w1:W256.t) (w2:W8.t) = VPSRL_32u8 w1 w2.
abbrev [-printing] (\vshr16u256) (w1:W256.t) (w2:W8.t) = VPSRL_16u16 w1 w2.
abbrev [-printing] (\vshr32u256) (w1:W256.t) (w2:W8.t) = VPSRL_8u32 w1 w2.
abbrev [-printing] (\vshr64u256) (w1:W256.t) (w2:W8.t) = VPSRL_4u64 w1 w2.

abbrev [-printing] (\vshl8u256)  (w1:W256.t) (w2:W8.t) = VPSLL_32u8 w1 w2.
abbrev [-printing] (\vshl16u256) (w1:W256.t) (w2:W8.t) = VPSLL_16u16 w1 w2.
abbrev [-printing] (\vshl32u256) (w1:W256.t) (w2:W8.t) = VPSLL_8u32 w1 w2.
abbrev [-printing] (\vshl64u256) (w1:W256.t) (w2:W8.t) = VPSLL_4u64 w1 w2.

abbrev [-printing] (\vsar8u256)  (w1:W256.t) (w2:W8.t) = VPSRA_32u8 w1 w2.
abbrev [-printing] (\vsar16u256) (w1:W256.t) (w2:W8.t) = VPSRA_16u16 w1 w2.
abbrev [-printing] (\vsar32u256) (w1:W256.t) (w2:W8.t) = VPSRA_8u32 w1 w2.
abbrev [-printing] (\vsar64u256) (w1:W256.t) (w2:W8.t) = VPSRA_4u64 w1 w2.

abbrev [-printing] (\vadd8u256)  (w1 w2:W256.t) = VPADD_32u8 w1 w2.
abbrev [-printing] (\vadd16u256) (w1 w2:W256.t) = VPADD_16u16 w1 w2.
abbrev [-printing] (\vadd32u256) (w1 w2:W256.t) = VPADD_8u32 w1 w2.
abbrev [-printing] (\vadd64u256) (w1 w2:W256.t) = VPADD_4u64 w1 w2.

abbrev [-printing] (\vsub8u256)  (w1 w2:W256.t) = VPSUB_32u8 w1 w2.
abbrev [-printing] (\vsub16u256) (w1 w2:W256.t) = VPSUB_16u16 w1 w2.
abbrev [-printing] (\vsub32u256) (w1 w2:W256.t) = VPSUB_8u32 w1 w2.
abbrev [-printing] (\vsub64u256) (w1 w2:W256.t) = VPSUB_4u64 w1 w2.

abbrev [-printing] (\vmul8u256)  (w1 w2:W256.t) = VPMULL_32u8 w1 w2.
abbrev [-printing] (\vmul16u256) (w1 w2:W256.t) = VPMULL_16u16 w1 w2.
abbrev [-printing] (\vmul32u256) (w1 w2:W256.t) = VPMULL_8u32 w1 w2.
abbrev [-printing] (\vmul64u256) (w1 w2:W256.t) = VPMULL_4u64 w1 w2.

(* ------------------------------------------------------------------- *)

(* Semantic of x86_extra *)
(*
| Oset0     of wsize  (* set register + flags to 0 (implemented using XOR x x or VPXOR x x) *)
| Oconcat128          (* concatenate 2 128 bits word into 1 256 word register *)   
| Ox86MOVZX32.
*)

abbrev [-printing] set0_8   = W8.ALU.set0_8_.
abbrev [-printing] set0_16  = W16.ALU.set0_16_.
abbrev [-printing] set0_32  = W32.ALU.set0_32_.
abbrev [-printing] set0_64  = W64.ALU.set0_64_.
abbrev [-printing] set0_128 = W128.zero. 
abbrev [-printing] set0_256 = W256.zero.

op concat_2u128 (h l: W128.t) = pack2 [l; h].

abbrev MOVZX32 (x : W32.t) = W64.of_int (W32.to_uint x).

(* -------------------------------------------------------------------- *)

(* Semantic for X86 assembly instructions *)
(*
| MOV    of wsize              (* copy *)
| MOVSX  of wsize & wsize      (* sign-extend *)
| MOVZX  of wsize & wsize      (* zero-extend *)
| CMOVcc of wsize              (* conditional copy *)
| XCHG   of wsize              (* exchanges the contents of two operands *)
*)

op MOV_8   (x:W8.t)  = x.
op MOV_16  (x:W16.t) = x.
op MOV_32  (x:W32.t) = x.
op MOV_64  (x:W64.t) = x.

op MOVSX_u16s8 (x:W8.t) = W16.of_int (W8.to_sint x).
op MOVSX_u32s8 (x:W8.t) = W32.of_int (W8.to_sint x).
op MOVSX_u64s8 (x:W8.t) = W64.of_int (W8.to_sint x).

op MOVSX_u16s16 (x:W16.t) = W16.of_int (W16.to_sint x).
op MOVSX_u32s16 (x:W16.t) = W32.of_int (W16.to_sint x).
op MOVSX_u64s16 (x:W16.t) = W64.of_int (W16.to_sint x).

op MOVSX_u32s32 (x:W32.t) = W32.of_int (W32.to_sint x).
op MOVSX_u64s32 (x:W32.t) = W64.of_int (W32.to_sint x).

op MOVZX_u16u8 (x:W8.t) = W16.of_int (W8.to_uint x).
op MOVZX_u32u8 (x:W8.t) = W32.of_int (W8.to_uint x).
op MOVZX_u64u8 (x:W8.t) = W64.of_int (W8.to_uint x).

op MOVZX_u32u16 (x:W16.t) = W32.of_int (W16.to_uint x).
op MOVZX_u64u16 (x:W16.t) = W64.of_int (W16.to_uint x).

op MOVZX_u64u32 (x:W32.t) = W64.of_int (W32.to_uint x).

abbrev [-printing] XCHG_8  (x y:W8.t)  = swap_ x y.
abbrev [-printing] XCHG_16 (x y:W16.t) = swap_ x y.
abbrev [-printing] XCHG_32 (x y:W32.t) = swap_ x y.
abbrev [-printing] XCHG_64 (x y:W64.t) = swap_ x y.

(* ------------------------------------------------------------------- *)



(*
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
*)

(* Remark: W8.ALU W16.ALU W32.ALU W64.ALU are exported *)
(* ALU defines the operators: 
   ADD SUB IMUL IMUL_r IMUL_ri DIV IDIV CQO ADC SBB NEG INC DEC LZCNT
*)

(* Flag *)
(*
| SETcc                           (* Set byte on condition *) 
*) 
(* Definied in W8.SETcc *)

(*
| BT     of wsize              (* Bit test, sets result to CF *)
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
*)

(* ALU defines the operators: 
   BT LEA TEST CMP AND ANDN OR XOR NOT
*)
(* -------------------------------------------------------------------- *)
(* CLC/STC *)
op CLC = false.
op STC = true.

(* -------------------------------------------------------------------- *)
  (* Bit shifts *)
(*
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
*)
(* W8.SHIFT W16.SHIFT W32.SHIFT W64.SHIFT are exported *)
(* SHIFT defines the operators:
   ROR ROL RCR RCL SHL SHR SAL SAR SHLD SHLD 
*)

(* 
| MULX    of wsize  (* mul unsigned, doesn't affect arithmetic flags *)
| ADCX    of wsize  (* add with carry flag, only writes carry flag *)  
| ADOX    of wsize  (* add with overflow flag, only writes overflow flag *)
*)
(* ALU defines the operators:
   MULX ADCX ADOX
*) 

(* -------------------------------------------------------------------- *)
(*
| BSWAP  of wsize                     (* byte swap *)
*)

op BSWAP_32: W32.t -> W32.t =
  W4u8.pack4  \o rev \o W4u8.Pack.to_list \o W4u8.unpack8.

op BSWAP_64: W64.t -> W64.t =
  W8u8.pack8 \o rev \o W8u8.Pack.to_list \o W8u8.unpack8.

lemma bswap32K: involutive BSWAP_32.
proof.
move=> v; rewrite /BSWAP_32 /(\o) /=.
by rewrite of_listK 2:revK 1:size_rev 1:size_to_list.
qed.

lemma bswap64K: involutive BSWAP_64.
proof.
move=> v; rewrite /BSWAP_64 /(\o) /=.
by rewrite of_listK 2:revK 1:size_rev 1:size_to_list.
qed.

(* -------------------------------------------------------------------- *)
(*
| POPCNT of wsize    (* Count bits set to 1 *)
| PEXT   of wsize    (* parallel bits extract *)
| PDEP   of wsize    (* parallel bits deposit *)
*)
(* ALU defines the operators:
   POPCNT PEXT PDEP
*) 

(* -------------------------------------------------------------------- *)
    (* MMX instructions *)
(*
    | MOVX  of wsize
*)
op MOVX_32 (v: W32.t) = v.
op MOVX_64 (v: W64.t) = v.

(* -------------------------------------------------------------------- *)
  (* SSE instructions *)
(*
| MOVD     of wsize
| MOVV     of wsize
| VMOV     of wsize
*)
op MOVV_32 (v: W32.t) = v.
op MOVV_64 (v: W64.t) = v.

op VMOV_32 (v:W32.t) =
  pack4 [v; W32.zero; W32.zero; W32.zero].

op VMOV_64 (v:W64.t) =
  pack2 [v; W64.zero].

abbrev [-printing] MOVD_32 = VMOV_32.
abbrev [-printing] MOVD_64 = VMOV_64.

(* -------------------------------------------------------------------- *)
(*
| VMOVDQA  `(wsize)
*)
op VMOVDQA_128 (x:W128.t) = x.
op VMOVDQA_256 (x:W256.t) = x.

(* -------------------------------------------------------------------- *)
(*
| VMOVDQU  `(wsize)
*)
op VMOVDQU_128 (x:W128.t) = x.
op VMOVDQU_256 (x:W256.t) = x.

(* -------------------------------------------------------------------- *)
(*
| VPMOVSX of velem & wsize & velem & wsize (* parallel sign-extension: sizes are source, source, target, target *)
*)
(* 128 *)
op VPMOVSX_8u8_8u16   (w:W64.t) : W128.t = pack8 (map MOVSX_u16s8  (W8u8.to_list w)).
op VPMOVSX_4u8_4u32   (w:W32.t) : W128.t = pack4 (map MOVSX_u32s8  (W4u8.to_list w)).
op VPMOVSX_2u8_2u64   (w:W16.t) : W128.t = pack2 (map MOVSX_u64s8  (W2u8.to_list w)).
op VPMOVSX_4u16_4u32  (w:W64.t) : W128.t = pack4 (map MOVSX_u32s16 (W4u16.to_list w)).
op VPMOVSX_2u16_2u64  (w:W32.t) : W128.t = pack2 (map MOVSX_u64s16 (W2u16.to_list w)).
op VPMOVSX_2u32_2u64  (w:W64.t) : W128.t = pack2 (map MOVSX_u64s32 (W2u32.to_list w)).
(* 256 *)          
op VPMOVSX_16u8_16u16 (w:W128.t) : W256.t = pack16 (map MOVSX_u16s8  (W16u8.to_list w)).
op VPMOVSX_8u8_8u32   (w:W64.t)  : W256.t = pack8  (map MOVSX_u32s8  (W8u8.to_list w)).
op VPMOVSX_4u8_4u64   (w:W32.t)  : W256.t = pack4  (map MOVSX_u64s8  (W4u8.to_list w)).
op VPMOVSX_8u16_8u32  (w:W128.t) : W256.t = pack8  (map MOVSX_u32s16 (W8u16.to_list w)).
op VPMOVSX_4u16_4u64  (w:W64.t)  : W256.t = pack4  (map MOVSX_u64s16 (W4u16.to_list w)).
op VPMOVSX_4u32_4u64  (w:W128.t)  : W256.t = pack4  (map MOVSX_u64s32 (W4u32.to_list w)).

(* -------------------------------------------------------------------- *)
(*
| VPMOVZX of velem & wsize & velem & wsize (* parallel zero-extension: sizes are source, source, target, target *)
*)

op VPMOVZX_8u8_8u16   (w:W64.t) : W128.t = pack8 (map MOVZX_u16u8  (W8u8.to_list w)).
op VPMOVZX_4u8_4u32   (w:W32.t) : W128.t = pack4 (map MOVZX_u32u8  (W4u8.to_list w)).
op VPMOVZX_2u8_2u64   (w:W16.t) : W128.t = pack2 (map MOVZX_u64u8  (W2u8.to_list w)).
op VPMOVZX_4u16_4u32  (w:W64.t) : W128.t = pack4 (map MOVZX_u32u16 (W4u16.to_list w)).
op VPMOVZX_2u16_2u64  (w:W32.t) : W128.t = pack2 (map MOVZX_u64u16 (W2u16.to_list w)).
op VPMOVZX_2u32_2u64  (w:W64.t) : W128.t = pack2 (map MOVZX_u64u32 (W2u32.to_list w)).
(* 256 *)          
op VPMOVZX_16u8_16u16 (w:W128.t) : W256.t = pack16 (map MOVZX_u16u8  (W16u8.to_list w)).
op VPMOVZX_8u8_8u32   (w:W64.t)  : W256.t = pack8  (map MOVZX_u32u8  (W8u8.to_list w)).
op VPMOVZX_4u8_4u64   (w:W32.t)  : W256.t = pack4  (map MOVZX_u64u8  (W4u8.to_list w)).
op VPMOVZX_8u16_8u32  (w:W128.t) : W256.t = pack8  (map MOVZX_u32u16 (W8u16.to_list w)).
op VPMOVZX_4u16_4u64  (w:W64.t)  : W256.t = pack4  (map MOVZX_u64u16 (W4u16.to_list w)).
op VPMOVZX_4u32_4u64  (w:W128.t)  : W256.t = pack4 (map MOVZX_u64u32 (W4u32.to_list w)).

(* -------------------------------------------------------------------- *)
(* 
| VPAND    `(wsize)
| VPANDN   `(wsize)
| VPOR     `(wsize)
| VPXOR    `(wsize)
*)
abbrev [-printing] VPAND_128 = W128.(`&`).
abbrev [-printing] VPAND_256 = W256.(`&`).
abbrev [-printing] VPANDN_128 (x y:W128.t) = invw x `&` y.
abbrev [-printing] VPANDN_256 (x y:W256.t) = invw x `&` y.
abbrev [-printing] VPOR_128 = W128.(`|`).
abbrev [-printing] VPOR_256 = W256.(`|`).
abbrev [-printing] VPXOR_128 = W128.(`^`).
abbrev [-printing] VPXOR_256 = W256.(`^`).


(* -------------------------------------------------------------------- *)
(*
| VPADD    `(velem) `(wsize)
| VPSUB    `(velem) `(wsize)
*)
(* Defined in WRuS *)

(* ------------------------------------------------------------------- *)
op VPAVG_16u8 (x y: W128.t) : W128.t =
  map2 (fun (x y : W8.t) => (W8.of_int ((to_uint x + to_uint y + 1) %/ 2))) x y.

op VPAVG_32u8 (x y: W256.t) : W256.t =
  map2 (fun (x y : W8.t) => (W8.of_int ((to_uint x + to_uint y + 1) %/ 2))) x y.

op VPAVG_8u16 (x y: W128.t) : W128.t =
  map2 (fun (x y : W16.t) => (W16.of_int ((to_uint x + to_uint y + 1) %/ 2))) x y.

op VPAVG_16u16 (x y: W256.t) : W256.t =
  map2 (fun (x y : W16.t) => (W16.of_int ((to_uint x + to_uint y + 1) %/ 2))) x y.

(* ------------------------------------------------------------------- *)
(*
| VPMULL   `(velem) `(wsize)
| VPMULH   `(velem) `(wsize)   (* signed multiplication of 16-bits*)
*)

(* ------------------------------------------------------------------- *)
(*
| VPMULHU  `(velem) `(wsize)
*)
op VPMULHU_8u16 (w1 w2: W128.t) : W128.t =
  map2 (fun (x y:W16.t) => mulhi x y) w1 w2.

op VPMULHU_16u16 (w1 w2: W256.t) : W256.t =
  map2 (fun (x y:W16.t) => mulhi x y) w1 w2.

(* ------------------------------------------------------------------- *)
(*
| VPMULHRS of velem & wsize (* Packed Multiply High with Round and Scale *)
*)

op round_scalew(x: int): W16.t =
  let p = ((W32.of_int x) `>>` (W8.of_int 14)) + (W32.of_int 1) in
  W2u16.truncateu16 (p `>>` (W8.of_int 1)).

op mulhrs (w1 w2:W16.t) = round_scalew (to_sint w1 * to_sint w2).

op VPMULHRS_8u16 (w1 w2: W128.t): W128.t =
  map2 mulhrs w1 w2.

op VPMULHRS_16u16 (w1 w2: W256.t): W256.t =
  map2 mulhrs w1 w2.

(* ------------------------------------------------------------------- *)
(*
| VPMUL    `(wsize)
*)
op mul64 (w1 w2 : W64.t) =
  (W2u32.sigextu64 (W2u32.truncateu32 w1)) *
  (W2u32.sigextu64 (W2u32.truncateu32 w2)).

op VPMUL_128 (w1 w2: W128.t) =
  map2 mul64 w1 w2.

op VPMUL_256 (w1 w2: W256.t) =
  map2 mul64 w1 w2.

(* ------------------------------------------------------------------- *)
(*
| VPMULU   `(wsize)
*)
op mulu64 (w1 w2 : W64.t) =
  (W2u32.zeroextu64 (W2u32.truncateu32 w1)) *
  (W2u32.zeroextu64 (W2u32.truncateu32 w2)).

op VPMULU_128 (w1 w2: W128.t) =
  map2 mulu64 w1 w2.

op VPMULU_256 (w1 w2: W256.t) =
  map2 mulu64 w1 w2.

(* ------------------------------------------------------------------- *)
(*
| VPEXTR   `(wsize)
| VPINSR   `(velem)
| VPSLL    `(velem) `(wsize)
| VPSRL    `(velem) `(wsize)
| VPSRA    `(velem) `(wsize)
| VPSLLV   `(velem) `(wsize)
| VPSRLV   `(velem) `(wsize)
*)
(* Defined in WRuS *)

(* ------------------------------------------------------------------- *)
(*
| VPSLLDQ  `(wsize)
| VPSRLDQ  `(wsize)
*)
op VPSLLDQ_128 (w1:W128.t) (w2:W8.t) =
  let n = to_uint w2 in
  let i = min n 16 in
  w1 `<<<` (8 * i).

op VPSLLDQ_256 (w1:W256.t) (w2:W8.t) =
  map (fun w => VPSLLDQ_128 w w2) w1.

op VPSRLDQ_128 (w1:W128.t) (w2:W8.t) =
  let n = to_uint w2 in
  let i = min n 16 in
  w1 `>>>` (8 * i).

op VPSRLDQ_256 (w1:W256.t) (w2:W8.t) =
  map (fun w => VPSRLDQ_128 w w2) w1.

(* ------------------------------------------------------------------- *)
(*
| VPSHUFB  `(wsize)
*)
op VPSHUFB_128_B (w:W128.t) (m : W8.t) =
  let i = W8.to_uint m in
  if 128 <= i then W8.zero
  else w \bits8 (i %% 16).

op VPSHUFB_128 (w m : W128.t) : W128.t =
  map (VPSHUFB_128_B w) m.

op VPSHUFB_256 (w m : W256.t) : W256.t =
  map2 VPSHUFB_128 w m.

(* ------------------------------------------------------------------- *)
(*
| VPSHUFD  `(wsize)
*)
op VPSHUFD_128_B (w : W128.t) (m : W8.t) (i : int) : W32.t =
  let m = W8.to_uint m in
  let p = (m %/ (2^(2*i)))%%4 in
  w \bits32 p.

op VPSHUFD_128 (w : W128.t) (m : W8.t) : W128.t =
  pack4 (map (VPSHUFD_128_B w m) (iotared 0 4)).

op VPSHUFD_256 (w : W256.t) (m : W8.t) : W256.t =
  map (fun w => VPSHUFD_128 w m) w.

(* ------------------------------------------------------------------- *)
(*
| VPSHUFHW `(wsize)
| VPSHUFLW `(wsize)
*)

op wpshufl_u64 (w:W64.t) (x:W8.t) = 
  pack4_t (W4u16.Pack.init (fun i => 
    w \bits16 (to_uint (x `>>>` 2*i))%%4)).

op VPSHUFHW_128 (w:W128.t) (x:W8.t) =
  pack2 [w \bits64 0; wpshufl_u64 (w \bits64 1) x].

op VPSHUFLW_128 (w:W128.t) (x:W8.t) = 
  pack2 [wpshufl_u64 (w \bits64 0) x; w \bits64 1].

op VPSHUFHW_256 (w:W256.t) (x:W8.t) = 
  map (fun w => VPSHUFHW_128 w x) w.

op VPSHUFLW_256 (w:W256.t) (x:W8.t) = 
  map (fun w => VPSHUFLW_128 w x) w.


(* ------------------------------------------------------------------- *)
(*
| VPBLEND  `(velem) `(wsize)
*)
op VPBLENDW_128 (w1 w2: W128.t) (i: W8.t) : W128.t =
  let choose = fun n =>
    let w = if i.[n] then w2 else w1 in
    w \bits16 n in
  pack8 [choose 0; choose 1; choose 2; choose 3; choose 4; choose 5; choose 6; choose 7].

op VPBLENDW_256 (w1 w2: W256.t) (i: W8.t) : W256.t =
  map2 (fun (w1 w2: W128.t) => VPBLENDW_128 w1 w2 i) w1 w2.

op VPBLENDD_128 (w1 w2: W128.t) (i:W8.t) : W128.t =
  let choose = fun n =>
     let w = if i.[n] then w2 else w1 in
     w \bits32 n in
  pack4 [choose 0; choose 1; choose 2; choose 3].

op VPBLENDD_256 (w1 w2: W256.t) (i:W8.t) : W256.t =
  let choose = fun n =>
     let w = if i.[n] then w2 else w1 in
     w \bits32 n in
  pack8 [choose 0; choose 1; choose 2; choose 3; choose 4; choose 5; choose 6; choose 7].

abbrev [-printing] VPBLEND_8u16 = VPBLENDW_128.
abbrev [-printing] VPBLEND_4u32 = VPBLENDD_128.
abbrev [-printing] VPBLEND_16u16 = VPBLENDW_256.
abbrev [-printing] VPBLEND_8u32 = VPBLENDD_256.

(* ------------------------------------------------------------------- *)
(*
| VPBLENDVB `(wsize)
*)
op VPBLENDVB_128 (v1 v2 m: W128.t) : W128.t =
  let choose = fun n =>
    let w = if msb (m \bits8 n) then v2 else v1 in
    w \bits8 n in
  pack16 [choose 0; choose 1; choose 2; choose 3; choose 4; choose 5; choose 6; choose 7;
          choose 8; choose 9; choose 10; choose 11; choose 12; choose 13; choose 14; choose 15].

op VPBLENDVB_256 (v1 v2 m: W256.t) : W256.t =
  pack2 [VPBLENDVB_128 (v1 \bits128 0) (v2 \bits128 0) (m \bits128 0);
         VPBLENDVB_128 (v1 \bits128 1) (v2 \bits128 1) (m \bits128 1)].

(* ------------------------------------------------------------------- *)
(*
| VPACKUS  `(velem) `(wsize)
*)
op packus_8u16 (w: W128.t) : W64.t =
  let pack = fun n =>
  if (w \bits16 n) \slt W16.zero then W8.zero
  else if (W16.of_int W8.max_uint) \sle (w \bits16 n) then (W8.of_int W8.max_uint)
  else (w \bits8 (2*n))
  in
  pack8 [pack 0; pack 1; pack 2; pack 3; pack 4; pack 5; pack 6; pack 7].

op VPACKUS_8u16 (w1 w2: W128.t) : W128.t =
  pack2 [packus_8u16 w1; packus_8u16 w2].

op VPACKUS_16u16 (w1 w2: W256.t) : W256.t =
  map2 VPACKUS_8u16 w1 w2.

op packus_4u32 (w: W128.t) : W64.t =
  let pack = fun n =>
  if (w \bits32 n) \slt W32.zero then W16.zero
  else if (W32.of_int W16.max_uint) \sle (w \bits32 n) then (W16.of_int W16.max_uint)
  else (w \bits16 (2*n))
  in
  pack4 [pack 0; pack 1; pack 2; pack 3].

op VPACKUS_4u32 (w1 w2: W128.t) : W128.t =
  pack2 [packus_4u32 w1; packus_4u32 w2].

op VPACKUS_8u32 (w1 w2: W256.t) : W256.t =
  map2 VPACKUS_4u32 w1 w2.

(* ------------------------------------------------------------------- *)
(*
| VPACKSS  `(velem) `(wsize)
*)
op packss_8u16 (w: W128.t) : W64.t =
  let pack = fun n =>
  if (w \bits16 n) \slt (W16.of_int W8.min_sint) then (W8.of_int W8.min_sint)
  else if (W16.of_int W8.max_sint) \sle (w \bits16 n) then (W8.of_int W8.max_sint)
  else (w \bits8 (2*n))
  in
  pack8 [pack 0; pack 1; pack 2; pack 3; pack 4; pack 5; pack 6; pack 7].

op VPACKSS_8u16 (w1 w2: W128.t) : W128.t =
  pack2 [packss_8u16 w1; packss_8u16 w2].

op VPACKSS_16u16 (w1 w2: W256.t) : W256.t =
  map2 VPACKSS_8u16 w1 w2.

op packss_4u32 (w: W128.t) : W64.t =
  let pack = fun n =>
  if (w \bits32 n) \slt (W32.of_int W16.min_sint) then (W16.of_int W16.min_sint)
  else if (W32.of_int W16.max_sint) \sle (w \bits32 n) then (W16.of_int W16.max_sint)
  else (w \bits16 (2*n))
  in
  pack4 [pack 0; pack 1; pack 2; pack 3].

op VPACKSS_4u32 (w1 w2: W128.t) : W128.t =
  pack2 [packss_4u32 w1; packss_4u32 w2].

op VPACKSS_8u32 (w1 w2: W256.t) : W256.t =
  map2 VPACKSS_4u32 w1 w2.

(* ------------------------------------------------------------------- *)
(*
| VSHUFPS  `(wsize)
*)
op VSHUFPS_128 (w1 w2 : W128.t) (m:W8.t) = 
  pack4 [VPSHUFD_128_B w1 m 0; VPSHUFD_128_B w1 m 1;
         VPSHUFD_128_B w2 m 2; VPSHUFD_128_B w2 m 3].

op VSHUFPS_256 (w1 : W256.t) (w2 : W256.t) (m : W8.t) : W256.t =
  map2 (fun w1 w2 => VSHUFPS_128 w1 w2 m) w1 w2.

(* ------------------------------------------------------------------- *)
(*
| VPBROADCAST of velem & wsize
*)
(* Defined in ALU *)

(* ------------------------------------------------------------------- *)
(*
| VMOVSHDUP of wsize (* Replicate 32-bit (“single”) high values *)
| VMOVSLDUP of wsize (* Replicate 32-bit (“single”) low values *)
*)

op VMOVSLDUP_128 (v: W128.t): W128.t =
  pack4 [v \bits32 0; v \bits32 0; v \bits32  2; v \bits32 2].

op VMOVSLDUP_256 (v: W256.t): W256.t =
  map VMOVSLDUP_128 v.

op VMOVSHDUP_128 (v: W128.t): W128.t =
  pack4 [v \bits32 1; v \bits32 1; v \bits32  3; v \bits32 3].

op VMOVSHDUP_256 (v: W256.t): W256.t =
  map VMOVSHDUP_128 v.

(* ------------------------------------------------------------------- *)
(*
| VPALIGNR  `(wsize)
*)
op VPALIGNR_128 (w1 w2: W128.t) (m: W8.t) : W128.t =
  pack2 [w2; w1] `>>>` (to_uint m * 8) \bits128 0.

op VPALIGNR_256 (w1 w2: W256.t) (m: W8.t) : W256.t =
  map2 (fun w1 w2 => VPALIGNR_128 w1 w2 m) w1 w2.

(* ------------------------------------------------------------------- *)
(*
| VBROADCASTI128
*)
(* Defined in ALU : VPBROADCAST_2u128 *)

(* ------------------------------------------------------------------- *)
(*
| VPUNPCKH `(velem) `(wsize)
| VPUNPCKL `(velem) `(wsize)
*)
op interleave_gen ['elem]
   (get:W128.t -> W64.t) (split_v : W64.t -> 'elem list) (pack_2v : 'elem list -> W128.t)
   (src1 src2: W128.t) =
  let l1 = split_v (get src1) in
  let l2 = split_v (get src2) in
  pack_2v (_interleave l1 l2).

op get_lo_2u64 (w:W128.t) = w \bits64 0.
op get_hi_2u64 (w:W128.t) = w \bits64 1.

op VPUNPCKL_16u8 (w1 w2:W128.t) =
  interleave_gen get_lo_2u64 W8u8.to_list W16u8.pack16 w1 w2.

op VPUNPCKL_8u16 (w1 w2:W128.t) =
  interleave_gen get_lo_2u64 W4u16.to_list W8u16.pack8 w1 w2.

op VPUNPCKL_4u32 (w1 w2:W128.t) =
  interleave_gen get_lo_2u64 W2u32.to_list W4u32.pack4 w1 w2.

op VPUNPCKL_2u64 (w1 w2:W128.t) =
  interleave_gen get_lo_2u64 (fun x => [x]) W2u64.pack2 w1 w2.

op VPUNPCKL_32u8 (w1 w2: W256.t) =
  map2 VPUNPCKL_16u8 w1 w2.

op VPUNPCKL_16u16 (w1 w2: W256.t) =
  map2 VPUNPCKL_8u16 w1 w2.

op VPUNPCKL_8u32 (w1 w2: W256.t) =
  map2 VPUNPCKL_4u32 w1 w2.

op VPUNPCKL_4u64 (w1 w2: W256.t) =
  map2 VPUNPCKL_2u64 w1 w2.

op VPUNPCKH_16u8 (w1 w2:W128.t) =
  interleave_gen get_hi_2u64 W8u8.to_list W16u8.pack16 w1 w2.

op VPUNPCKH_8u16 (w1 w2:W128.t) =
  interleave_gen get_hi_2u64 W4u16.to_list W8u16.pack8 w1 w2.

op VPUNPCKH_4u32 (w1 w2:W128.t) =
  interleave_gen get_hi_2u64 W2u32.to_list W4u32.pack4 w1 w2.

op VPUNPCKH_2u64 (w1 w2:W128.t) =
  interleave_gen get_hi_2u64 (fun x => [x]) W2u64.pack2 w1 w2.

op VPUNPCKH_32u8 (w1 w2: W256.t) =
  map2 VPUNPCKH_16u8 w1 w2.

op VPUNPCKH_16u16 (w1 w2: W256.t) =
  map2 VPUNPCKH_8u16 w1 w2.

op VPUNPCKH_8u32 (w1 w2: W256.t) =
  map2 VPUNPCKH_4u32 w1 w2.

op VPUNPCKH_4u64 (w1 w2: W256.t) =
  map2 VPUNPCKH_2u64 w1 w2.

(* ------------------------------------------------------------------- *)
(*
| VEXTRACTI128
*)
op VEXTRACTI128 (w:W256.t) (i:W8.t) : W128.t =
  w \bits128 b2i i.[0].

(* ------------------------------------------------------------------- *)
(*
| VINSERTI128
*)
op VINSERTI128 (w:W256.t) (x: W128.t) (i:W8.t): W256.t =
  let i = W8.to_uint i %% 2 in
  pack2 (map (fun j => if j = i then x else w \bits128 j) [0;1]).

(* ------------------------------------------------------------------- *)
(*
| VPERM2I128
*)
op VPERM2I128 (w1 w2: W256.t) (i:W8.t) : W256.t =
  let choose = fun n =>
     if i.[n+3] then W128.zero
     else
       let w = if i.[n+1] then w2 else w1 in
       w \bits128 b2i i.[n] in
  pack2 [choose 0; choose 4].

(* ------------------------------------------------------------------- *)
(*
| VPERMD
*)
op permd (v: W256.t) (i: W32.t) : W32.t =
  v \bits32 (to_uint i %% 8).

op VPERMD (i: W256.t) (w: W256.t) : W256.t =
  map (permd w) i.

(* ------------------------------------------------------------------- *)
(*
| VPERMQ
*)
op VPERMQ (w:W256.t) (i:W8.t) : W256.t =
  let choose = fun n => w \bits64 ((to_uint i %/ n) %% 4) in
  pack4 [choose 1; choose 4; choose 16; choose 64].

(* ------------------------------------------------------------------- *)
(*
| VPMOVMSKB of wsize & wsize (* source size (U128/256) & dest. size (U32/64) *)
*)
op VPMOVMSKB_u128u32 (v: W128.t) =
   let vb = W16u8.to_list v in
   W32.bits2w (map W8.msb vb).

op VPMOVMSKB_u128u64 (v: W128.t) =
   let vb = W16u8.to_list v in
   W64.bits2w (map W8.msb vb).

op VPMOVMSKB_u256u32 (v: W256.t) =
  let vb = W32u8.to_list v in
  W32.bits2w (map W8.msb vb).

op VPMOVMSKB_u256u64 (v: W256.t) =
  let vb = W32u8.to_list v in
  W64.bits2w (map W8.msb vb).

(* ------------------------------------------------------------------- *)
(*
| VPCMPEQ of velem & wsize
| VPCMPGT of velem & wsize
*)
(* FIXME: Add this in ALU *)

(* ------------------------------------------------------------------- *)
(*
| VPMADDUBSW of wsize
*)
op hadd: int list -> int list.

axiom hadd_nil : hadd [] = [].
axiom hadd_cons2 x y t : hadd (x :: y :: t) = (x + y) :: hadd t.

hint rewrite haddE: hadd_nil hadd_cons2.

op packssw(x: int): W16.t =
  if x < W16.min_sint then (W16.of_int W16.min_sint)
  else if W16.max_sint <= x then (W16.of_int W16.max_sint)
  else (W16.of_int x).

op VPMADDUBSW_128 (w1 w2: W128.t) : W128.t =
  let v1 = map W8.to_uint (W16u8.to_list w1) in
  let v2 = map W8.to_sint (W16u8.to_list w2) in
  pack8 (map packssw (hadd (map2 Int.( * ) v1 v2))).

op VPMADDUBSW_256 (w1 w2: W256.t) : W256.t =
  let v1 = map W8.to_uint (W32u8.to_list w1) in
  let v2 = map W8.to_sint (W32u8.to_list w2) in
  pack16 (map packssw (hadd (map2 Int.( * ) v1 v2))).

(* ------------------------------------------------------------------- *)
(*
| VPMADDWD of wsize
*)

op VPMADDWD_128 (w1 w2: W128.t) : W128.t =
  let v1 = map W16.to_sint (W8u16.to_list w1) in
  let v2 = map W16.to_sint (W8u16.to_list w2) in
  pack4 (map W32.of_int (hadd (map2 Int.( * ) v1 v2))).

op VPMADDWD_256 (w1 w2: W256.t) : W256.t =
  let v1 = map W16.to_sint (W16u16.to_list w1) in
  let v2 = map W16.to_sint (W16u16.to_list w2) in
  pack8 (map W32.of_int (hadd (map2 Int.( * ) v1 v2))).

(* ------------------------------------------------------------------- *)
(*
| VMOVLPD   (* Store low 64-bits from XMM register *)
*)
op VMOVLPD (v: W128.t) : W64.t =
  v \bits64 0.

(* ------------------------------------------------------------------- *)
(*
| VMOVHPD   (* Store high 64-bits from XMM register *)
*)
op VMOVHPD (v: W128.t) : W64.t =
  v \bits64 1.

(* ------------------------------------------------------------------- *)
(*
| VPMINU of velem & wsize
| VPMINS of velem & wsize
| VPMAXU of velem & wsize
| VPMAXS of velem & wsize
*)
(* Defined in WRuS *)

(* ------------------------------------------------------------------- *)
(*
| VPTEST `(wsize)
*)
op VPTEST_128 (v1 v2: W128.t) =
  let OF = false in
  let CF = ZF_of ((invw v1) `&` v2) in
  let SF = false in
  let PF = false in
  let ZF = ZF_of (v1 `&` v2) in
  (OF, CF, SF, PF, ZF).

op VPTEST_256 (v1 v2: W256.t) =
  let OF = false in
  let CF = ZF_of ((invw v1) `&` v2) in
  let SF = false in
  let PF = false in
  let ZF = ZF_of (v1 `&` v2) in
  (OF, CF, SF, PF, ZF).

(* ------------------------------------------------------------------- *)
(* Monitoring *)
(*
| RDTSC   of wsize
| RDTSCP  of wsize
*)
(* We do not provid a model of those instructions *)

(* ------------------------------------------------------------------- *)
(*
(* AES instructions *)
| AESDEC
| VAESDEC
| AESDECLAST
| VAESDECLAST
| AESENC
| VAESENC
| AESENCLAST
| VAESENCLAST
| AESIMC
| VAESIMC
| AESKEYGENASSIST
| VAESKEYGENASSIST 
.
*)
(* ------------------------------------------------------------------- *)
(* AES instruction *)

abbrev [-printing] VAESDEC          = AESDEC.
abbrev [-printing] VAESDECLAST      = AESDECLAST.
abbrev [-printing] VAESENC          = AESENC.
abbrev [-printing] VAESENCLAST      = AESENCLAST.
abbrev [-printing] VAESIMC          = AESIMC.
abbrev [-printing] VAESKEYGENASSIST = AESKEYGENASSIST.

(* ------------------------------------------------------------------- *)
(* PCLMULQDQ instructions *)
(*
| PCLMULQDQ
| VPCLMULQDQ  of wsize
*)
op clmulq (x y: W64.t): W128.t =
 let x128 =  W128.of_int (to_uint x) in
 foldr (fun i r => (if y.[i] then x128 `<<<` i else W128.zero) `^` r)
       W128.zero
       (iota_ 0 64).

op PCLMULQDQ (v1 v2: W128.t) (k: W8.t): W128.t =
 let x0 = v1 \bits64 (b2i k.[0]) in
 let x1 = v2 \bits64 (b2i k.[4]) in
 clmulq x0 x1.

abbrev [-printing] VPCLMULQDQ_128 = PCLMULQDQ.

op VPCLMULQDQ_256 (v1 v2: W256.t) (k: W8.t): W256.t =
 pack2 [ PCLMULQDQ (v1 \bits128 0) (v2 \bits128 0) k
       ; PCLMULQDQ (v1 \bits128 1) (v2 \bits128 1) k ].

(* -------------------------------------------------------------------- *)

hint simplify (W16u8.of_int_bits8_div).
hint simplify (W8.of_uintK)@1.
hint simplify W32.get_out@0.

abbrev [-printing] const_rotate8_128 = (W128.of_int 18676936380593224926704134051422339075).
abbrev [-printing] const_rotate16_128 = (W128.of_int 17342576855639742879858139805557719810).
abbrev [-printing] const_rotate24_128 = (W128.of_int 16028905388486802350658220295983399425).

lemma rotate8_128_E w :
  VPSHUFB_128 w const_rotate8_128 = W4u32.map (fun w => W32.rol w 8) w.
proof.
  have h : W128.all_eq
    (VPSHUFB_128 w const_rotate8_128) (W4u32.map (fun w => W32.rol w 8) w).
  + by cbv W128.all_eq VPSHUFB_128 VPSHUFB_128_B W16u8.unpack8.
  by apply (W128.all_eq_eq _ _ h).
qed.

lemma rotate16_128_E w :
  VPSHUFB_128 w const_rotate16_128 = W4u32.map (fun w => W32.rol w 16) w.
proof.
  have h : W128.all_eq
    (VPSHUFB_128  w const_rotate16_128) (W4u32.map (fun w => W32.rol w 16) w).
  + by cbv W128.all_eq VPSHUFB_128 VPSHUFB_128_B  W16u8.unpack8.
  by apply (W128.all_eq_eq _ _ h).
qed.

lemma rotate24_128_E w :
  (VPSHUFB_128 w const_rotate24_128) = W4u32.map (fun w => W32.rol w 24) w.
proof.
  have h : W128.all_eq
    (VPSHUFB_128 w const_rotate24_128) (W4u32.map (fun w => W32.rol w 24) w).
  + by cbv W128.all_eq VPSHUFB_128 VPSHUFB_128_B W16u8.unpack8.
  by apply (W128.all_eq_eq _ _ h).
qed.
hint simplify (rotate8_128_E, rotate16_128_E, rotate24_128_E).

abbrev [-printing] const_rotate8_256 =
  W256.of_int 6355432118420048154175784972596847518577147054203239762089463134348153782275.

abbrev [-printing] const_rotate16_256 =
  W256.of_int 5901373100945378232718128989223044758631764214521116316503579100742837863170.

abbrev [-printing] const_rotate24_256 =
  W256.of_int 5454353864746073763129182254217446065883741921538078285974850505695092212225.

lemma iteri_red n (opr : int -> 'a -> 'a) x : 
  0 < n => iteri n opr x = opr (n-1) (iteri (n-1) opr x).
proof. smt (iteriS). qed.

lemma rotate8_256_E w :
  VPSHUFB_256 w const_rotate8_256 = W8u32.map (fun w => W32.rol w 8) w.
proof. by apply: (W256.all_eq_eq _ _ _); cbv delta. qed.

lemma rotate16_256_E w :
  VPSHUFB_256 w const_rotate16_256 = W8u32.map (fun w => W32.rol w 16) w.
proof. by apply: (W256.all_eq_eq _ _ _); cbv delta. qed.

lemma rotate24_256_E w :
  VPSHUFB_256 w const_rotate24_256 = W8u32.map (fun w => W32.rol w 24) w.
proof. by apply: (W256.all_eq_eq _ _ _); cbv delta. qed.

hint simplify (rotate8_256_E, rotate16_256_E, rotate24_256_E).
