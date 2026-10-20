(* -------------------------------------------------------------------- *)
require export JUtils JWord.

(* ------------------------------------------------------------------- *)

(* Semantics of the vector operators of expressions (a +4u32 b, ...):
   the lane-wise operators of JWord. *)
abbrev [-printing] (\vshr8u128)  (w1:W128.t) (w2:W128.t) = VPSRL_16u8 w1 w2.
abbrev [-printing] (\vshr16u128) (w1:W128.t) (w2:W128.t) = VPSRL_8u16 w1 w2.
abbrev [-printing] (\vshr32u128) (w1:W128.t) (w2:W128.t) = VPSRL_4u32 w1 w2.
abbrev [-printing] (\vshr64u128) (w1:W128.t) (w2:W128.t) = VPSRL_2u64 w1 w2.

abbrev [-printing] (\vshl8u128)  (w1:W128.t) (w2:W128.t) = VPSLL_16u8 w1 w2.
abbrev [-printing] (\vshl16u128) (w1:W128.t) (w2:W128.t) = VPSLL_8u16 w1 w2.
abbrev [-printing] (\vshl32u128) (w1:W128.t) (w2:W128.t) = VPSLL_4u32 w1 w2.
abbrev [-printing] (\vshl64u128) (w1:W128.t) (w2:W128.t) = VPSLL_2u64 w1 w2.

abbrev [-printing] (\vsar8u128)  (w1:W128.t) (w2:W128.t) = VPSRA_16u8 w1 w2.
abbrev [-printing] (\vsar16u128) (w1:W128.t) (w2:W128.t) = VPSRA_8u16 w1 w2.
abbrev [-printing] (\vsar32u128) (w1:W128.t) (w2:W128.t) = VPSRA_4u32 w1 w2.
abbrev [-printing] (\vsar64u128) (w1:W128.t) (w2:W128.t) = VPSRA_2u64 w1 w2.

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

abbrev [-printing] (\vshr8u256)  (w1:W256.t) (w2:W128.t) = VPSRL_32u8 w1 w2.
abbrev [-printing] (\vshr16u256) (w1:W256.t) (w2:W128.t) = VPSRL_16u16 w1 w2.
abbrev [-printing] (\vshr32u256) (w1:W256.t) (w2:W128.t) = VPSRL_8u32 w1 w2.
abbrev [-printing] (\vshr64u256) (w1:W256.t) (w2:W128.t) = VPSRL_4u64 w1 w2.

abbrev [-printing] (\vshl8u256)  (w1:W256.t) (w2:W128.t) = VPSLL_32u8 w1 w2.
abbrev [-printing] (\vshl16u256) (w1:W256.t) (w2:W128.t) = VPSLL_16u16 w1 w2.
abbrev [-printing] (\vshl32u256) (w1:W256.t) (w2:W128.t) = VPSLL_8u32 w1 w2.
abbrev [-printing] (\vshl64u256) (w1:W256.t) (w2:W128.t) = VPSLL_4u64 w1 w2.

abbrev [-printing] (\vsar8u256)  (w1:W256.t) (w2:W128.t) = VPSRA_32u8 w1 w2.
abbrev [-printing] (\vsar16u256) (w1:W256.t) (w2:W128.t) = VPSRA_16u16 w1 w2.
abbrev [-printing] (\vsar32u256) (w1:W256.t) (w2:W128.t) = VPSRA_8u32 w1 w2.
abbrev [-printing] (\vsar64u256) (w1:W256.t) (w2:W128.t) = VPSRA_4u64 w1 w2.

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
(* Semantic of sopn *)
(*
| Ocopy     of wsize & positive
| Onop
| Omulu     of wsize   (* cpu   : [sword; sword]        -> [sword;sword] *)
| Oaddcarry of wsize   (* cpu   : [sword; sword; sbool] -> [sbool;sword] *)
| Osubcarry of wsize   (* cpu   : [sword; sword; sbool] -> [sbool;sword] *)
| Oasm      of asm_op_t.
*)

op copy_8   ['a] (x:'a) = x.
op copy_16  ['a] (x:'a) = x.
op copy_32  ['a] (x:'a) = x.
op copy_64  ['a] (x:'a) = x.
op copy_128 ['a] (x:'a) = x.
op copy_256 ['a] (x:'a) = x.

op NOP (_:unit) = ().

abbrev [-printing] mulu_8   = W8.mulu.
abbrev [-printing] mulu_16  = W16.mulu.
abbrev [-printing] mulu_32  = W32.mulu.
abbrev [-printing] mulu_64  = W64.mulu.
abbrev [-printing] mulu_128 = W128.mulu.
abbrev [-printing] mulu_256 = W256.mulu.

abbrev [-printing] adc_8   = W8.addc.
abbrev [-printing] adc_16  = W16.addc.
abbrev [-printing] adc_32  = W32.addc.
abbrev [-printing] adc_64  = W64.addc.
abbrev [-printing] adc_128 = W128.addc.
abbrev [-printing] adc_256 = W256.addc.

abbrev [-printing] sbb_8   = W8.subc.
abbrev [-printing] sbb_16  = W16.subc.
abbrev [-printing] sbb_32  = W32.subc.
abbrev [-printing] sbb_64  = W64.subc.
abbrev [-printing] sbb_128 = W128.subc.
abbrev [-printing] sbb_256 = W256.subc.

op swap_ ['a] (x y : 'a) = (y, x).
