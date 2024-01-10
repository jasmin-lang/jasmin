(* -------------------------------------------------------------------- *)
require export JUtils JWord.

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
