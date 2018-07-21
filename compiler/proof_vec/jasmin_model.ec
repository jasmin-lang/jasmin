(* -------------------------------------------------------------------- *)
require import AllCore BitEncoding IntDiv SmtMap Ring List StdOrder Bool.
(*---*) import CoreMap Map Ring.IntID IntOrder.
require export Jasmin_utils Jasmin_array Jasmin_word Jasmin_memory.

(* -------------------------------------------------------------------- *)
abbrev x86_MOVD_32 (x : W32.t) = pack4 [x; W32.zero; W32.zero; W32.zero].

op x86_ROL_32 (x : W32.t) (cnt : W8.t) =
  let result = W32.rol x (to_uint cnt) in
  let CF = result.[0] in
  let OF = Logic.(^) CF result.[31] in
  (CF, OF, result)
  axiomatized by x86_ROL_32_E.

(* -------------------------------------------------------------------- *)
op x86_SHLD_32 :
  W32.t -> W32.t -> W8.t -> (bool * bool * bool * bool * bool * W32.t).

op x86_SHRD_32 :
  W32.t -> W32.t -> W8.t -> (bool * bool * bool * bool * bool * W32.t).

op x86_SHLD_64 :
  W64.t -> W64.t -> W8.t -> (bool * bool * bool * bool * bool * W64.t).

op x86_SHRD_64 :
  W64.t -> W64.t -> W8.t -> (bool * bool * bool * bool * bool * W64.t).

(* -------------------------------------------------------------------- *)

op x86_VPSHUFB_128_B (w:W128.t) (m : W8.t) =
  let i = W8.to_uint m in
  if 128 <= i then W8.zero 
  else w \bits8 (i %% 16).
    
op x86_VPSHUFB_128 (w m : W128.t) : W128.t =
  map (x86_VPSHUFB_128_B w) m.

op x86_VPSHUFB_256_B (w:W256.t) (m : W8.t) =
  let i = W8.to_uint m in
  if 128 <= i then W8.zero 
  else w \bits8 (i %% 16).
    
op x86_VPSHUFB_256 (w m : W256.t) : W256.t =
  map (x86_VPSHUFB_256_B w) m.

(* -------------------------------------------------------------------- *)
op x86_VPSHUFD_128_B (w : W128.t) (m : W8.t) (i : int) : W32.t =
  let m = W8.to_uint m in
  let p = (m %/ (2^(2*i)))%%4 in
  w \bits32 p.

op x86_VPSHUFD_128 (w : W128.t) (m : W8.t) : W128.t =
  pack4 (map (x86_VPSHUFD_128_B w m) (iota_ 0 4)).

op x86_VPSHUFD_256_B (w : W256.t) (m : W8.t) (i : int) : W64.t =
  let m = W8.to_uint m in
  let p = (m %/ (2^(2*i)))%%4 in
  w \bits64 p.

op x86_VPSHUFD_256 (w : W256.t) (m : W8.t) : W256.t =
  pack4 (map (x86_VPSHUFD_256_B w m) (iota_ 0 4)).

(* -------------------------------------------------------------------- *)
abbrev [-printing] x86_VPBROADCASTI_2u128 = x86_VPBROADCAST_2u128.

(* -------------------------------------------------------------------- *)

op mulu_64 (w1 w2 : W64.t) = 
  (W2u32.zeroextu64 (W2u32.truncateu32 w1)) *
  (W2u32.zeroextu64 (W2u32.truncateu32 w2)).
 
(* -------------------------------------------------------------------- *)

op x86_VPEXTR_64 (w:W128.t) (i:W8.t) = 
  if W8.to_uint i = 0 then (w \bits64 0)
  else if W8.to_uint i = 1 then (w \bits64 1)
  else W64.of_int 0.

op x86_MOVD_64 (v:W64.t) = 
  pack2 [v; W64.zero]. 

op x86_VPINSR_2u64 (v1:W128.t) (v2:W64.t) (i:W8.t) = 
  if W8.to_uint i = 0 then (pack2 [v2; v1 \bits64 1])
  else if W8.to_uint i = 1 then (pack2 [v1 \bits64 0; v2])
  else v1.

abbrev [-printing] x86_VPAND_128 = W128.(`&`).
abbrev [-printing] x86_VPOR_128 = W128.(`|`).
abbrev [-printing] x86_VPXOR_128 = W128.(`^`).

abbrev [-printing] x86_VPAND_256 = W256.(`&`).
abbrev [-printing] x86_VPOR_256  = W256.(`|`).
abbrev [-printing] x86_VPXOR_256 = W256.(`^`).

op x86_VPMULU_128 (w1 w2: W128.t) = 
  map2 mulu_64 w1 w2.

op x86_VPERM2I128 (w1 w2: W256.t) (i:W8.t) : W256.t = 
  let choose = fun n =>
     if i.[n+3] then W128.zero
     else
       let w = if i.[n+1] then w2 else w1 in
       w1 \bits128 b2i i.[n] in
  pack2 [choose 0; choose 4].

op x86_VEXTRACTI128 (w:W256.t) (i:W8.t) : W128.t = 
  w \bits128 b2i i.[0].

(* ------------------------------------------------------------------- *)
op interleave_gen ['elem] 
   (get:W128.t -> W64.t) (split_v : W64.t -> 'elem list) (pack_2v : 'elem list -> W128.t)
   (src1 src2: W128.t) = 
  let l1 = split_v (get src1) in
  let l2 = split_v (get src2) in
  pack_2v (interleave l1 l2).

op get_lo_2u64 (w:W128.t) = w \bits64 0.
op get_hi_2u64 (w:W128.t) = w \bits64 1.

op x86_VPUNPCKL_16u8 (w1 w2:W128.t) = 
  interleave_gen get_lo_2u64 W8u8.to_list W16u8.pack16 w1 w2.

op x86_VPUNPCKL_8u16 (w1 w2:W128.t) = 
  interleave_gen get_lo_2u64 W4u16.to_list W8u16.pack8 w1 w2.

op x86_VPUNPCKL_4u32 (w1 w2:W128.t) = 
  interleave_gen get_lo_2u64 W2u32.to_list W4u32.pack4 w1 w2.

op x86_VPUNPCKL_2u64 (w1 w2:W128.t) = 
  interleave_gen get_lo_2u64 (fun x => [x]) W2u64.pack2 w1 w2.

op x86_VPUNPCKL_32u8 (w1 w2: W256.t) = 
  map2 x86_VPUNPCKL_16u8 w1 w2.

op x86_VPUNPCKL_16u16 (w1 w2: W256.t) = 
  map2 x86_VPUNPCKL_8u16 w1 w2.

op x86_VPUNPCKL_8u32 (w1 w2: W256.t) = 
  map2 x86_VPUNPCKL_4u32 w1 w2.

op x86_VPUNPCKL_4u64 (w1 w2: W256.t) = 
  map2 x86_VPUNPCKL_2u64 w1 w2.

op x86_VPUNPCKH_16u8 (w1 w2:W128.t) = 
  interleave_gen get_hi_2u64 W8u8.to_list W16u8.pack16 w1 w2.

op x86_VPUNPCKH_8u16 (w1 w2:W128.t) = 
  interleave_gen get_hi_2u64 W4u16.to_list W8u16.pack8 w1 w2.

op x86_VPUNPCKH_4u32 (w1 w2:W128.t) = 
  interleave_gen get_hi_2u64 W2u32.to_list W4u32.pack4 w1 w2.

op x86_VPUNPCKH_2u64 (w1 w2:W128.t) = 
  interleave_gen get_hi_2u64 (fun x => [x]) W2u64.pack2 w1 w2.

op x86_VPUNPCKH_32u8 (w1 w2: W256.t) = 
  map2 x86_VPUNPCKH_16u8 w1 w2.

op x86_VPUNPCKH_16u16 (w1 w2: W256.t) = 
  map2 x86_VPUNPCKH_8u16 w1 w2.

op x86_VPUNPCKH_8u32 (w1 w2: W256.t) = 
  map2 x86_VPUNPCKH_4u32 w1 w2.

op x86_VPUNPCKH_4u64 (w1 w2: W256.t) = 
  map2 x86_VPUNPCKH_2u64 w1 w2.

(* ------------------------------------------------------------------- *)
(* Leakages                                                            *)

type leakage_t = [
  | LeakAddr of address list
  | LeakCond of bool
  | LeakFor  of (int * int)
].

type leakages_t = leakage_t list.


