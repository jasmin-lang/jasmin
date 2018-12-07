(* -------------------------------------------------------------------- *)
require import AllCore BitEncoding IntDiv SmtMap Ring List StdOrder Bool.
(*---*) import CoreMap Map Ring.IntID IntOrder.
require export Jasmin_utils Jasmin_array Jasmin_word Jasmin_word_array Jasmin_memory.

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
    
op x86_VPSHUFB_256 (w m : W256.t) : W256.t =
  map2 x86_VPSHUFB_128 w m.

hint simplify (W16u8.of_int_bits8_div).
hint simplify (W8.of_uintK)@1. 
hint simplify W32.get_out@0.

abbrev [-printing] const_rotate8_128 = (W128.of_int 18676936380593224926704134051422339075).
abbrev [-printing] const_rotate16_128 = (W128.of_int 17342576855639742879858139805557719810).
abbrev [-printing] const_rotate24_128 = (W128.of_int 16028905388486802350658220295983399425).

lemma rotate8_128_E w : 
  x86_VPSHUFB_128 w const_rotate8_128 = W4u32.map (fun w => W32.rol w 8) w.
proof.
  have h : W128.all_eq 
    (x86_VPSHUFB_128 w const_rotate8_128) (W4u32.map (fun w => W32.rol w 8) w).
  + by cbv W128.all_eq x86_VPSHUFB_128 x86_VPSHUFB_128_B W16u8.unpack8 (%%) (%/). 
  by apply (W128.all_eq_eq _ _ h).
qed.

lemma rotate16_128_E w : 
  x86_VPSHUFB_128 w const_rotate16_128 = W4u32.map (fun w => W32.rol w 16) w.
proof.
  have h : W128.all_eq 
    (x86_VPSHUFB_128  w const_rotate16_128) (W4u32.map (fun w => W32.rol w 16) w).
  + by cbv W128.all_eq x86_VPSHUFB_128 x86_VPSHUFB_128_B  W16u8.unpack8 (%%) (%/).
  by apply (W128.all_eq_eq _ _ h).
qed.

lemma rotate24_128_E w :
  (x86_VPSHUFB_128 w const_rotate24_128) = W4u32.map (fun w => W32.rol w 24) w.
proof.
  have h : W128.all_eq 
    (x86_VPSHUFB_128 w const_rotate24_128) (W4u32.map (fun w => W32.rol w 24) w).
  + by cbv W128.all_eq x86_VPSHUFB_128 x86_VPSHUFB_128_B W16u8.unpack8 (%%) (%/).
  by apply (W128.all_eq_eq _ _ h).
qed.
hint simplify (rotate8_128_E, rotate16_128_E, rotate24_128_E).

abbrev [-printing] const_rotate8_256 = 
  W256.of_int 6355432118420048154175784972596847518577147054203239762089463134348153782275.

abbrev [-printing] const_rotate16_256 = 
  W256.of_int 5901373100945378232718128989223044758631764214521116316503579100742837863170.

abbrev [-printing] const_rotate24_256 =
  W256.of_int 5454353864746073763129182254217446065883741921538078285974850505695092212225.

(*lemma pack8u32_bits128 ws i : 0 <= i < 2 => 
  W8u32.pack8_t ws \bits128 i = pack4 [ws.[4*i];ws.[4*i+1];ws.[4*i+2];ws.[4*i+3] ].
proof.
  move=> /(mema_iota 0 2 i); move: i; apply /List.allP => /=.
  by split; apply W128.all_eq_eq;cbv delta.
qed. *)

lemma pack2_4u32_8u32 (w0 w1 w2 w3 w4 w5 w6 w7 :W32.t) :
   pack2 [pack4 [w0;w1;w2;w3]; pack4 [w4; w5; w6; w7]] =
   pack8 [w0; w1; w2; w3; w4; w5; w6; w7].
proof. by apply W256.all_eq_eq;cbv W256.all_eq (%/) (%%). qed.

lemma rotate8_256_E w : 
  x86_VPSHUFB_256 w const_rotate8_256 = W8u32.map (fun w => W32.rol w 8) w.
proof.
  rewrite -(W8u32.unpack32K w) /unpack32 /= /x86_VPSHUFB_256 -{1}pack2_4u32_8u32.
  rewrite -(W2u128.unpack128K const_rotate8_256) /unpack128 /=.
  rewrite !W2u128.of_int_bits128_div 1,2://.
  rewrite -W128.of_int_mod; cbv (%/) (%%). 
  by rewrite pack2_4u32_8u32.
qed.

lemma rotate16_256_E w : 
  x86_VPSHUFB_256 w const_rotate16_256 = W8u32.map (fun w => W32.rol w 16) w.
proof.
  rewrite -(W8u32.unpack32K w) /unpack32 /= /x86_VPSHUFB_256 -{1}pack2_4u32_8u32.
  rewrite -(W2u128.unpack128K const_rotate16_256) /unpack128 /=.
  rewrite !W2u128.of_int_bits128_div 1,2://.
  rewrite -W128.of_int_mod; cbv (%/) (%%).
  by rewrite pack2_4u32_8u32.
qed.

lemma rotate24_256_E w : 
  x86_VPSHUFB_256 w const_rotate24_256 = W8u32.map (fun w => W32.rol w 24) w.
proof.
  rewrite -(W8u32.unpack32K w) /unpack32 /= /x86_VPSHUFB_256 -{1}pack2_4u32_8u32.
  rewrite -(W2u128.unpack128K const_rotate24_256) /unpack128 /=.
  rewrite !W2u128.of_int_bits128_div 1,2://.
  rewrite -W128.of_int_mod; cbv (%/) (%%).
  by rewrite pack2_4u32_8u32.
qed.

hint simplify (rotate8_256_E, rotate16_256_E, rotate24_256_E).

(* -------------------------------------------------------------------- *)
op x86_VPSHUFD_128_B (w : W128.t) (m : W8.t) (i : int) : W32.t =
  let m = W8.to_uint m in
  let p = (m %/ (2^(2*i)))%%4 in
  w \bits32 p.

op x86_VPSHUFD_128 (w : W128.t) (m : W8.t) : W128.t =
  pack4 (map (x86_VPSHUFD_128_B w m) (iota_ 0 4)).

op x86_VPSHUFD_256 (w : W256.t) (m : W8.t) : W256.t =
  map (fun w => x86_VPSHUFD_128 w m) w.



(* -------------------------------------------------------------------- *)
abbrev [-printing] x86_VPBROADCASTI_2u128 = x86_VPBROADCAST_2u128.

(* -------------------------------------------------------------------- *)

op mulu_64 (w1 w2 : W64.t) = 
  (W2u32.zeroextu64 (W2u32.truncateu32 w1)) *
  (W2u32.zeroextu64 (W2u32.truncateu32 w2)).
 
(* -------------------------------------------------------------------- *)

(* FIXME it is really the semantics? In particular the last if *)
op x86_VPEXTR_64 (w:W128.t) (i:W8.t) = 
  if W8.to_uint i = 0 then (w \bits64 0)
  else if W8.to_uint i = 1 then (w \bits64 1)
  else W64.of_int 0.

op x86_MOVD_64 (v:W64.t) = 
  pack2 [v; W64.zero]. 

op x86_VPINSR_2u64 (v1:W128.t) (v2:W64.t) (i:W8.t) = 
  let i = W8.to_uint i %% 2 in
  pack2 (map (fun j => if j = i then v2 else v1 \bits64 j) [0;1]).

op x86_VPINSR_4u32 (v1:W128.t) (v2:W32.t) (i:W8.t) = 
  let i = W8.to_uint i %% 4 in
  pack4 (map (fun j => if j = i then v2 else v1 \bits32 j) [0;1;2;3]).

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
       w \bits128 b2i i.[n] in
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
op x86_VPSLLDQ_128 (w1:W128.t) (w2:W8.t) = 
  let n = to_uint w2 in
  let i = min n 16 in 
  w1 `<<<` (8 * i).
 
(* ------------------------------------------------------------------- *)
(* Leakages                                                            *)

type leakage_t = [
  | LeakAddr of address list
  | LeakCond of bool
  | LeakFor  of (int * int)
].

type leakages_t = leakage_t list.


