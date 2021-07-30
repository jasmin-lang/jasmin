(* -------------------------------------------------------------------- *)
require import AllCore BitEncoding IntDiv SmtMap Ring List StdOrder Bool.
(*---*) import CoreMap Map Ring.IntID IntOrder.
require export JUtils JArray JWord JWord_array JMemory AES.

(* -------------------------------------------------------------------- *)
abbrev MOVSZ32 (x : W32.t) = pack4 [x; W32.zero; W32.zero; W32.zero].
abbrev [-printing] setw0_128 = W128.of_int 0.
abbrev [-printing] setw0_256 = W256.of_int 0.

op concat_2u128 (h l: W128.t) = pack2 [l; h].
(* -------------------------------------------------------------------- *)

op VPSHUFB_128_B (w:W128.t) (m : W8.t) =
  let i = W8.to_uint m in
  if 128 <= i then W8.zero
  else w \bits8 (i %% 16).

op VPSHUFB_128 (w m : W128.t) : W128.t =
  map (VPSHUFB_128_B w) m.

op VPSHUFB_256 (w m : W256.t) : W256.t =
  map2 VPSHUFB_128 w m.

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
  + by cbv W128.all_eq VPSHUFB_128 VPSHUFB_128_B W16u8.unpack8 edivz.
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
  + by cbv W128.all_eq VPSHUFB_128 VPSHUFB_128_B W16u8.unpack8 edivz.
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

(* -------------------------------------------------------------------- *)
op VPSHUFD_128_B (w : W128.t) (m : W8.t) (i : int) : W32.t =
  let m = W8.to_uint m in
  let p = (m %/ (2^(2*i)))%%4 in
  w \bits32 p.

op VPSHUFD_128 (w : W128.t) (m : W8.t) : W128.t =
  pack4 (map (VPSHUFD_128_B w m) (iotared 0 4)).

op VPSHUFD_256 (w : W256.t) (m : W8.t) : W256.t =
  map (fun w => VPSHUFD_128 w m) w.

op VSHUFPS_128 (w1 w2 : W128.t) (m:W8.t) = 
  pack4 [VPSHUFD_128_B w1 m 0; VPSHUFD_128_B w1 m 1;
         VPSHUFD_128_B w2 m 2; VPSHUFD_128_B w2 m 3].

op VSHUFPS_256 (w1 : W256.t) (w2 : W256.t) (m : W8.t) : W256.t =
  map2 (fun w1 w2 => VSHUFPS_128 w1 w2 m) w1 w2.

(* -------------------------------------------------------------------- *)
abbrev [-printing] VPBROADCASTI_2u128 = VPBROADCAST_2u128.

(** TODO : CHECKME **)
abbrev [-printing] VBROADCAST_2u128 = VPBROADCAST_2u128.

(* -------------------------------------------------------------------- *)
abbrev [-printing] subc_8 = W8.subc.
abbrev [-printing] addc_8 = W8.addc.
abbrev [-printing] mulu_8 = W8.mulu.

abbrev [-printing] subc_16 = W16.subc.
abbrev [-printing] addc_16 = W16.addc.
abbrev [-printing] mulu_16 = W16.mulu.

abbrev [-printing] subc_32 = W32.subc.
abbrev [-printing] addc_32 = W32.addc.
abbrev [-printing] mulu_32 = W32.mulu.

abbrev [-printing] subc_64 = W64.subc.
abbrev [-printing] addc_64 = W64.addc.
abbrev [-printing] mulu_64 = W64.mulu.

op mulu64 (w1 w2 : W64.t) =
  (W2u32.zeroextu64 (W2u32.truncateu32 w1)) *
  (W2u32.zeroextu64 (W2u32.truncateu32 w2)).

(* -------------------------------------------------------------------- *)

(* FIXME it is really the semantics? In particular the last if *)
op VPEXTR_64 (w:W128.t) (i:W8.t) =
  if W8.to_uint i = 0 then (w \bits64 0)
  else if W8.to_uint i = 1 then (w \bits64 1)
  else W64.of_int 0.

op VMOV_32 (v:W32.t) =
  pack4 [v; W32.zero; W32.zero; W32.zero].

op VMOV_64 (v:W64.t) =
  pack2 [v; W64.zero].

abbrev [-printing] MOVD_32 = VMOV_32.
abbrev [-printing] MOVD_64 = VMOV_64.

op VPINSR_2u64 (v1:W128.t) (v2:W64.t) (i:W8.t) =
  let i = W8.to_uint i %% 2 in
  pack2 (map (fun j => if j = i then v2 else v1 \bits64 j) [0;1]).

op VPINSR_4u32 (v1:W128.t) (v2:W32.t) (i:W8.t) =
  let i = W8.to_uint i %% 4 in
  pack4 (map (fun j => if j = i then v2 else v1 \bits32 j) [0;1;2;3]).

abbrev [-printing] VPAND_128 = W128.(`&`).
abbrev [-printing] VPOR_128 = W128.(`|`).
abbrev [-printing] VPXOR_128 = W128.(`^`).

op VPANDN_128 (x y:W128.t) = W128.invw x `&` y.

abbrev [-printing] VPAND_256 = W256.(`&`).
abbrev [-printing] VPOR_256  = W256.(`|`).
abbrev [-printing] VPXOR_256 = W256.(`^`).

op VPANDN_256 (x y:W256.t) = W256.invw x `&` y.

op VPMULU_128 (w1 w2: W128.t) =
  map2 mulu64 w1 w2.

op VPMULU_256 (w1 w2: W256.t) =
  map2 mulu64 w1 w2.

(* quick fix *)
op VPMULU (w1 w2: W256.t) =
  map2 mulu64 w1 w2.

(* FIXME: check this *)
op VPERM2I128 (w1 w2: W256.t) (i:W8.t) : W256.t =
  let choose = fun n =>
     if i.[n+3] then W128.zero
     else
       let w = if i.[n+1] then w2 else w1 in
       w \bits128 b2i i.[n] in
  pack2 [choose 0; choose 4].

op VPERMQ (w:W256.t) (i:W8.t) : W256.t =
  let choose = fun n => w \bits64 ((to_uint i %/ n) %% 4) in
  pack4 [choose 1; choose 4; choose 16; choose 64].

op VEXTRACTI128 (w:W256.t) (i:W8.t) : W128.t =
  w \bits128 b2i i.[0].

(* ------------------------------------------------------------------- *)
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
op VPSLLV_4u64 (w1:W256.t) (w2:W256.t) =
  let sll = fun (x1 x2:W64.t) => x1 `<<<` W64.to_uint x2 in
  map2 sll w1 w2.

op VPSRLV_4u64 (w1:W256.t) (w2:W256.t) =
  let srl = fun (x1 x2:W64.t) => x1 `>>>` W64.to_uint x2 in
  map2 srl w1 w2.

(* ------------------------------------------------------------------- *)
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

(* ------------------------------------------------------------------- *)

(* AES instruction *)

abbrev [-printing] VAESDEC          = AESDEC.
abbrev [-printing] VAESDECLAST      = AESDECLAST.
abbrev [-printing] VAESENC          = AESENC.
abbrev [-printing] VAESENCLAST      = AESENCLAST.
abbrev [-printing] VAESIMC          = AESIMC.
abbrev [-printing] VAESKEYGENASSIST = AESKEYGENASSIST.

(* ------------------------------------------------------------------- *)
abbrev [-printing] (\vshr32u128) (w1:W128.t) (w2:W8.t) = VPSRL_4u32 w1 w2.
abbrev [-printing] (\vshl32u128) (w1:W128.t) (w2:W8.t) = VPSLL_4u32 w1 w2.
abbrev [-printing] (\vadd32u128) (w1 w2:W128.t) = VPADD_4u32 w1 w2.


abbrev [-printing] (\vshr32u256) (w1:W256.t) (w2:W8.t) = VPSRL_8u32 w1 w2.
abbrev [-printing] (\vshl32u256) (w1:W256.t) (w2:W8.t) = VPSLL_8u32 w1 w2.

abbrev [-printing] (\vshr64u256) (w1:W256.t) (w2:W8.t) = VPSRL_4u64 w1 w2.
abbrev [-printing] (\vshl64u256) (w1:W256.t) (w2:W8.t) = VPSLL_4u64 w1 w2.

abbrev [-printing] (\vadd32u256) (w1 w2:W256.t) = VPADD_8u32 w1 w2.
abbrev [-printing] (\vadd64u256) (w1 w2:W256.t) = VPADD_4u64 w1 w2.
(*abbrev [-printing] (\vsub64u256) (w1:W256.t) (w2:W8.t) = VPSUB_4u64 w1 w2.*)

(* ------------------------------------------------------------------- *)
(* Leakages                                                            *)

type leakage_t = [
  | LeakAddr of address list
  | LeakCond of bool
  | LeakFor  of (int * int)
].

type leakages_t = leakage_t list.
