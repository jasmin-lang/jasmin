(* -------------------------------------------------------------------- *)
require import AllCore BitEncoding IntDiv SmtMap Ring List StdOrder Bool.
(*---*) import CoreMap Map Ring.IntID IntOrder.
require export Jasmin_utils Jasmin_array Jasmin_word Jasmin_memory.

(*
axiom VPAND_128_32 (w1 w2 : p4u32):
  (pack_4u32 w1 `&` pack_4u32 w2) = 
  pack_4u32 (map2_4u32 W32.(`&`) w1 w2).

axiom VPOR_128_32 (w1 w2 : p4u32):
  (pack_4u32 w1 `|` pack_4u32 w2) = 
  pack_4u32 (map2_4u32 W32.(`|`) w1 w2).

axiom VPXOR_128_32 (w1 w2 : p4u32):
  (pack_4u32 w1 `^` pack_4u32 w2) = 
  pack_4u32 (map2_4u32 W32.(`^`) w1 w2).

hint simplify (VPAND_128_32, VPOR_128_32, VPXOR_128_32)@0.
*)
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

abbrev x86_VPSLL_16u8 (w : W128.t) (cnt : W8.t) = 
  map (fun (w:W8.t) => w `<<` cnt) w.

abbrev x86_VPSLL_8u16 (w : W128.t) (cnt : W8.t) = 
  map (fun (w:W16.t) => w `<<` cnt) w.

abbrev x86_VPSLL_4u32 (w : W128.t) (cnt : W8.t) = 
  map (fun (w:W32.t) => w `<<` cnt) w.

abbrev x86_VPSLL_2u64 (w : W128.t) (cnt : W8.t) = 
  map (fun (w:W64.t) => w `<<` cnt) w.

abbrev x86_VPSRL_16u8 (w : W128.t) (cnt : W8.t) = 
  map (fun (w:W8.t) => w `>>` cnt) w.

abbrev x86_VPSRL_8u16 (w : W128.t) (cnt : W8.t) = 
  map (fun (w:W16.t) => w `>>` cnt) w.

abbrev x86_VPSRL_4u32 (w : W128.t) (cnt : W8.t) = 
  map (fun (w:W32.t) => w `>>` cnt) w.

abbrev x86_VPSRL_2u64 (w : W128.t) (cnt : W8.t) = 
  map (fun (w:W64.t) => w `>>` cnt) w.

(* -------------------------------------------------------------------- *)

op x86_VPSHUFB_128_B (w:W128.t) (m : W8.t) =
  let i = W8.to_uint m in
  if 128 <= i then W8.zero 
  else w \bits8 (i %% 16).
    
op x86_VPSHUFB_128 (w m : W128.t) : W128.t =
  map (x86_VPSHUFB_128_B w) m.

(*axiom VPAND_128_8 (w1 w2 : p16u8):
  (pack_16u8 w1 `&` pack_16u8 w2) = 
  pack_16u8 (map2_16u8 W8.(`&`) w1 w2).

axiom VPOR_128_8 (w1 w2 : p16u8):
  (pack_16u8 w1 `|` pack_16u8 w2) = 
  pack_16u8 (map2_16u8 W8.(`|`) w1 w2).

axiom VPXOR_128_8 (w1 w2 : p16u8):
  (pack_16u8 w1 `^` pack_16u8 w2) = 
  pack_16u8 (map2_16u8 W8.(`^`) w1 w2).

hint simplify VPAND_128_8.
hint simplify VPOR_128_8.
hint simplify VPXOR_128_8.
*)
(* -------------------------------------------------------------------- *)
op x86_VPSHUFD_128_B (w : W128.t) (m : W8.t) (i : int) : W32.t =
  let m = W8.to_uint m in
  let p = (m %/ (2^(2*i)))%%4 in
  w \bits32 p.

op x86_VPSHUFD_128 (w : W128.t) (m : W8.t) : W128.t =
  pack4 (mkseq (x86_VPSHUFD_128_B w m) 4).


(* -------------------------------------------------------------------- *)

op mulu_64 (w1 w2 : W64.t) = 
  let (p1,p2) = (W32.mulu (w1 \bits32 0) (w2 \bits32 0)) in
  pack2 [p1; p2].
 
(* -------------------------------------------------------------------- *)

op x86_VPADD_2u64 (w1 : W128.t) (w2:W128.t) = 
   map2 W64.(+) w1 w2.


op x86_VPEXTR_64 (w:W128.t) (i:W8.t) = 
  if W8.to_uint i = 0 then (w \bits64 0)
  else if W8.to_uint i = 1 then (w \bits64 1)
  else W64.of_int 0.

op x86_VPINSR_2u64 (v1:W128.t) (v2:W64.t) (i:W8.t) = 
  if W8.to_uint i = 0 then (pack2 [v2; v1 \bits64 1])
  else if W8.to_uint i = 1 then (pack2 [v1 \bits64 0; v2])
  else v1.

op x86_MOVD_64 (v:W64.t) = 
  pack2 [v; W64.zero]. 

op x86_VPUNPCKL_2u64 (w1 w2: W128.t) = 
  pack2 [w1 \bits64 0; w2 \bits64 0].

op x86_VPUNPCKH_2u64 (w1 w2: W128.t) = 
  pack2 [w1 \bits64 1; w2 \bits64 1].

abbrev x86_VPAND_128 = W128.(`&`).
abbrev x86_VPOR_128 = W128.(`|`).

op x86_VPMULU_128 (w1 w2: W128.t) = 
  map2 mulu_64 w1 w2.

(*
axiom VPAND_128_64 w1 w2:
  pack_2u64 w1 `&` pack_2u64 w2 = 
  pack_2u64(w1.`1 `&` w2.`1, w1.`2 `&` w2.`2).

axiom VPOR_128_64 w1 w2:
  pack_2u64 w1 `|` pack_2u64 w2 = 
  pack_2u64(w1.`1 `|` w2.`1, w1.`2 `|` w2.`2).

axiom VPXOR_128_64 w1 w2:
  pack_2u64 w1 `^` pack_2u64 w2 = 
  pack_2u64(w1.`1 `^` w2.`1, w1.`2 `^` w2.`2).

hint simplify (VPAND_128_64, VPOR_128_64, VPXOR_128_64)@0.
*)

(* ------------------------------------------------------------------- *)
(* Leakages                                                            *)

type leakage_t = [
  | LeakAddr of address list
  | LeakCond of bool
  | LeakFor  of (int * int)
].

type leakages_t = leakage_t list.


