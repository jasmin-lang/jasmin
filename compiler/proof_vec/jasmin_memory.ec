(* -------------------------------------------------------------------- *)
require import AllCore SmtMap List IntDiv.
(*---*) import CoreMap. 
require import Jasmin_utils Jasmin_word.

(* -------------------------------------------------------------------- *)
theory W8List.
  abbrev "_.[_]" (w : W8.t list) (i : int) = nth (W8.of_int 0) w i.
end W8List.
export W8List.

(* -------------------------------------------------------------------- *)
type address = W64.t.

type global_mem_t = (address, W8.t) map.

op stores (m : global_mem_t) (a : address) (w : W8.t list) =
  foldl (fun (m:global_mem_t) i => m.[a + W64.of_int i <- w.[i]]) m (iota_ 0 (size w)).

(* ------------------------------------------------------------------- *)
op loadW8   (m : global_mem_t) (a : address) = m.[a].

op loadW16  (m : global_mem_t) (a : address) = 
  pack2_t (W2u8.Pack.init (fun i => m.[a + W64.of_int i])).

op loadW32  (m : global_mem_t) (a : address) = 
  pack4_t (W4u8.Pack.init (fun i => m.[a + W64.of_int i])).

op loadW64  (m : global_mem_t) (a : address) = 
  pack8_t (W8u8.Pack.init (fun i => m.[a + W64.of_int i])).

op loadW128 (m : global_mem_t) (a : address) = 
  pack16_t (W16u8.Pack.init (fun i => m.[a + W64.of_int i])).

op loadW256 (m : global_mem_t) (a : address) = 
  pack32_t (W32u8.Pack.init (fun i => m.[a + W64.of_int i])).

lemma loadW32_bits8 m p i : 0 <= i < 4 =>
  loadW32 m p \bits8 i = loadW8 m (p + W64.of_int i).
proof. by move=> hi;rewrite /loadW32 pack4bE // initiE. qed.

lemma loadW128_bits8 m p i : 0 <= i < 16 =>
  loadW128 m p \bits8 i = loadW8 m (p + W64.of_int i).
proof. by move=> hi;rewrite /loadW128 pack16bE // initiE. qed.

lemma loadW128_bits32 m p i : 0 <= i < 4 =>
  loadW128 m p \bits32 i = loadW32 m (p + W64.of_int i * W64.of_int 4).
proof. 
  move=> hi; rewrite /loadW128 /loadW32.
  apply W32.wordP => j hj.
  rewrite bits32iE // pack4wE // initiE; 1:by apply divz_cmp.
  rewrite pack16wE; 1:by apply W4u32.in_bound. 
  rewrite initiE /=; 1:by apply divz_cmp => //=;apply W4u32.in_bound.
  have -> : i * 32 = (i * 4) * 8 by ring. 
  by rewrite modzMDl divzMDl // -addrA. 
qed.

lemma load4u32 mem p : 
  pack4
    [loadW32 mem p;
     loadW32 mem (p + W64.of_int 4);
     loadW32 mem (p + W64.of_int 8);
     loadW32 mem (p + W64.of_int 12)] =
  loadW128 mem p.
proof.
  have -> : W4u32.Pack.of_list
          [loadW32 mem p; loadW32 mem (p + (of_int 4)%W64);
           loadW32 mem (p + (of_int 8)%W64); loadW32 mem (p + (of_int 12)%W64)] =
         W4u32.Pack.init (fun i => loadW32 mem (p + W64.of_int (i * 4))).
  + by apply W4u32.Pack.ext_eq_all; rewrite /all_eq /= addr0. 
  apply (can_inj _ _ W4u32.unpack32K); apply W4u32.Pack.packP => i hi.
  by rewrite pack4K initiE //=  get_unpack32 // loadW128_bits32.
qed.

(* ------------------------------------------------------------------- *)
op storeW8 (m : global_mem_t) (a : address) (w : W8.t) =
  m.[a <- w]
axiomatized by storeW8E.

op storeW16 (m : global_mem_t) (a : address) (w : W16.t) =
  stores m a (to_list (unpack8 w))
axiomatized by storeW16E.

op storeW32 (m : global_mem_t) (a : address) (w : W32.t) =
  stores m a (to_list (unpack8 w))
axiomatized by storeW32E.

op storeW64 (m : global_mem_t) (a : address) (w : W64.t) =
  stores m a (to_list (unpack8 w))
axiomatized by storeW64E.

op storeW128 (m : global_mem_t) (a : address) (w : W128.t) =
  stores m a (to_list (unpack8 w))
axiomatized by storeW128E.

op storeW256 (m : global_mem_t) (a : address) (w : W256.t) =
  stores m a (to_list (unpack8 w))
axiomatized by storeW256E.

(* ------------------------------------------------------------------- *)
(* Global Memory                                                       *)

module Glob = {
  var mem : global_mem_t
}.

(* ------------------------------------------------------------------- *)
(* Safety                                                              *)

(* FIXME : define this *)
op is_valid (m:global_mem_t) (p:W64.t) (ws:wsize) : bool.

axiom is_valid_store8 mem sz ptr1 ptr2 w : 
  is_valid (storeW8 mem ptr2 w) ptr1 sz = is_valid mem ptr1 sz.
hint simplify is_valid_store8.

axiom is_valid_store16 mem sz ptr1 ptr2 w : 
  is_valid (storeW16 mem ptr2 w) ptr1 sz = is_valid mem ptr1 sz.
hint simplify is_valid_store16.

axiom is_valid_store32 mem sz ptr1 ptr2 w : 
  is_valid (storeW32 mem ptr2 w) ptr1 sz = is_valid mem ptr1 sz.
hint simplify is_valid_store32.

axiom is_valid_store64 mem sz ptr1 ptr2 w : 
  is_valid (storeW64 mem ptr2 w) ptr1 sz = is_valid mem ptr1 sz.
hint simplify is_valid_store64.

axiom is_valid_store128 mem sz ptr1 ptr2 w : 
  is_valid (storeW128 mem ptr2 w) ptr1 sz = is_valid mem ptr1 sz.
hint simplify is_valid_store128.

axiom is_valid_store256 mem sz ptr1 ptr2 w : 
  is_valid (storeW256 mem ptr2 w) ptr1 sz = is_valid mem ptr1 sz.
hint simplify is_valid_store256.


