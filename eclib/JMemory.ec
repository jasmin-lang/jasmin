(* -------------------------------------------------------------------- *)
require import AllCore SmtMap List IntDiv.
(*---*) import CoreMap StdOrder.IntOrder.
require import JUtils JWord.

(* -------------------------------------------------------------------- *)
theory W8List.
  abbrev "_.[_]" (w : W8.t list) (i : int) = nth (W8.of_int 0) w i.
end W8List.
export W8List.

(* -------------------------------------------------------------------- *)
type address = int.

type global_mem_t.

op "_.[_]" : global_mem_t -> address -> W8.t.
op "_.[_<-_]" : global_mem_t -> address -> W8.t -> global_mem_t.

axiom mem_eq_ext (m1 m2:global_mem_t) : (forall j, m1.[j] = m2.[j]) => m1 = m2.

axiom get_setE m x y w :
  m.[x <- w].[y] = if y = x then w else m.[y].

lemma get_set_eqE_s m x y w :
  y = x => m.[x <- w].[y] = w.
proof. by rewrite get_setE => ->. qed.

lemma get_set_neqE_s m x y w :
  y <> x => m.[x <- w].[y] = m.[y].
proof. by rewrite get_setE => ->. qed.

hint simplify (get_set_eqE_s, get_set_neqE_s).

op allocated8 : global_mem_t -> address -> bool.

axiom allocated8_setE y w m x: allocated8 m.[y<-w] x = allocated8 m x.

(* ------------------------------------------------------------------- *)

op stores (m : global_mem_t) (a : address) (w : W8.t list) =
  foldl (fun (m:global_mem_t) i => m.[a + i <- w.[i]]) m (iotared 0 (size w))
axiomatized by storesE.

lemma foldl_in_eq (f1 f2:'a -> 'b -> 'a) (s:'b list) a :
   (forall a b, b \in s => f1 a b = f2 a b) => foldl f1 a s = foldl f2 a s.
proof.
  elim: s a => [ | b s hrec] a //= hin.
  by rewrite hin // hrec // => ?? h;apply hin;rewrite h.
qed.

lemma store0 m a : stores m a [] = m.
proof. by rewrite storesE. qed.

lemma stores_cons m a w ws : stores m a (w::ws) = stores (m.[a <- w]) (a + 1) ws.
proof.
  rewrite !storesE iotaredE /= addrC iotaS 1:List.size_ge0. 
  rewrite (addzC 0 1) iota_addl /=.
  rewrite -(revK (iota_ 0 (size ws))) map_rev !foldl_rev foldr_map /=.
  rewrite -!foldl_rev !revK; apply foldl_in_eq => m0 i /mem_iota /= h /#.
qed.

lemma allocated8_stores ws a m x : allocated8 (stores m a ws) x = allocated8 m x.
proof.
  elim: ws m a => //= w ws; 1: by rewrite store0.
  by move=> hrec m a; rewrite stores_cons hrec allocated8_setE.
qed.

lemma get_storesE m p l j: (stores m p l).[j] = if p <= j < p + size l then nth W8.zero l (j - p) else m.[j].
proof.
  elim: l m p => [ | w l hrec] m p.
  + by rewrite store0 /#.
  rewrite stores_cons hrec /= get_setE; smt (size_ge0).
qed.

(* ------------------------------------------------------------------- *)
op loadW8   (m : global_mem_t) (a : address) = m.[a].

op loadW16  (m : global_mem_t) (a : address) =
  pack2_t (W2u8.Pack.init (fun i => m.[a + i])).

op loadW32  (m : global_mem_t) (a : address) =
  pack4_t (W4u8.Pack.init (fun i => m.[a + i])).

op loadW64  (m : global_mem_t) (a : address) =
  pack8_t (W8u8.Pack.init (fun i => m.[a + i])).

op loadW128 (m : global_mem_t) (a : address) =
  pack16_t (W16u8.Pack.init (fun i => m.[a + i])).

op loadW256 (m : global_mem_t) (a : address) =
  pack32_t (W32u8.Pack.init (fun i => m.[a + i])).

lemma loadW32_bits8 m p i : 0 <= i < 4 =>
  loadW32 m p \bits8 i = loadW8 m (p + i).
proof. by move=> hi;rewrite /loadW32 pack4bE // initiE. qed.

lemma loadW128_bits8 m p i : 0 <= i < 16 =>
  loadW128 m p \bits8 i = loadW8 m (p + i).
proof. by move=> hi;rewrite /loadW128 pack16bE // initiE. qed.

lemma loadW128_bits32 m p i : 0 <= i < 4 =>
  loadW128 m p \bits32 i = loadW32 m (p + i * 4).
proof.
  move=> hi; rewrite /loadW128 /loadW32.
  apply W32.wordP => j hj.
  rewrite bits32iE // pack4wE // initiE; 1:by apply divz_cmp.
  rewrite pack16wE; 1:by apply W4u32.in_bound.
  rewrite initiE /=; 1:by apply divz_cmp => //=;apply W4u32.in_bound.
  have -> : i * 32 = (i * 4) * 8 by ring.
  by rewrite modzMDl divzMDl // -addzA.
qed.

lemma loadW128_bits64 m p i : 0 <= i < 2 =>
  loadW128 m p \bits64 i = loadW64 m (p + i * 8).
proof.
  move=> hi; rewrite /loadW128 /loadW64.
  apply W64.wordP => j hj.
  rewrite bits64iE // pack8wE // initiE; 1:by apply divz_cmp.
  rewrite pack16wE; 1:by apply W2u64.in_bound.
  rewrite initiE /=; 1:by apply divz_cmp => //=;apply W2u64.in_bound.
  have -> : i * 64 = (i * 8) * 8 by ring.
  by rewrite modzMDl divzMDl // -addzA.
qed.

lemma load4u8 mem p :
  pack4
    [loadW8 mem p;
     loadW8 mem (p + 1);
     loadW8 mem (p + 2);
     loadW8 mem (p + 3)] =
  loadW32 mem p.
proof.
  have -> : W4u8.Pack.of_list
          [loadW8 mem p; loadW8 mem (p + 1);
           loadW8 mem (p + 2); loadW8 mem (p + 3)] =
         W4u8.Pack.init (fun i => loadW8 mem (p + i)).
  + by apply W4u8.Pack.all_eqP; rewrite /all_eq.
  apply (can_inj _ _ W4u8.unpack8K); apply W4u8.Pack.packP => i hi.
  rewrite /loadW32 pack4K //=. 
qed.

lemma load4u32 mem p :
  pack4
    [loadW32 mem p;
     loadW32 mem (p + 4);
     loadW32 mem (p + 8);
     loadW32 mem (p + 12)] =
  loadW128 mem p.
proof.
  have -> : W4u32.Pack.of_list
          [loadW32 mem p; loadW32 mem (p + 4);
           loadW32 mem (p + 8); loadW32 mem (p + 12)] =
         W4u32.Pack.init (fun i => loadW32 mem (p + i * 4)).
  + by apply W4u32.Pack.all_eqP; rewrite /all_eq.
  apply (can_inj _ _ W4u32.unpack32K); apply W4u32.Pack.packP => i hi.
  by rewrite pack4K initiE //= get_unpack32 // loadW128_bits32.
qed.

lemma load2u64 mem p:
   pack2 [loadW64 mem p; loadW64 mem (p + 8)]
   = loadW128 mem p.
proof.
  have ->: W2u64.Pack.of_list
         [loadW64 mem p; loadW64 mem (p + 8)] =
         W2u64.Pack.init (fun i => loadW64 mem (p + i * 8)).
  + by apply W2u64.Pack.all_eqP; rewrite /all_eq.
  apply (can_inj _ _ W2u64.unpack64K); apply W2u64.Pack.packP => i hi.
  by rewrite pack2K initiE //=  get_unpack64 // loadW128_bits64.
qed.

(* ------------------------------------------------------------------- *)
op storeW8 (m : global_mem_t) (a : address) (w : W8.t) =
  m.[a <- w]
axiomatized by storeW8E.

op storeW16 (m : global_mem_t) (a : address) (w : W16.t) =
  stores m a (W2u8.to_list w)
axiomatized by storeW16E.

op storeW32 (m : global_mem_t) (a : address) (w : W32.t) =
  stores m a (W4u8.to_list w)
axiomatized by storeW32E.

op storeW64 (m : global_mem_t) (a : address) (w : W64.t) =
  stores m a (W8u8.to_list w)
axiomatized by storeW64E.

op storeW128 (m : global_mem_t) (a : address) (w : W128.t) =
  stores m a (W16u8.to_list w)
axiomatized by storeW128E.

op storeW256 (m : global_mem_t) (a : address) (w : W256.t) =
  stores m a (W32u8.to_list w)
axiomatized by storeW256E.

(*
lemma pack4u32_bits8_nth i (ws:W32.t list) : 0 <= i < 16 =>
  W4u32.pack4 ws \bits8 i = nth W32.zero ws (i %/ 4) \bits8 (i%%4).
proof.
  move=> hi; rewrite -W4u32.Pack.get_of_list; first by apply divz_cmp.
  move: (W4u32.Pack.of_list ws) => w.
  apply W8.wordP => k hk.
  rewrite -W4u32.pack4bE; 1: by apply divz_cmp.
  rewrite bits8iE // bits8iE // bits32iE; 1: smt(modz_cmp).
  congr; rewrite {1}(divz_eq i 4); ring.
qed.

lemma pack2u64_bits8_nth i (ws:W64.t list) : 0 <= i < 16 =>
  W2u64.pack2 ws \bits8 i = nth W64.zero ws (i %/ 8) \bits8 (i%%8).
proof.
  move=> hi; rewrite -W2u64.Pack.get_of_list; first by apply divz_cmp.
  move: (W2u64.Pack.of_list ws) => w.
  apply W8.wordP => k hk.
  rewrite -W2u64.pack2bE; 1: by apply divz_cmp.
  rewrite bits8iE // bits8iE // bits64iE; 1: smt(modz_cmp).
  congr; rewrite {1}(divz_eq i 8); ring.
qed.
*)

lemma store4u32 mem ptr w0 w1 w2 w3 :
  storeW128 mem ptr (W4u32.pack4 [w0; w1; w2; w3]) =
  storeW32
    (storeW32
       (storeW32
          (storeW32 mem ptr w0)
          (ptr + 4) w1)
       (ptr + 8) w2)
    (ptr + 12) w3.
proof. by rewrite storeW128E !storeW32E /= !storesE /=. qed.

lemma store2u64 mem ptr w0 w1:
  storeW128 mem ptr (W2u64.pack2 [w0; w1]) =
  storeW64 (storeW64 mem ptr w0) (ptr + 8) w1.
proof.  by rewrite storeW128E !storeW64E /= !storesE /=. qed.

lemma store4u8 mem ptr w0 w1 w2 w3 :
  storeW32 mem ptr (W4u8.pack4 [w0; w1; w2; w3]) =
  storeW8
    (storeW8
       (storeW8
          (storeW8 mem ptr w0)
          (ptr + 1) w1)
       (ptr + 2) w2)
    (ptr + 3) w3.
proof. by rewrite storeW32E !storeW8E storesE /=. qed.

lemma get_storeW32E m p (w:W32.t) j :
  (storeW32 m p w).[j] = if p <= j < p + 4 then w \bits8 (j - p) else m.[j].
proof. rewrite storeW32E /= get_storesE /= /#. qed.

(* ------------------------------------------------------------------- *)
(* Global Memory                                                       *)

module Glob = {
  var mem : global_mem_t
}.
