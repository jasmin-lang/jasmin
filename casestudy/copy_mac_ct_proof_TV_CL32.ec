require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel Leakage_models.

require import Array64 WArray64.

require Copy_mac_ct.

clone import Copy_mac_ct.T with
theory LeakageModel <- LeakageModelTVCL32.

equiv l_rotate_offset_TVCL md_size_ : M.rotate_offset_TV ~ M.rotate_offset_TV:
={M.leakages, md_size, scan_start} /\ md_size{1} = md_size_ /\
(0 <= (to_uint (mac_start - scan_start)) < 2^8){1} /\
(0 <= (to_uint (mac_start - scan_start)) < 2^8){2} /\
(16 <= to_uint md_size <= 64){1}
==> ={M.leakages} /\ 0 <= to_uint res{1} < to_uint md_size_ /\ 0 <= to_uint res{2} < to_uint md_size_.
proof.
  proc; wp; skip => /> *.
  rewrite /leak_div_32 /leak_div_32_TV !l_rotate_offset_div_core //.
  smt (W32.to_uint_small W32.to_uint_cmp).
qed.

(* md_size : mac tag size --> public *)
(* orig_len : length of record : header + data + mac tag + padding --> public *)
(* out : mac tag is stored in out --> public *)
(* rec : whole message including header, message, tag, padding --> public *)

op wf_rec mem (rec:W64.t) (orig_len md_size : W32.t) =
 let mac_end = loadW32 mem (to_uint (rec + W64.of_int 4)) in
 to_uint md_size <= to_uint mac_end /\
 1 <= to_uint orig_len - to_uint mac_end <= 256.

lemma wf_rec_cond_md_size_mac_end mem rec orig_len md_size :
  16 <= W32.to_uint md_size <= 64 =>
  wf_rec mem rec orig_len md_size =>
  let mac_end = loadW32 mem (to_uint (rec + W64.of_int 4)) in
  if (md_size + W32.of_int 256 \ult orig_len) then
     0 <= to_uint (mac_end - md_size - (orig_len - (md_size + W32.of_int 256))) < 256
  else 0 <= to_uint (mac_end - md_size - W32.zero) < 256.
proof.
  rewrite /wf_rec /=.
  pose mac_end := loadW32 _ _; move: mac_end => mac_end hmd [h1 [h2 h3]].
  have -> : mac_end - md_size - (orig_len - (md_size + W32.of_int 256)) =
            mac_end - (orig_len - W32.of_int 256) by ring.
  rewrite W32.ultE W32.to_uintD_small /= 1:/#.
  case: (to_uint md_size + 256 < to_uint orig_len) => h; last first.
  + rewrite W32.WRingA.subr0 W32.to_uintB 1:W32.uleE 1:// /#.
  rewrite W32.to_uintB ?W32.uleE W32.to_uintB ?W32.uleE /=; smt(W32.to_uint_cmp).
qed.

lemma or_add_and (x y:W64.t) : x `|` y = (x `&` invw y) + y.
proof.
  have -> : x `|` y = (x `&` invw y) `|` y.
  + by apply W64.wordP => i hi; rewrite !W64.orwE !W64.andwE W64.invwE /#.
  by apply W64.orw_disjoint; rewrite -W64.andwA (W64.andwC (invw y)) W64.andw_invw W64.andw0.
qed.

lemma and_invw32 (x:W64.t) :
  0 <= to_uint x < 64 =>
  0 <= to_uint (x `&` invw (W64.of_int 32)) < 32.
proof.
  move=> h.
  pose x' := (x `&` invw (W64.of_int 32)).
  rewrite (divz_eq (to_uint x') 32); have -> /# : to_uint x' %/ 32 = 0.
  have -> : 32 = 2 ^ 5 by done.
  rewrite -W64.to_uint_shr 1:// -W64.to_uint0; congr.
  apply W64.wordP => i hi.
  rewrite /x' W64.shrwE hi /=.
  have hi5 : 0 <= i + 5 by smt().
  rewrite -(b2i_eq1 x.[i + 5])  -(b2i_eq1 (W64.of_int 32).[i + 5]) !W64.b2i_get 1,2://.
  rewrite to_uint_small 1://.
  case (i = 0) => [-> // | hi0].
  rewrite divz_small 2://.
  have /= /#: 2 ^ 6 <= 2 ^ (i + 5).
  apply StdOrder.IntOrder.ler_weexpn2l => // /#.
qed.

lemma offset_div (p offset : W64.t) :
  to_uint p + 32 <= W64.modulus =>
  32 %| to_uint p =>
  0 <= to_uint offset < 32 =>
  to_uint (p + offset) %/ 32  = to_uint p %/ 32.
proof. move=> /= h1 h2 h3; rewrite W64.to_uintD_small /= 1:/# divzDl 1:// /#. qed.

lemma offset_div_and (p offset : W64.t) :
  to_uint p + 32 <= W64.modulus =>
  32 %| to_uint p =>
  0 <= to_uint offset < 64 =>
  to_uint (p + (offset `&` invw (W64.of_int 32))) %/ 32  = to_uint p %/ 32.
proof. by move=> h1 h2 h3; rewrite offset_div // and_invw32. qed.

lemma offset_div_or (p offset : W64.t) :
  to_uint p + 64 <= W64.modulus =>
  32 %| to_uint p =>
  0 <= to_uint offset < 64 =>
  to_uint (p + (offset `|` (W64.of_int 32))) %/ 32  = to_uint p %/ 32 + 1.
proof.
  move=> /= h1 h2 h3.
  rewrite or_add_and (W64.WRingA.addrC ( offset `&` _)) W64.WRingA.addrA.
  have heq : to_uint (p + W64.of_int 32) = to_uint p + 32.
  + by rewrite W64.to_uintD_small /= 1:/#.
  rewrite offset_div_and ?heq //= /#.
qed.

lemma to_uint_truncateu32_small (x: W64.t) :
    to_uint x < W32.modulus =>
    to_uint (truncateu32 x) = to_uint x.
proof.
  move => h; rewrite to_uint_truncateu32 modz_small => />.
  smt (W64.to_uint_cmp).
qed.

equiv l_rotate_mac_CL32 : M.rotate_mac_CL32 ~ M.rotate_mac_CL32 :
  ={M.leakages, out, md_size, rotated_mac} /\ 64 %| W64.to_uint rotated_mac{1} /\
  to_uint rotated_mac{1} + 64 <= W64.modulus /\ (* This hypothesis is implied by  64 %| W64.to_uint rotated_mac{1} we should remove it *)
  16 <= to_uint md_size{1} <= 64 /\
  0 <= to_uint rotate_offset{1} < to_uint md_size{1}  /\ 0 <= to_uint rotate_offset{2} < to_uint md_size{1}
  ==>
  ={M.leakages}.
proof.
  proc.
  while (={out, rotated_mac, md_size, i, M.leakages, zero} /\ 64 %| W64.to_uint rotated_mac{1} /\
         to_uint rotated_mac{1} + 64 <= W64.modulus /\
         16 <= to_uint md_size{1} <= 64 /\
         zero{1} = W64.zero /\
         0 <= to_uint ro{1} < to_uint md_size{1}  /\ 0 <= to_uint ro{2} < to_uint md_size{1});
  wp; skip => />; last by rewrite !to_uint_zeroextu64.
  move => &1 &2 hmod nover h1 h2 h3 h4 h5 h6 hi.
  rewrite /leak_mem /leak_mem_CL32.
  have hro1 : 0 <= to_uint ro{1} && to_uint ro{1} < 64 by smt().
  have hro2 : 0 <= to_uint ro{2} && to_uint ro{2} < 64 by smt().
  have h32 : 32 %| to_uint rotated_mac{2} by smt().
  rewrite !offset_div_or //=.
  have hle32: to_uint rotated_mac{2} + 32 <= W64.modulus by smt().
  rewrite !offset_div_and //=.
  have heq1 : to_uint (ro{1} + W64.one) = to_uint ro{1} + 1 by rewrite W64.to_uintD_small //= /#.
  have hlt1 : to_uint (ro{1} + W64.one) < W32.modulus by rewrite heq1 /= /#.
  have heq2 : to_uint (ro{2} + W64.one) = to_uint ro{2} + 1 by rewrite W64.to_uintD_small //= /#.
  have hlt2 : to_uint (ro{2} + W64.one) < W32.modulus by rewrite heq2 /= /#.
  case: (md_size{2} \ule truncateu32 (ro{1} + W64.one));
  rewrite uleE to_uint_truncateu32_small // heq1 /=;
  case: (md_size{2} \ule truncateu32 (ro{2} + W64.one));
  rewrite uleE to_uint_truncateu32_small // heq2 /= /#.
qed.

equiv l_init_rotated_mac_mem :
  M.init_rotated_mac_mem ~ M.init_rotated_mac_mem :
  ={md_size, rotated_mac, data, orig_len, scan_start, M.leakages} ==> ={M.leakages}.
proof. by proc; sim. qed.

equiv l_final : M.ssl3_cbc_copy_mac_TV_CL32 ~ M.ssl3_cbc_copy_mac_TV_CL32 :
={M.leakages, md_size, orig_len, out, rec, rotated_mac} /\
(loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){1} = (loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){2} /\
to_uint rotated_mac{2} + 64 <= W64.modulus /\ 64 %| to_uint rotated_mac{2} /\
16 <= to_uint md_size{2} <= 64 /\
(wf_rec Glob.mem rec orig_len md_size){1} /\ (wf_rec Glob.mem rec orig_len md_size){2}
==> ={M.leakages}.
proof.
  proc.
  call l_rotate_mac_CL32; wp.
  ecall (l_rotate_offset_TVCL md_size{1}); wp.
  call l_init_rotated_mac_mem; wp => /=.
  inline *; wp; skip => |> &1 &2; smt (wf_rec_cond_md_size_mac_end).
qed.
