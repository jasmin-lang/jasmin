require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Array128 WArray128 Lucky13_split_div64_log.

equiv l_constant_time_lt_jasmin : M.constant_time_lt_jasmin ~ M.constant_time_lt_jasmin :
  ={M.leakages} ==> ={M.leakages}.
proof. by proc; inline *; sim. qed.

equiv l_rotate_offset_div md_size_ : M.rotate_offset_div ~ M.rotate_offset_div:
={M.leakages, md_size, scan_start} /\ md_size{1} = md_size_ /\
(0 <= (to_uint (mac_start - scan_start)) < 2^8){1} /\ 
(0 <= (to_uint (mac_start - scan_start)) < 2^8){2} /\
(16 <= to_uint md_size <= 64){1}
==> ={M.leakages} /\ 0 <= to_uint res{1} < to_uint md_size_ /\ 0 <= to_uint res{2} < to_uint md_size_.
proof.
  proc; wp; skip => />.
admitted.

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

lemma offset_div (p:W64.t) (offset: W32.t): 
  to_uint p + 64 <= W64.modulus => 
  64 %| to_uint p => 
  0 <= to_uint offset < 64 => 
  to_uint (p + zeroextu64 offset) %/ 64  = to_uint p %/ 64.
proof.
  move=> /= h1 h2 h3; rewrite W64.to_uintD_small to_uint_zeroextu64 /= 1:/# divzDl 1:// /#.
qed.

equiv l_rotate_mac_ct : M.rotate_mac_cache ~ M.rotate_mac_cache : 
  ={M.leakages, out, md_size, rotated_mac} /\ 64 %| W64.to_uint rotated_mac{1} /\
  to_uint rotated_mac{1} + 64 <= W64.modulus /\
  16 <= to_uint md_size{1} <= 64 /\
  0 <= to_uint rotate_offset{1} < to_uint md_size{1}  /\ 0 <= to_uint rotate_offset{2} < to_uint md_size{1}
  ==> 
  ={M.leakages}.
proof.
  proc.
  while (={out, rotated_mac, md_size, i, j, M.leakages} /\ 64 %| W64.to_uint rotated_mac{1} /\
         to_uint rotated_mac{1} + 64 <= W64.modulus /\
         16 <= to_uint md_size{1} <= 64 /\ 
         0 <= to_uint rotate_offset{1} < to_uint md_size{1}  /\ 0 <= to_uint rotate_offset{2} < to_uint md_size{1}).
  + inline *; wp; skip => /> &1 &2 hmod nover h1 h2 h3 h4 h5 h6 hi.
    rewrite !offset_div //= 1,2:/#.
    split; rewrite uleE.
    + case: (to_uint md_size{2} <= to_uint (rotate_offset{1} + W32.one)) => /=; smt(W32.to_uint_cmp).
    case: (to_uint md_size{2} <= to_uint (rotate_offset{2} + W32.one)) => /=; smt(W32.to_uint_cmp).
  by wp; skip => />. 
qed.
print (%|).
equiv l_final : M.ssl3_cbc_copy_mac_jasmin_cache ~ M.ssl3_cbc_copy_mac_jasmin_cache :
={M.leakages, md_size, orig_len, out, rec, rotated_mac} /\
(loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){1} = (loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){2} /\
to_uint rotated_mac{2} + 64 <= W64.modulus /\ 64 %| to_uint rotated_mac{2} /\
16 <= to_uint md_size{2} <= 64 /\
(wf_rec Glob.mem rec orig_len md_size){1} /\ (wf_rec Glob.mem rec orig_len md_size){2}  
==> ={M.leakages}.
proof.
  proc.
  call l_rotate_mac_ct; wp.
  ecall (l_rotate_offset_div md_size{1}); wp.
  while (={i, j, orig_len, data, rotated_mac, md_size, M.leakages}); 1: by inline*;sim.
  wp => /=; while (={i, rotated_mac, md_size, M.leakages}); 1: by sim.
  wp; skip => |> &1 &2; smt (wf_rec_cond_md_size_mac_end).
qed.

