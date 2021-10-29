require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Array128 WArray128 Lucky13_split_full_log.

equiv l_constant_time_lt_jasmin : M.constant_time_lt_jasmin ~ M.constant_time_lt_jasmin :
={M.leakages}
==> ={M.leakages}.
proof.
proc; inline *; sim.
qed.

equiv l_rotate_offset_div : M.rotate_offset_div ~ M.rotate_offset_div:
={M.leakages, md_size, scan_start} /\
(0 <= (to_uint (mac_start - scan_start)) < 2^8){1} /\ 
(0 <= (to_uint (mac_start - scan_start)) < 2^8){2} /\
(16 <= to_uint md_size <= 64){1}
==> ={M.leakages}.
proof.
  proc; wp; skip => />.
admitted.

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

equiv l_rotate_mac_ct : M.rotate_mac ~ M.rotate_mac : ={M.leakages, out, md_size} ==> ={M.leakages}.
proof. by proc; inline *; sim. qed.

equiv l_final : M.ssl3_cbc_copy_mac_jasmin ~ M.ssl3_cbc_copy_mac_jasmin :
={M.leakages, md_size, orig_len, out, rec} /\
(loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){1} = 
(loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){2} /\
16 <= to_uint md_size{2} <= 64 /\
(wf_rec Glob.mem rec orig_len md_size){1} /\ 
(wf_rec Glob.mem rec orig_len md_size){2}  
==> ={M.leakages}.
proof.
  proc.
  call l_rotate_mac_ct; wp.
  call l_constant_time_lt_jasmin; wp.
  while (={M.leakages, temp, out, md_size}); 1: by sim.
  wp => /=; conseq />.
  call l_rotate_offset_div; wp.
  while (={i, j, orig_len, data, md_size, M.leakages}); 1: by inline*;sim.
  wp => /=; while (={i, md_size, M.leakages}); 1: by sim.
  wp; skip => |> &1 &2; smt (wf_rec_cond_md_size_mac_end).
qed.
