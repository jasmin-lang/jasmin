require import Jasmin_model Poly1305_avx_5xp_ct.

(*equiv poly1305_ct : M.poly1305 ~ M.poly1305 : ={M.leakages} ==> ={M.leakages}.
proc; inline *;sim.
*)

equiv poly1305_ct : M.poly1305 ~ M.poly1305 : 
  ={k, inlen, in_0, out, M.leakages} ==> ={M.leakages}.
proof. proc => /=; inline *; sim. qed.
