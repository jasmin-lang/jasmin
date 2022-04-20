require import Poly1305_savx2_CT.

equiv poly1305_avx2_CT : M.poly1305_avx2 ~ M.poly1305_avx2 : 
  ={k, in_0, out, inlen, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim. qed.

