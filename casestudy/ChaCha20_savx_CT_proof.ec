require import ChaCha20_savx_CT.

equiv chacha20_avx_ct : 
  M.chacha20_avx ~ M.chacha20_avx : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.