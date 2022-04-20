require import ChaCha20_sref_CT.

equiv chacha20_ref_ct : 
  M.chacha20_ref ~ M.chacha20_ref : ={output, plain, len, nonce, key, M.leakages} ==> ={M.leakages}.
proof. proc;inline *;sim => />. qed.