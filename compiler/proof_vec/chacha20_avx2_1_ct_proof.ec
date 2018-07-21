require import Jasmin_model Chacha20_avx2_1_ct.
(*
   out    : output pointer;
   outlen : length to output;
   key    : pointer to the key (the key is secret but not its address);
   nonce  : pointer to the nonce (same remark that for key);
   rounds : number of rounds
*)

equiv chacha_ct : M.chacha ~ M.chacha : 
  ={out, outlen, key, nonce, rounds, M.leakages} ==> ={M.leakages}.
proof. by proc; inline *; sim. qed.

