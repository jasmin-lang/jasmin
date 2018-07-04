require import Jasmin_model Gimliv_ct.

equiv gimli_body_ct : M.gimli_body ~ M.gimli_body : ={M.leakages} ==> ={M.leakages}.
proof.
  proc; inline *; sim.
qed.

