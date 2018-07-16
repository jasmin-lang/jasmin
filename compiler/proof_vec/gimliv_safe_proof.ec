require import List Jasmin_model Int IntDiv CoreMap Gimliv_safe.

hoare gimli_bodyS : M.gimli_body : M.safe ==> M.safe.
proof.
  proc; wp.
  while (M.safe); 2: by auto.
  by inline *; wp; skip.
qed.

hoare gimliS : M.gimli : 
  M.safe /\
  is_valid Glob.mem state W128 /\
  is_valid Glob.mem (state + W64.of_int 16) W128 /\
  is_valid Glob.mem (state + W64.of_int 32) W128
  ==> 
  M.safe.
proof.
  by proc; wp; call gimli_bodyS; wp; skip.
qed.




