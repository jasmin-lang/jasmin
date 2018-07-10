require import List Jasmin_model Int IntDiv CoreMap Gimliv_safe.

hoare gimli_bodyS : M.gimli_body : M.safe ==> M.safe.
proof.
  proc.
  seq 1 : (M.safe /\ is_init round); 1: by auto.
  while (M.safe /\ is_init round); 2: by auto.
  inline *; wp; skip; rewrite /is_init => />.
qed.

hoare gimliS : M.gimli : 
  M.safe /\
  is_valid Glob.mem state W128 /\
  is_valid Glob.mem (state + W64.of_int 16) W128 /\
  is_valid Glob.mem (state + W64.of_int 32) W128
  ==> 
  M.safe.
proof.
  proc.
  wp; call gimli_bodyS; wp; skip.
  cbv delta => /> &1.  
  rewrite W64.addr0 => />.
qed.




