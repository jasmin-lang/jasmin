require import List Jasmin_model Int IntDiv CoreMap Gimliv_safe.

hoare gimli_bodyS : M.gimli_body : M.safe ==> M.safe.
proof.
  proc.
  seq 1 : (M.safe /\ is_init round); 1: by auto.
  while (M.safe /\ is_init round); 2: by auto.
  inline *; wp; skip; rewrite /is_init => />.
qed.

(* TODO move this *)
axiom addw0 (w : W64.t) : w + W64.zeros = w.
axiom of_uint0 : W64.of_uint 0 = W64.zeros.

axiom is_valid_store128 mem sz ptr1 ptr2 w : 
  is_valid (storeW128 mem ptr2 w) ptr1 sz = is_valid mem ptr1 sz.
hint simplify is_valid_store128.

hoare gimliS : M.gimli : 
  M.safe /\
  is_valid Glob.mem state W128 /\
  is_valid Glob.mem (state + W64.of_uint 16) W128 /\
  is_valid Glob.mem (state + W64.of_uint 32) W128
  ==> 
  M.safe.
proof.
  proc.
  wp; call gimli_bodyS; wp; skip.
  cbv delta => /> &1.  
  rewrite of_uint0 addw0 => />.
qed.




