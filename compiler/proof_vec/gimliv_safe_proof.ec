require import List Jasmin_model Int IntDiv CoreMap Gimliv_safe.

hoare gimli_bodyS : M.gimli_body : M.safe ==> M.safe.
proof.
  proc.
  seq 1 : (M.safe /\ is_init round); 1: by auto.
  while (M.safe /\ is_init round); 2: by auto.
  inline *; wp; skip; rewrite /is_init => />.
qed.

