require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Mod_patch.


lemma lzcnt_zero : forall w, LZCNT_64 (w << LZCNT_64 w) = 0.

equiv l2 : M.verify_mod_const ~ M.verify_mod_const : ={M.leakages, b} ==> ={M.leakages}.
proof.
  proc.
  wp=> //=.
  rewrite /leak_div //=.
  inline *=> />; wp.
  simplify. skip=> />.
  move=> &1 &2 //=.
  
