require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Mod_patch_bash.


lemma lzcnt_zero : forall (w: t), leak_div (w `<<<` leak_div w) = 0.
admitted.

equiv l2 : M.verify_mod_const ~ M.verify_mod_const : ={M.leakages, b} ==> ={M.leakages}.
proof.
  proc.
  wp=> //=.
  rewrite /leak_div //=.
  inline *=> />; wp.
  simplify. skip=> />.
  move=> &1 &2 //=.
  case: ((LZCNT_64 a{1}).`6 = W64.zero) =>//=.
  (* leading zero of a is 0 *)
  + move=> h1 />. case: ((LZCNT_64 a{2}).`6 = W64.zero)=> //=.
    (* leading zero of a is 0 *)
    + move=> h2 /=. rewrite /LZCNT_64 /leak_div /= in h1. rewrite /LZCNT_64 /leak_div /= in h2.
      search _ of_int.
      
