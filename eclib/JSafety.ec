require import AllCore IntDiv CoreMap List Distr StdBigop.
import Bigbool.


lemma and_iota (F : int -> bool) i l :
    BBAnd.big predT F  (iota_ i l) <=> forall k, i <= k < i + l => F k.
proof.
  rewrite  BBAnd.bigP filter_predT List.allP.
  smt(mem_iota ).
qed.

