require import AllCore.
from Jasmin require import JWord.

require Loops.

lemma loops_forty_correct : hoare [ Loops.M.forty: true ==> res = W32.of_int 40 ].
proof. by proc; unroll for ^while; auto. qed.

lemma loops_for_nest_correct : hoare [ Loops.M.for_nest: true ==> res = W32.of_int 2000 ].
proof.
  proc; wp.
  while (0 <= i <= inc /\ k = 100 * i).
  - wp.
    while (0 <= j <= inc_0 /\ k = 100 * i + j); by auto => /#.
  auto => /#.
qed.
