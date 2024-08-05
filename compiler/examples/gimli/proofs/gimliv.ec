require Gimli_avx Gimli_x86.
import List Int JWord JModel_x86.

import Array12.

lemma zeroextu128E (x: W32.t) :
  zeroextu128 x = pack4[ x; W32.zero; W32.zero; W32.zero ].
proof. by rewrite W4u32.zeroextu128E of_listE. qed.

op eqstate (v: W128.t * W128.t * W128.t) (s: W32.t Array12.t) =
  v.`1 = pack4 [ s.[0]; s.[1]; s.[2]; s.[3] ] /\
  v.`2 = pack4 [ s.[4]; s.[5]; s.[6]; s.[7] ] /\
  v.`3 = pack4 [ s.[8]; s.[9]; s.[10]; s.[11] ].

 equiv gimli_ref_equiv :
    Gimli_avx.M.gimli_body ~ Gimli_x86.M.gimli :
    eqstate arg{1} arg{2} ==> eqstate res{1} res{2}.
proof.
  proc; inline *; wp.
  while (={round} /\ eqstate (x{1}, y{1}, z{1}) state{2}); auto.
  unroll for{2} ^while; wp; skip => />.
  by rewrite !/VPSHUFD_128 !/VPSHUFD_128_B /= zeroextu128E.
qed.
