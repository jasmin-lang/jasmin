require import List.
require import JUtils JWord.

op sigma0 (w: W32.t) : W32.t = (w `|>>>|` 7) +^ (w `|>>>|` 18) +^ (w `>>>` 3).
op sigma1 (w: W32.t) : W32.t = (w `|>>>|` 17) +^ (w `|>>>|` 19) +^ (w `>>>` 10).

op msg1 (m1 m2: W128.t) : W128.t =
  let s1 = W4u32.to_list m1 in
  pack4 (map2 (fun x y => x + sigma0 y) s1 (rcons (behead s1) (m2 \bits32 0))).

op msg2 (m1 m2: W128.t) : W128.t =
  let w14 = m2 \bits32 2 in
  let w15 = m2 \bits32 3 in
  let w16 = (m1 \bits32 0) + sigma1 w14 in
  let w17 = (m1 \bits32 1) + sigma1 w15 in
  let w18 = (m1 \bits32 2) + sigma1 w16 in
  let w19 = (m1 \bits32 3) + sigma1 w17 in
  pack4 [w16; w17; w18; w19].
