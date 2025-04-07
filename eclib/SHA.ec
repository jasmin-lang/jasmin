require import List.
require import JUtils JWord.

op ch (e f g: W32.t) : W32.t = (e `&` f) +^ (invw e `&` g).

op maj (a b c: W32.t) : W32.t = a `&` b +^ a `&` c +^ b `&` c.

op sum0 (a: W32.t) : W32.t = (a `|>>>|` 2) +^ (a `|>>>|` 13) +^ (a `|>>>|` 22).
op sum1 (e: W32.t) : W32.t = (e `|>>>|` 6) +^ (e `|>>>|` 11) +^ (e `|>>>|` 25).

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

op rnds2 (x y z: W128.t) : W128.t =
  let unpack = fun m : W128.t => (m \bits32 0, m \bits32 1, m \bits32 2, m \bits32 3) in
  let (h0, g0, d0, c0) = unpack x in
  let (f0, e0, b0, a0) = unpack y in
  let (wk0, wk1) = (z \bits32 0, z \bits32 1) in
  let t0 = ch e0 f0 g0 + sum1 e0 + wk0 + h0 in
  let a1 = t0 + maj a0 b0 c0 + sum0 a0 in
  let e1 = t0 + d0 in
  let t1 = ch e1 e0 f0 + sum1 e1 + wk1 + g0 in
  let a2 = t1 + maj a1 a0 b0 + sum0 a1 in
  let e2 = t1 + c0 in
  pack4 [e1; e2; a1; a2].
