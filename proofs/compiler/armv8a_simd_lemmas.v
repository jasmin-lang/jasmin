(* Properties of the ARMv8-A Advanced SIMD semantics of armv8a_simd.v.

   Proof-only: nothing in the compiler depends on this file. It states what
   the transcribed instruction semantics compute, in the terms of the
   standards they implement:
   - [split_vec_make_vec]: the elements of a packed vector are the packed
     words, element 0 first;
   - the SHA-2 helper functions of the Arm pseudocode are the FIPS 180-4
     functions (those of sha256.v for SHA-256, which armv8a_simd.v uses;
     defined below for SHA-512);
   - [SHA256H_rounds]: SHA256H and SHA256H2 perform four FIPS 180-4 SHA-256
     rounds; [SHA256SU_schedule]: SHA256SU0 then SHA256SU1 compute four
     message-schedule words;
   - [SHA512H_H2_rounds]: SHA512H, SHA512H2 and an element-wise addition
     perform two SHA-512 rounds; [SHA512SU_schedule]: SHA512SU0 then
     SHA512SU1 compute two message-schedule words;
   - the [*_instr_*] lemmas: the same statements about the [id_semi] of the
     instruction descriptions, which fix the role of each operand;
   - [xar_rolE]: XAR by 64 - r is a left rotation by r of the XOR.
   These are statements about the semantics as transcribed; they do not
   validate the transcription against the architecture. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype tuple div ssralg word_ssrZ.
Require Import utils word sha256 sem_type arch_decl armv8a_simd armv8a_instr_decl.
Import Utf8 ZArith.

(* [word] is opaque in Jasmin; the proof relates it to the underlying
   [mathcomp.word] words to compare bits. *)
Transparent word.
Lemma split_vec_make_vec (ve sz : wsize) (l : seq (word ve)) :
  (size l * ve)%nat = sz -> split_vec ve (make_vec sz l) = l.
Proof.
  move=> hsz.
  have hve : (0 < nat_of_wsize ve)%nat by case: (ve).
  have hn : (nat_of_wsize sz %/ ve + nat_of_wsize sz %% ve)%nat = size l.
  - by rewrite -hsz mulnK // modnMl addn0.
  rewrite /split_vec hn.
  apply: (@eq_from_nth (word ve) (wrepr ve 0%Z)); first by rewrite size_map size_iota.
  rewrite size_map size_iota => i hi.
  rewrite (nth_map 0%nat) ?size_iota // nth_iota // add0n.
  apply/eqP/mathcomp.word.word.eq_from_wbit => j.
  rewrite mathcomp.word.word.subwordE mathcomp.word.word.wbit_t2wE (nth_mktuple _ _ j).
  have hlt : (j + i * ve < nat_of_wsize sz)%nat.
  - rewrite -hsz; apply: (@leq_trans (ve + i * ve)); first by rewrite ltn_add2r ltn_ord.
    by rewrite -mulSn leq_mul2r hi orbT.
  rewrite /make_vec /wrepr.
  rewrite -[(j + i * ve)%nat]/(nat_of_ord (Ordinal hlt)) mathcomp.word.word.wbit_mkword /=.
  rewrite -[mathcomp.word.word.wcat_r l]/(mathcomp.word.word.urepr (mathcomp.word.word.wcat (in_tuple l))).
  rewrite mathcomp.word.word.wcat_wbitE.
  rewrite addnC divnMDl // modnMDl divn_small // modn_small // addn0.
  by congr (mathcomp.word.word.wbit (mathcomp.word.word.toword _) _); apply: set_nth_default.
Qed.
Opaque word.

(* SHAchoose ([J1.4.3.51 SHAchoose]) is [ch]. *)
Lemma sha_chooseE (x y z : u32) : wxor (wand (wxor y z) x) z = ch x y z.
Proof.
  apply/eqP/eq_from_wbit_n => i.
  rewrite /ch !(wxorE, wandE) wN1E ltn_ord.
  by case: (wbit_n x i); case: (wbit_n y i); case: (wbit_n z i).
Qed.

(* SHAmajority ([J1.4.3.52 SHAmajority]) is the Maj of FIPS 180-4 at every
   size: [maj] of sha256.v at 32 bits, [Maj64] below at 64 bits. *)
Lemma sha_majorityE ws (x y z : word ws) :
  sha_majority x y z = wxor (wand x y) (wxor (wand x z) (wand y z)).
Proof.
  apply/eqP/eq_from_wbit_n => i.
  rewrite /sha_majority !(wxorE, wandE, worE).
  by case: (wbit_n x i); case: (wbit_n y i); case: (wbit_n z i).
Qed.

(* FIPS 180-4, 6.2.2 step 3: one SHA-256 round on the working variables
   (a, b, c, d, e, f, g, h), with [wk] = K_t + W_t. *)
Definition sha256_round (s : u32 * u32 * u32 * u32 * u32 * u32 * u32 * u32) (wk : u32) :=
  let '(a, b, c, d, e, f, g, h) := s in
  let t1 := (h + Σ₁ e + ch e f g + wk)%R in
  let t2 := (Σ₀ a + maj a b c)%R in
  ((t1 + t2)%R, a, b, c, (d + t1)%R, e, f, g).

Definition abcd_efgh (s : u32 * u32 * u32 * u32 * u32 * u32 * u32 * u32) :=
  let '(a, b, c, d, e, f, g, h) := s in ((a, b, c, d), (e, f, g, h)).

Lemma sha256hash_stepE s wk :
  sha256hash_step (abcd_efgh s) wk = abcd_efgh (sha256_round s wk).
Proof.
  case: s => [[[[[[[a b] c] d] e] f] g] h] /=.
  by rewrite (GRing.addrC d) !GRing.addrA.
Qed.

Lemma sha256hash_foldE s l :
  foldl sha256hash_step (abcd_efgh s) l = abcd_efgh (foldl sha256_round s l).
Proof.
  by elim: l s => [// | wk l ih] s /=; rewrite sha256hash_stepE ih.
Qed.

Definition sha256_state (abcd efgh : u128) :=
  let '(a, b, c, d) := elems4_of abcd in
  let '(e, f, g, h) := elems4_of efgh in
  (a, b, c, d, e, f, g, h).

Lemma abcd_efgh_state abcd efgh :
  abcd_efgh (sha256_state abcd efgh) = (elems4_of abcd, elems4_of efgh).
Proof. by rewrite /sha256_state; case: elems4_of => [[[? ?] ?] ?]; case: elems4_of => [[[? ?] ?] ?]. Qed.

(* SHA256H and SHA256H2 perform the four FIPS 180-4 rounds whose K_t + W_t
   are the elements of [wk], element 0 first: SHA256H returns the new
   (a, b, c, d) and SHA256H2 the new (e, f, g, h), element 0 first. *)
Lemma sha256hash_rounds abcd efgh wk :
  let s := foldl sha256_round (sha256_state abcd efgh) (split_vec U32 wk) in
  let '(a, b, c, d, e, f, g, h) := s in
  sha256hash abcd efgh wk true = make_vec U128 [:: a; b; c; d ]
  /\ sha256hash abcd efgh wk false = make_vec U128 [:: e; f; g; h ].
Proof.
  rewrite /sha256hash -abcd_efgh_state sha256hash_foldE.
  by case: foldl => [[[[[[[a b] c] d] e] f] g] h].
Qed.


(* -------------------------------------------------------------------- *)
(* Elements of a packed vector. *)

Lemma velem_at_make_vec (ve : wsize) (l : seq (word ve)) i :
  (size l * ve)%nat = U128 -> velem_at ve (make_vec U128 l) i = nth (wrepr ve 0) l i.
Proof. by move=> h; rewrite /velem_at split_vec_make_vec. Qed.

Lemma lift2_vec_make_vec (ve : wsize) op (l1 l2 : seq (word ve)) :
  (size l1 * ve)%nat = U128 -> (size l2 * ve)%nat = U128 ->
  lift2_vec ve op U128 (make_vec U128 l1) (make_vec U128 l2) = make_vec U128 (map2 op l1 l2).
Proof. by move=> h1 h2; rewrite /lift2_vec !split_vec_make_vec. Qed.

Lemma elems4_of_make_vec (a b c d : u32) :
  elems4_of (make_vec U128 [:: a; b; c; d ]) = (a, b, c, d).
Proof. by rewrite /elems4_of !velem_at_make_vec. Qed.

Lemma split_vec_make_vec4 (a b c d : u32) :
  split_vec U32 (make_vec U128 [:: a; b; c; d ]) = [:: a; b; c; d ].
Proof. exact: split_vec_make_vec. Qed.

(* SHA256H and SHA256H2 on packed working variables: [abcd] holds (a, b, c,
   d) and [efgh] holds (e, f, g, h), element 0 first, and [wk] holds K_t +
   W_t for four consecutive rounds. *)
Lemma SHA256H_rounds (a b c d e f g h k0 k1 k2 k3 : u32) :
  let '(a', b', c', d', e', f', g', h') :=
    foldl sha256_round (a, b, c, d, e, f, g, h) [:: k0; k1; k2; k3 ] in
  let abcd := make_vec U128 [:: a; b; c; d ] in
  let efgh := make_vec U128 [:: e; f; g; h ] in
  let wk := make_vec U128 [:: k0; k1; k2; k3 ] in
  sha256hash abcd efgh wk true = make_vec U128 [:: a'; b'; c'; d' ]
  /\ sha256hash abcd efgh wk false = make_vec U128 [:: e'; f'; g'; h' ].
Proof.
  have := sha256hash_rounds (make_vec U128 [:: a; b; c; d ])
            (make_vec U128 [:: e; f; g; h ]) (make_vec U128 [:: k0; k1; k2; k3 ]).
  rewrite /sha256_state !elems4_of_make_vec split_vec_make_vec4.
  by case: (foldl _ _ _) => [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
Qed.

(* SHA256SU0 then SHA256SU1 compute the next four message-schedule words of
   FIPS 180-4, 6.2.2 step 1:
     W_t = σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}. *)
Lemma SHA256SU_schedule (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : u32) :
  let w16 := (σ₁ w14 + w9 + σ₀ w1 + w0)%R in
  let w17 := (σ₁ w15 + w10 + σ₀ w2 + w1)%R in
  let w18 := (σ₁ w16 + w11 + σ₀ w3 + w2)%R in
  let w19 := (σ₁ w17 + w12 + σ₀ w4 + w3)%R in
  sha256su1
    (sha256su0 (make_vec U128 [:: w0; w1; w2; w3 ]) (make_vec U128 [:: w4; w5; w6; w7 ]))
    (make_vec U128 [:: w8; w9; w10; w11 ])
    (make_vec U128 [:: w12; w13; w14; w15 ])
  = make_vec U128 [:: w16; w17; w18; w19 ].
Proof.
  rewrite /sha256su1 /sha256su0 split_vec_make_vec4 /=.
  rewrite !velem_at_make_vec //=.
  have E (x y z u : u32) :
    add_word (add_word x (add_word y u)) z = add_word (add_word (add_word x z) y) u.
  - have : (x + (y + u) + z = x + z + y + u)%R.
    + by rewrite GRing.addrA (GRing.addrAC (x + y)%R) (GRing.addrAC x).
    exact.
  by rewrite !E.
Qed.

(* -------------------------------------------------------------------- *)
(* SHA-512: FIPS 180-4, 4.1.3 and 6.4.2. *)

Definition Ch64 (x y z : u64) : u64 := wxor (wand x y) (wand (wnot x) z).
Definition Maj64 (x y z : u64) : u64 := wxor (wand x y) (wxor (wand x z) (wand y z)).
Definition Sigma0_512 (x : u64) : u64 := wxor (wror x 28) (wxor (wror x 34) (wror x 39)).
Definition Sigma1_512 (x : u64) : u64 := wxor (wror x 14) (wxor (wror x 18) (wror x 41)).
Definition sigma0_512 (x : u64) : u64 := wxor (wror x 1) (wxor (wror x 8) (wshr x 7)).
Definition sigma1_512 (x : u64) : u64 := wxor (wror x 19) (wxor (wror x 61) (wshr x 6)).

Lemma sha_majority64E (a b c : u64) : sha_majority a b c = Maj64 a b c.
Proof. exact: sha_majorityE. Qed.

Lemma sha512_Sigma0E x : sha512_Sigma0 x = Sigma0_512 x.
Proof. by rewrite /sha512_Sigma0 /Sigma0_512 wxorA. Qed.

Lemma sha512_Sigma1E x : sha512_Sigma1 x = Sigma1_512 x.
Proof. by rewrite /sha512_Sigma1 /Sigma1_512 wxorA. Qed.

Lemma sha512_sigma0E x : sha512_sigma0 x = sigma0_512 x.
Proof. by rewrite /sha512_sigma0 /sigma0_512 wxorA. Qed.

Lemma sha512_sigma1E x : sha512_sigma1 x = sigma1_512 x.
Proof. by rewrite /sha512_sigma1 /sigma1_512 wxorA. Qed.

Definition sha512_round (s : u64 * u64 * u64 * u64 * u64 * u64 * u64 * u64) (kw : u64) :=
  let '(a, b, c, d, e, f, g, h) := s in
  let t1 := (h + Sigma1_512 e + Ch64 e f g + kw)%R in
  let t2 := (Sigma0_512 a + Maj64 a b c)%R in
  ((t1 + t2)%R, a, b, c, (d + t1)%R, e, f, g).

(* SHA512SU0 then SHA512SU1 compute the next two message-schedule words of
   FIPS 180-4, 6.4.2 step 1:
     W_t = σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}. *)
Lemma SHA512SU_schedule (w0 w1 w2 w3 w9 w10 w14 w15 : u64) :
  sha512su1
    (sha512su0 (make_vec U128 [:: w0; w1 ]) (make_vec U128 [:: w2; w3 ]))
    (make_vec U128 [:: w14; w15 ])
    (make_vec U128 [:: w9; w10 ])
  = make_vec U128
      [:: (sigma1_512 w14 + w9 + sigma0_512 w1 + w0)%R;
          (sigma1_512 w15 + w10 + sigma0_512 w2 + w1)%R ].
Proof.
  rewrite /sha512su1 /sha512su0 !velem_at_make_vec //=.
  rewrite !sha512_sigma0E !sha512_sigma1E.
  have E (x y z u : u64) :
    add_word (add_word (add_word u y) x) z = add_word (add_word (add_word x z) y) u.
  - have : (u + y + x + z = x + z + y + u)%R.
    + by rewrite (GRing.addrC u y) (GRing.addrAC y u x) (GRing.addrAC (y + x)%R u z)
                 (GRing.addrC y x) (GRing.addrAC x y z).
    exact.
  by rewrite (E (sigma1_512 w14)) (E (sigma1_512 w15)).
Qed.

Lemma Maj64_perm (a b c : u64) : Maj64 c b a = Maj64 a b c.
Proof.
  rewrite /Maj64 (wandC c b) (wandC c a) (wandC b a).
  by rewrite wxorC (wxorC (wand a c)) -wxorA.
Qed.

Lemma Ch64E (e f g : u64) : wxor (wand e f) (wand (wnot e) g) = Ch64 e f g.
Proof. by []. Qed.

(* Two SHA-512 rounds with SHA512H, SHA512H2 and an element-wise addition.
   [x; y] is the vector [make_vec U128 [:: x; y]]: x in element 0 (the low
   64 bits), y in element 1. The state pairs are packed in order, (a, b) as
   [a; b], and so on. With k0 = K_t + W_t and k1 = K_{t+1} + W_{t+1}:
     hw = SHA512H([g + k1; h + k0], [f; g], [d; e])
   SHA512H2(hw, [c; _], [a; b]) is [a; b] after the two rounds, and
   [c; d] + hw is [e; f] after them. The operands [f; g] and [d; e] are
   EXT #8 of adjacent state registers, and [g + k1; h + k0] is [g; h] plus
   the W+K pair with its elements swapped. *)
Lemma SHA512H_H2_rounds (a b c d e f g h k0 k1 x : u64) :
  let '(a2, b2, c2, d2, e2, f2, g2, h2) :=
    sha512_round (sha512_round (a, b, c, d, e, f, g, h) k0) k1 in
  let hw := sha512h (make_vec U128 [:: (g + k1)%R; (h + k0)%R ])
                    (make_vec U128 [:: f; g ]) (make_vec U128 [:: d; e ]) in
  sha512h2 hw (make_vec U128 [:: c; x ]) (make_vec U128 [:: a; b ])
    = make_vec U128 [:: a2; b2 ]
  /\ lift2_vec U64 +%R U128 (make_vec U128 [:: c; d ]) hw
    = make_vec U128 [:: e2; f2 ].
Proof.
  rewrite /= /sha512h /sha512h2 !velem_at_make_vec //=.
  rewrite !sha512_Sigma1E !sha512_Sigma0E !sha_majority64E !Ch64E (Maj64_perm a b c).
  rewrite !add_wordE.
  set T1 := (h + Sigma1_512 e + Ch64 e f g + k0)%R.
  have -> : (Ch64 e f g + Sigma1_512 e + (h + k0) = T1)%R.
  - by rewrite GRing.addrA (GRing.addrC (_ + _)%R h) (GRing.addrC (Ch64 _ _ _)) GRing.addrA.
  set a1 := (T1 + (Sigma0_512 a + Maj64 a b c))%R.
  have -> : (Maj64 a b c + Sigma0_512 a + T1 = a1)%R.
  - by rewrite GRing.addrC (GRing.addrC (Maj64 _ _ _)).
  rewrite (GRing.addrC T1 d).
  set e1 := (d + T1)%R.
  set T1' := (g + Sigma1_512 e1 + Ch64 e1 e f + k1)%R.
  have -> : (Ch64 e1 e f + Sigma1_512 e1 + (g + k1) = T1')%R.
  - by rewrite GRing.addrA (GRing.addrC (_ + _)%R g) (GRing.addrC (Ch64 _ _ _)) GRing.addrA.
  have -> : (Maj64 a1 a b + Sigma0_512 a1 + T1' = T1' + (Sigma0_512 a1 + Maj64 a1 a b))%R.
  - by rewrite GRing.addrC (GRing.addrC (Maj64 _ _ _)).
  split; first by [].
  by rewrite lift2_vec_make_vec.
Qed.

(* -------------------------------------------------------------------- *)
(* The same statements about the instruction descriptions, whose [id_semi]
   is the semantics of the instructions in the compiler: they fix which
   operand of each instruction holds which part of the state. *)

Section INSTR.
Context (opts : armv8a_options).

Lemma SHA256H_H2_instr_rounds (a b c d e f g h k0 k1 k2 k3 : u32) :
  let '(a', b', c', d', e', f', g', h') :=
    foldl sha256_round (a, b, c, d, e, f, g, h) [:: k0; k1; k2; k3 ] in
  let abcd := make_vec U128 [:: a; b; c; d ] in
  let efgh := make_vec U128 [:: e; f; g; h ] in
  let wk := make_vec U128 [:: k0; k1; k2; k3 ] in
  id_semi (armv8a_SHA256H_instr opts) abcd efgh wk = ok (make_vec U128 [:: a'; b'; c'; d' ])
  /\ id_semi (armv8a_SHA256H2_instr opts) efgh abcd wk = ok (make_vec U128 [:: e'; f'; g'; h' ]).
Proof.
  move: (SHA256H_rounds a b c d e f g h k0 k1 k2 k3).
  case: (foldl sha256_round (a, b, c, d, e, f, g, h) [:: k0; k1; k2; k3 ])
    => [[[[[[[a' b'] c'] d'] e'] f'] g'] h'] [h1 h2].
  by split => /=; rewrite /id_semi /= /armv8a_SHA256H_semi /armv8a_SHA256H2_semi ?h1 ?h2.
Qed.

Lemma SHA256SU_instr_schedule
  (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : u32) :
  let w16 := (σ₁ w14 + w9 + σ₀ w1 + w0)%R in
  let w17 := (σ₁ w15 + w10 + σ₀ w2 + w1)%R in
  let w18 := (σ₁ w16 + w11 + σ₀ w3 + w2)%R in
  let w19 := (σ₁ w17 + w12 + σ₀ w4 + w3)%R in
  Let x := id_semi (armv8a_SHA256SU0_instr opts)
             (make_vec U128 [:: w0; w1; w2; w3 ]) (make_vec U128 [:: w4; w5; w6; w7 ]) in
  id_semi (armv8a_SHA256SU1_instr opts) x
    (make_vec U128 [:: w8; w9; w10; w11 ]) (make_vec U128 [:: w12; w13; w14; w15 ])
  = ok (make_vec U128 [:: w16; w17; w18; w19 ]).
Proof.
  rewrite /id_semi /= /armv8a_SHA256SU1_semi /armv8a_SHA256SU0_semi.
  by rewrite (SHA256SU_schedule w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15).
Qed.

(* The element-wise addition is VADD at 64-bit elements. *)
Lemma SHA512H_H2_instr_rounds (a b c d e f g h k0 k1 x : u64) :
  opts_size opts = U64 ->
  let '(a2, b2, c2, d2, e2, f2, g2, h2) :=
    sha512_round (sha512_round (a, b, c, d, e, f, g, h) k0) k1 in
  Let hw := id_semi (armv8a_SHA512H_instr opts)
              (make_vec U128 [:: (g + k1)%R; (h + k0)%R ])
              (make_vec U128 [:: f; g ]) (make_vec U128 [:: d; e ]) in
  Let ab := id_semi (armv8a_SHA512H2_instr opts) hw
              (make_vec U128 [:: c; x ]) (make_vec U128 [:: a; b ]) in
  Let ef := id_semi (armv8a_VADD_instr opts) (make_vec U128 [:: c; d ]) hw in
  ok (ab, ef) = ok (make_vec U128 [:: a2; b2 ], make_vec U128 [:: e2; f2 ]).
Proof.
  move=> hsz.
  move: (SHA512H_H2_rounds a b c d e f g h k0 k1 x).
  case: (sha512_round (sha512_round (a, b, c, d, e, f, g, h) k0) k1)
    => [[[[[[[a2 b2] c2] d2] e2] f2] g2] h2] /= [hab hef].
  by rewrite /id_semi /= /armv8a_SHA512H_semi /armv8a_SHA512H2_semi /armv8a_VADD_semi hsz hab hef.
Qed.

Lemma SHA512SU_instr_schedule (w0 w1 w2 w3 w9 w10 w14 w15 : u64) :
  Let x := id_semi (armv8a_SHA512SU0_instr opts)
             (make_vec U128 [:: w0; w1 ]) (make_vec U128 [:: w2; w3 ]) in
  id_semi (armv8a_SHA512SU1_instr opts) x
    (make_vec U128 [:: w14; w15 ]) (make_vec U128 [:: w9; w10 ])
  = ok (make_vec U128
          [:: (sigma1_512 w14 + w9 + sigma0_512 w1 + w0)%R;
              (sigma1_512 w15 + w10 + sigma0_512 w2 + w1)%R ]).
Proof.
  rewrite /id_semi /= /armv8a_SHA512SU1_semi /armv8a_SHA512SU0_semi.
  by rewrite SHA512SU_schedule.
Qed.

End INSTR.

(* -------------------------------------------------------------------- *)
(* SHA-3: the Keccak-f[1600] steps of FIPS 202, 3.2, with each 64-bit word
   A[x, y] of the state in a 64-bit element, so that a register holds the
   same word of two states. With C[x] the column parities of θ:
     θ:   D[x] = C[x - 1] XOR ROT(C[x + 1], 1)   = RAX1(C[x - 1], C[x + 1])
     θ+ρ: ROT(A[x, y] XOR D[x], r)              = XAR(A[x, y], D[x], 64 - r)
     χ:   A[x] XOR (NOT A[x + 1] AND A[x + 2])  = BCAX(A[x], A[x + 2], A[x + 1])
   and the parities are folded with EOR3. The rotation of ρ is a left
   rotation by r; XAR rotates right, by 64 - r, or by 0 when r = 0 (the
   immediate is in [0, 63]). This correspondence is informal: only the
   rotation identity below is proved here. *)

Lemma xar_rolE (n m : u128) (r : Z) :
  xar n m (64 - r) = lift1_vec U64 (fun x => wrol x r) U128 (wxor n m).
Proof.
  rewrite /xar /lift1_vec /lift1_vec'; congr make_vec.
  by apply: eq_map => x; exact: (wror_opp x r).
Qed.
