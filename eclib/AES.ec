require import List JArray JWord.

(* --------------------------------------------------------------- *)
(* Operation on bytes                                              *)
op Sbox : W8.t -> W8.t.
op InvSbox : W8.t -> W8.t.

axiom InvSboxK w : InvSbox (Sbox w) = w.

(* --------------------------------------------------------------- *)
(* Operations on word                                              *)
op SubWord (w : W32.t) = map Sbox w. 
op InvSubWord (w : W32.t) = map InvSbox w. 

lemma InvSubWordK w : InvSubWord (SubWord w) = w.
proof. 
  rewrite /SubWord /InvSubWord; apply W4u8.wordP => i hi.
  by rewrite !W4u8.mapbE 1,2:// InvSboxK.
qed.

op RotWord (w:W32.t) = 
  W4u8.pack4 [w \bits8 1; w \bits8 2; w \bits8 3; w \bits8 0].

(* --------------------------------------------------------------- *)
(* Operations on state                                             *)

(* Column representation of matrix *)
(* s00, s01, s02, s03
   s10, s11, s12, s13
   s20, s21, s22, s23
   s30, s31, s32, s33 *)

op to_matrix (s:W128.t) = 
  let s_ = fun i j => (s \bits32 j) \bits8 i in
  (s_ 0 0, s_ 0 1, s_ 0 2, s_ 0 3,
   s_ 1 0, s_ 1 1, s_ 1 2, s_ 1 3,
   s_ 2 0, s_ 2 1, s_ 2 2, s_ 2 3,
   s_ 3 0, s_ 3 1, s_ 3 2, s_ 3 3).

op to_state m = 
  let (s00, s01, s02, s03,
       s10, s11, s12, s13,
       s20, s21, s22, s23,
       s30, s31, s32, s33) = m in
   let c0 = W4u8.pack4 [s00; s10; s20; s30] in
   let c1 = W4u8.pack4 [s01; s11; s21; s31] in
   let c2 = W4u8.pack4 [s02; s12; s22; s32] in
   let c3 = W4u8.pack4 [s03; s13; s23; s33] in
   W4u32.pack4 [c0; c1; c2; c3].
(*
lemma to_state_to_matrix m : 
  to_matrix (to_state m) = m.
proof. by case m => *; rewrite /to_state /to_matrix /=. qed.
*)

(* SubBytes *)

op SubBytes (s : W128.t) = map SubWord s. 

op InvSubBytes (s : W128.t) = map InvSubWord s.

lemma InvSubBytesK w : InvSubBytes (SubBytes w) = w.
proof. 
  rewrite /SubBytes /InvSubBytes; apply W4u32.wordP => i hi.
  by rewrite !W4u32.mapbE 1,2:// InvSubWordK.
qed.

(* AddRoundKey *)

op AddRoundKey (w1 w2 : W128.t) = w1 `^` w2.

(* ShiftRows *)

op ShiftRows (s : W128.t) = 
 let (s00, s01, s02, s03,
      s10, s11, s12, s13,
      s20, s21, s22, s23,
      s30, s31, s32, s33) = to_matrix s in
  to_state (s00, s01, s02, s03,
            s11, s12, s13, s10,
            s22, s23, s20, s21,
            s33, s30, s31, s32)
axiomatized by ShiftRowsE.

op InvShiftRows (s : W128.t) = 
 let (s00, s01, s02, s03,
      s11, s12, s13, s10,
      s22, s23, s20, s21,
      s33, s30, s31, s32) = to_matrix s in
  to_state 
     (s00, s01, s02, s03,
      s10, s11, s12, s13,           
      s20, s21, s22, s23,           
      s30, s31, s32, s33)
axiomatized by InvShiftRowsE.
           
lemma InvShiftRowsK s  : InvShiftRows (ShiftRows s) = s.
proof.
  by apply W16u8.allP; rewrite ShiftRowsE InvShiftRowsE /to_matrix /to_state /=.
qed.

(* MixColumns *)

op MixColumns : W128.t -> W128.t. 

op InvMixColumns : W128.t -> W128.t. 

axiom InvMixColumnsK s : InvMixColumns (MixColumns s) = s.
axiom InvMixColumnsD (s1 s2:W128.t) : InvMixColumns (s1 `^` s2) = InvMixColumns s1 `^` InvMixColumns s2.

(* --------------------------------------------------------------- *)
(* Semantic of x86 AES Instructions                                *)

op AESDEC (state rkey: W128.t) = 
  let state = InvShiftRows state in
  let state = InvSubBytes state in
  let state = InvMixColumns state in
  AddRoundKey state rkey
axiomatized by AESDECE.

op AESDECLAST (state rkey: W128.t) = 
  let state = InvShiftRows state in
  let state = InvSubBytes state in
  AddRoundKey state rkey
axiomatized by AESDECLASTE.

op AESENC (state rkey: W128.t) = 
  let state = ShiftRows state in
  let state = SubBytes state in
  let state = MixColumns state in
  AddRoundKey state rkey
axiomatized by AESENCE.

op AESENCLAST (state rkey: W128.t) = 
  let state = ShiftRows state in
  let state = SubBytes state in
  AddRoundKey state rkey
axiomatized by AESENCLASTE.

abbrev [-printing] AESIMC = InvMixColumns.

op AESKEYGENASSIST (state: W128.t) (rcon:W8.t) = 
  let rcon = W4u8.pack4 [rcon; W8.zero; W8.zero; W8.zero] in
  let x1 = state \bits32 1 in 
  let x3 = state \bits32 3 in 
  let y0 = SubWord x1 in
  let y1 = RotWord (SubWord x1) `^` rcon in
  let y2 = SubWord x3 in 
  let y3 = RotWord (SubWord x3) `^` rcon in
  W4u32.pack4 [y0; y1; y2; y3]
axiomatized by AESKEYGENASSISTE.

(* --------------------------------------------------------------------- *)
(* x86 AES instructions slittly differs form AES specification           *) 
(* - x86 AESENC/AESENCLAST swap the SubBytes annd ShiftRows operations   *)   
(* - x86 AESDEC instruction assumes that InvMixColumns has been applied  *)
(*   to rkeys, we do not assume it here and use the normal specification *)
(* So we redefine it to have the standard specification                  *)

op AESENC_ (state rkey: W128.t) =
  let state = SubBytes state in 
  let state = ShiftRows state in
  let state = MixColumns state in
  AddRoundKey state rkey
axiomatized by AESENC_E.

op AESENCLAST_  (state rkey: W128.t) =
  let state = SubBytes state in 
  let state = ShiftRows state in
  AddRoundKey state rkey
axiomatized by AESENCLAST_E.
  
op AESDEC_ (state rkey: W128.t) = 
  let state = InvShiftRows state in
  let state = InvSubBytes state in
  let state = AddRoundKey state rkey in
  InvMixColumns state
axiomatized by AESDEC_E.

lemma ShiftRows_SubBytes s : ShiftRows (SubBytes s) = SubBytes (ShiftRows s).
proof. by rewrite !ShiftRowsE; cbv delta. qed.

lemma AESENC_AESENC_ s k : AESENC s k = AESENC_ s k.
proof.
  by rewrite AESENCE AESENC_E /= ShiftRows_SubBytes.
qed.

lemma AESENCLAST_AESENCLAST_ s k : AESENCLAST s k = AESENCLAST_ s k.
proof.
  by rewrite AESENCLASTE AESENCLAST_E /= ShiftRows_SubBytes.
qed.

lemma AESDEC_AESDEC_ s k : AESDEC s (InvMixColumns k) = AESDEC_ s k.
proof. by rewrite AESDECE AESDEC_E /= InvMixColumnsD. qed.



