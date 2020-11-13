require import List JArray JWord.

op Sbox : W8.t -> W8.t.
op InvSbox : W8.t -> W8.t.

op SubWord (w : W32.t) = map Sbox w. 

op RotWord (w:W32.t) = 
  W4u8.pack4 [w \bits8 1; w \bits8 2; w \bits8 3; w \bits8 0].

op SubBytes (w : W128.t) = map Sbox w. 

op InvSubBytes (w : W128.t) = map SubWord w. 

op AddRoundKey (w1 w2 : W128.t) = w1 `^` w2.

op ShiftRows : W128.t -> W128.t.
op InvShiftRows : W128.t -> W128.t.

op MixColumns : W128.t -> W128.t. 
op InvMixColumns : W128.t -> W128.t. 

op AESDEC (state rkey: W128.t) = 
  let state = InvShiftRows state in
  let state = InvSubBytes state in
  let state = InvMixColumns state in
  AddRoundKey state rkey.

op AESDECLAST (state rkey: W128.t) = 
  let state = InvShiftRows state in
  let state = InvSubBytes state in
  AddRoundKey state rkey.

op AESENC (state rkey: W128.t) = 
  let state = ShiftRows state in
  let state = SubBytes state in
  let state = MixColumns state in
  AddRoundKey state rkey.

op AESENCLAST (state rkey: W128.t) = 
  let state = ShiftRows state in
  let state = SubBytes state in
  AddRoundKey state rkey.

abbrev [-printing] AESIMC = InvMixColumns.

op AESKEYGENASSIST (state: W128.t) (rcon:W8.t) = 
  let rcon = W4u8.pack4 [rcon; W8.zero; W8.zero; W8.zero] in
(*  let x0 = state \bits32 0 in  *)
  let x1 = state \bits32 1 in 
(*  let x2 = state \bits32 2 in *)
  let x3 = state \bits32 3 in 
  let y0 = SubWord x1 in
  let y1 = RotWord (SubWord x1) `^` rcon in
  let y2 = SubWord x3 in 
  let y3 = RotWord (SubWord x3) `^` rcon in
  W4u32.pack4 [y0; y1; y2; y3].



