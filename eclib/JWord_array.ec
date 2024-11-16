(* -------------------------------------------------------------------- *)
require import AllCore Distr DList BitEncoding IntDiv SmtMap List StdOrder BitEncoding Bool.
(*---*) import Ring.IntID IntOrder BS2Int.
require import JUtils JArray JWord.

abstract theory WArray.

  clone include MonoArray with
    type elem <- W8.t,
    op dfl    <- W8.zero.

  op darray = dmap (dlist W8.dword size) of_list.

  op get8 (t:t) (i:int)  : W8.t = t.[i].
  abbrev [-printing] get8_direct = get8.

  op get16_direct (t:t) (i:int) : W16.t =
    pack2_t (W2u8.Pack.init (fun j => t.[i + j]))
  axiomatized by get16E.

  abbrev get16 (t:t) (i:int) : W16.t = get16_direct t (2 * i).

  op get32_direct (t:t) (i:int) : W32.t =
    pack4_t (W4u8.Pack.init (fun j => t.[i + j]))
  axiomatized by get32E.

  abbrev get32 (t:t) (i:int) : W32.t = get32_direct t (4 * i).

  op get64_direct (t:t) (i:int) : W64.t =
    pack8_t (W8u8.Pack.init (fun j => t.[i + j]))
  axiomatized by get64E.

  abbrev get64 (t:t) (i:int) : W64.t = get64_direct t (8 * i).

  op get128_direct (t:t) (i:int) : W128.t =
    pack16_t (W16u8.Pack.init (fun j => t.[i + j]))
  axiomatized by get128E.

  abbrev get128 (t:t) (i:int) : W128.t = get128_direct t (16 * i).

  op get256_direct (t:t) (i:int) : W256.t =
    pack32_t (W32u8.Pack.init (fun j => t.[i + j]))
  axiomatized by get256E.

  abbrev get256 (t:t) (i:int) : W256.t = get256_direct t (32 * i).

  op set8 (t:t) (i:int) (w:W8.t) : t = t.[i <- w].
  abbrev [-printing] set8_direct (t:t) (i:int) (w:W8.t) : t = t.[i <- w].

  op set16_direct (t:t) (i:int) (w:W16.t) =
    init (fun k => if i <= k < i+2 then w \bits8 (k - i) else t.[k])
  axiomatized by set16E.

  abbrev set16 (t:t) (i:int) (w:W16.t) = set16_direct t (2*i) w.

  op set32_direct (t:t) (i:int) (w:W32.t) =
    init (fun k => if i <= k < i+4 then w \bits8 (k - i) else t.[k])
  axiomatized by set32E.

  abbrev set32 (t:t) (i:int) (w:W32.t) = set32_direct t (4 * i) w.

  op set64_direct (t:t) (i:int) (w:W64.t) =
    init (fun k => if i <= k < i+8 then w \bits8 (k - i) else t.[k])
  axiomatized by set64E.

  abbrev set64 (t:t) (i:int) (w:W64.t) = set64_direct t (8 * i) w.

  op set128_direct (t:t) (i:int) (w:W128.t) =
    init (fun k => if i <= k < i+16 then w \bits8 (k - i) else t.[k])
  axiomatized by set128E.

  abbrev set128 (t:t) (i:int) (w:W128.t) = set128_direct t (16 * i) w.

  op set256_direct (t:t) (i:int) (w:W256.t) =
    init (fun k => if i <= k < i+32 then w \bits8 (k - i) else t.[k])
  axiomatized by set256E.

  abbrev set256 (t:t) (i:int) (w:W256.t) = set256_direct t (32 * i) w.

  (* ----------------------------------------------------- *)

  lemma get_set8E t x y w:
    0 <= x < size =>
    get8 (set8 t x w) y = if y = x then w else get8 t y.
  proof. apply get_setE. qed.

  lemma get8_set16_directE t x y w :
    0 <= x => x + 2 <= WArray.size =>
    get8 (set16_direct t x w) y = if x <= y < x+2 then w \bits8 (y - x) else get8 t y.
  proof.
    move=> hx hs; rewrite set16E /get8.
    case: (x <= y < x + 2) => hy.
    + by rewrite initiE 1:/# /= hy.
    case: (0 <= y < WArray.size) => hy1; last by rewrite !get_out.
    rewrite initiE //= /#.
  qed.

  lemma get8_set16E t x y w :
    0 <= x => 2*(x + 1) <= WArray.size =>
    get8 (set16 t x w) y = if 2*x <= y < 2*(x+1) then w \bits8 (y - 2*x) else get8 t y.
  proof. smt(get8_set16_directE). qed.

  lemma get_set16E t x y w:
    0 <= x => 2*(x + 1) <= WArray.size =>
    get16 (set16 t x w) y = if y = x then w else get16 t y.
  proof.
    move=> hx hs; rewrite set16E !get16E.
    case: (y = x) => [-> | hne].
    + rewrite -(W2u8.unpack8K w);congr.
      apply W2u8.Pack.ext_eq => k hk; rewrite W2u8.get_unpack8 1:// W2u8.Pack.initiE //= initiE //= /#.
    congr; apply W2u8.Pack.init_ext => k hk /=; rewrite initE.
    by case: (0 <= 2 * y + k < WArray.size) => [ /# | /get_out ->].
  qed.

  lemma get8_set32_directE t x y w :
    0 <= x => x + 4 <= WArray.size =>
    get8 (set32_direct t x w) y = if x <= y < x+4 then w \bits8 (y - x) else get8 t y.
  proof.
    move=> hx hs; rewrite set32E /get8.
    case: (x <= y < x + 4) => hy.
    + by rewrite initiE 1:/# /= hy.
    case: (0 <= y < WArray.size) => hy1; last by rewrite !get_out.
    rewrite initiE //= /#.
  qed.

  lemma get8_set32E t x y w :
    0 <= x => 4*(x + 1) <= WArray.size =>
    get8 (set32 t x w) y = if 4*x <= y < 4*(x+1) then w \bits8 (y - 4*x) else get8 t y.
  proof. smt(get8_set32_directE). qed.

  lemma get_set32E t x y w:
    0 <= x => 4*(x + 1) <= WArray.size =>
    get32 (set32 t x w) y = if y = x then w else get32 t y.
  proof.
    move=> hx hs; rewrite set32E !get32E.
    case: (y = x) => [-> | hne].
    + rewrite -(W4u8.unpack8K w);congr.
      apply W4u8.Pack.ext_eq => k hk; rewrite W4u8.get_unpack8 //= W4u8.Pack.initiE //= initiE /#.
    congr; apply W4u8.Pack.init_ext => k hk /=; rewrite initE.
    by case: (0 <= 4 * y + k < WArray.size) => [ /# | /get_out ->].
  qed.

  lemma get8_set64_directE t x y w :
    0 <= x => x + 8 <= WArray.size =>
    get8 (set64_direct t x w) y = if x <= y < x+8 then w \bits8 (y - x) else get8 t y.
  proof.
    move=> hx hs; rewrite set64E /get8.
    case: (x <= y < x + 8) => hy.
    + by rewrite initiE 1:/# /= hy.
    case: (0 <= y < WArray.size) => hy1; last by rewrite !get_out.
    rewrite initiE //= /#.
  qed.

  lemma get8_set64E t x y w :
    0 <= x => 8*(x + 1) <= WArray.size =>
    get8 (set64 t x w) y = if 8*x <= y < 8*(x+1) then w \bits8 (y - 8*x) else get8 t y.
  proof. smt (get8_set64_directE). qed.

  lemma get_set64E t x y w:
    0 <= x => 8*(x + 1) <= WArray.size =>
    get64 (set64 t x w) y = if y = x then w else get64 t y.
  proof.
    move=> hx hs; rewrite set64E !get64E.
    case: (y = x) => [-> | hne].
    + rewrite -(W8u8.unpack8K w);congr.
      apply W8u8.Pack.ext_eq => k hk; rewrite W8u8.get_unpack8 //= W8u8.Pack.initiE //= initiE /#.
    congr; apply W8u8.Pack.init_ext => k hk /=; rewrite initE.
    by case: (0 <= 8 * y + k < WArray.size) => [ /# | /get_out ->].
  qed.

  lemma get8_set128_directE t x y w :
    0 <= x => x + 16 <= WArray.size =>
    get8 (set128_direct t x w) y = if x <= y < x+16 then w \bits8 (y - x) else get8 t y.
  proof.
    move=> hx hs; rewrite set128E /get8.
    case: (x <= y < x + 16) => hy.
    + by rewrite initiE 1:/# /= hy.
    case: (0 <= y < WArray.size) => hy1; last by rewrite !get_out.
    rewrite initiE //= /#.
  qed.

  lemma get8_set128E t x y w :
    0 <= x => 16*(x + 1) <= WArray.size =>
    get8 (set128 t x w) y = if 16*x <= y < 16*(x+1) then w \bits8 (y - 16*x) else get8 t y.
  proof. smt(get8_set128_directE). qed. 

  lemma get_set128E t x y w:
    0 <= x => 16*(x + 1) <= WArray.size =>
    get128 (set128 t x w) y = if y = x then w else get128 t y.
  proof.
    move=> hx hs; rewrite set128E !get128E.
    case: (y = x) => [-> | hne].
    + rewrite -(W16u8.unpack8K w);congr.
      apply W16u8.Pack.ext_eq => k hk; rewrite W16u8.get_unpack8 //= W16u8.Pack.initiE //= initiE /#.
    congr; apply W16u8.Pack.init_ext => k hk /=; rewrite initE.
    by case: (0 <= 16 * y + k < WArray.size) => [ /# | /get_out ->].
  qed.

  lemma get8_set256_directE t x y w :
    0 <= x => x + 32 <= WArray.size =>
    get8 (set256_direct t x w) y = if x <= y < x+32 then w \bits8 (y - x) else get8 t y.
  proof.
    move=> hx hs; rewrite set256E /get8.
    case: (x <= y < x + 32) => hy.
    + by rewrite initiE 1:/# /= hy.
    case: (0 <= y < WArray.size) => hy1; last by rewrite !get_out.
    rewrite initiE //= /#.
  qed.

  lemma get8_set256E t x y w :
    0 <= x => 32*(x + 1) <= WArray.size =>
    get8 (set256 t x w) y = if 32*x <= y < 32*(x+1) then w \bits8 (y - 32*x) else get8 t y.
  proof. smt(get8_set256_directE). qed. 

  lemma get_set256E t x y w:
    0 <= x => 32*(x + 1) <= WArray.size =>
    get256 (set256 t x w) y = if y = x then w else get256 t y.
  proof.
    move=> hx hs; rewrite set256E !get256E.
    case: (y = x) => [-> | hne].
    + rewrite -(W32u8.unpack8K w);congr.
      apply W32u8.Pack.ext_eq => k hk; rewrite W32u8.get_unpack8 //= W32u8.Pack.initiE //= initiE /#.
    congr; apply W32u8.Pack.init_ext => k hk /=; rewrite initE.
    by case: (0 <= 32 * y + k < WArray.size) => [ /# | /get_out ->].
  qed.

  hint simplify get_set8E, get8_set16E,  get8_set16_directE,  get_set16E,
                           get8_set32E,  get8_set32_directE,  get_set32E,
                           get8_set64E,  get8_set64_directE,  get_set64E,
                           get8_set128E, get8_set128_directE, get_set128E,
                           get8_set256E, get8_set256_directE, get_set256E.

  (* ------------------------------------------------- *)

  op init8 (f:int -> W8.t) =
    init f.

  op init16 (f:int -> W16.t) =
    init (fun i => f (i %/ 2) \bits8 (i%%2)).

  op init32 (f:int -> W32.t) =
    init (fun i => f (i %/ 4) \bits8 (i%%4)).

  op init64 (f:int -> W64.t) =
    init (fun i => f (i %/ 8) \bits8 (i%%8)).

  op init128 (f:int -> W128.t) =
    init (fun i => f (i %/ 16) \bits8 (i%%16)).

  op init256 (f:int -> W256.t) =
    init (fun i => f (i %/ 32) \bits8 (i%%32)).

  (* ------------------------------------------------- *)

  clone PolyArray as ArrayW8.

  op of_array8 (a: W8.t ArrayW8.t) = init8 (ArrayW8."_.[_]" a).

  op to_array8 (a:t) = ArrayW8.init (fun i => get8 a i).

  (*
op (a: ArrayN' Wws): WArrayN.initWS (fun i -> a.[i])
op (a: WArrayN'): ArrayN.init (fun i -> getWS a i)
    *)
end WArray.

(* Array of words, where the word size is any number of bytes. Viewed as array
of word or as byte array. *)
abstract theory ArrayWords.
  (* size of a word in bytes *)
  op sizeW: int.
  axiom gt0_sizeW: 0 < sizeW.

  (* size of the array in words *)
  op sizeA: int.
  axiom gt0_sizeA: 0 < sizeA.

  clone WT as Word with
    op size <- 8 * sizeW
    proof gt0_size by rewrite pmulr_rgt0 // gt0_sizeW.

  clone import PolyArray as ArrayN with
    op size <- sizeA
    proof ge0_size by rewrite ltzW gt0_sizeA.

  (* Equivalent array of bytes *)
  clone import WArray as WArrayN with
    op size <- sizeW * sizeA
    proof ge0_size by rewrite pmulr_rge0 1:gt0_sizeW ltzW gt0_sizeA.

  (* Conversion between WArrayN.t and Word.t ArrayN.t *)
  clone W_WS as Wu8 with
    op sizeS <= W8.size, op sizeB <= W8.size*sizeW, op r <= sizeW,
    theory WS <= W8, theory WB <= Word
    proof gt0_r by apply gt0_sizeW, sizeBrS by rewrite mulzC.

  (* direct means offset in bytes, not in words *)
  op wa_get_direct (t: WArrayN.t) (i: int): Word.t =
    Wu8.pack'R_t (Wu8.Pack.init (fun j => WArrayN."_.[_]" t (i+j))).
  abbrev wa_get (t: WArrayN.t) (i: int): Word.t = wa_get_direct t (sizeW*i).
  op wa_set_direct (t: WArrayN.t) (i: int) (w: Word.t) =
    WArrayN.init (fun k => if i <= k < i + sizeW then Wu8.\bits'S w (k-i) else t.[k]).

  op of_word_array (a: Word.t ArrayN.t) =
    WArrayN.init (fun i => Wu8.\bits'S a.[i %/ sizeW] (i%%sizeW)).
  op to_word_array (a: WArrayN.t) = ArrayN.init (fun i => wa_get a i).

  op get_direct (a: Word.t ArrayN.t) = wa_get_direct (of_word_array a).
  op set_direct (a: Word.t ArrayN.t) (i: int) (w: Word.t) =
    to_word_array (wa_set_direct (of_word_array a) i w).
end ArrayWords.

(* Sub-array (get, set) where the sub-array may have a different type than the
base array. Conversion views arrays of words as equivalent to byte arrays. *)
abstract theory SubArrayCast.
  op sizeWS: int.
  axiom gt0_sizeWS: 0 < sizeWS.

  op sizeWB: int.
  axiom gt0_sizeWB: 0 < sizeWB.

  op sizeS: int.
  axiom gt0_sizeS: 0 < sizeS.

  op sizeB: int.
  axiom gt0_sizeB: 0 < sizeB.

  clone WT as WordS with
    op size <- 8 * sizeWS
    proof gt0_size by rewrite pmulr_rgt0 1:// gt0_sizeWS.

  clone WT as WordB with
    op size <- 8 * sizeWB
    proof gt0_size by rewrite pmulr_rgt0 1:// gt0_sizeWB.

  clone ArrayWords as ArrayWordsS with
    op sizeW <- sizeWS, op sizeA <- sizeS, theory Word <- WordS
    proof gt0_sizeW by apply gt0_sizeWS, gt0_sizeA by apply gt0_sizeS.

  clone ArrayWords as ArrayWordsB with
    op sizeW <- sizeWB, op sizeA <- sizeB, theory Word <- WordB
    proof gt0_sizeW by apply gt0_sizeWB, gt0_sizeA by apply gt0_sizeB.

  op get_sub_direct (a: WordB.t ArrayWordsB.ArrayN.t) (i: int) =
    ArrayWordsS.to_word_array (
      ArrayWordsS.WArrayN.init (fun j =>
        ArrayWordsB.WArrayN."_.[_]" (ArrayWordsB.of_word_array a) (i + j)
      )
    ).

  op set_sub_direct (a: WordB.t ArrayWordsB.ArrayN.t) (i: int) (b: WordS.t ArrayWordsS.ArrayN.t) =
    ArrayWordsB.to_word_array (
      ArrayWordsB.WArrayN.init (fun j =>
        if i <= j < i + sizeWS * sizeS then
          ArrayWordsS.WArrayN."_.[_]" (ArrayWordsS.of_word_array b) (j - i)
        else
          ArrayWordsB.WArrayN."_.[_]" (ArrayWordsB.of_word_array a) j
        )
      ).

  op get_sub (a: WordB.t ArrayWordsB.ArrayN.t) (i: int) = get_sub_direct a (sizeWB*i).

  op set_sub (a: WordB.t ArrayWordsB.ArrayN.t) (i: int) (b: WordS.t ArrayWordsS.ArrayN.t) =
    set_sub_direct a (sizeWB*i) b.
end SubArrayCast.

(* Particular case of SubArrayCast where both array's word types are the same.
Still not a simple sub-array since indices may be a number of bytes
non-multiple of the word size. *)
abstract theory SubArrayDirect.
  op sizeW: int.
  axiom gt0_sizeW: 0 < sizeW.

  clone WT as Word with
    op size <- 8 * sizeW
    proof gt0_size by rewrite pmulr_rgt0 1:// gt0_sizeW.

  clone include SubArrayCast with
    op sizeWS <- sizeW, op sizeWB <- sizeW, theory WordS <- Word, theory WordB <- Word
    proof gt0_sizeWS by apply gt0_sizeW, gt0_sizeWB by apply gt0_sizeW.
end SubArrayDirect.

(* Access to array words (get, set) where the word may have a different type
than the base array. Conversion views arrays of words and words as equivalent
to byte arrays. *)
abstract theory ArrayAccessCast.
  op sizeWS: int.
  axiom gt0_sizeWS: 0 < sizeWS.

  op sizeWB: int.
  axiom gt0_sizeWB: 0 < sizeWB.

  op sizeB: int.
  axiom gt0_sizeB: 0 < sizeB.

  clone WT as WordS with
    op size <- 8 * sizeWS
    proof gt0_size by rewrite pmulr_rgt0 1:// gt0_sizeWS.

  clone WT as WordB with
    op size <- 8 * sizeWB
    proof gt0_size by rewrite pmulr_rgt0 1:// gt0_sizeWB.

  clone ArrayWords as ArrayWordsB with
    op sizeW <- sizeWB, op sizeA <- sizeB, theory Word <- WordB
    proof gt0_sizeW by apply gt0_sizeWB, gt0_sizeA by apply gt0_sizeB.

  clone W_WS as WSu8 with
    op sizeS <= W8.size, op sizeB <= W8.size*sizeWS, op r <= sizeWS,
    theory WS <= W8, theory WB <= WordS
    proof gt0_r by apply gt0_sizeWS, sizeBrS by rewrite mulzC.


  op get_cast_direct (a: WordB.t ArrayWordsB.ArrayN.t) (i: int) =
    WSu8.pack'R_t (
      WSu8.Pack.init (fun j => ArrayWordsB.WArrayN."_.[_]" (ArrayWordsB.of_word_array a) (i+j))
    ).

  op set_cast_direct (a: WordB.t ArrayWordsB.ArrayN.t) (i: int) (b: WordS.t) =
    ArrayWordsB.to_word_array (
      ArrayWordsB.WArrayN.init (fun j =>
        if i <= j < i + sizeWS then
          WSu8.\bits'S b (j - i)
        else
          ArrayWordsB.WArrayN."_.[_]" (ArrayWordsB.of_word_array a) j
        )
      ).

  op get_cast (a: WordB.t ArrayWordsB.ArrayN.t) (i: int) =
    get_cast_direct a (sizeWB*i).

  op set_cast (a: WordB.t ArrayWordsB.ArrayN.t) (i: int) (b: WordS.t) =
    set_cast_direct a (sizeWB*i) b.
end ArrayAccessCast.
