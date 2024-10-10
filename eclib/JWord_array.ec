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

  clone import PolyArray as ArrayW8.

  op of_array8 (a: W8.t ArrayW8.t) = init8 (fun i -> a.[i]).

  op to_array8 (a: t) = ArrayW8.init (fun i -> get8 a i).


op (a: ArrayN' Wws): WArrayN.initWS (fun i -> a.[i])
op (a: WArrayN'): ArrayN.init (fun i -> getWS a i)
  

end WArray.

(* Array of words, where the word size is any number of bytes *)
abstract theory ArrayWords
    (* size of a word in bytes *)
    op sizeW: int.
    axiom gt0_sizeW: 0 < sizeW.

    (* size of the array in words *)
    op sizeA: int.
    axiom gt0_sizeA: 0 < sizeA.

    clone BitWord as Word with
        op size <- 8 * sizeW
        proof gt0_size by done.

    clone PolyArray as ArrayN with
        size <= sizeA
        proof ge0_size by done.

    (* Equivalent array of bytes *)
    clone WArray as WArrayN with
        size <= sizeW * sizeA
        proof ge0_size by done.

    (* Conversion between WArrayN.t and Word.t ArrayN.t *)
    clone W_WS as Wu8 with
        op sizeS <- W8.size, op sizeB <- Word.size, op r <- sizeW,
        theory WS <- W8, theory WB <- Word
        proof gt0_r by done, sizeBrS by done.

    (* direct means offset in bytes, not in words *)
    op wa_get_direct (t: WArrayN.t) (i: int): Word.t =
        Wu8.pack'R_t (Wu8.Pack.init (fun j => t.[i+j])).
    abbrev wa_get (t: WArrayN.t) (i: int): Word.t = wa_get_direct t (sizeW*i).
    op wa_set_direct (t: WArrayN.t) (i: int) (w: Word.t) =
        WArrayN.init (fun k => if i <= k < i + sizeW then w \bits8 (k-i) else t.[k]).

    op of_word_array (a: Word.t ArrayN.t) =
        WArrayN.init (fun i => a.[i %/ sizeW] \bits8 (i%%sizeW)).
    op to_word_array (a: WArrayN.t) =
        ArrayN.init (fun i -> wa_get a i).

    op get_direct (a: Word.t ArrayN.t) = wa_get_direct (of_word_array a).
    op set_direct (a: Word.t ArrayN.t) (i: int) (w: Word.t) =
        to_word_array (wa_set_direct (of_word_array a) i w).

end ArrayWords.

(* Array slicing *)
theory SubArray.
    op sizeS: int.
    axiom gt0_sizeS: 0 < sizeS.

    op sizeB: int.
    axiom gt0_sizeB: 0 < sizeB.

    (* Sub-array *)
    clone PolyArray as ArrayS with
        size <= sizeS
        proof ge0_size by done.

    (* Base array *)
    clone PolyArray as ArrayB with
        size <= sizeB
        proof ge0_size by done.

  op get_sub (a: 'a ArrayB.t) (i: int) = ArrayS.init (fun j -> a.[i + j]).

  op set_sub (a: 'a ArrayB.t) (i: int) (b: 'a ArrayS.t) =
    ArrayB.init (fun j -> if i <= j < i + sizeS then b.[j - i] else a.[j]).
end SubArray.

theory SubArrayDirect.
    op sizeW: int.
    axiom gt0_sizeW: 0 < sizeW.

    op sizeS: int.
    axiom gt0_sizeS: 0 < sizeS.

    op sizeB: int.
    axiom gt0_sizeB: 0 < sizeB.

    clone BitWord as Word with
        op size <- 8 * sizeW
        proof gt0_size by done.

    clone ArrayWords as ArrayWordsS with
        op sizeW <- sizeW, op sizeA <- sizeS, theory Word <- Word
        proof gt0_sizeW by done, gt0_sizeA by done.

    clone ArrayWords as ArrayWordsB with
        op sizeW <- sizeW, op sizeA <- sizeB, theory Word <- Word
        proof gt0_sizeW by done, gt0_sizeA by done.

    op get_sub_direct (a: Word.t ArrayWordsB.ArrayN.t) (i: int) =
        ArrayWordsS.ArrayN.init (fun j -> ArrayWordsB.get_direct a (i + j)).

    op set_sub_direct (a: W16.t ArrayB.t) (i: int) (b: W16.t ArrayS.t) =
        let aw = ArrayWordsB.of_word_array a in
        let bw = ArrayWordsS.of_word_array b in
        (* FIXME: change init8 and get8 to init and _.[_] *)
        ArrayWordsB.to_word_array (
            ArrayWordsB.WArrayN.init8 (fun j ->
            if i <= j < i * sizeW * sizeS then get8 bw (j - i) else get8 aw j
            )
        ).
end SubArrayDirect.

(*
theory ArrayWords16.
  op size: int.
  clone PolyArray as ArrayN with size <= size.
  clone WArray as WArrayN with size <= 2 * size.
  (* FIXME: prove axioms of cloned theories. *)

  op of_w16_array (a: W16.t ArrayN.t) = WArrayN.init16 (fun i -> a.[i]).
  op to_w16_array (a: WArrayN.t) = ArrayN.init (fun i -> get16 a i).

  op get16_direct (a: W16.t ArrayN.t) = WArrayN.get16_direct (of_w16_array a).
  op set16_direct (a: W16.t ArrayN.t) (i: int) (w: W16.t) =
    to_w16_array (WArrayN.set16_direct (of_w16_array a) i w).

end ArrayWords16.

theory SubArray16Direct.
  op sizeS: int.
  op sizeB: int.

  clone ArrayWords16 as ArrayWords16S with size <= sizeS.
  clone ArrayWords16 as ArrayWords16B with size <= sizeB.

  op get_sub_direct (a: W16.t ArrayB.t) (i: int) =
    ArrayWords16S.ArrayN.init (fun j -> get16_direct (ArrayWords16B.of_w16_array a) (i + j)).


  op set_sub_direct (a: W16.t ArrayB.t) (i: int) (b: W16.t ArrayS.t) =
    let aw = ArrayWords16B.of_w16_array a in
    let bw = ArrayWords16S.of_w16_array b in
    (* FIXME: change init8 and get8 to init and _.[_] *)
      ArrayWords16B.to_w16_array (
        ArrayWords16B.WArrayN.init8 (fun j ->
          if i <= j < i * 2 * sizeS then get8 bw (j - i) else get8 aw j
        )
      ).

end SubArray16Direct.
*)

(* TODO: do this for pairs of Wsizes. Do this as generic theory. exemple: JWord.ec, theory W_WS and clones. *)


(*
from Jasmin require import JWord_array.
require import Array8.

clone export WArray as WArray8  with op size <- 8.
clone export ArrayWords8 as ArrayWords8_8 with op size <- 8, theory ArrayN <- Array8, theory WArrayN <- WArray8.
*)


 
