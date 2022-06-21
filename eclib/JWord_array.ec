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

end WArray.



 
