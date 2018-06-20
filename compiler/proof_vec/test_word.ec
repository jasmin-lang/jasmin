require import Int.

abstract theory W.

type t.
op size : int.
op (+)  : t -> t -> t.
op (-)  : t -> t -> t.
op (%)  : t -> t -> t.
op ( * ): t -> t -> t.
op (/)  : t -> t -> t.
op ( & ): t -> t -> t.
op (|)  : t -> t -> t.
op ( >>): t -> t -> t. 
op (<<) : t -> t -> t.
op (|>>): t -> t -> t. 
op (<)  : t -> t -> t.
op (<=) : t -> t -> t.
 
op adc: t -> t -> bool -> (bool * bool * bool * bool * bool * t).
op of_int: int -> t.
end W.

(* example below *)

(*theory W8.
  clone include W with op size = 8.
end W8.*) 
 
clone W as W8   with op size = 8.
clone W as W16  with op size = 16.
clone W as W32  with op size = 32.
clone W as W64  with op size = 64.
clone W as W128 with op size = 128.
clone W as W256 with op size = 256.

op sigext_8_8:   W16.t -> W8.t.
op sigext_8_16:  W16.t -> W16.t.
op sigext_8_32:  W16.t -> W32.t.
op sigext_8_64:  W16.t -> W64.t.
op sigext_8_128: W16.t -> W128.t.
op sigext_8_256: W16.t -> W256.t.

op sigext_16_8:   W16.t -> W8.t.
op sigext_16_16:  W16.t -> W16.t.
op sigext_16_32:  W16.t -> W32.t.
op sigext_16_64:  W16.t -> W64.t.
op sigext_16_128: W16.t -> W128.t.
op sigext_16_256: W16.t -> W256.t.

op sigext_32_8:   W32.t -> W8.t.
op sigext_32_16:  W32.t -> W16.t.
op sigext_32_32:  W32.t -> W32.t.
op sigext_32_64:  W32.t -> W64.t.
op sigext_32_128: W32.t -> W128.t.
op sigext_32_256: W32.t -> W256.t.

op sigext_64_8:   W64.t -> W8.t.
op sigext_64_16:  W64.t -> W16.t.
op sigext_64_32:  W64.t -> W32.t.
op sigext_64_64:  W64.t -> W64.t.
op sigext_64_128: W64.t -> W128.t.
op sigext_64_256: W64.t -> W256.t.

op sigext_128_8:   W128.t -> W8.t.
op sigext_128_16:  W128.t -> W16.t.
op sigext_128_32:  W128.t -> W32.t.
op sigext_128_64:  W128.t -> W64.t.
op sigext_128_128: W128.t -> W128.t.
op sigext_128_256: W128.t -> W256.t.

op sigext_256_8:   W256.t -> W8.t.
op sigext_256_16:  W256.t -> W16.t.
op sigext_256_32:  W256.t -> W32.t.
op sigext_256_64:  W256.t -> W64.t.
op sigext_256_128: W256.t -> W128.t.
op sigext_256_256: W256.t -> W256.t.

