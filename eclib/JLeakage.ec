require import AllCore List Bool.
require import JMemory JWord.
(* ------------------------------------------------------------------- *)
(* Leakages                                                            *)

type leakage_glob_t = [
  | LeakAddr of address list
  | LeakCond of bool
  | LeakFor  of (int * int)
].

type leakages_glob_t = leakage_glob_t list.

type base_leakage = [
  | Leak_int_ of int
  | Leak_bool_ of bool
  | LeakW8_  of W8.t
  | LeakW16_  of W16.t
  | LeakW32_  of W32.t
  | LeakW64_  of W64.t
  | LeakW128_  of W128.t
  | LeakW256_  of W256.t
  ].

type leakage = [
  | LeakBase of base_leakage
  | LeakNode of leakage & leakage
  | LeakEmpty
].

op [opaque] Leak_int x = LeakBase (Leak_int_ x).
op [opaque] Leak_bool x = LeakBase (Leak_bool_ x).
op [opaque] Leak_W8 x = LeakBase (LeakW8_ x).
op [opaque] Leak_W16 x = LeakBase (LeakW16_ x).
op [opaque] Leak_W32 x = LeakBase (LeakW32_ x).
op [opaque] Leak_W64 x = LeakBase (LeakW64_ x).
op [opaque] Leak_W128 x = LeakBase (LeakW128_ x).
op [opaque] Leak_W256 x = LeakBase (LeakW256_ x).

type leakages = leakage list.

(* Leakage constructor *)
op LeakList_ (l : leakages) : leakage =
  with l = "[]" => LeakEmpty
  with l = (::) x xs => LeakNode x (LeakList_ xs).

op [opaque] LeakList (l : leakages) = LeakList_ l.

