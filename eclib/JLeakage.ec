require import AllCore List Bool.
require import JMemory.
(* ------------------------------------------------------------------- *)
(* Leakages                                                            *)

type base_leakage = [
  | LeakAddr of address list
  | LeakCond of bool
  | LeakFor  of (int * int)
  | LeakW32  of W32.t ].

type leakage = [
  | LeakBase of base_leakage 
  | LeakNode of leakage & leakage
  | LeakEmpty
].

type leakages = leakage list.

(* Leakage constructor *)
op LeakList_ (l : leakages) : leakage = 
  with l = "[]" => LeakEmpty
  with l = (::) x xs => LeakNode x (LeakList_ xs).

op [opaque] LeakList (l : leakages) = LeakList_ l.



type leakage_t = [
  | LeakAddr of address list
  | LeakCond of bool
  | LeakFor  of (int * int)
].

type leakages_t = leakage_t list.


op zlog2 : int -> int.

