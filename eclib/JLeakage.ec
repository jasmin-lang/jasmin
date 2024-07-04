require import AllCore List Bool.
require import JMemory JWord.
(* ------------------------------------------------------------------- *)
(* Leakages                                                            *)

type base_leakage = [
  | LeakAddr_ of address list
  | LeakCond_ of bool
  | LeakFor_  of (int * int)
  | LeakW32_  of W32.t ].

type leakage = [
  | LeakBase of base_leakage 
  | LeakNode of leakage & leakage
  | LeakEmpty
].

op [opaque] LeakAddr x = LeakBase (LeakAddr_ x).
op [opaque] LeakCond x = LeakBase (LeakCond_ x).
op [opaque] LeakFor x = LeakBase (LeakFor_ x).
op [opaque] LeakW32 x = LeakBase (LeakW32_ x).

type leakages = leakage list.

(* Leakage constructor *)
op LeakList_ (l : leakages) : leakage = 
  with l = "[]" => LeakEmpty
  with l = (::) x xs => LeakNode x (LeakList_ xs).

op [opaque] LeakList (l : leakages) = LeakList_ l.


(*
type leakage_t = [
  | LeakAddr of address list
  | LeakCond of bool
  | LeakFor  of (int * int)
].

type leakages_t = leakage_t list.

*)

op zlog2 : int -> int.

