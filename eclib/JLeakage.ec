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

type leakage_value = [
  | Leak_int_ of int
  | Leak_bool_ of bool
  | Leak_W8_  of W8.t
  | Leak_W16_  of W16.t
  | Leak_W32_  of W32.t
  | Leak_W64_  of W64.t
  | Leak_W128_  of W128.t
  | Leak_W256_  of W256.t
  ].

type base_leakage = [
  (* branches, for loop iteration counts, etc. *)
  | ControlFlow of leakage_value
  (* Array offset possibly combining with other such values and with array access indices *)
  | Offset of leakage_value
  (* Memory address or array index *)
  | Address of leakage_value
  (* Plain data leakage (e.g.: operand) *)
  | Data of leakage_value
].

type leakage = [
  | LeakBase of base_leakage
  | LeakNode of leakage & leakage
  | LeakEmpty
].


op [opaque] Leak_addr x  = LeakBase (Address x).
op [opaque] Leak_offset x = LeakBase (Offset x).
op [opaque] Leak_data x = LeakBase (Data x).

op [opaque] Leak_cond x  = LeakBase (ControlFlow (Leak_bool_ x)).
op [opaque] Leak_bound x = LeakBase (ControlFlow (Leak_int_ x)).

type leakages = leakage list.

(* Leakage constructor *)
op LeakList_ (l : leakages) : leakage =
  with l = "[]" => LeakEmpty
  with l = (::) x xs => LeakNode x (LeakList_ xs).

op [opaque] LeakList (l : leakages) = LeakList_ l.

