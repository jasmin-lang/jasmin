(* -------------------------------------------------------------------- *)
(* EasyCrypt model of the Jasmin ARMv8.1-M instructions: the ones of
   ARMv7-M (JModel_m4, re-exported), and the conditional selects. *)
require import AllCore List Bool.
require export JModel_m4.

(* -------------------------------------------------------------------- *)
(* Conditional selects: the first source when the condition holds, the
   second one, respectively unchanged, incremented, inverted and negated,
   otherwise. *)

op CSEL (x y: W32.t) (c: bool) : W32.t = if c then x else y.
op CSINC (x y: W32.t) (c: bool) : W32.t = if c then x else y + W32.one.
op CSINV (x y: W32.t) (c: bool) : W32.t = if c then x else invw y.
op CSNEG (x y: W32.t) (c: bool) : W32.t = if c then x else W32.zero - y.
