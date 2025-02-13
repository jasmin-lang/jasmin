require import AllCore List Bool.
require import JMemory JWord.
(* ------------------------------------------------------------------- *)
(* Leakages                                                            *)

(* Legacy global leakge *)
type leakage_glob_t = [
  | LeakAddr of address list
  | LeakCond of bool
  | LeakForBounds  of (int * int)
].

(* Legacy global leakge *)
type leakages_glob_t = leakage_glob_t list.

(* All types that can be leaked. For arrays, we use a byte list to keep the
number of types bounded. *)
type leakage_value = [
  | Leak_int_ of int
  | Leak_bool_ of bool
  | Leak_W8_  of W8.t
  | Leak_W16_  of W16.t
  | Leak_W32_  of W32.t
  | Leak_W64_  of W64.t
  | Leak_W128_  of W128.t
  | Leak_W256_  of W256.t
  | Leak_array_ of W8.t list
  ].

(* A single leakage element: classify leakage according to their kind, which is useful when considering leakage models. *)
type leakage_point = [
  (* branches, for loop iteration counts, etc. *)
  | ControlFlow of leakage_value
  (* Array offset possibly combining with other such values and with array access indices *)
  | Offset of leakage_value
  (* Memory address or array index *)
  | Address of leakage_value
  (* Plain data leakage (e.g.: operand) *)
  | Data of leakage_value
].

(* Leakage involved in the evaluation of a single expression or lvalue. *)
type leakage_expr = leakage_point list.

(* Leakage of an operation:
    - leakage for each lvalue place computation
    - leakage for each operand evaluation
    - values of operands
    - values of operation result values
*)
type leakage_op =
    leakage_expr list * leakage_expr list * leakage_value list * leakage_value list.

(* Tree structure of leakage *)
type leakage = [
  | LeakExpr of leakage_expr
  | LeakOp of leakage_op
    (* lvs leakage, es leakage, leakage in call *)
  | LeakCall of (leakage_expr list * leakage_expr list * leakage)
  | LeakNode of leakage & leakage
  | LeakEmpty
].

type leakages = leakage list.

(* Leakage constructor *)
op LeakList_ (l : leakages) : leakage =
  with l = "[]" => LeakEmpty
  with l = (::) x xs => LeakNode x (LeakList_ xs).

op [opaque] LeakList (l : leakages) = LeakList_ l.

op [opaque] LeakBranch (cond: bool) = LeakExpr ([ControlFlow (Leak_bool_ cond)]).

op [opaque] LeakNIter (n: int) = LeakExpr ([ControlFlow (Leak_int_ n)]).

op [opaque] LeakBounds (b: int * int) =
    LeakExpr ([ControlFlow (Leak_int_ b.`1); ControlFlow (Leak_int_ b.`2)]).

op [opaque] LeakIf (cond: bool) (cond_leak: leakage_expr) (leak_c: leakage) = 
    LeakList [ LeakBranch cond; LeakExpr cond_leak; leak_c].

op [opaque] LeakFor (lb: int) (ub: int) (lb_leak: leakage_expr) (ub_leak: leakage_expr) (leak_cs: leakages) =
    LeakList [
        LeakBounds (lb, ub);
        LeakExpr lb_leak;
        LeakExpr ub_leak;
        LeakList leak_cs
    ].

op [opaque] LeakWhile (c1_leaks: leakages) (cond_leaks: leakages) (c2_leaks: leakages) =
    LeakList [
        LeakNIter (size cond_leaks); LeakList cond_leaks; LeakList c1_leaks; LeakList c2_leaks
    ].

