open Jasmin
open Prog

(*
Complementary module for the grange type to help determine :
- first and last value of a range
- increment and comparison operator for a range
*)
type t = int grange

let first ((d, f, l) : t) : int gexpr =
    match d with
    | E.UpTo -> f
    | E.DownTo -> l

let last ((d, f, l) : t) : int gexpr =
    match d with
    | E.UpTo -> l
    | E.DownTo -> f

let incr_operator ((d, _, _) : t) : E.sop2 =
    match d with
    | E.UpTo -> E.Oadd Op_int
    | E.DownTo -> E.Osub Op_int

let cmp_operator ((d, _, _) : t) : E.sop2 =
    match d with
    | E.UpTo -> E.Olt Cmp_int
    | E.DownTo -> E.Ogt Cmp_int
