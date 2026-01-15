open Jasmin
open Prog
open Operators

type t = range

let first ((d, f, l) : t) : expr =
    match d with
    | E.UpTo -> f
    | E.DownTo -> l

let last ((d, f, l) : t) : expr =
    match d with
    | E.UpTo -> l
    | E.DownTo -> f

let incr_operator ((d, _, _) : t) : sop2 =
    match d with
    | E.UpTo -> Oadd Op_int
    | E.DownTo -> Osub Op_int

let cmp_operator ((d, _, _) : t) : sop2 =
    match d with
    | E.UpTo -> Olt Cmp_int
    | E.DownTo -> Ogt Cmp_int
