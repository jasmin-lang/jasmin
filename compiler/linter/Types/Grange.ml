open Jasmin
open Prog
open Operators

type t = range

let first ((d, f, l) : t) : expr =
    match d with
    | UpTo -> f
    | DownTo -> l

let last ((d, f, l) : t) : expr =
    match d with
    | UpTo -> l
    | DownTo -> f

let incr_operator ((d, _, _) : t) : sop2 =
    match d with
    | UpTo -> Oadd Op_int
    | DownTo -> Osub Op_int

let cmp_operator ((d, _, _) : t) : sop2 =
    match d with
    | UpTo -> Olt Cmp_int
    | DownTo -> Ogt Cmp_int
