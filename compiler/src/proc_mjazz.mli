module Path = BatPathGen.OfString
module F = Format
module L = Location
module A = Annotations
module S = Syntax
module E = Expr
module P = Prog
module M = Mprog
module W = Wsize
module T = Type

type mjazzerror =
  | MJazzIncompatibleNS
  | NonToplevelRequire
  | NonExistentMod of M.modulename
  | InnerPModule of M.modulename
  | MJazzNYS
  | MJazzInternal of string
  | MJazzStringError of string

exception MJazzError of L.t * mjazzerror

val pp_mjazzerror: F.formatter -> mjazzerror -> unit

val parse_file :
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Pretyping.arch_info ->
  (string*string) list ->
  string ->
  string list list
  * (Prog.funname * (Z.t * Z.t) list) Location.located list
  * (unit, ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op) Prog.pprog
  * (unit, ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op) Mprog.mpprog



