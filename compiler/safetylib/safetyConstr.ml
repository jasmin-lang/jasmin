open Jasmin
open Utils
open Apron

open SafetyUtils
open SafetyVar
open SafetyExpr
    
(******************)
(* Tcons1 Wrapper *)
(******************)

module Mtcons : sig
  type t
  type typ = Apron.Lincons0.typ

  val make : Mtexpr.t -> typ -> t

  val to_atcons  : t -> Apron.Environment.t -> Tcons1.t
  val to_lincons : t -> Apron.Environment.t -> Lincons1.t option

  val get_expr : t -> Mtexpr.t
  val get_typ : t -> typ

  (* This does not check equality of the underlying Apron environments. *)
  val equal_tcons : t -> t -> bool

  val print : Format.formatter -> t -> unit
end = struct
  (* EQ | SUPEQ | SUP | DISEQ | EQMOD of Apron.Scalar.t *)
  type typ = Apron.Lincons0.typ

  type t = { expr : Mtexpr.t;
             typ : typ }

  let make t ty = { expr = t; typ = ty }

  let to_atcons t env = Tcons1.make (Mtexpr.to_aexpr t.expr env) t.typ

  let to_lincons t env =
    Option.map (fun linexpr -> Lincons1.make linexpr t.typ)
      (Mtexpr.to_linexpr t.expr env)

  let get_expr t = t.expr
  let get_typ t = t.typ

  let equal_tcons t t' =
    Mtexpr.equal_mexpr t.expr t'.expr
    && t.typ = t'.typ

  let print ppf t = 
    Format.fprintf ppf "%a %s 0" 
      Mtexpr.print t.expr
      (Lincons1.string_of_typ t.typ)
end



(***************************************)
(* Boolean combination of constraints. *)
(***************************************)

type btcons =
  | BLeaf of Mtcons.t
  | BVar of Bvar.t
  | BAnd of btcons * btcons
  | BOr of btcons * btcons

let rec pp_btcons ppf = function
  | BLeaf t -> Mtcons.print ppf t

  | BVar bv -> Bvar.print ppf bv

  | BAnd (bl,br) ->
    Format.fprintf ppf "(%a@ AND@ %a)"
      pp_btcons bl pp_btcons br

  | BOr (bl,br) ->
    Format.fprintf ppf "(%a@ OR@ %a)"
      pp_btcons bl pp_btcons br

let rec equal_btcons bt bt' = match bt, bt' with
  | BOr (b1, b2),  BOr (b1', b2')
  | BAnd (b1, b2), BOr (b1', b2') ->
    equal_btcons b1 b1' && equal_btcons b2 b2'
  | BLeaf t, BLeaf t' -> Mtcons.equal_tcons t t'
  | BVar bv, BVar bv' -> bv = bv'
  | _ -> false
  
let true_tcons1 =
  let zero_t = Coeff.s_of_int 0 in
  Mtcons.make (Mtexpr.cst zero_t) Tcons1.EQ

let false_tcons1 =
  let zero_t = Coeff.s_of_int 0 in
  Mtcons.make (Mtexpr.cst zero_t) Tcons1.DISEQ

(* Return the negation of c, except for EQMOD.
   For EQMOD, we return a constraint that always hold. *)
let flip_constr c =
  let t = Mtcons.get_expr c in
  match Mtcons.get_typ c with
  | Tcons1.EQ -> Mtcons.make t Tcons1.DISEQ |> Option.some
  | Tcons1.DISEQ -> Mtcons.make t Tcons1.EQ |> Option.some
  | Tcons1.SUPEQ ->
    let mt = Mtexpr.unop Texpr1.Neg t in
    Mtcons.make mt Tcons1.SUP |> Option.some

  | Tcons1.SUP ->
    let mt = Mtexpr.unop Texpr1.Neg t in
    Mtcons.make mt Tcons1.SUPEQ |> Option.some

  | Tcons1.EQMOD _ -> None (* Remark: For small i, we could do something *)


exception Bop_not_supported

let rec flip_btcons : btcons -> btcons option = fun c ->
  let rec flip_btcons_aux = function
    | BLeaf c -> begin match flip_constr c with
        | Some fc -> BLeaf fc
        | None -> raise Bop_not_supported end
    | BVar bv -> BVar (Bvar.not bv)
    | BAnd (bl,br) -> BOr (flip_btcons_aux bl, flip_btcons_aux br)
    | BOr (bl,br) -> BAnd (flip_btcons_aux bl, flip_btcons_aux br) in

  try Some (flip_btcons_aux c) with Bop_not_supported -> None


(* Type of expression that have been split to remove IfThenElse *)
type s_expr = (btcons list * Mtexpr.t option) list

let sexpr_from_simple_expr : Mtexpr.t -> s_expr = fun expr ->
  [([], Some expr)]

let pp_s_expr fmt (e : s_expr) =
  let pp_el fmt (l,t_opt) =
    Format.fprintf fmt "@[<v 0>%d constraints:@;@[<v 1>%a@]@;term: @[%a@]@]"
      (List.length l)
      (pp_list pp_btcons) l
      (pp_opt Mtexpr.print) t_opt in

  Format.fprintf fmt "@[<v 0>%a@]"
    (pp_list pp_el) e
