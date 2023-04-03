open Jasmin
open Prog
open Apron
open Wsize
    
open SafetyVar
open SafetyUtils

let round_typ = Texpr1.Zero

(*---------------------------------------------------------------*)
(* Texpr1 Wrapper *)

module Mtexpr : sig
  type unop = Apron.Texpr0.unop
  type binop = Apron.Texpr0.binop
  type typ = Apron.Texpr0.typ
  type round = Apron.Texpr0.round

  type t = private
    | Mcst of Coeff.t
    | Mvar of mvar
    | Munop of unop * t * typ * round
    | Mbinop of binop * t * t * typ * round

  val to_aexpr : t -> Apron.Environment.t -> Texpr1.t
  val to_linexpr : t -> Apron.Environment.t -> Linexpr1.t option

  val cst : Coeff.t -> t
  val var : mvar -> t
  val unop : unop -> t -> t
  val binop : binop -> t -> t -> t

  val get_var : t -> mvar list
  val contains_mod : t -> bool

  val weak_cp : mvar -> int -> mvar
  val weak_transf : int Mm.t -> t -> int Mm.t * t

  val equal_mexpr  : t -> t -> bool

  val print : Format.formatter -> t -> unit
end = struct
  type unop = Texpr0.unop
  type binop = Texpr0.binop
  type typ = Apron.Texpr0.typ
  type round = Apron.Texpr0.round

  type t =
    | Mcst of Coeff.t
    | Mvar of mvar
    | Munop of unop * t * typ * round
    | Mbinop of binop * t * t * typ * round

  let rec e_aux = function
    | Mcst c -> Texpr1.Cst c
    | Mvar mvar -> begin match mvar with
        | Mlocal (AarraySlice (_,ws,_)) | Mglobal (AarraySlice (_,ws,_)) ->
          assert (ws = U8);
          Texpr1.Var (avar_of_mvar mvar)
        | _ -> Texpr1.Var (avar_of_mvar mvar) end
    | Munop (op1, a, t, r) -> Texpr1.Unop (op1, e_aux a, t, r)
    | Mbinop (op2, a, b, t, r) -> Texpr1.Binop (op2, e_aux a, e_aux b, t, r)

  let to_aexpr t env = Texpr1.of_expr env (e_aux t)

  let print ppf t = e_aux t |> Texpr1.print_expr ppf

  (* Return sum_{j = 0}^{len - 1} (2^8)^(len - 1 - j) * (U8)v[offset + j] *)
  let rec build_term_array v scope offset len =
    let slice = AarraySlice (v,U8,offset + len - 1) in
    let tv = Mvar (of_scope scope slice) in
    let ptwo = Mcst (Coeff.s_of_mpqf (mpq_pow (8 * (len - 1)))) in
    let t = Mbinop (Texpr1.Mul, ptwo, tv, Texpr1.Int, round_typ) in
    if len = 1 then tv
    else Mbinop (Texpr1.Add,
                 t,
                 build_term_array v scope offset (len - 1),
                 Texpr1.Int, round_typ)

  let cst c = Mcst c

  let var v0 = match v0 with
    | Mglobal (AarraySlice (v,ws,i)) | Mlocal (AarraySlice (v,ws,i)) ->
      let scope = get_scope v0 in
      build_term_array v scope i (size_of_ws ws)

    | _ -> Mvar v0

  let unop op1 a = Munop (op1, a, Texpr1.Int, round_typ) 

  let binop op2 a b = Mbinop (op2, a, b, Texpr1.Int, round_typ)

  let weak_cp v i = Temp ("wcp_" ^ string_of_mvar v, i, ty_mvar v)

  let to_linexpr t env =
    let exception Linexpr_failure in

    let rec linexpr t =
      match t with
      | Mvar m ->
        let l = Linexpr1.make env in
        Linexpr1.set_list l [Coeff.s_of_int 1 ,avar_of_mvar m] None;
        l

      | Mcst c ->
        let l = Linexpr1.make env in
        Linexpr1.set_cst l c;
        l

      | Munop (op, e, Texpr0.Int, _) ->
        let l = linexpr e in
        begin match op with
          | Texpr0.Neg ->
            let l' = Linexpr1.make env in
            Linexpr1.iter (fun c v -> Linexpr1.set_coeff l' v (Coeff.neg c)) l;
            Linexpr1.set_cst l' (Coeff.neg (Linexpr1.get_cst l));
            l'
          | _ -> raise Linexpr_failure end

      | Mbinop (op, e1, e2, Texpr0.Int, _) ->
        let coef op c1 c2 =
          if op = Texpr0.Add then coeff_add c1 c2
          else coeff_add c1 (Coeff.neg c2) in

        let l1, l2 = linexpr e1, linexpr e2 in
        begin match op with
          | Texpr0.Add | Texpr0.Sub ->
            let lres = Linexpr1.make env in
            Linexpr1.set_cst lres
              (coef op (Linexpr1.get_cst l1) (Linexpr1.get_cst l2));

            let vars = ref [] in
            Linexpr1.iter (fun _ c -> vars := c :: !vars) l1;
            Linexpr1.iter (fun _ c -> vars := c :: !vars) l2;
            let vs = List.sort_uniq Stdlib.compare !vars in

            List.iter (fun v ->
                let c1,c2 = Linexpr1.get_coeff l1 v, Linexpr1.get_coeff l2 v in
                Linexpr1.set_coeff lres v (coef op c1 c2);
              ) vs;
            lres

          | _ -> raise Linexpr_failure end
      | _ -> raise Linexpr_failure in

    try Some (linexpr t) with Linexpr_failure -> None


  (* We rewrite the expression to perform soundly weak updates *)
  let rec weak_transf map e =
    match e with
    | Mcst c -> (map, Mcst c)
    | Mvar mvar ->
      if weak_update mvar then
        let i = Mm.find_default 0 mvar map in
        let map' = Mm.add mvar (i + 1) map in
        (map', Mvar (weak_cp mvar i))
      else (map, Mvar mvar)

    | Munop (op1, a, t, r) ->
      let map',a' = weak_transf map a in
      (map', Munop (op1, a', t, r))

    | Mbinop (op2, a, b, t, r) ->
      let map',a' = weak_transf map a in
      let map'',b' = weak_transf map' b in
      (map'', Mbinop (op2, a', b', t, r))

  let get_var e =
    let rec aux acc = function
      | Mcst _ -> acc
      | Mvar mvar -> mvar :: acc
      | Munop (_, a, _, _) -> aux acc a
      | Mbinop (_, a, b, _, _) -> aux (aux acc a) b in
    aux [] e
    |> u8_blast_vars ~blast_arrays:true
    |> List.sort_uniq Stdlib.compare

  let rec contains_mod = function
    | Mvar _ | Mcst _ -> false
    | Munop (_, a, _, _) -> contains_mod a
    | Mbinop (op2, a, b, _, _) ->
      (op2 = Texpr0.Mod) || (contains_mod a) || (contains_mod b)

  let rec equal_mexpr_aux t t' = match t, t' with
    | Mvar v, Mvar v' -> v = v'
    | Mcst c, Mcst c' -> Coeff.equal c c'
    | Munop (op, e, typ, rnd), Munop (op', e', typ', rnd') 
      -> op = op' && typ = typ' && rnd = rnd' && equal_mexpr_aux e e'
    | Mbinop (op, e1, e2, typ, rnd), Mbinop (op', e1', e2', typ', rnd') 
      -> op = op' && typ = typ' && rnd = rnd' 
         && equal_mexpr_aux e1 e1'
         && equal_mexpr_aux e2 e2'
    | _ -> false

  let equal_mexpr  t t' = equal_mexpr_aux t t'
end


let cst_of_mpqf n = Mtexpr.cst (Coeff.s_of_mpqf n)

(* Return the texpr 2^n - y *)
let cst_pow_minus n y = cst_of_mpqf (mpq_pow_minus n y)


let mtexpr_of_z z =
  let mpq_z = mpq_of_z z in
  Mtexpr.cst (Coeff.s_of_mpq mpq_z)
