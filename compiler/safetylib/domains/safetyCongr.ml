open Jasmin
open Utils
open Apron

open SafetyConstr
open SafetyUtils
open SafetyVar
open SafetyExpr 
open SafetyInterfaces

(********************************)
(* Numerical Domain: Congruence *)
(********************************)

let pp_z fmt z = Format.fprintf fmt "%s" (Z.to_string z)
let pp_bool fmt b =
  Format.fprintf fmt "%s" (if b then "true" else "false")
  
  
(* Congruence lattice *)
module Congr = struct

  (* Bot represents the empty set
     (a,b) represents aℤ + b, where a = 0 or (0 < a and 0 ≤ b < a). *) 
  type t = Bot | V of Z.t * Z.t

  let print fmt = function
    | Bot -> Format.fprintf fmt "⊥"
    | V (a,b) when Z.equal a Z.zero -> 
      Format.fprintf fmt "{%s}" (Z.to_string b)
    | V (a,_) when Z.equal a Z.one -> 
      Format.fprintf fmt "ℤ"
    | V (a,b) when Z.equal b Z.zero -> 
      Format.fprintf fmt "%s.ℤ" (Z.to_string a)
    | V (a,b) -> 
      Format.fprintf fmt "%s.ℤ + %s" (Z.to_string a) (Z.to_string b)         

  let top = V (Z.one, Z.zero)
  let bot = Bot

  let make a b =
    if Z.equal a Z.zero
    then V (a, b)
    else
      let a = Z.abs a in
      V (a, Z.erem b a)

  let of_coeff (c : Coeff.t) = 
    let int = match c with
    | Coeff.Scalar s   -> scalar_to_zint s
    | Coeff.Interval i -> interval_to_zint i in
    match int with
    | None -> top
    | Some c -> V (Z.zero, c)
    
  let mem_v x (a,b) = 
    if Z.equal a Z.zero
    then Z.equal x b
    else Z.equal (Z.erem x a) b

  let mem x = function
    | Bot -> false
    | V (a,b) -> mem_v x (a,b)

  let meet_v (a,b) (a',b') =
    match Z.equal a Z.zero, Z.equal a' Z.zero with
    | true, true   -> if Z.equal b b' then V (a,b) else Bot
    | true, false  -> if mem_v b (a',b') then V (a,b) else Bot
    | false, true  -> if mem_v b' (a,b) then V (a',b') else Bot
    | false, false ->
      let gcd, u, _v = Z.gcdext a a' in
      if Z.rem (Z.sub b b') gcd = Z.zero 
      then
        let b'' = Z.sub b (Z.div (Z.mul a (Z.mul u (Z.sub b b'))) gcd) in
        make (Z.lcm a a') b''
      else Bot

  let meet t t' = match t, t' with
    | Bot, _ | _, Bot -> Bot
    | V (a,b), V (a',b') -> meet_v (a,b) (a',b')
                     
  (* gcd extended to the case where [a] or [b] is zero. *)
  let gcd_z (a:Z.t) (b:Z.t) : Z.t =
    if      Z.equal a Z.zero then b
    else if Z.equal b Z.zero then a
    else                          Z.gcd a b
    
  let join_v (a,b) (a',b') =
    let a'' = gcd_z (gcd_z a a') (Z.sub b b') in
    make a'' b'

  let join t t' = match t, t' with
    | Bot, t'' | t'', Bot -> t''
    | V (a,b), V (a',b') -> join_v (a,b) (a',b')

  (* divisibility extended to the case where [a] or [b] is zero *)
  let divides_z a b =
    if Z.equal a Z.zero then Z.equal b Z.zero
    else Z.equal (Z.rem b a) Z.zero

  (* erem extended to the case where [b] is zero *)
  let erem_z a b =
    if Z.equal b Z.zero then a else Z.erem a b

  let is_included t t' = match t,t' with
    | Bot, _ -> true
    | _, Bot -> false
    | V (a,b), V (a',b') ->
      divides_z a' a && erem_z b a' = b'

  let is_bottom t = is_included t bot
  let is_top t = is_included top t

  let bmap f = function
    | Bot -> Bot
    | V (a,b) -> f (a,b) 

  let bmap2 f t t' = match t, t' with
    | Bot,_ | _, Bot -> Bot
    | V (a,b), V (a',b') -> f (a,b) (a',b')
                                                  
  let neg_v (a,b) = make a (Z.neg b)
  let neg = bmap neg_v
  
  let add_v (a,b) (a',b') = make (gcd_z a a') (Z.add b b')
  let add = bmap2 add_v

  let sub_v (a,b) (a',b') = make (gcd_z a a') (Z.sub b b')
  let sub = bmap2 sub_v
      
  let mul_v (a,b) (a',b') =
    let a'' = gcd_z (gcd_z (Z.mul a a') (Z.mul a b')) (Z.mul a' b) in
    make a'' (Z.mul b b')
  let mul = bmap2 mul_v

  let div_v (a,b) (a',b') =
    if Z.equal a' Z.zero then
      if Z.equal b' Z.zero then Bot 
      else if divides_z b' a && divides_z b' b
      then make (Z.div a b') (Z.div b b')
      else top 
    else top
  let div = bmap2 div_v

  let modulo_v (a,b) (a',b') =
  if Z.equal a' Z.zero then
    if Z.equal b' Z.zero then Bot
    else make (gcd_z a b') (Z.rem b b')
  else make (gcd_z (gcd_z a a') b') b      
  let modulo = bmap2 modulo_v

  let to_int = function
    | Bot -> Interval.bottom
    | V (a,b) when Z.equal a Z.zero ->
      let b = Mpqf.of_string (Z.to_string b) in
      Interval.of_mpqf b b
    | _ -> Interval.top
end

module AbsNumCongr : AbsNumType = struct
  (* Missing entries are [Top]. *)
  type t = Congr.t Mm.t

  let make vs =
    List.fold_left (fun t v -> Mm.add v Congr.top t) Mm.empty vs

  let value v t = Mm.find_default Congr.top v t
      
  let app2 f a b =
    Mm.merge (fun _ c c' ->
        let c  = Option.default Congr.top c
        and c' = Option.default Congr.top c' in
        Some (f c c')) a b

  let appl f l = match l with
    | [] -> raise (Aint_error "appl: empty list")
    | a :: l -> List.fold_left (fun a b -> app2 f a b) a l
    
  let meet = app2 Congr.meet   
  let meet_list = appl Congr.meet

  let join = app2 Congr.join     
  let join_list = appl Congr.join

  let widening _ = app2 Congr.meet

  let forget_list t l =
    if l = [] then t else
      Mm.filter (fun k _ -> not (List.mem k l)) t

  let is_included a a' =
    let am =
      Mm.merge (fun _ x y' -> Some (Option.default Congr.top x,
                                    Option.default Congr.top y'))
        a a' in
    Mm.for_all (fun _ (x,y) -> Congr.is_included x y) am
    
  let is_bottom t = Mm.exists (fun _ -> Congr.is_bottom) t 
    (* if Mm.exists (fun _ -> Congr.is_bottom) t then begin
     *   let k,v = Mm.choose (Mm.filter (fun _ v -> Congr.is_bottom v) t) in
     *   Format.eprintf "FOUND: %a: %a@.@." pp_mvar k Congr.print v;
     *   assert false end
     * else false *)
      
  let bottom t =
    assert (Mm.cardinal t <> 0);
    Mm.map (fun _ -> Congr.bot) t
      
  let top t =
    assert (Mm.cardinal t <> 0);
    Mm.map (fun _ -> Congr.top) t

  let expand t v l =
    assert (Mm.mem v t && List.for_all (fun x -> not (Mm.mem x t)) l);
    let c = value v t in
    List.fold_left (fun t v' ->
        Mm.add v' c t) t l 

  let fold t l = match l with
    | [] -> raise (Aint_error "congruence fold: empty list")
    | v :: l' ->
      let cl' = List.map (fun x -> value x t) l'
      and cv  = value v t in
      let c = List.fold_left Congr.join cv cl' in
      (* Remove [l'] and update [v]. *)
      Mm.filter_map (fun x c' ->
          if x = v
          then Some c
          else if List.mem x l' then None
          else Some c') t

  let bound_variable t v = Congr.to_int (value v t)
      
  let rec eval t e = match e with
    | Mtexpr.Mcst i -> Congr.of_coeff i
    | Mtexpr.Mvar v -> value v t
    | Mtexpr.Munop (op,e, Texpr0.Int,_) ->
      begin
        match op with
        | Texpr0.Neg -> Congr.neg (eval t e)
        | Texpr0.Cast | Texpr0.Sqrt -> assert false
      end         
      
    | Mtexpr.Mbinop (op,e1,e2, Texpr0.Int,_) ->
      begin 
        match op with
        | Texpr0.Add -> Congr.add    (eval t e1) (eval t e2)
        | Texpr0.Sub -> Congr.sub    (eval t e1) (eval t e2)
        | Texpr0.Mul -> Congr.mul    (eval t e1) (eval t e2)
        | Texpr0.Div -> Congr.div    (eval t e1) (eval t e2)
        | Texpr0.Mod -> Congr.modulo (eval t e1) (eval t e2)
        | _ -> assert false
      end
      
    | _ -> assert false
    
  let bound_texpr t e = Congr.to_int (eval t e)

  let assign_expr_one force t (v,e) = 
    let c = eval t e in
    let c =
      if weak_update v && not force
      then Congr.join c (value v t)
      else c in
    Mm.add v c t

  let assign_expr ?force:(force=false) t ves =
    let ves = List.filter (fun (v,_) -> match v with
        | Mlocal (AarraySlice _) -> false (* FIXME: add an option *)          
        | _ -> true
      ) ves in
    List.fold_left (assign_expr_one force) t ves
    
  let sat_constr t cnstr = match Mtcons.get_typ cnstr with
    | Lincons1.EQMOD n ->
      let c = eval t (Mtcons.get_expr cnstr) in
      begin
        match scalar_to_zint n with
        | Some n -> Congr.is_included c (Congr.make n Z.zero)
        | None -> false
      end
    | _ -> false
                               
  (* We do no implement any assume. *)
  let meet_constr t _ = t
  let meet_constr_list t _ = t

  (* TODO: remove ?*)
  let unify _ _ = assert false

  let change_environment t l =
    (* Remove values not in [l] *)
    let t = Mm.filter (fun k _ -> List.mem k l) t in
    List.fold_left (fun t v ->
        if not (Mm.mem v t)
        then Mm.add v Congr.top t
        else t
      ) t l
      
  let remove_vars t l = forget_list t l

  let get_env t =
    let l = List.map (fun x -> avar_of_mvar (fst x)) (Mm.bindings t) in
    env_of_list l   
  let to_box _t = assert false
    
  let of_box _box = assert false

  let print ?full:(_=false) fmt t =
    let bindings =
      List.filter (fun (x,t) ->
          not (variables_ignore (avar_of_mvar x)) &&
          not (Congr.is_top t)
        ) (Mm.bindings t)
    in
    Format.fprintf fmt "@[<v 0>@[<hv 0>%a@]@;@]"
      (pp_list
         ~sep:(fun fmt () -> Format.fprintf fmt ";@ ")
         (fun fmt (v,t) ->
            Format.fprintf fmt "%a ∈ %a" pp_mvar v Congr.print t))
      bindings
end


