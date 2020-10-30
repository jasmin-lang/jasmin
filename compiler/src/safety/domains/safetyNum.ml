open Utils
open Prog
open Apron
open Wsize

module Config = SafetyConfig

open SafetyUtils
open SafetyVar
open SafetyExpr 
open SafetyConstr
open SafetyInterfaces



(**********************)
(* Generic Thresholds *)
(**********************)

let int_thresholds =
  (* For unsigned *)
  List.map (fun i -> mpq_pow_minus i 1) [8;16;32;64;128;256]
  (* (\* For signed *\)
   * @ List.map (fun i -> mpq_pow_minus i 1) [7;15;31;63;127;255]
   * @ List.map (fun i -> mpq_pow_minus i 0) [7;15;31;63;127;255] *)

let neg i = Mpqf.neg i


let lcons env v i vneg iminus =
  let e = Linexpr1.make env in
  let ci = Coeff.s_of_mpqf (if iminus then neg i else i)
  and cv = Coeff.s_of_int (if vneg then -1 else 1) in
  let () = Linexpr1.set_list e [cv,v] (Some ci) in
  e

(* Makes the bounds 'v >= 0' and 'v <= 2^N-1' for 'N' in {8;16;32;64;128;256} *)
let thresholds_uint env v =
  let acc = 
    [Lincons1.make (lcons env v (Mpqf.of_int 0) false true) Lincons0.SUPEQ] in
  List.fold_left (fun acc i ->
      let lc = lcons env v i in
      Lincons1.make (lc true false) Lincons0.SUPEQ :: acc
    ) acc int_thresholds

(* FIXME: rename *)
let thresholds_zero env =
  let vars = Environment.vars env
             |> fst
             |> Array.to_list in
    List.fold_left (fun thrs v -> thresholds_uint env v @ thrs
    ) [] vars

  (* List.map (fun v ->
   *     Lincons1.make (lcons env v (Mpqf.of_int 0) false true) Lincons0.SUPEQ
   *   ) vars *)
    
let thresholds_vars env =
  let vars = Environment.vars env
             |> fst
             |> Array.to_list in

  List.fold_left (fun acc v ->
      List.fold_left (fun acc i ->
          let lc = lcons env v i in
          (Lincons1.make (lc true true) Lincons0.SUPEQ)
          :: (Lincons1.make (lc true false) Lincons0.SUPEQ)
          :: (Lincons1.make (lc false true) Lincons0.SUPEQ)
          :: (Lincons1.make (lc false false) Lincons0.SUPEQ)
          :: acc) acc int_thresholds)
    [] vars


let thresholds_param env param =
  let param_pts  = Utils.odfl [] param.pointers
  and param_rels = Utils.odfl [] param.relationals  in

  let vars = fst (Environment.vars env)
             |> Array.to_list in
  
  let param_rels = List.filter_map (fun v -> match mvar_of_avar v with
      | MinValue gv ->
        if List.mem gv.v_name param_rels then Some v else None
      | _ -> None) vars in
  
  let thrs_v v =
    List.map (fun inv ->
        let e = Linexpr1.make env in
        let cv, cinv = Coeff.s_of_int (-1), Coeff.s_of_int 1 in
        let c0 = Coeff.s_of_int 0 in
        let () = Linexpr1.set_list e [(cv,v);(cinv,inv)] (Some c0) in
        Lincons1.make e Lincons0.SUPEQ
      ) param_rels in
                
  List.fold_left (fun thrs v ->
      match mvar_of_avar v with
      | MmemRange (MemLoc gv) ->
        if List.mem gv.v_name param_pts
        then thrs_v v @ thrs
        else thrs
      | _ -> thrs
    ) [] vars


(************************************)
(* Numerical Domain Pretty Printing *)
(************************************)

module type AprManager = sig
  type t

  val man : t Apron.Manager.t
end

module PP (Man : AprManager) : sig
  val pp : Format.formatter -> Man.t Apron.Abstract1.t -> unit
end = struct
  let coeff_eq_1 (c: Coeff.t) = match c with
    | Coeff.Scalar s when Scalar.cmp_int s 1 = 0 -> true
    | Coeff.Interval i when
        Scalar.cmp_int i.Interval.inf 1 = 0 &&
        Scalar.cmp_int i.Interval.sup 1 = 0 -> true
    | _ -> false

  let coeff_eq_0 (c: Coeff.t) = match c with
    | Coeff.Scalar s -> Scalar.cmp_int s 0 = 0
    | Coeff.Interval i ->
      Scalar.cmp_int i.Interval.inf 0 = 0
      && Scalar.cmp_int i.Interval.sup 0 = 0

  let coeff_cmp_0 (c: Coeff.t) = match c with
    | Coeff.Scalar s -> Some (Scalar.cmp_int s 0)
    | Coeff.Interval i ->
      if Scalar.cmp_int i.Interval.inf 0 > 0 then Some 1
      else if Scalar.cmp_int i.Interval.sup 0 < 0 then Some (-1)
      else None

  let pp_coef_var_list fmt l =
    match l with
    | [] -> Format.fprintf fmt "0"
    | _ -> Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt " + ")
             (fun fmt (c, v) ->
                if coeff_eq_1 c then
                  Format.fprintf fmt "%s" (Var.to_string v)
                else
                  Format.fprintf fmt "%a·%s" Coeff.print c (Var.to_string v)) fmt l

  let pp_typ fmt (x, b) = match x, b with
    | Lincons1.DISEQ, _ -> Format.fprintf fmt "!="
    | Lincons1.EQ, _ -> Format.fprintf fmt "="
    | Lincons1.SUP, false -> Format.fprintf fmt ">"
    | Lincons1.SUP, true -> Format.fprintf fmt "<"
    | Lincons1.SUPEQ, false -> Format.fprintf fmt "≥"
    | Lincons1.SUPEQ, true -> Format.fprintf fmt "≤"
    | Lincons1.EQMOD _, _ -> assert false

  let neg_list l =
    List.map (fun (c, v) -> Coeff.neg c, v) l

  let linexpr_to_list_pair env (x: Linexpr1.t) =
    let envi, _ = Environment.vars env in
    Array.fold_left (fun (pos, neg) var ->
        let c = Linexpr1.get_coeff x var in
        if coeff_eq_0 c then (pos, neg)
        else match coeff_cmp_0 c with
          | None -> (c, var) :: pos, neg
          | Some x when x > 0 -> (c, var) :: pos, neg
          | Some _ -> pos, (c, var)::neg
      ) ([], []) envi

  let pp_lincons fmt lc =
    let cst = Lincons1.get_cst lc in
    let typ = Lincons1.get_typ lc in
    let pos, neg =
      linexpr_to_list_pair (Lincons1.get_env lc) (Lincons1.get_linexpr1 lc) in
    if coeff_eq_0 (cst) then
      Format.fprintf fmt "%a %a %a"
        pp_coef_var_list pos
        pp_typ (typ, false)
        pp_coef_var_list (neg_list neg)
    else
      match coeff_cmp_0 (cst) with
      | Some x when x > 0 ->
        if pos = [] then
          Format.fprintf fmt "%a %a %a"
            pp_coef_var_list (neg_list neg)
            pp_typ (typ, true)
            Coeff.print cst
        else if neg = [] then
          Format.fprintf fmt "%a %a %a"
            pp_coef_var_list pos pp_typ
            (typ, false)
            Coeff.print (Coeff.neg cst)
        else 
          Format.fprintf fmt "%a %a %a + %a"
            pp_coef_var_list (neg_list neg)
            pp_typ (typ, true) pp_coef_var_list pos Coeff.print cst
      | _ ->
        if neg = [] then
          Format.fprintf fmt "%a %a %a"
            pp_coef_var_list pos pp_typ (typ, false)
            Coeff.print (Coeff.neg cst)
        else if pos = [] then
          Format.fprintf fmt "%a %a %a" pp_coef_var_list (neg_list neg)
            pp_typ (typ, true) Coeff.print (cst)
        else 
          Format.fprintf fmt "%a %a %a + %a" pp_coef_var_list pos
            pp_typ (typ, false) pp_coef_var_list (neg_list neg)
            Coeff.print (Coeff.neg cst)

  let pp_lincons_earray fmt ea =
    let rec read n =
      if n < 0 then []
      else
        let x = Lincons1.array_get ea n in
        x :: (read (n-1))
    in
    let l = read (Lincons1.array_length ea -1) in
    match l with
    | [] -> Format.fprintf fmt "⊤"
    | _ -> 
      Format.fprintf fmt "{%a}"
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
                                   pp_lincons) l


  let pp fmt x =
    let man = Man.man in
    if Abstract1.is_bottom man x then
      Format.fprintf fmt "⊥"
    else
      let ea = Abstract1.to_lincons_array man x in
      pp_lincons_earray fmt ea
end


(*******************)
(* Abstract Values *)
(*******************)

module BoxManager : AprManager with type t = Box.t = struct
  type t = Box.t

  let man = Box.manager_alloc ()
end

let top_box env = 
  let bman = BoxManager.man in
  Abstract1.top bman env

let bottom_box env = 
  let bman = BoxManager.man in
  Abstract1.bottom bman env

module OctManager : AprManager = struct
  type t = Oct.t

  let man = Oct.manager_alloc ()
end

module PplManager : AprManager = struct
  type t = Ppl.strict Ppl.t

  let man = Ppl.manager_alloc_strict ()
end


(******************************************)
(* Numerical Domains: Boxes and Polyhedra *)
(******************************************)

(* Polyhedra or boxes abstract domain. *)
module AbsNumI (Manager : AprManager) (PW : ProgWrap) : AbsNumType = struct

  type t = Manager.t Abstract1.t
  let man = Manager.man

  let is_relational () = Ppl.manager_is_ppl man
    
  let make l =
    let vars = u8_blast_vars ~blast_arrays:true l |>
               List.map avar_of_mvar in
    let env = env_of_list vars in
    Abstract1.top man env

  let lce a a' =
    let lce = Environment.lce (Abstract1.env a) (Abstract1.env a') in
    (Abstract1.change_environment man a lce false,
     Abstract1.change_environment man a' lce false)

  let env_lce l =
    if l = [] then raise (Aint_error "Lce of an empty list");
    List.fold_left Environment.lce (List.hd l) l

  let lce_list l =
    if l = [] then raise (Aint_error "Lce of an empty list");
    let lce = List.map Abstract1.env l |> env_lce in
    List.map (fun a -> Abstract1.change_environment man a lce false) l

  let meet a a' =
    let a,a' = lce a a' in
    Abstract1.meet man a a'

  let meet_list a_list =
    if a_list = [] then raise (Aint_error "Meet of an empty list");
    let a_list = lce_list a_list in
    Abstract1.meet_array man (Array.of_list a_list)

  let join a a' =
    let a,a' = lce a a' in
    Abstract1.join man a a'

  let join_list a_list =
    if a_list = [] then raise (Aint_error "Join of an empty list");
    let a_list = lce_list a_list in
    Abstract1.join_array man (Array.of_list a_list)

  let earray_to_list ea = 
    List.init
      (Lincons1.array_length ea)
      (fun i -> Lincons1.array_get ea i)
    
  let to_earray env l =
    let arr = Lincons1.array_make env (List.length l) in
    let () = List.iteri (fun i c -> Lincons1.array_set arr i c) l in
    arr

  let thrs_of_oc oc env =
    match omap_dfl (fun x -> Mtcons.to_lincons x env) None oc with
    | None -> []
    | Some lc -> [lc]

  (* let enrich_widening a a' res =
   *   let env = Abstract1.env a in
   *   let ea = Abstract1.to_lincons_array man a
   *            |> earray_to_list in
   *   let to_add = List.filter (fun lin -> Abstract1.sat_lincons man a' lin) ea
   *                |> to_earray env in
   *   Abstract1.meet_lincons_array man res to_add *)

  let compute_thresholds env oc =
    let vars = omap_dfl (fun c -> 
        Mtexpr.get_var_mexpr (Mtcons.get_expr c).mexpr
      ) [] oc in
    let thrs_vars = 
      List.map (fun v -> thresholds_uint env (avar_of_mvar v)) vars 
      |> List.flatten in
    let thrs_oc = thrs_of_oc oc env in
    let thrs = thrs_oc @ thrs_vars in
    let thrs =
      if Config.sc_more_threshold ()
      then thresholds_vars env @ thrs
      else thrs in
    let thrs =
      if Config.sc_zero_threshold ()
      then thresholds_zero env @ thrs
      else thrs in
    let thrs =
      if Config.sc_param_threshold ()
      then thresholds_param env PW.param @ thrs
      else thrs in

    if is_relational () then
      debug(fun () -> Format.eprintf "@[<v 2>threshold(s):@; %a@."
               (pp_list Lincons1.print) thrs);
    thrs

  let widening oc a a' =
    let a,a' = lce a a' in
    let env = Abstract1.env a in
    
    let thrs = compute_thresholds env oc in
    
    (* Be careful to join a and a' before calling widening. Some abstract domain,
       e.g. Polka, seem to assume that a is included in a'
       (and may segfault otherwise!). *)
    let res = Abstract1.widening_threshold man a a' (thrs |> to_earray env) in
    (* if Config.sc_enrich_widening
     * then enrich_widening a a' res
     * else  *)res

  let forget_list a l =
    let l = u8_blast_vars ~blast_arrays:true l in
    let env = Abstract1.env a in
    let al = List.filter
        (Environment.mem_var env) (List.map avar_of_mvar l) in
    Abstract1.forget_array man a (Array.of_list al) false

  let is_included a a' =
    let a,a' = lce a a' in
    Abstract1.is_leq man a a'

  let is_bottom a = Abstract1.is_bottom man a

  let bottom_man man a = Abstract1.bottom man (Abstract1.env a)
  let bottom = bottom_man man

  let top_man man a = Abstract1.top man (Abstract1.env a)
  let top = top_man man

  let check_u8 vs =
    assert (List.for_all (function
        | Mvalue (AarrayEl (_,ws,_)) -> ws = U8
        | _ -> true) vs)
      
  (* v and v_list should not contain Mvalue (AarrayEl) elements
     of size different than U8. *)
  let expand_man man a v v_list =
    check_u8 (v :: v_list);
    let v_array = Array.of_list (List.map avar_of_mvar v_list) in
    Abstract1.expand man a (avar_of_mvar v) v_array

  (* v_list should not contain Mvalue (AarrayEl) elements
     of size different than U8. *)
  let fold_man man a v_list =
    check_u8 (v_list);
    (* PPL implementation of the fold operation is bugged. *)   
    (* let v_array = Array.of_list (List.map avar_of_mvar v_list) in 
     * Abstract1.fold man a v_array *)

    (* We do it instead using assignments and joins. *)
    let v, vs = match List.map avar_of_mvar v_list with
      | v :: vs -> v, vs
      | [] -> raise (Failure "fold_man: empty list") in
    let env = Abstract1.env a in
    
    let ass = List.map (fun v' ->
        let ev' = Texpr1.of_expr env (Texpr1.Var v') in
        Abstract1.assign_texpr man a v ev' None) vs in
    let arr = Array.of_list (a :: ass) in
    let a = Abstract1.join_array man arr in

    (* We remove the variables [vs]. *)
    let vars = Environment.vars env
               |> fst
               |> Array.to_list in
    let nvars = List.filter (fun x -> not (List.mem x vs)) vars in
    let new_env = env_of_list nvars in

    Abstract1.change_environment man a new_env false

  
  let expand a v v_list = expand_man man a v v_list

  let fold a v_list = fold_man man a v_list

  let add_weak_cp_man man a map =
    Mm.fold (fun v i a ->
        let vs = List.init i (Mtexpr.weak_cp v) in
        expand_man man a v vs) map a

  let rem_weak_cp_man man a map =
    Mm.fold (fun v i a ->
        let vs = List.init i (Mtexpr.weak_cp v) in
        fold_man man a (v :: vs)) map a

  let add_weak_cp = add_weak_cp_man man

  let rem_weak_cp = rem_weak_cp_man man

  let prepare_env env mexpr =
    let vars_mexpr =
      List.map avar_of_mvar (Mtexpr.get_var_mexpr mexpr) |> Array.of_list
    and empty_var_array = Array.make 0 (Var.of_string "") in
    let env_mexpr = Environment.make vars_mexpr empty_var_array in
    Environment.lce env env_mexpr

  let bound_texpr_man man a (e : Mtexpr.t) =
    (* We use a different variable for each occurrence of weak variables *)
    let map,mexpr = Mtexpr.weak_transf Mm.empty e.mexpr in
    let a = add_weak_cp_man man a map in

    let env = prepare_env (Abstract1.env a) e.mexpr in
    let a = Abstract1.change_environment man a env false in
    let e' = Mtexpr.to_aexpr { Mtexpr.mexpr = mexpr;
                               Mtexpr.env = env } in

    Abstract1.bound_texpr man a e'

  let bound_texpr = bound_texpr_man man

  let bound_variable t v = match v with
    | Mvalue (AarrayEl _) ->
      let env = Abstract1.env t in
      bound_texpr t (Mtexpr.var env v)
    | _ -> Abstract1.bound_variable man t (avar_of_mvar v)

  let env_add_mvar env v =
    let add_single v env =
      let av = avar_of_mvar v in
      if Environment.mem_var env av then env
      else
        Environment.add env
          (Array.of_list [av])
          (Array.make 0 (Var.of_string "")) in

    match v with
    | Mvalue (AarrayEl _ ) ->
      List.fold_left
        (fun x y -> add_single y x) env
        (u8_blast_var ~blast_arrays:true v)

    | _ -> add_single v env

  (* Relational assignment. *)
  let assign_expr_rel force a v e =
    (* We use a different variable for each occurrence of weak variables *)
    let map,mexpr = Mtexpr.weak_transf Mm.empty Mtexpr.(e.mexpr) in

    let a = add_weak_cp a map in
    (* We do the same for the variable receiving the assignment *)
    let v_weak = weak_update v && not force in
    let a,v_cp = if v_weak then
        let v_cp = Temp ("weaklv_" ^ string_of_mvar v,0, ty_mvar v) in
        (expand a v [v_cp], v_cp)
      else (a, v) in
    (* If v is not in the environment, we add it *)
    let env = env_add_mvar (Abstract1.env a) v_cp in

    (* We add the variables in mexpr to the environment *)
    let env = prepare_env env mexpr in
    let a = Abstract1.change_environment man a env false in
    let e' = Mtexpr.to_aexpr { Mtexpr.mexpr = mexpr;
                               Mtexpr.env = env } in

    let a = Abstract1.assign_texpr man a (avar_of_mvar v_cp) e' None in

    (* We fold back the added variables *)
    let a = rem_weak_cp a map in
    if v_weak then fold a [v; v_cp] else a


  (* Forced non relational assignment *)
  let assign_expr_norel force a v e =
    (* We do a copy of v if we do a weak assignment *)
    let v_weak = weak_update v && not force in
    let a,v_cp = if v_weak then
        let v_cp = Temp ("weaklv_" ^ string_of_mvar v,0, ty_mvar v) in
        (expand a v [v_cp], v_cp)
      else (a, v) in

    (* If v is not in the environment, we add it *)
    let env = env_add_mvar (Abstract1.env a) v_cp in
    let a = Abstract1.change_environment man a env false in

    let int = Coeff.Interval (bound_texpr a e) in
    let eint = Texpr1.cst env int in

    let a = Abstract1.assign_texpr man a (avar_of_mvar v_cp) eint None in

    (* We fold back v, if needed *)
    if v_weak then fold a [v; v_cp] else a

  let e_complex e =
    (is_relational ()) && (Mtexpr.contains_mod Mtexpr.(e.mexpr))

  let es_complex es = List.exists e_complex es

  (* If the domain is relational, and if e contains a modulo, then we just
     return the interval of variations of e (i.e. we forget all relations
     between v_cp and the other variables). *)
  let assign_expr_aux force a v e =
    if e_complex e then
      assign_expr_norel force a v e
    else assign_expr_rel force a v e


  (* Return the j-th term of the expression e seen in base b = 2^8:
     ((e - (e mod b^j)) / b^j) mod b *)
  let get_block e j =
    let bj = mpq_pow (8 * j) |> Mpqf.of_mpq |> cst_of_mpqf Mtexpr.(e.env)
    and b = mpq_pow 8 |> Mpqf.of_mpq |> cst_of_mpqf Mtexpr.(e.env) in
    (* e - (e mod b^j) *)
    let e1 = Mtexpr.binop Texpr1.Sub e (Mtexpr.binop Texpr1.Mod e bj ) in
    (* e1 / b^j) mod b *)
    Mtexpr.binop Texpr1.Mod ( Mtexpr.binop Texpr1.Div e1 bj) b

  (* If force is true then we do a forced strong update on v. *)
  let assign_expr ?force:(force=false) a v e = match v with
    | Mvalue (AarrayEl (gv,ws,i)) ->
      let offset = (int_of_ws ws) / 8 * i in
      List.fold_left (fun a j ->
          let p = offset + j in
          let mvj = Mvalue (AarrayEl (gv, U8, p)) in
          let mej = get_block e j in
          assign_expr_aux force a mvj mej)
        a (List.init ((int_of_ws ws) / 8) (fun j -> j))

    | _ -> assign_expr_aux force a v e

  module PP = PP(Manager)
      
  let print : ?full:bool -> Format.formatter -> t -> unit =
    fun ?full:(full=false) fmt a ->
      if full && (is_relational ()) then
        Format.fprintf fmt "@[<v 0>@[%a@]@;@]"
          PP.pp a
      (* Abstract1.print a *)
      ;

      let (arr_vars, _) = Environment.vars (Abstract1.env a) in
      let vars = Array.to_list arr_vars in

      let pp_abs fmt v =
        let vi = Abstract1.bound_variable man a v in
        Format.fprintf fmt "@[%s ∊ %a@]"
          (Var.to_string v)
          Interval.print vi in

      let pp_sep fmt () = Format.fprintf fmt "@;" in

      let vars_p = List.filter (fun v ->
          (not (Config.sc_ignore_unconstrained ()) ||
           (not !(Config.sc_nrel_no_print ()) || is_relational ()) &&
           not (Abstract1.is_variable_unconstrained man a v)) &&
          not (variables_ignore v)) vars in

      if vars_p <> [] then
        Format.fprintf fmt "@[<v 0>%a@]" (pp_list ~sep:pp_sep pp_abs) vars_p
      else ()

  (* Precond: env is not empty
     (Box1 seems to not behave correctly on empty env) *)
  let to_box1 : 'a Abstract1.t -> Abstract1.box1 = fun a ->
    let vars,_ = Environment.vars (Abstract1.env a) in
    assert (Array.length vars <> 0);
    Abstract1.to_box man a

  (* Precond: env is not empty
     (Box1 seems to not behave correctly on empty env) *)
  let box1_to_box : Abstract1.box1 -> Box.t Abstract1.t = fun box ->
    let env = box.box1_env in
    let vars,_ = Environment.vars env in
    let bman = BoxManager.man in
    assert (Array.length vars <> 0);
    Abstract1.of_box bman env vars Abstract1.(box.interval_array)
        
  let to_box :  t -> Box.t Abstract1.t = fun a ->
    (* We do this because box1 does not behave correctly on empty env *)
    if Abstract1.is_top man a then 
      top_box (Abstract1.env a)
    else if Abstract1.is_bottom man a then 
      bottom_box (Abstract1.env a)
    else to_box1 a |> box1_to_box

  (* Precond: env is not empty
     (Box1 seems to not behave correctly on empty env) *)
  let of_box1 (box : Abstract1.box1) =
    let env = box.box1_env in
    let vars,_ = Environment.vars env in
    assert (Array.length vars <> 0);
    Abstract1.of_box man env vars Abstract1.(box.interval_array)

  let of_box : Box.t Abstract1.t -> t = fun a ->
    let bman = BoxManager.man in 
    if Abstract1.is_top bman a then 
      Abstract1.top man (Abstract1.env a)
    else if Abstract1.is_bottom bman a then 
      Abstract1.bottom man (Abstract1.env a)
    else
      Abstract1.to_box bman a |> of_box1

  let trivially_false man a c =
    let int = bound_texpr_man man a (Mtcons.get_expr c) in
    let oi = interval_to_int int in

    Utils.omap_dfl (fun i -> match Mtcons.get_typ c with
        | Tcons0.DISEQ -> i = 0
        | Tcons0.EQ -> i <> 0
        | Tcons0.SUP -> i <= 0
        | Tcons0.SUPEQ -> i < 0
        | Tcons0.EQMOD n -> match scalar_to_int n with
          | None -> false
          | Some n -> (i mod n) <> 0
      ) false oi

  let meet_constr_man man a cs =
    let cs = List.filter (fun c -> not (trivially_false man a c)) cs in
    if cs = [] then bottom_man man a
    else
      let map,cs = List.fold_left (fun (map, acc) c ->
          let e = Mtcons.get_expr c in

          (* We use a different variable for each occurrence of weak variables *)
          let map,mexpr = Mtexpr.weak_transf map e.mexpr in

          (* We prepare the expression *)
          let env = prepare_env (Abstract1.env a) mexpr in
          let ae = Mtexpr.to_aexpr { Mtexpr.mexpr = mexpr;
                                     Mtexpr.env = env } in
          let c = Tcons1.make ae (Mtcons.get_typ c) in
          (map, c :: acc)
        ) (Mm.empty,[]) cs in

      let a = add_weak_cp_man man a map in
      let env = List.map Tcons1.get_env cs |> env_lce in

      (* We evaluate the constraint *)
      let c_array = Tcons1.array_make env (List.length cs) in
      List.iteri (fun i c -> Tcons1.array_set c_array i c) cs;

      let a = Abstract1.change_environment man a env false in
      let a = Abstract1.meet_tcons_array man a c_array in

      (* We fold back the added variables *)
      rem_weak_cp_man man a map

  let meet_constr_norel a cs =
    let bman = BoxManager.man in
    let ac = meet_constr_man bman (to_box a) cs
             |> of_box in
    meet a ac

  let meet_constr_list a cs =
    let es = List.map Mtcons.get_expr cs in
    if es_complex es then meet_constr_norel a cs
    else meet_constr_man man a cs

  let meet_constr a c = meet_constr_list a [c]

  let unify a a' = Abstract1.unify man a a'

  let change_environment a mvars =
    let env_vars = u8_blast_vars ~blast_arrays:true mvars
                   |> List.map avar_of_mvar
                   |> Array.of_list
    and empty_var_array = Array.make 0 (Var.of_string "") in
    let new_env = Environment.make env_vars empty_var_array in
    Abstract1.change_environment man a new_env false

  let remove_vars a mvars =
    let vars = Environment.vars (Abstract1.env a)
               |> fst
               |> Array.to_list
    and rem_vars = u8_blast_vars ~blast_arrays:true mvars
                   |> List.map avar_of_mvar  in

    let nvars = List.filter (fun x -> not (List.mem x rem_vars)) vars in
    let new_env = env_of_list nvars in
    
    Abstract1.change_environment man a new_env false

  let get_env a = Abstract1.env a

end
