open Utils
open Prog
    
open SafetyUtils
open SafetyVar
open SafetyInterfaces

(*****************************)
(* Points-to Abstract Domain *)
(*****************************)

let pp_memloc fmt = function MemLoc v -> Format.fprintf fmt "%s" v.v_name

let pp_memlocs fmt l =
  pp_list ~sep:(fun fmt () -> Format.fprintf fmt "@ ") pp_memloc fmt l

let pp_ptr fmt = function
  | Ptrs m -> Format.fprintf fmt "%a" pp_memlocs m
  | TopPtr -> Format.fprintf fmt "#TopPtr"




module PointsToImpl : PointsTo = struct
  (* Points-to abstract value *)
  type t = { pts : mem_loc list Ms.t }
             (* top : mem_loc list } *)

  let make mls =
    let string_of_var v = match v.v_ty with
      | Arr _ -> raise (Aint_error "Array(s) in export function's inputs")
      | Bty _ -> string_of_mvar (Mvalue (Avar v)) in

    let pts = List.fold_left (fun pts x -> match x with
        | MemLoc v -> Ms.add (string_of_var v) [x] pts)
        Ms.empty mls in
    { pts = pts }
    (* { pts = pts ; top = mls } *)

  let meet : t -> t -> t = fun t t' ->
    let pts'' =
      Ms.merge (fun _ aop bop -> match aop,bop with
          | None, x | x, None -> x (* None corresponds to TopPtr *)

          | Some l, Some l' ->
            let l_inter = List.filter (fun x -> List.mem x l') l in
            Some (List.sort_uniq Stdlib.compare l_inter )
        ) t.pts t'.pts in

    { t with pts = pts'' }

  let join : t -> t -> t = fun t t' ->
    let pts'' =
      Ms.merge (fun _ aop bop -> match aop,bop with
          | None, _ | _, None -> None (* None corresponds to TopPtr *)

          | Some l, Some l' ->
            Some (List.sort_uniq Stdlib.compare (l @ l'))
        ) t.pts t'.pts in

    { t with pts = pts'' }

  let widening t t' = join t t'

  let svar_points_to : t -> string -> ptrs = fun t s_var ->
    if Ms.mem s_var t.pts then Ptrs (Ms.find s_var t.pts)
    else TopPtr

  let var_points_to : t -> mvar -> ptrs = fun t var ->
    (* We correctly tracked points-to information only for 
       variables (e.g. array elements are not properly handled, and
       consequently can point to anybody.). *)
    match var with
    | Mvalue (Avar _) -> svar_points_to t (string_of_mvar var)
    | _ -> TopPtr

  let forget_list : t -> mvar list -> t = fun t l_rem ->
    let l_rem = u8_blast_vars ~blast_arrays:true l_rem in
    let vl_rem = List.map string_of_mvar l_rem in
    { t with pts = Ms.filter (fun v _ -> not (List.mem v vl_rem)) t.pts }

  let is_included : t -> t -> bool = fun t t' ->
    Ms.for_all (fun v l ->
        if not (Ms.mem v t'.pts) then true
        else
          let l' = Ms.find v t'.pts in
          List.for_all (fun x -> List.mem x l') l
      ) t.pts

  (* let top_mem_loc : t -> mem_loc list = fun t -> t.top *)

  let join_ptrs_list ptrss =
    let rec aux acc = function
      | [] -> Ptrs (List.sort_uniq Stdlib.compare acc)
      | TopPtr :: _ -> TopPtr
      | Ptrs l :: tail -> aux (l @ acc) tail in

    aux [] ptrss

  let pt_assign : t -> string -> ptrs -> t = fun t v ptrs -> match ptrs with
    | Ptrs vpts -> { t with pts = Ms.add v vpts t.pts }
    | TopPtr -> { t with pts = Ms.remove v t.pts }

  let assign_ptr_expr : t -> mvar -> ptr_expr -> t = fun t v e -> match e with
    | PtTopExpr -> { t with pts = Ms.remove (string_of_mvar v) t.pts }
    | PtVars el ->
      let v_pts =
        List.fold_left (fun acc var ->
            var_points_to t var :: acc) [] el
        |> join_ptrs_list in

      pt_assign t (string_of_mvar v) v_pts

  let print ppf t =
    Format.fprintf ppf "@[<hov 4>* Points-to:@ %a@]@;"
      (pp_list ~sep:(fun _ _ -> ()) (fun ppf (k,l) ->
           if l <> [] then
             Format.fprintf ppf "(%s → %a);@,"
               k pp_memlocs l;))
      (List.filter (fun (x,_) -> not (svariables_ignore x)) (Ms.bindings t.pts))

end
