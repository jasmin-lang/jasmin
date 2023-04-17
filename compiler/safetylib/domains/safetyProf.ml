open SafetyUtils
open SafetyInterfaces

(*------------------------------------------------------------*)
(* Profiling *)

module Prof : sig
  val record : string -> unit
  val is_recorded : string -> bool
  val call : string -> float -> unit
  val reset_all : unit -> unit

  val print : Format.formatter -> unit -> unit
end = struct
  let lrec = ref []

  let record s =
    let () = assert (not (List.mem_assoc s !lrec)) in
    lrec := (s,(0,0.)) :: !lrec
              
  let is_recorded s = List.mem_assoc s !lrec

  let call s t =
    lrec := assoc_up s (fun (x,t') -> (x + 1,t +. t')) !lrec
  
  let reset_all () = lrec := []

  let print fmt () =
    let pp_el fmt (a, (b,f)) =
      Format.fprintf fmt "%10d %s : %1f seconds" b a f in

    Format.fprintf fmt "@[<v>Statistiques:@;@[<v>%a@]@]@."
      (pp_list pp_el) (List.sort (fun (a,(_,f)) (a',(_,f')) ->
          if a = a' then 0
          else if f > f' then -1 else 1) !lrec)
end

(*------------------------------------------------------------*)
(* Numerical Domain With Profiling *)

module type NumWrap = sig
  val prefix : string
  module Num : AbsNumType
end

module MakeAbsNumProf (A : NumWrap) : AbsNumType with type t = A.Num.t = struct
  include A.Num

  (*----------------------------------------------------------------*)
  (* Profiling for the new functions. *)
  let record s = Prof.record (A.prefix^s) 

  let call s = Prof.call (A.prefix^s)   


  (*----------------------------------------------------------------*)
  let () = record "make"
  let make x =
    let t = Sys.time () in
    let r = A.Num.make x in
    let () = call "make" (Sys.time () -. t) in
    r

  let () = record "is_bottom"
  let is_bottom x =
    let t = Sys.time () in
    let r = A.Num.is_bottom x in
    let () = call "is_bottom" (Sys.time () -. t) in
    r

  let () = record "bottom"
  let bottom x =
    let t = Sys.time () in
    let r = A.Num.bottom x in
    let () = call "bottom" (Sys.time () -. t) in
    r

  let () = record "meet_list"
  let meet_list x =
    let t = Sys.time () in 
    let r = A.Num.meet_list x in
    let () = call "meet_list" (Sys.time () -. t) in
    r

  let () = record "join_list"
  let join_list x =
    let t = Sys.time () in
    let r = A.Num.join_list x in
    let () = call "join_list" (Sys.time () -. t) in
    r

  let () = record "meet"
  let meet x y =
    let t = Sys.time () in
    let r = A.Num.meet x y in
    let () = call "meet" (Sys.time () -. t) in
    r

  let () = record "join"
  let join x y =
    let t = Sys.time () in
    let r = A.Num.join x y in
    let () = call "join" (Sys.time () -. t) in
    r

  let () = record "widening"
  let widening x y =
    let t = Sys.time () in
    let r = A.Num.widening x y in
    let () = call "widening" (Sys.time () -. t) in
    r

  let () = record "is_included"
  let is_included x y =
    let t = Sys.time () in
    let r = A.Num.is_included x y in
    let () = call "is_included" (Sys.time () -. t) in
    r

  let () = record "forget_list"
  let forget_list x y =
    let t = Sys.time () in
    let r = A.Num.forget_list x y in
    let () = call "forget_list" (Sys.time () -. t) in
    r

  let () = record "fold"
  let fold x y =
    let t = Sys.time () in
    let r = A.Num.fold x y in
    let () = call "fold" (Sys.time () -. t) in
    r

  let () = record "bound_variable"
  let bound_variable x y =
    let t = Sys.time () in
    let r = A.Num.bound_variable x y in
    let () = call "bound_variable" (Sys.time () -. t) in
    r

  let () = record "bound_texpr"
  let bound_texpr x y =
    let t = Sys.time () in
    let r = A.Num.bound_texpr x y in
    let () = call "bound_texpr" (Sys.time () -. t) in
    r

  let () = record "meet_constr"
  let meet_constr x y =
    let t = Sys.time () in
    let r = A.Num.meet_constr x y in
    let () = call "meet_constr" (Sys.time () -. t) in
    r

  let () = record "sat_constr"
  let sat_constr x y =
    let t = Sys.time () in
    let r = A.Num.sat_constr x y in
    let () = call "sat_constr" (Sys.time () -. t) in
    r

  let () = record "unify"
  let unify x y =
    let t = Sys.time () in
    let r = A.Num.unify x y in
    let () = call "unify" (Sys.time () -. t) in
    r

  let () = record "expand"
  let expand x y z =
    let t = Sys.time () in
    let r = A.Num.expand x y z in
    let () = call "expand" (Sys.time () -. t) in
    r

  let () = record "assign_expr"
  let assign_expr ?force:(force=false) x y =
    let t = Sys.time () in
    let r = A.Num.assign_expr ~force:force x y in
    let () = call "assign_expr" (Sys.time () -. t) in
    r

  let () = record "to_box"
  let to_box x =
    let t = Sys.time () in
    let r = A.Num.to_box x in
    let () = call "to_box" (Sys.time () -. t) in
    r

  let () = record "of_box"
  let of_box x =
    let t = Sys.time () in
    let r = A.Num.of_box x in
    let () = call "of_box" (Sys.time () -. t) in
    r

end

 
(*---------------------------------------------------------------*)
module type DisjWrap = sig
  val prefix : string
  module Num : AbsDisjType
end

module MakeAbsDisjProf (A : DisjWrap) : AbsDisjType = struct
  module AProf = MakeAbsNumProf (struct
      let prefix = A.prefix
      module Num = struct
        include A.Num
        let of_box _ = assert false
      end
    end)

  include AProf

  let of_box         = A.Num.of_box
  let new_cnstr_blck = A.Num.new_cnstr_blck
  let add_cnstr      = A.Num.add_cnstr
  let pop_cnstr_blck = A.Num.pop_cnstr_blck
  let pop_all_blcks  = A.Num.pop_all_blcks
  let to_shape       = A.Num.to_shape
  let top_no_disj    = A.Num.top_no_disj
  let remove_disj    = A.Num.remove_disj
  let set_rel        = A.Num.set_rel
  let set_unrel      = A.Num.set_unrel
  let dom_st_update  = A.Num.dom_st_update
                         
  (*----------------------------------------------------------------*)
  (* Profiling for the new functions. *)
  let record s = Prof.record ("D."^s) 

  let call s = Prof.call ("D."^s) 

  (*----------------------------------------------------------------*)
  let () = record "of_box"
  let of_box x y =
    let t = Sys.time () in
    let r = of_box x y in
    let () = call "of_box" (Sys.time () -. t) in
    r

  let () = record "to_shape"
  let to_shape x y =
    let t = Sys.time () in
    let r = to_shape x y in
    let () = call "to_shape" (Sys.time () -. t) in
    r

  let () = record "top_no_disj"
  let top_no_disj x =
    let t = Sys.time () in
    let r = top_no_disj x in
    let () = call "top_no_disj" (Sys.time () -. t) in
    r

  let () = record "remove_disj"
  let remove_disj x =
    let t = Sys.time () in
    let r = remove_disj x in
    let () = call "remove_disj" (Sys.time () -. t) in
    r

  let () = record "new_cnstr_blck"
  let new_cnstr_blck x =
    let t = Sys.time () in
    let r = new_cnstr_blck x in
    let () = call "new_cnstr_blck" (Sys.time () -. t) in
    r

  let () = record "add_cnstr"
  let add_cnstr x ~meet y z =
    let t = Sys.time () in
    let r = add_cnstr x ~meet y z in
    let () = call "add_cnstr" (Sys.time () -. t) in
    r

  let () = record "pop_cnstr_blck"
  let pop_cnstr_blck x loc =
    let t = Sys.time () in
    let r = pop_cnstr_blck x loc in
    let () = call "pop_cnstr_blck" (Sys.time () -. t) in
    r

  let () = record "pop_all_blcks"
  let pop_all_blcks x =
    let t = Sys.time () in
    let r = pop_all_blcks x in
    let () = call "pop_all_blcks" (Sys.time () -. t) in
    r

  let () = record "set_rel"
  let set_rel x v =
    let t = Sys.time () in
    let r = set_rel x v in
    let () = call "set_rel" (Sys.time () -. t) in
    r

  let () = record "set_unrel"
  let set_unrel x v =
    let t = Sys.time () in
    let r = set_unrel x v in
    let () = call "set_unrel" (Sys.time () -. t) in
    r

  let () = record "dom_st_update"
  let dom_st_update x v l =
    let t = Sys.time () in
    let r = dom_st_update x v l in
    let () = call "dom_st_update" (Sys.time () -. t) in
    r

end
