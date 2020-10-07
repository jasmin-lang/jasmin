open Utils
      
(* Information attached to instructions. *)
type minfo = { i_instr_number : int; }

type overlap = { program_point    : int;
                 never_overlaps   : Sint.t;
                 always_overlaps  : Sint.t;
                 overlaps_checked : Sint.t; }

type annot_prog =
  { annot_stmt : (Prog.ty, (minfo * overlap)) Prog.gstmt;
    annot_return : overlap; }

let merge o o' =
  assert (o.program_point = o'.program_point);
  { program_point    = o.program_point;
    never_overlaps   = Sint.inter o.never_overlaps  o'.never_overlaps;
    always_overlaps  = Sint.inter o.always_overlaps o'.always_overlaps;
    overlaps_checked = Sint.union o.overlaps_checked o'.overlaps_checked}

let pp_overlap fmt o =
  let pp_pp fmt i =
    if i = -2
    then  Format.fprintf fmt "[Return]"
    else Format.fprintf fmt "%d" i in

  let rec pp_list ?sep:(msep = Format.pp_print_space) pp_el fmt l = match l with
  | [] -> Format.fprintf fmt ""
  | h :: t -> Format.fprintf fmt "%a%a%a" pp_el h msep ()
                  (pp_list ~sep:msep pp_el) t
  in
                    
  let pp_set s fmt si =
    if Sint.is_empty si then ()
    else
      Format.fprintf fmt "@[<hov 2>%a: %s: %a@]@;"
        pp_pp o.program_point s
        (pp_list (fun fmt i -> Format.fprintf fmt "%d" i))
        (Sint.elements si)
  in

  if Sint.is_empty o.overlaps_checked then
    Format.fprintf fmt "%a: "
      pp_pp o.program_point
  else
    Format.fprintf fmt "@;@[<v 0>%a%a%a%a: @]"
      (pp_set "never aliases") o.never_overlaps
      (pp_set "always aliases") o.always_overlaps
      (pp_set "checked aliasing with") o.overlaps_checked
      pp_pp o.program_point