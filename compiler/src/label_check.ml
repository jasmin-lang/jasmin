open Prog 
open Utils


type function_label = {
  loc : L.t;
  fname : string;
}

type duplicate_label_warn = {
  first_decl : function_label;
  conflict_decl : function_label;
}

let pp_duplicate_label_warn fmt {first_decl={loc=first_loc; fname=first_fname}; conflict_decl={loc=_;fname=second_fname}} =
  Format.fprintf fmt
    "Function '%s' and function '%s' (declared at %s) have conflicting assembly label names."
    second_fname
    first_fname
    (Location.tostring first_loc)


let warn_duplicate_label warn = 
  warning Always (L.i_loc0 warn.conflict_decl.loc) "%a" pp_duplicate_label_warn warn

let check_labels_fun (f: ('len,'info,'asm) gfunc) ((errors, label_map): (((duplicate_label_warn list) * function_label Ms.t ))) : (duplicate_label_warn list) * function_label Ms.t = 
  let fn_label = PrintCommon.escape f.f_name.fn_name in
  if f.f_cc != Internal then 
    match Ms.find_opt fn_label label_map with
    | None -> errors, Ms.add fn_label {loc=f.f_loc;fname=f.f_name.fn_name} label_map
    | Some (label) -> 
      let conflict = {first_decl=label; conflict_decl={loc=f.f_loc; fname=f.f_name.fn_name}} in
      conflict::errors, label_map
  else errors,label_map

let get_labels_errors (prog: ('len,'info,'asm) gprog) = 
    fst (List.fold_left (
      fun label_map f -> 
        match f with 
        | MIfun f -> check_labels_fun f label_map
        | _ -> label_map
    ) ([],Ms.empty) prog)