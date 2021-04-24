open Utils
open X86_sem
open Cost
open Cost_linear
open Format

let string_of_pelem_ tbl =
  function
  | LblF fn -> Ppasm.string_of_funname tbl fn
  | LblL -> "L"
  | LblB b -> if b then "T" else "F"

let pp_pelem tbl fmt (p, n) =
  fprintf fmt "%s.%d" (string_of_pelem_ tbl p) (Conv.int_of_nat n)

let pp_bpath tbl = pp_list ":" (pp_pelem tbl)

let pp_cost tbl fmt (x: Cost.Sm.t) : unit =
  Cost.Sm.Ml.fold (fun k v () ->
      let k : pelem list = Obj.magic k in
      fprintf fmt "[%a] ↦ [%a];@ " (pp_bpath tbl) k (pp_bpath tbl) v
      )
    x ()

let pp_linear_cost tbl fmt (x: Cost_linear.Sm.t) : unit =
  Cost_linear.Sm.Ml.fold (fun k v () ->
      let k : Datatypes.nat = Obj.magic k in
      fprintf fmt "%d ↦ [%a];@ " (Conv.int_of_nat k) (pp_bpath tbl) v
    )
    x ()

let labels (body: asm list) =
  let h : (int, unit) Hashtbl.t = Hashtbl.create 97 in
  List.iteri (fun i ->
      function
      | LABEL _ -> Hashtbl.add h i ()
      | _ -> ()) body;
  h

(* Linear combination of source counters *)
let summarize_linear_cost body (x: Cost_linear.Sm.t) =
  let labels = labels body in
  let h : (scost, int) Hashtbl.t = Hashtbl.create 97 in
  Cost_linear.Sm.Ml.fold (fun k v () ->
      let k : Datatypes.nat = Obj.magic k in
      if not (Hashtbl.mem labels (Conv.int_of_nat k))
      then match Hashtbl.find h v with
           | exception Not_found -> Hashtbl.add h v 1
           | n -> Hashtbl.replace h v (n + 1)
    ) x ();
  h

let pp_result tbl fmt : (scost, int) Hashtbl.t -> unit =
  Hashtbl.iter (fun p n ->
      fprintf fmt "[%a] × %d@." (pp_bpath tbl) p n
    )

let extra_asm_cost fd : int =
  let tosave, saved_stack = fd.xfd_extra in
  (* save / restore callee-saved registers *)
  2 * List.length tosave
  + match saved_stack with
    | SavedStackNone  -> 0
    | SavedStackReg _ -> (* save RSP, sub, and, restore RSP *) 4
    | SavedStackStk _ -> (* save RSP to RBP, sub, and, save RBP, restore RSP *) 5

let pp tbl (fn, fd) fmt tr : unit =
  fprintf fmt "Global cost transformer for function %s:@." (Ppasm.string_of_funname tbl fn);
  match transform_costs_l tr with
  | None -> failwith "error message"
  | Some m ->
     (* pp_linear_cost tbl fmt (m fn) *)
     let c = summarize_linear_cost fd.xfd_body (m fn) in
     pp_result tbl fmt c;
     fprintf fmt "ASM cost (prologue/epilogue): %d.@." (extra_asm_cost fd)
