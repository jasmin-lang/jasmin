open Utils
open Prog

module Live = Liveness
module G = IntervalGraphColoring

type liverange = G.graph Mint.t

(* --------------------------------------------------- *)
let pp_var = Printer.pp_var ~debug: true

let pp_range fmt (x, (lo, hi)) =
  Format.fprintf fmt "%a: [%d; %d]" pp_var x lo hi

let pp_ranges fmt (sz, g) =
  Format.fprintf fmt "%d ↦ %a" sz (pp_list "@ " pp_range) (Mv.bindings g)

let pp_color fmt (x, i) =
  Format.fprintf fmt "%a: %a" pp_var x pp_var i

let pp_coloring fmt (sz, c) =
  Format.fprintf fmt "%d ↦ %a" sz (pp_list "@ " pp_color) (Mv.bindings c)

(* --------------------------------------------------- *)
let incr_liverange r x d : liverange =
  let s = size_of x.v_ty in
  let g = Mint.find_default Mv.empty s r in
  let i =
    match Mv.find x g with
    | (lo, hi) -> assert (hi <= d); (lo, d)
    | exception Not_found -> (d, d)
  in
  let g = Mv.add x i g in
  Mint.add s g r

let live_ranges_stmt (alias: Alias.alias) (ptr_classes: Sv.t) d c =

let stack_pointers = Hashtbl.create 117 in

let get_stack_pointer x =
  try Hashtbl.find stack_pointers x
  with Not_found ->
    let r = V.mk x.v_name (Stack Direct) u64 x.v_dloc in
    Hashtbl.add stack_pointers x r;
    r
in

let preprocess_liveset (s: Sv.t) : Sv.t * Sv.t =
  Sv.fold (fun x (s, all) ->
      if is_ty_arr x.v_ty
      then
        let s, all =
          let r = Alias.((normalize_var alias x).in_var) in
          if Sv.mem r ptr_classes
          then s, all
          else Sv.add r s, Sv.add x all
        in
        if is_stk_ptr_kind x.v_kind
        then Sv.add (get_stack_pointer x) s, Sv.add x all
        else s, all
      else
        if is_stack_kind x.v_kind
        then Sv.add x s, Sv.add x all
        else s, all
    ) s (Sv.empty, Sv.empty)
in

let process_live_info d (acc, stack) (i: Sv.t) =
  let process_live_var x acc =
    incr_liverange acc x d
  in
  let i, all = preprocess_liveset i in
  let acc = Sv.fold process_live_var i acc in
  (acc, Sv.union stack all)
in

let rec live_ranges_instr_r d_acc =
  function
  | (Cassgn _ | Copn _ | Ccall _) -> d_acc
  | Cif (_, s1, s2)
  | Cwhile (_, s1, _, s2) ->
     let d_acc = live_ranges_stmt d_acc s1 in
     let d_acc = live_ranges_stmt d_acc s2 in
     d_acc
  | Cfor _ -> assert false
and live_ranges_instr (d, acc) { i_desc ; i_info = before, after } =
  let acc = process_live_info d acc before in
  let d, acc = live_ranges_instr_r (d + 1, acc) i_desc in
  d + 1, process_live_info d acc after
and live_ranges_stmt d_acc s =
  List.fold_left live_ranges_instr d_acc s

in live_ranges_stmt d c, stack_pointers

(* --------------------------------------------------- *)
let check_class ptr_classes args x s =
  let s = Sv.add x s in
  if not (Sv.disjoint args s) && not (Sv.mem x ptr_classes) then
    hierror "cannot put a reg ptr argument into the local stack"

(* --------------------------------------------------- *)
let alloc_stack_fd get_fun fd =
  if !Glob_options.debug then Format.eprintf "alloc_stack %s@." fd.f_name.fn_name;
  let result = fd in
  let alias =
    let get_cc fn =
      match (get_fun fn).f_cc with
      | Subroutine si -> si
      | (Export | Internal) -> assert false
    in
    Alias.analyze_fd get_cc fd in
  let classes = Alias.classes alias in
  let ptr_args = List.fold_left (fun s x -> if is_reg_ptr_kind x.v_kind then Sv.add x s else s) Sv.empty fd.f_args in
  let ptr_classes = Mv.fold (fun x s acc -> if Sv.for_all (fun y -> is_ptr y.v_kind) (Sv.add x s) then Sv.add x acc else acc) classes Sv.empty in
  Mv.iter (check_class ptr_classes ptr_args) classes;
  let fd = Live.live_fd false fd in
  let (_, (ranges, all_stack_vars)), stack_pointers = live_ranges_stmt alias ptr_classes (0, (Mint.empty, Sv.empty)) fd.f_body in
  Format.eprintf "Ranges: %a@." (pp_list "@ " pp_ranges) (Mint.bindings ranges);
  let coloring = Mint.mapi G.solve ranges in
  Format.eprintf "Colors: %a@." (pp_list "@ " pp_coloring) (Mint.bindings coloring);
  Format.eprintf "All stack vars: %a@." (pp_list "@ " pp_var) (Sv.elements all_stack_vars);
  Format.eprintf "alias: %a@." Alias.pp_alias alias;

  let slots = ref Sv.empty in
  let stk = ref Mv.empty in
  let add_slot slot = slots := Sv.add slot !slots in
  let add_stack x slot range = stk := Mv.add x (`Stack (slot,range)) !stk in
  let add_stack_ptr x slot = stk := Mv.add x (`StackPtr slot) !stk in
  let add_glob x slot range = stk := Mv.add x (`Glob (slot,range)) !stk in
  let dovar v =
    match v.v_kind with
    | Stack Direct ->
      if is_ty_arr v.v_ty then
        let c = Alias.normalize_var alias v in
        if c.scope = E.Sglob then     add_glob v c.in_var c.range
        else
          begin
            let sz = size_of c.in_var.v_ty in
            let slot =
              try Mv.find c.in_var (Mint.find sz coloring)
              with Not_found ->
                hierror "%a %a" pp_var v pp_var c.in_var in
            add_slot slot;
            add_stack v slot c.range
          end
      else
        let sz = size_of v.v_ty in
        let slot =
          try Mv.find v (Mint.find sz coloring)
          with Not_found -> assert false in
        add_slot slot;
        add_stack v slot (0, sz)

    | Stack (Pointer _) ->
      let xp =
        try Hashtbl.find stack_pointers v
        with Not_found -> assert false in
      let sz = size_of xp.v_ty in
      let slot =
        try Mv.find xp (Mint.find sz coloring)
        with Not_found -> assert false in
      add_slot slot;
      add_stack_ptr v slot
    | _ -> () in
  Sv.iter dovar all_stack_vars;

  Format.eprintf "slots = %a@." (pp_list "@ " pp_var) (Sv.elements !slots);
  let pp_stk fmt (x, stkk) =
    match stkk with
    | `Glob  (y, r) -> Format.fprintf fmt "%a -> %%G%a" pp_var x pp_range (y,r)
    | `Stack (y, r) -> Format.fprintf fmt "%a -> %a" pp_var x pp_range (y,r)
    | `StackPtr y -> Format.fprintf fmt "%a |-> %a" pp_var x pp_var y in
  Format.eprintf "Stk : @[<v>%a@]@." (pp_list "@ " pp_stk) (Mv.bindings !stk);

  result
