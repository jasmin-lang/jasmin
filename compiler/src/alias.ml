open Utils
open Printer
open Prog

(* Interval within a variable; [lo; hi[ *)
type slice = { in_var : int ggvar ; range : int * int }

type alias = slice Mv.t

(* --------------------------------------------------- *)
let pp_var fmt x = pp_var ~debug:true fmt x

let pp_ggvar fmt { gv ; gs } =
  Format.fprintf fmt "%s%a" (if gs = Expr.Slocal then "" else "#g:") pp_var (L.unloc gv)

let pp_range fmt (lo, hi) =
  Format.fprintf fmt "%d; %d" lo hi

let pp_slice fmt s =
  Format.fprintf fmt "%a[%a[" pp_ggvar s.in_var pp_range s.range

let pp_binding fmt x s =
  Format.fprintf fmt "%a ↦ %a;@ " pp_var x pp_slice s

let pp_aliasing fmt a =
  Mv.iter (pp_binding fmt) a

let pp_alias fmt a =
  Format.fprintf fmt "{@[<hov>@ %a@]}"
    pp_aliasing a

(* --------------------------------------------------- *)
let size_of_range (lo, hi) = hi - lo

let range_in_slice (lo, hi) { in_var ; range = (u, v) } =
  if u + hi <= v
  then { in_var ; range = u + lo, u + hi }
  else hierror "range_in_slice: range not included"

let range_of_var x =
  0, size_of x.v_ty

let slice_of_var gv =
  let range = range_of_var (L.unloc gv) in
  { in_var = { gv ; gs = E.Slocal } ; range }

let normalize_slice a s =
  let rec loop b s =
    match s with
    | { in_var = { gs = E.Sglob } } as s -> b, s
    | { in_var = { gv } ; range } ->
       let x = L.unloc gv in
       match Mv.find x a with
       | exception Not_found -> b, s
       | s -> loop true (range_in_slice range s)
  in
  let b, s' = loop false s in
  let a' = if b then Mv.add (L.unloc s.in_var.gv) s' a else a in
  a', s'

let range_of_asub aa ws len i =
  match get_ofs aa ws i with
  | None -> assert false
  | Some start -> start, start + arr_size ws len

let normalize_asub a aa ws len gv i =
  normalize_slice a { in_var = { gv ; gs = E.Slocal } ; range = range_of_asub aa ws len i }

(* Partial order on variables, by scope and size *)
let compare_ggvar gx gy =
  if gx = gy
  then 0
  else
    let x = L.unloc gx.gv in
    let y = L.unloc gy.gv in
    let sx = size_of x.v_ty in
    let sy = size_of y.v_ty in
    match gx.gs, gy.gs with
    | E.Sglob, E.Sglob -> assert false
    | E.Sglob, E.Slocal -> assert(sy <= sx); 1
    | E.Slocal, E.Sglob -> assert (sx <= sy); -1
    | E.Slocal, E.Slocal ->
       let c = Stdlib.Int.compare sx sy in
       if c = 0 then V.compare x y
       else c

(* x1[e1:n1] = x2[e2:n2] *)
let merge_slices _loc a s1 s2 =
  (* Format.eprintf "Alias: merging slices at %a: %a and %a@." pp_iloc loc pp_slice s1 pp_slice s2; *)
  assert (size_of_range s1.range = size_of_range s2.range);
  let c = compare_ggvar s1.in_var s2.in_var in
  if c = 0 then (assert (s1 = s2); a)
  else
    if c < 0
    then
      let x = L.unloc s1.in_var.gv in
      let lo = fst s2.range - fst s1.range in
      Mv.add x { s2 with range = lo, lo + size_of x.v_ty } a
    else (* c > 0 *)
      let x = L.unloc s2.in_var.gv in
      let lo = fst s1.range - fst s2.range in
      Mv.add x { s1 with range = lo, lo + size_of x.v_ty } a

let kill a =
  function
  | Lvar x -> assert (not (Mv.mem (L.unloc x) a)); a
  | Lasub _ -> assert false
  | Lnone _ | Lmem _ | Laset _ -> a

let assign_var a x =
  function
  | Pvar ({ gv ; gs = E.Slocal } as in_var) ->
     let a, s =  normalize_slice a { in_var ; range = range_of_var (L.unloc gv) } in
     if L.unloc s.in_var.gv = x
     then a
     else Mv.add x s a
  | Pvar ({ gs = E.Sglob } as in_var) ->
     let range = range_of_var x in
     Mv.add x { in_var ; range } a
  | Parr_init _ -> assert (not (Mv.mem x a)); a
  | Psub (aa, ws, len, y, i) ->
     assert (y.gs = E.Slocal); (* TODO? *)
     let a, s = normalize_asub a aa ws len y.gv i in
     begin match Mv.find x a with
     | exception Not_found -> Mv.add x s a
     | s' -> assert (s = s'); a (* FIXME *)
     end
  | (Pconst _ | Pbool _ | Pget _ | Pload _ | Papp1 _ | Papp2 _ | PappN _ | Pif _) -> assert false

let assign_sub loc a s =
  function
  | Pvar ({ gv ; gs = E.Slocal } as in_var) ->
     let a, s' =  normalize_slice a { in_var ; range = range_of_var (L.unloc gv) } in
     merge_slices loc a s s'
  | _ -> hierror "assign_sub: unexpected RHS"

let assign_arr loc a x e =
  match x with
  | Lvar x -> assign_var a (L.unloc x) e
  | Lasub (aa, ws, len, x, i) ->
     let a, s = normalize_asub a aa ws len x i in
     assign_sub loc a s e
  | Lnone _ | Lmem _ | Laset _ -> a

(** FIXME: union and inclusion test are garbage *)
let merge_slice loc x x1 x2 =
  if x1 = x2 then Some x1
  else
    hierror "Alias: at %a cannot merge slices for variable %a: %a and %a" pp_iloc loc pp_var x pp_slice x1 pp_slice x2

let merge loc a1 a2 =
  Format.eprintf "Merging alias at %a: %a and %a@." pp_iloc loc pp_alias a1 pp_alias a2;
  Mv.merge (fun x s1 s2 ->
      match s1 with
      | None -> s2
      | Some x1 ->
         match s2 with
         | None -> s1
         | Some x2 -> merge_slice loc x x1 x2
    ) a1 a2

let incl_slice loc x x1 x2 =
  if x1 = x2
  then true
  else
    hierror "Alias: at %a cannot compare slices for variable %a: %a and %a" pp_iloc loc pp_var x pp_slice x1 pp_slice x2

exception NotIncluded

let incl loc a1 a2 =
  try
    let _ =
      Mv.merge (fun x s1 s2 ->
          match s1 with
          | None -> Some ()
          | Some x1 ->
             match s2 with
             | None -> raise NotIncluded
             | Some x2 -> if incl_slice loc x x1 x2 then Some () else raise NotIncluded
        ) a1 a2
    in true
  with NotIncluded -> false

let rec analyze_instr cc a loc =
  function
  | Cfor _ -> assert false
  | Ccall (_, xs, fn, es) ->
     List.fold_left2 (fun a x ->
         function
         | None -> kill a x
         | Some n -> assign_arr loc a x (List.nth es n)
       )
       a xs (cc fn).returned_params
  | Cassgn (x, _, ty, e) -> if is_ty_arr ty then assign_arr loc a x e else kill a x
  | Copn (xs, _, _, _) -> List.fold_left kill a xs
  | Cif(_, s1, s2) ->
     let a1 = analyze_stmt cc a s1 in
     let a2 = analyze_stmt cc a s2 in
     merge loc a1 a2
  | Cwhile (_, s1, _, s2) ->
     let rec loop a =
       let a' = a in
       let a' = analyze_stmt cc a' s2 in
       let a' = analyze_stmt cc a' s1 in
       if incl loc a' a
       then a
       else loop (merge loc a' a)
     in loop (analyze_stmt cc a s1)
and analyze_instr_r cc a { i_loc ; i_desc } = analyze_instr cc a i_loc i_desc
and analyze_stmt cc a s =
  List.fold_left (analyze_instr_r cc) a s

let analyze_fd cc fd =
  let a = analyze_stmt cc Mv.empty fd.f_body in
  Format.eprintf "Aliasing forest for function %s:@.%a@." fd.f_name.fn_name pp_alias a

let analyze_prog fds =
  let cc : subroutine_info Hf.t = Hf.create 17 in
  let get_cc = Hf.find cc in
  List.fold_right (fun fd () ->
      begin match fd.f_cc with
      | Subroutine si -> Hf.add cc fd.f_name si
      | Export -> ()
      | Internal -> assert false
      end;
      analyze_fd get_cc fd)
    fds
    ()
