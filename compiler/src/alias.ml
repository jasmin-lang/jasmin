open Utils
open Printer
open Prog

(* Interval within a variable; [lo; hi[ *)
type slice = { in_var : var ; scope : E.v_scope  ; range : int * int }

type alias = slice Mv.t

(* --------------------------------------------------- *)
let pp_var fmt x = pp_var ~debug:true fmt x

let pp_scope fmt s =
  Format.fprintf fmt "%s" (if s = E.Slocal then "" else "#g:")

let pp_range fmt (lo, hi) =
  Format.fprintf fmt "%d; %d" lo hi

let pp_slice fmt s =
  Format.fprintf fmt "%a%a[%a[" pp_scope s.scope pp_var s.in_var pp_range s.range

let pp_binding fmt x s =
  Format.fprintf fmt "%a ↦ %a;@ " pp_var x pp_slice s

let pp_aliasing fmt a =
  Mv.iter (pp_binding fmt) a

let pp_alias fmt a =
  Format.fprintf fmt "{@[<hov>@ %a@]}"
    pp_aliasing a

(* --------------------------------------------------- *)
let size_of_range (lo, hi) = hi - lo

let range_in_slice (lo, hi) s =
  let (u, v) = s.range in
  if u + hi <= v
  then { s with range = u + lo, u + hi }
  else hierror "range_in_slice: range not included"

let range_of_var x =
  0, size_of x.v_ty

let slice_of_var ?(scope=E.Slocal) in_var =
  let range = range_of_var in_var in
  { in_var ; scope ; range }

let rec normalize_var a x =
  match Mv.find x a with
  | exception Not_found -> slice_of_var x
  | s -> normalize_slice a s
and normalize_slice a =
  function
  | { scope = E.Sglob } as s -> s
  | { in_var ; range } ->
     range_in_slice range (normalize_var a in_var)

let normalize_gvar a { gv ; gs } =
  let x = L.unloc gv in
  if gs = E.Sglob then slice_of_var ~scope:gs x
  else normalize_var a x

let normalize_map a : alias =
  Mv.fold (fun x s acc ->
      Mv.add x (normalize_slice a s) acc
    ) a Mv.empty

exception NotIncluded

(* Precondition: both maps are normalized *)
let incl a1 a2 =
  (* Format.eprintf "%a ≤ %a ?@." pp_alias a1 pp_alias a2; *)
  try
    let _ =
      Mv.merge (fun _x s1 s2 ->
          match s1 with
          | None -> None
          | Some x1 ->
             match s2 with
             | None -> raise NotIncluded
             | Some x2 -> if x1 = x2 then None else raise NotIncluded
        ) a1 a2
    in true
  with NotIncluded -> false

(* Partial order on variables, by scope and size *)
let compare_gvar x gx y gy =
  if V.equal x y
  then (assert (gx = gy); 0)
  else
    let sx = size_of x.v_ty in
    let sy = size_of y.v_ty in
    match gx, gy with
    | E.Sglob, E.Sglob -> assert false
    | E.Sglob, E.Slocal -> assert(sy <= sx); 1
    | E.Slocal, E.Sglob -> assert (sx <= sy); -1
    | E.Slocal, E.Slocal ->
       let c = Stdlib.Int.compare sx sy in
       if c = 0 then V.compare x y
       else c

(* Precondition: s1 and s2 are normal forms (aka roots) in a *)
(* x1[e1:n1] = x2[e2:n2] *)
let merge_slices a s1 s2 =
  (* Format.eprintf "Alias: merging slices at %a: %a and %a@." pp_iloc loc pp_slice s1 pp_slice s2; *)
  assert (size_of_range s1.range = size_of_range s2.range);
  let c = compare_gvar s1.in_var s1.scope s2.in_var s2.scope in
  if c = 0 then (assert (s1 = s2); a)
  else
    let s1, s2 = if c < 0 then s1, s2 else s2, s1 in
    let x = s1.in_var in
    let lo = fst s2.range - fst s1.range in
    Mv.add x { s2 with range = lo, lo + size_of x.v_ty } a

(* Precondition: both maps are normalized *)
let merge a1 a2 =
  Mv.fold (fun x s a ->
      let s1 = normalize_slice a s in
      let s2 = normalize_slice a (slice_of_var x) in
      merge_slices a s1 s2
    ) a1 a2

let range_of_asub aa ws len i =
  match get_ofs aa ws i with
  | None -> assert false
  | Some start -> start, start + arr_size ws len

let normalize_asub a aa ws len x i =
  let s = normalize_gvar a x in
  range_in_slice (range_of_asub aa ws len i) s

let slice_of_pexpr a =
  function
  | Parr_init _ -> None
  | Pvar x -> Some (normalize_gvar a x)
  | Psub (aa, ws, len, x, i) -> Some (normalize_asub a aa ws len x i)
  | (Pconst _ | Pbool _ | Pget _ | Pload _ | Papp1 _ | Papp2 _ | PappN _ | Pif _) -> assert false

let slice_of_lval a =
  function
  | Lvar x -> Some (normalize_var a (L.unloc x))
  | Lasub (aa, ws, len, gv, i) -> Some (normalize_asub a aa ws len { gv ; gs = E.Slocal } i)
  | (Lmem _ | Laset _ | Lnone _) -> None

let assign_arr a x e =
  match slice_of_lval a x, slice_of_pexpr a e with
  | None, _ | _, None -> a
  | Some d, Some s -> merge_slices a d s

let rec analyze_instr_r cc a =
  function
  | Cfor _ -> assert false
  | Ccall (_, xs, fn, es) ->
     List.fold_left2 (fun a x ->
         function
         | None -> a
         | Some n -> assign_arr a x (List.nth es n)
       )
       a xs (cc fn).returned_params
  | Cassgn (x, _, ty, e) -> if is_ty_arr ty then assign_arr a x e else a
  | Copn _ -> a
  | Cif(_, s1, s2) ->
     let a1 = analyze_stmt cc a s1 |> normalize_map in
     let a2 = analyze_stmt cc a s2 |> normalize_map in
     merge a1 a2
  | Cwhile (_, s1, _, s2) ->
     (* Precondition: a is in normal form *)
     let rec loop a =
       let a' = a in
       let a' = analyze_stmt cc a' s2 in
       let a' = analyze_stmt cc a' s1 in
       let a' = normalize_map a' in
       if incl a' a
       then a'
       else loop (merge a' a |> normalize_map)
     in loop (analyze_stmt cc a s1 |> normalize_map)
and analyze_instr cc a { i_loc ; i_desc } =
  try analyze_instr_r cc a i_desc
  with HiError e -> hierror "At %a: %s" pp_iloc i_loc e
and analyze_stmt cc a s =
  List.fold_left (analyze_instr cc) a s

let analyze_fd cc fd =
  let a = analyze_stmt cc Mv.empty fd.f_body |> normalize_map in
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
