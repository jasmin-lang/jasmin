open Utils
open Printer
open Prog
open Wsize

let hierror = hierror ~kind:"compilation error" ~sub_kind:"stack allocation"
(* Most of the errors have no location initially, but they are added later
   by catching the exception and reemiting it with more information. *)
let hierror_no_loc ?funname = hierror ~loc:Lnone ?funname

type sub_slice_kind =
  | Exact
    (* the range is exact *)
  | Sub of Wsize.wsize
    (* the precise offset is not known, we remember that it is a subpart
       and its alignment *)

type slice = { in_var : var ; scope : E.v_scope ; range : int * int; kind : sub_slice_kind }

type alias = slice Mv.t

(* --------------------------------------------------- *)
let pp_var fmt x = pp_var ~debug:!Glob_options.debug fmt x

let pp_scope fmt s =
  Format.fprintf fmt "%s" (if s = E.Slocal then "" else "#g:")

let pp_range fmt (lo, hi) =
  Format.fprintf fmt "%d; %d" lo hi

let pp_slice fmt s =
  match s.kind with
  | Exact ->
    Format.fprintf fmt "%a%a[%a[" pp_scope s.scope pp_var s.in_var pp_range s.range
  | Sub ws ->
   Format.fprintf fmt "%a%a ⊆ [%a[ (aligned on %a)" pp_scope s.scope pp_var s.in_var pp_range s.range PrintCommon.pp_wsize ws

let pp_binding fmt x s =
  Format.fprintf fmt "%a ↦ %a;@ " pp_var x pp_slice s

let pp_aliasing fmt a =
  Mv.iter (pp_binding fmt) a

let pp_alias fmt a =
  Format.fprintf fmt "{@[<hov>@ %a@]}"
    pp_aliasing a

(* --------------------------------------------------- *)
let align_of_offset lo =
  if lo land 0x1f = 0 then U256
  else if lo land 0xf = 0 then U128
  else if lo land 0x7 = 0 then U64
  else if lo land 0x3 = 0 then U32
  else if lo land 0x1 = 0 then U16
  else U8

let wsize_min = Utils0.cmp_min wsize_cmp

let range_in_slice (lo, hi) kind s =
  match kind, s.kind with
  | Exact, Exact ->
      let (u, v) = s.range in
      if u + hi <= v
      then { s with range = u + lo, u + hi }
      else
        hierror_no_loc "cannot access the subarray [%a[ of %a, the access overflows, your program is probably unsafe"
          pp_range (lo, hi) pp_slice s
  | Sub ws, Exact ->
      { s with kind = Sub (wsize_min ws (align_of_offset (fst s.range))) }
  | Exact, Sub ws ->
      { s with kind = Sub (wsize_min ws (align_of_offset lo)) }
  | Sub ws1, Sub ws2 ->
      { s with kind = Sub (wsize_min ws1 ws2) }

let range_of_var x =
  0, size_of x.v_ty

let slice_of_var ?(scope=E.Slocal) in_var =
  let range = range_of_var in_var in
  { in_var ; scope ; range; kind = Exact }

let rec normalize_var a x =
  match Mv.find x a with
  | exception Not_found -> slice_of_var x
  | s -> normalize_slice a s
and normalize_slice a s =
  if s.scope = E.Sglob then s
  else
    range_in_slice s.range s.kind (normalize_var a s.in_var)

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
let compare_gvar params x gx y gy =
  let check_size kind x1 s1 x2 s2 =
    if not (s1 <= s2) then
      hierror_no_loc "cannot merge a %s and a local that is larger (%a of size %i, and %a of size %i)"
        kind pp_var x2 s2 pp_var x1 s1
  in

  if V.equal x y
  then (assert (gx = gy); 0)
  else
    let sx = size_of x.v_ty in
    let sy = size_of y.v_ty in
    match gx, gy with
    | E.Sglob, E.Sglob -> 
      hierror_no_loc "cannot merge two globals (%a and %a)" pp_var x pp_var y
    | E.Sglob, E.Slocal -> 
      if (Sv.mem y params) then hierror_no_loc "cannot merge a global and a param (%a and %a)" pp_var x pp_var y;
      check_size "global" y sy x sx;
      1
    | E.Slocal, E.Sglob -> 
      if (Sv.mem x params) then hierror_no_loc "cannot merge a param and a global (%a and %a)" pp_var x pp_var y;
      check_size "global" x sx y sy;
      -1
    | E.Slocal, E.Slocal ->
      match Sv.mem x params, Sv.mem y params with
      | true, true -> 
        hierror_no_loc "cannot merge two params (%a and %a)" pp_var x pp_var y;
      | true, false -> check_size "param" y sy x sx; 1
      | false, true -> check_size "param" x sx y sy; -1
      | false, false ->
        let c = Stdlib.Int.compare sx sy in
        if c = 0 then
          match is_ptr x.v_kind, is_ptr y.v_kind with
          | true, false -> -1
          | false, true -> 1
          | _, _ -> V.compare x y
        else c

(* Precondition: s1 and s2 are normal forms (aka roots) in a *)
(* x1[e1:n1] = x2[e2:n2] *)
let merge_slices params a s1 s2 =
  let c = compare_gvar params s1.in_var s1.scope s2.in_var s2.scope in
  if c = 0 then
    (* in particular, s1.in_var and s2.in_var are the same variable *)
    if s1 = s2 || s1.kind <> Exact || s2.kind <> Exact then
      (* when s1.kind or s2.kind is Sub _, we cannot be precise, we prefer not to fail, and we don't update a *)
      a
    else
      hierror_no_loc "cannot merge distinct slices of the same array: %a and %a" pp_slice s1 pp_slice s2
  else
    let s1, s2 = if c < 0 then s1, s2 else s2, s1 in
    let x = s1.in_var in
    let y = s2.in_var in
    let lo = fst s2.range - fst s1.range in
    let hi = lo + size_of x.v_ty in
    if lo < 0 || size_of y.v_ty < hi
    then hierror_no_loc "merging slices %a and %a may introduce invalid accesses; consider declaring variable %a smaller" pp_slice s1 pp_slice s2 pp_var x;
    Mv.add x { s2 with range = lo, hi; kind = s1.kind } a

(* Precondition: both maps are normalized *)
let merge params a1 a2 =
  Mv.fold (fun x s a ->
      let s1 = normalize_slice a s in
      let s2 = normalize_slice a (slice_of_var x) in
      merge_slices params a s1 s2
    ) a1 a2

let range_of_asub aa ws len _gv i =
  match get_ofs aa ws i with
  | None ->
      let range = (0, arr_size ws len) in
      let kind =
        begin match aa with
        | AAscale -> Sub ws
        | AAdirect -> Sub U8
        end
      in
      range, kind
  | Some start -> (start, start + arr_size ws len), Exact

let normalize_asub a aa ws len x i =
  let s = normalize_gvar a x in
  let range, kind = range_of_asub aa ws len x.gv i in
  range_in_slice range kind s

let slice_of_pexpr a =
  function
  | Parr_init _ -> None
  | Pvar x -> Some (normalize_gvar a x)
  | Psub (aa, ws, len, x, i) -> Some (normalize_asub a aa ws len x i)
  | (Pconst _ | Pbool _ | Pget _ | Pload _ | Papp1 _ | Papp2 _ | PappN _ ) -> assert false
  | Pif _ -> hierror_no_loc "conditional move of (ptr) arrays is not supported yet"

let slice_of_lval a =
  function
  | Lvar x -> Some (normalize_var a (L.unloc x))
  | Lasub (aa, ws, len, gv, i) -> Some (normalize_asub a aa ws len { gv ; gs = E.Slocal } i)
  | (Lmem _ | Laset _ | Lnone _) -> None

let assign_arr params a x e =
  match slice_of_lval a x, slice_of_pexpr a e with
  | None, _ | _, None -> a
  | Some d, Some s -> merge_slices params a d s

let syscall_cc (o : 'a Syscall_t.syscall_t) =
  match o with
  | Syscall_t.RandomBytes _ -> [Some 0]

let link_array_return params a xs es cc =
  List.fold_left2 (fun a x ->
          function
          | None -> a
          | Some n -> assign_arr params a x (List.nth es n)
        )
        a xs cc

let opn_cc o = 
  match o with
  | Sopn.Oslh (SLHprotect_ptr_fail _) -> Some [Some 0]
  | Sopn.Opseudo_op(Pseudo_operator.Oswap _) -> Some [Some 1; Some 0]
  | _ -> None 

let rec analyze_instr_r params cc a =
  function
  | Cfor _ -> assert false
  | Ccall (xs, fn, es) -> link_array_return params a xs es (cc fn)
  | Csyscall (xs, o, es) -> link_array_return params a xs es (syscall_cc o)
  | Cassgn (x, _, ty, e) -> if is_ty_arr ty then assign_arr params a x e else a
  | Copn (xs, _, o, es) -> 
    (* A special case for operators that can return array *)
    begin match opn_cc o with 
    | None -> a 
    | Some l -> link_array_return params a xs es l
    end
  | Cif(_, s1, s2) ->
     let a1 = analyze_stmt params cc a s1 |> normalize_map in
     let a2 = analyze_stmt params cc a s2 |> normalize_map in
     merge params a1 a2
  | Cwhile (_, s1, _, _, s2) ->
     (* Precondition: a is in normal form *)
     let rec loop a =
       let a' = a in
       let a' = analyze_stmt params cc a' s2 in
       let a' = analyze_stmt params cc a' s1 in
       let a' = normalize_map a' in
       if incl a' a
       then a'
       else loop (merge params a' a |> normalize_map )
     in loop (analyze_stmt params cc a s1 |> normalize_map)
and analyze_instr params cc a { i_loc ; i_desc } =
  try analyze_instr_r params cc a i_desc
  with HiError e -> raise (HiError (add_iloc e i_loc))
and analyze_stmt params cc a s =
  List.fold_left (analyze_instr params cc) a s

let analyze_fd cc fd =
  let params = Sv.of_list fd.f_args in
  try analyze_stmt params cc Mv.empty fd.f_body |> normalize_map
  with (HiError e) -> raise (HiError { e with err_funname = Some fd.f_name.fn_name })

(* --------------------------------------------------- *)
let classes (a: alias) : Sv.t Mv.t =
  Mv.fold (fun x s c ->
      let y = s.in_var in
      Mv.modify_def Sv.empty y (Sv.add x) c
      ) a Mv.empty
