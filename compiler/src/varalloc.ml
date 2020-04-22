open Utils
open Wsize
open Prog

module Live = Liveness
module G = IntervalGraphColoring

type liverange = G.graph Mint.t

(* --------------------------------------------------- *)
type param_info = { 
  pi_ptr      : var;
  pi_writable : bool;
  pi_align    : wsize;
}

type ptr_kind = 
  | Stack    of var * ByteSet.interval 
  | StackPtr of var 
  | RegPtr   of var  
  | Glob     of var * ByteSet.interval

type stk_alloc_oracle_t =
  { sao_calls  : Sf.t
  ; sao_params : param_info option list (* Allocation of pointer params *)
  ; sao_return : int option list        (* Where to find the param input region *)
  ; sao_slots  : (var * wsize * int) list 
  ; sao_align : wsize
  ; sao_size  : int               (* Not normalized with respect to sao_local_align *)
  ; sao_alloc : ptr_kind Hv.t
  }

type glob_alloc_oracle_t = 
  { gao_slots  : (var * wsize * int) list 
  ; gao_align : wsize
  ; gao_size  : int               (* Not normalized with respect to sao_local_align *)
  }


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

let pp_tbl fmt (name,tbl) =
  Format.fprintf fmt "@[<v>%s@ %a@]" name 
    (pp_list "@ " (fun fmt (x,ws) -> Format.fprintf fmt "%a -> %s" pp_var x (string_of_ws ws)))
    (Hv.to_list tbl )

let pp_stk fmt (x, stkk) =
  match stkk with
  | Glob  (y, r) -> Format.fprintf fmt "%a -> %%G%a" pp_var x pp_range (y,(r.min,r.max))
  | Stack (y, r) -> Format.fprintf fmt "%a -> %a" pp_var x pp_range (y,(r.min,r.max))
  | StackPtr y -> Format.fprintf fmt "%a |s-> %a" pp_var x pp_var y 
  | RegPtr   y -> Format.fprintf fmt "%a |r-> %a" pp_var x pp_var y 

  

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

type alignment = wsize Hv.t

let classes_alignment (onfun : funname -> param_info option list) gtbl alias c = 
  let ltbl = Hv.create 117 in
  let calls = ref Sf.empty in

  let set x scope ws = 
    let tbl = if scope = E.Sglob then gtbl else ltbl in
    Hv.modify_def U8 x (fun ws' -> if wsize_lt ws' ws then ws else ws') tbl in

  let add_ggvar x ws i = 
    let x' = L.unloc x.gv in
    if is_gkvar x then
      begin
        let c = Alias.normalize_var alias x' in
        set c.in_var c.scope ws;
        if (fst c.range + i) land (size_of_ws ws - 1) <> 0 then
          hierror "bad range alignment"
      end
    else set x' E.Sglob ws in

  let rec add_e = function
    | Pconst _ | Pbool _ | Parr_init _  | Pvar _ -> ()
    | Pget (_,ws, x, e) -> add_ggvar x ws 0; add_e e
    | Psub (_,_,_,_,e) | Pload (_, _, e) | Papp1 (_, e) -> add_e e
    | Papp2 (_, e1,e2) -> add_e e1; add_e e2
    | PappN (_, es) -> add_es es 
    | Pif (_,e1,e2,e3) -> add_e e1; add_e e2; add_e e3 
  and add_es es = List.iter add_e es in

  let add_lv = function
    | Lnone _ | Lvar _ -> ()
    | Lmem (_, _, e) | Lasub (_,_,_,_,e) -> add_e e
    | Laset(_,ws,x,e) -> add_ggvar (gkvar x) ws 0; add_e e in

  let add_lvs = List.iter add_lv in
  
  let add_p opi e = 
    match opi, e with
    | None, _ -> add_e e
    | Some pi, Pvar x ->  add_ggvar x pi.pi_align 0
    | Some pi, Psub(aa,ws,_, x, e) ->
      let i = 
        match get_ofs aa ws e with
        | None -> hierror "not able to find the subindex" 
        | Some i -> i in
      add_ggvar x pi.pi_align i
    | _, _ -> assert false in

  let rec add_i i = 
    match i.i_desc with
    | Cassgn(x,_,_,e) -> add_lv x; add_e e
    | Copn(xs,_,_,es) -> add_lvs xs; add_es es
    | Cif(e,c1,c2) | Cwhile (_,c1,e,c2) -> 
      add_e e; add_c c1; add_c c2
    | Cfor _ -> assert false 
    | Ccall(_, xs, fn, es) -> 
      add_lvs xs;
      calls := Sf.add fn !calls; 
      List.iter2 add_p (onfun fn) es 

  and add_c c = List.iter add_i c in 

  add_c c;
  ltbl, !calls
 
(* --------------------------------------------------- *)
let get_slot coloring x = 
  let sz = size_of x.v_ty in
  try Mv.find x (Mint.find sz coloring)
  with Not_found -> assert false 

let get_stack_pointer stack_pointers x =
  try Hashtbl.find stack_pointers x
  with Not_found -> assert false 

let init_slots stack_pointers alias coloring fv =
  let slots = ref Sv.empty in
  let lalloc = Hv.create 1017 in
  let add_slot slot = slots := Sv.add slot !slots in
  let add_local x info = Hv.add lalloc x info in

  (* FIXME: move definition of interval in Alias *)
  let r2i (min,max) = ByteSet.{min;max} in
  let dovar v =
    match v.v_kind with
    | Stack Direct ->
      if is_ty_arr v.v_ty then
        let c = Alias.normalize_var alias v in
        if c.scope = E.Sglob then add_local v (Glob (c.in_var, r2i c.range))
        else
          begin
            let slot = get_slot coloring c.in_var in
            add_slot slot;
            add_local v (Stack(slot, r2i c.range))
          end
      else
        let sz = size_of v.v_ty in
        let slot = get_slot coloring v in
        add_slot slot;
        add_local v (Stack(slot, r2i(0, sz)))

    | Stack (Pointer _) ->
      let xp = get_stack_pointer stack_pointers v in
      let sz = size_of xp.v_ty in
      let slot =
        try Mv.find xp (Mint.find sz coloring)
        with Not_found -> assert false in
      add_slot slot;
      add_local v (StackPtr slot)
    | Reg (Pointer _) ->
      let p = V.mk v.v_name (Reg Direct) u64 v.v_dloc in
      add_local v (RegPtr p) 
    | _ -> () in

  Sv.iter dovar fv;
  !slots, lalloc

(* --------------------------------------------------- *)
let all_alignment ctbl alias params lalloc =

  let get_align c = try Hv.find ctbl c.Alias.in_var with Not_found -> U8 in
  let doparam x =
    match x.v_kind with
    | Reg Direct -> None
    | Reg (Pointer writable) ->
      let c = Alias.normalize_var alias x in
      assert (V.equal x c.in_var && c.scope = E.Slocal);
      let pi_ptr = 
        match Hv.find lalloc x with
        | RegPtr p -> p
        | _ | exception Not_found -> assert false in
      let pi_writable = writable = Writable in
      let pi_align = get_align c in 
      Some { pi_ptr; pi_writable; pi_align } 
    | _ -> assert false in
  let params = List.map doparam params in

  let atbl = Hv.create 1007 in
  let set slot ws = 
    Hv.modify_def U8 slot (fun ws' -> if wsize_lt ws' ws then ws else ws') atbl in
  let doalloc x pk =
    match pk with
    | Glob _ | RegPtr _ -> ()
    | Stack(slot,_) ->
      let ws = 
        match x.v_ty with
        | Arr _ -> get_align (Alias.normalize_var alias x)
        | Bty (U ws) -> ws
        | _ -> assert false in
      set slot ws
    | StackPtr(slot) ->
      set slot U64 in
  Hv.iter doalloc lalloc;
  params, atbl


(* --------------------------------------------------- *)
let alloc_local_stack slots atbl = 
  let do1 x = 
    let ws = 
      try Hv.find atbl x 
      with Not_found -> 
        match x.v_ty with
        | Arr _ -> U8
        | Bty (U ws) -> ws 
        | _ -> assert false
    in
    (x, ws) in

  let slots = List.map do1 slots in

  (* Sort by alignment, bigger first *) 
  let cmp (_,ws1) (_,ws2) = 
    match Wsize.wsize_cmp ws1 ws2 with
    | Lt -> 1
    | Eq -> 0
    | Gt -> -1 in
  let slots = List.sort cmp slots in

  let stk_align = 
    match slots with
    | [] -> U8
    | (_,ws) :: _ -> ws in

  let size = ref 0 in
  
  let init_slot (x,ws) = 
    let s = size_of_ws ws in
    let pos = !size in
    let n = size_of x.v_ty in
    let pos = 
      if pos mod s = 0 then pos
      else (pos/s + 1) * s in
    size := pos + n;
    (x,ws,pos) in

  let slots = List.map init_slot slots in
  stk_align, slots, !size

(* --------------------------------------------------- *)
let alloc_stack_fd get_info gtbl fd =
  if !Glob_options.debug then Format.eprintf "alloc_stack %s@." fd.f_name.fn_name;
  let alias =
    let get_cc fn = (get_info fn).sao_return in
    Alias.analyze_fd get_cc fd in
  let classes = Alias.classes alias in

  let ptr_args = 
    List.fold_left (fun s x -> if is_reg_ptr_kind x.v_kind then Sv.add x s else s) 
      Sv.empty fd.f_args in
  (* Comprend pas ce code *)
  let ptr_classes = 
    Mv.fold (fun x s acc -> 
        if Sv.for_all (fun y -> is_ptr y.v_kind) (Sv.add x s) then Sv.add x acc else acc) 
      classes Sv.empty in
  Mv.iter (check_class ptr_classes ptr_args) classes;

  let fd = Live.live_fd false fd in
  let (_, (ranges, all_stack_vars)), stack_pointers = 
    live_ranges_stmt alias ptr_classes (0, (Mint.empty, Sv.empty)) fd.f_body in

  let coloring = Mint.mapi G.solve ranges in

  Format.eprintf "Ranges: %a@." (pp_list "@ " pp_ranges) (Mint.bindings ranges);
  Format.eprintf "Colors: %a@." (pp_list "@ " pp_coloring) (Mint.bindings coloring);
  Format.eprintf "All stack vars: %a@." (pp_list "@ " pp_var) (Sv.elements all_stack_vars);
  Format.eprintf "alias: %a@." Alias.pp_alias alias;

  
  let slots, lalloc = init_slots stack_pointers alias coloring (vars_fc fd) in

  Format.eprintf "slots = %a@." (pp_list "@ " pp_var) (Sv.elements slots);
  Format.eprintf "lalloc : @[<v>%a@]@." (pp_list "@ " pp_stk) 
    (Hv.to_list lalloc);

  let getfun fn = (get_info fn).sao_params in
  let ctbl, sao_calls = classes_alignment getfun gtbl alias fd.f_body in
  Format.eprintf "%a@ %a@." pp_tbl ("globals", gtbl) pp_tbl ("classes", ctbl);
  let sao_params, atbl = all_alignment ctbl alias fd.f_args lalloc in
  let sao_return = 
    match fd.f_cc with
    | Export -> List.map (fun _ -> None) fd.f_ret 
    | Subroutine {returned_params} -> returned_params
    | Internal -> assert false in

  let sao_align, sao_slots, sao_size = alloc_local_stack (Sv.elements slots) atbl in
    
  let sao_alloc = List.iter (Hv.remove lalloc) fd.f_args; lalloc in
 
  {
    sao_calls;
    sao_params;
    sao_return;
    sao_slots;
    sao_align;
    sao_size;
    sao_alloc; 
  } 

let alloc_stack_prog (globs, fds) =
  let gtbl = Hv.create 107 in
  let ftbl = Hf.create 107 in
  let get_info fn = Hf.find ftbl fn in
  let set_info fn sao = Hf.add ftbl fn sao in
  let doit fd = 
    let sao = alloc_stack_fd get_info gtbl fd in
    set_info fd.f_name sao in
  List.iter doit (List.rev fds);
  let gao_align, gao_slots, gao_size = 
    alloc_local_stack (List.map fst globs) gtbl in
  { gao_align; gao_slots; gao_size }, ftbl 

(*let extend_sao sao extra = *)
  

