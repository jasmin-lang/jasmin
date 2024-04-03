open Utils
open Wsize
open Memory_model
open Prog

module Live = Liveness
module G = IntervalGraphColoring

let hierror = hierror ~kind:"compilation error" ~sub_kind:"variable allocation"

type liverange = G.graph Mint.t

(* --------------------------------------------------- *)
(** Invariant: heuristic is always higher than the strict constraint *)
type alignment_constraint =
  { ac_strict: wsize
  ; ac_heuristic: wsize }

let no_alignment_constraint = { ac_strict = U8; ac_heuristic = U8 }

type param_info = {
  pi_ptr      : var;
  pi_writable : bool;
  pi_align    : alignment_constraint;
}

type ptr_kind = 
  | Direct   of var * Interval.interval * E.v_scope
  | StackPtr of var 
  | RegPtr   of var  

type stk_alloc_oracle_t =
  { sao_calls  : Sf.t
  ; sao_params : param_info option list (* Allocation of pointer params *)
  ; sao_return : int option list        (* Where to find the param input region *)
  ; sao_slots  : (var * wsize * int) list 
  ; sao_align : wsize
  ; sao_size  : int               (* Not normalized with respect to sao_local_align *)
  ; sao_alloc : ptr_kind Hv.t
  ; sao_modify_rsp : bool
  }

type glob_alloc_oracle_t = 
  { gao_data : Obj.t list 
  ; gao_slots  : (var * wsize * int) list 
  ; gao_align : wsize
  ; gao_size  : int               (* Not normalized with respect to sao_local_align *)
  }

 
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

let live_ranges_stmt pd (alias: Alias.alias) (ptr_classes: var -> bool) d c =

let stack_pointers = Hv.create 117 in

let get_stack_pointer pd x =
  try Hv.find stack_pointers x
  with Not_found ->
    let r = V.mk x.v_name (Stack Direct) (tu pd) x.v_dloc x.v_annot in
    Hv.add stack_pointers x r;
    r
in

let preprocess_liveset (s: Sv.t) : Sv.t =
  Sv.fold (fun x s ->
      if is_ty_arr x.v_ty
      then
        let s =
          let r = Alias.((normalize_var alias x).in_var) in
          if ptr_classes r
          then s
          else Sv.add r s
        in
        if is_stk_ptr_kind x.v_kind
        then Sv.add (get_stack_pointer pd x) s
        else s
      else
        if is_stack_kind x.v_kind
        then Sv.add x s
        else s
    ) s Sv.empty
in

let process_live_info d acc (i: Sv.t) =
  let process_live_var x acc =
    incr_liverange acc x d
  in
  let i = preprocess_liveset i in
  Sv.fold process_live_var i acc
in

let rec live_ranges_instr_r d_acc =
  function
  | (Cassgn _ | Copn _ | Csyscall _ | Ccall _) -> d_acc
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
let check_class f_name f_loc ptr_classes args x s =
  let s = Sv.add x s in
  if not (Sv.disjoint args s) && not (ptr_classes x) then
    hierror ~loc:(Lone f_loc) ~funname:f_name "cannot put a reg ptr argument into the local stack"

(* --------------------------------------------------- *)
let max_align al ws ac =
  let max_align ws' = if wsize_lt ws' ws then ws else ws' in
  match al with
  | Aligned -> { ac_strict = max_align ac.ac_strict; ac_heuristic = max_align ac.ac_heuristic }
  | Unaligned -> { ac with ac_heuristic = max_align ac.ac_heuristic }

type alignment = alignment_constraint Hv.t

let classes_alignment (onfun : funname -> param_info option list) (gtbl: alignment) alias c : alignment * Sf.t =
  let ltbl = Hv.create 117 in
  let calls = ref Sf.empty in

  let set al x scope ws =
    let tbl = if scope = E.Sglob then gtbl else ltbl in
    Hv.modify_def no_alignment_constraint x (max_align al ws) tbl in

  let add_ggvar al x ws i =
    let x' = L.unloc x.gv in
    if is_gkvar x then
      begin
        let c = Alias.normalize_var alias x' in
        set al c.in_var c.scope ws;
        if al == Aligned && (fst c.range + i) land (size_of_ws ws - 1) <> 0 then
            hierror ~loc:(Lone (L.loc x.gv)) "bad range alignment for %a[%d]/%s in %a"
              (Printer.pp_var ~debug:true) x' i (string_of_ws ws)
              Alias.pp_slice c
      end
    else set al x' E.Sglob ws in

  let rec add_e = function
    | Pconst _ | Pbool _ | Parr_init _  | Pvar _ -> ()
    | Pget (al, _, ws, x, e) -> add_ggvar al x ws 0; add_e e
    | Psub (_,_,_,_,e) | Pload (_, _, _, e) | Papp1 (_, e) -> add_e e
    | Papp2 (_, e1,e2) -> add_e e1; add_e e2
    | PappN (_, es) -> add_es es 
    | Pif (_,e1,e2,e3) -> add_e e1; add_e e2; add_e e3 
  and add_es es = List.iter add_e es in

  let add_lv = function
    | Lnone _ | Lvar _ -> ()
    | Lmem (_, _, _, e) | Lasub (_,_,_,_,e) -> add_e e
    | Laset(al, _, ws,x,e) -> add_ggvar al (gkvar x) ws 0; add_e e in

  let add_lvs = List.iter add_lv in
  
  let add_p opi e = 
    match opi, e with
    | None, _ -> add_e e
    | Some pi, Pvar x ->
       add_ggvar Aligned x pi.pi_align.ac_strict 0;
       add_ggvar Unaligned x pi.pi_align.ac_heuristic 0
    | Some pi, Psub(aa,ws,_, x, e) ->
      let i = 
        match get_ofs aa ws e with
        | None ->
          (* this error is probably always caught before by the similar code in alias.ml *)
          hierror ~loc:(Lone (L.loc x.gv)) "Cannot compile sub-array %a that has a non-constant start index" (Printer.pp_var ~debug:true) (L.unloc x.gv)
        | Some i -> i in
      add_ggvar Aligned x pi.pi_align.ac_strict i;
      add_ggvar Unaligned x pi.pi_align.ac_heuristic i
    | _, _ -> assert false in

  let rec add_ir i_desc =
    match i_desc with
    | Cassgn(x,_,_,e) -> add_lv x; add_e e
    | Copn(xs,_,_,es) | Csyscall(xs,_,es) -> add_lvs xs; add_es es
    | Cif(e,c1,c2) | Cwhile (_,c1,e,c2) -> 
      add_e e; add_c c1; add_c c2
    | Cfor _ -> assert false 
    | Ccall(xs, fn, es) ->
      add_lvs xs;
      calls := Sf.add fn !calls; 
      List.iter2 add_p (onfun fn) es 

  and add_i { i_loc; i_desc } =
    try add_ir i_desc
    with HiError e -> raise (HiError (add_iloc e i_loc))

  and add_c c = List.iter add_i c in 

  add_c c;
  ltbl, !calls
 
(* --------------------------------------------------- *)
let err_var_not_initialized x =
  hierror ~loc:Lnone "variable “%a” (declared at %a) may not be initialized" (Printer.pp_var ~debug:true) x Location.pp_loc x.v_dloc

let get_slot ?var coloring x =
  let sz = size_of x.v_ty in
  try Mv.find x (Mint.find sz coloring)
  with Not_found -> err_var_not_initialized (Option.default x var)

let get_stack_pointer stack_pointers x =
  try Hv.find stack_pointers x
  with Not_found -> assert false 

let init_slots pd stack_pointers alias coloring fv =
  let slots = ref Sv.empty in
  let lalloc = Hv.create 1017 in
  let add_slot slot = slots := Sv.add slot !slots in
  let add_local x info = Hv.add lalloc x info in

  (* FIXME: move definition of interval in Alias *)
  let r2i (min,max) = Interval.{min;max} in
  let dovar v =
    match v.v_kind with
    | Stack Direct ->
      if is_ty_arr v.v_ty then
        let c = Alias.normalize_var alias v in
        if c.scope = E.Sglob then
          add_local v (Direct (c.in_var, r2i c.range, E.Sglob))
        else
          begin
            let slot = get_slot coloring c.in_var in
            add_slot slot;
            add_local v (Direct (slot, r2i c.range, E.Slocal))
          end
      else
        let sz = size_of v.v_ty in
        let slot = get_slot coloring v in
        add_slot slot;
        add_local v (Direct (slot, r2i(0, sz), E.Slocal))

    | Stack (Pointer _) ->
      let xp = get_stack_pointer stack_pointers v in
      let slot = get_slot ~var:v coloring xp in
      add_slot slot;
      add_local v (StackPtr slot)
    | Reg (k, Pointer _) ->
      let p = V.mk v.v_name (Reg(k, Direct)) (tu pd) v.v_dloc v.v_annot in
      add_local v (RegPtr p) 
    | _ -> () in

  Sv.iter dovar fv;
  !slots, lalloc

(* --------------------------------------------------- *)
let all_alignment pd (ctbl: alignment) alias params lalloc : param_info option list * wsize Hv.t =

  let get_align c =
    try Hv.find ctbl c.Alias.in_var
    with Not_found -> no_alignment_constraint in
  let doparam x =
    match x.v_kind with
    | Reg (_, Direct) -> None
    | Reg (_, Pointer w) ->
      let c = Alias.normalize_var alias x in
      assert (V.equal x c.in_var && c.scope = E.Slocal);
      let pi_ptr = 
        match Hv.find lalloc x with
        | RegPtr p -> p
        | _ | exception Not_found -> assert false in
      let pi_writable = w = Writable in
      let pi_align = get_align c in
      Some { pi_ptr; pi_writable; pi_align }
    | _ -> assert false in
  let params = List.map doparam params in

  let atbl = Hv.create 1007 in
  let set slot ws = 
    Hv.modify_def U8 slot (fun ws' -> if wsize_lt ws' ws then ws else ws') atbl in
  let doalloc x pk =
    match pk with
    | Direct (_, _, E.Sglob) | RegPtr _ -> ()
    | Direct (slot, _, E.Slocal) ->
      let ws = 
        match x.v_ty with
        | Arr _ -> (get_align (Alias.normalize_var alias x)).ac_heuristic
        | Bty (U ws) -> ws
        | _ -> assert false in
      set slot ws
    | StackPtr(slot) ->
      set slot pd in
  Hv.iter doalloc lalloc;
  params, atbl


(* --------------------------------------------------- *)
let round_ws ws sz =
  let d = size_of_ws ws in
  if sz mod d = 0 then sz
  else (sz/d + 1) * d

let alloc_local_stack size slots atbl =
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

  let size = ref size in
  
  let init_slot (x,ws) = 
    let pos = round_ws ws !size in
    let n = size_of x.v_ty in
    size := pos + n;
    (x,ws,pos) in

  let slots = List.map init_slot slots in
  stk_align, slots, !size

(* --------------------------------------------------- *)
let alloc_stack_fd callstyle pd get_info gtbl fd =
  if !Glob_options.debug then Format.eprintf "ALLOC STACK %s@." fd.f_name.fn_name;
  let alias =
    let get_cc fn = (get_info fn).sao_return in
    Alias.analyze_fd get_cc fd in
  let classes = Alias.classes alias in

  let ptr_args = 
    List.fold_left (fun s x -> if is_reg_ptr_kind x.v_kind then Sv.add x s else s) 
      Sv.empty fd.f_args in
  (* True if z is a pointer aliasing only other pointers *)
  let ptr_classes z =
    match Mv.find z classes with
    | exception Not_found -> is_ptr z.v_kind
    | cls -> Sv.for_all (fun y -> is_ptr y.v_kind) (Sv.add z cls)
  in
  Mv.iter (check_class fd.f_name.fn_name fd.f_loc ptr_classes ptr_args) classes;

  let fd = Live.live_fd false fd in
  let (_, ranges), stack_pointers =
    live_ranges_stmt pd alias ptr_classes (0, Mint.empty) fd.f_body in

  let coloring = Mint.mapi G.solve ranges in

  let slots, lalloc = init_slots pd stack_pointers alias coloring (vars_fc fd) in

  let getfun fn = (get_info fn).sao_params in
  let ctbl, sao_calls =
    try classes_alignment getfun gtbl alias fd.f_body
    with HiError e -> raise (HiError { e with err_funname = Some fd.f_name.fn_name })
  in
  let sao_return =
    match fd.f_cc with
    | Export {returned_params} | Subroutine {returned_params} -> returned_params
    | Internal -> assert false in

  let sao_params, atbl = all_alignment pd ctbl alias fd.f_args lalloc in

  let ra_on_stack =
    match fd.f_cc with 
    | Internal -> assert false 
    | Export _ ->
        if fd.f_annot.retaddr_kind = Some OnReg then 
             Utils.warning Always (L.i_loc fd.f_loc [])
              "for function %s, return address by reg not allowed for export function, annotation is ignored"
              fd.f_name.fn_name;
        false (* For export function ra is not counted in the frame *)
    | Subroutine _ -> 
      match callstyle with 
      | Arch_full.StackDirect -> 
        if fd.f_annot.retaddr_kind = Some OnReg then 
          Utils.warning Always (L.i_loc fd.f_loc [])
            "for function %s, return address by reg not allowed for that architecture, annotation is ignored"
            fd.f_name.fn_name;
        true
      | Arch_full.ByReg oreg ->  (* oreg = Some r implies that all call use r,
                                    so if the function performs some call r will be overwritten,
                                    so ra need to be saved on stack *)
        let dfl = oreg <> None && has_call_or_syscall fd.f_body in
        match fd.f_annot.retaddr_kind with
        | None -> dfl
        | Some k -> 
            if k = OnReg && dfl then 
              Utils.warning Always (L.i_loc fd.f_loc []) 
                "for function %s, return address by reg not possible, annotation is ignored" fd.f_name.fn_name;
            dfl || k = OnStack in

  let sao_align, sao_slots, sao_size =
    alloc_local_stack
      (* if ra_on_stack we add some space for the return address,
         the alignment will be automatically corrected *)
      (if ra_on_stack then size_of_ws pd else 0) (Sv.elements slots) atbl in

  (* FIXME: 1- make this U128 arch (call-conv) dependent; 2- make it a semantic requirement. *)
  let sao_align = if has_syscall fd.f_body && wsize_lt sao_align U128 then U128 else sao_align in

  let sao_alloc = List.iter (Hv.remove lalloc) fd.f_args; lalloc in

  let sao_modify_rsp = 
    sao_size <> 0 || ra_on_stack ||
      Sf.exists (fun fn -> (get_info fn).sao_modify_rsp) sao_calls in
  let sao = {
    sao_calls;
    sao_params;
    sao_return;
    sao_slots;
    sao_align;
    sao_size;
    sao_alloc; 
    sao_modify_rsp;
  } in
  sao

let alloc_mem (gtbl: wsize Hv.t) globs =
  let gao_align, gao_slots, gao_size = alloc_local_stack 0 (List.map fst globs) gtbl in
  let t = Array.make gao_size (Word0.wrepr U8 (Conv.cz_of_int 0)) in
  let get x = 
    try List.assoc x globs with Not_found -> assert false in

  let doslot (v, _, ofs) = 
    match get v with
    | Global.Gword(ws, w) ->
      let w = Memory_model.LE.encode ws w in
      List.iteri (fun i w -> t.(ofs + i) <- w) w 

    | Global.Garr(p, gt) ->
      let ip = Conv.int_of_pos p in
      for i = 0 to ip - 1 do
        let w = 
          match Warray_.WArray.get p Aligned Warray_.AAdirect U8 gt (Conv.cz_of_int i) with
          | Ok w -> w
          | _    -> assert false in
        t.(ofs + i) <- w
      done  in

  List.iter doslot gao_slots;
  { gao_data = Array.to_list t; gao_align; gao_slots; gao_size }

let alloc_stack_prog callstyle pd (globs, fds) =
  let gtbl = Hv.create 107 in
  let ftbl = Hf.create 107 in
  let get_info fn = Hf.find ftbl fn in
  let set_info fn sao = Hf.add ftbl fn sao in
  let doit fd = 
    let sao = alloc_stack_fd callstyle pd get_info gtbl fd in
    set_info fd.f_name sao in
  List.iter doit (List.rev fds);
  let gao =  alloc_mem (Hv.map (fun _ x -> x.ac_heuristic) gtbl) globs in
  gao, ftbl 

let extend_sao sao extra =
  let tbl = Hv.create 11 in
  let doit x = 
    match x.v_ty with
    | Bty (U ws) -> Hv.add tbl x ws 
    | _          -> assert false in
  List.iter doit extra;
    
  let align, slots, size = alloc_local_stack sao.sao_size extra tbl in
  let align = if wsize_lt align sao.sao_align then sao.sao_align else align in
  let slots = List.map (fun (x,_,pos) -> (x,pos)) slots in
  size - sao.sao_size, align, slots


  

