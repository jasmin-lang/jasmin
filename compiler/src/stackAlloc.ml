open Utils
open Wsize
open Prog

exception NotModifiable

module Info : 
sig 
  type 'a t 
  (* [init a modifiable] *)
  val init : 'a -> bool -> 'a t
  val modifiable : 'a t -> bool
  val info : 'a t -> 'a
  val update : 'a -> 'a t -> unit

end 
=
struct

  type 'a t = {
      mutable info : 'a;
      modifiable   : bool;
    }

  let modifiable i = i.modifiable
  let info i = i.info

  let init info modifiable = { info; modifiable }

  let update a i = 
    if modifiable i then i.info <- a
    else raise NotModifiable
   
end
open Info

(* ------------------------------------------------------------------ *)
type mem_pos = {
    mp_s        : var;           (* the original program variable                *)
    mp_p        : var;           (* the pointer to the region, a target variable *)
    mp_align    : wsize Info.t;  (* Alignment of the variable                    *)
    mp_writable : bool Info.t;   (* the region is writable of not                *)
  }

let mp_equal mp1 mp2 = V.equal mp1.mp_s mp2.mp_s
  
module Mmp = Map.Make (struct
  type t = mem_pos   
  let compare x y = V.compare x.mp_s y.mp_s
end)

(* ----------------------------------------------------------------- *)
type ptr_kind = 
  | Pmem    of mem_pos
  | Pregptr of var               (* Name of the corresponding pointer *)

type pmap = ptr_kind Mv.t

let get_pk pmap (x:var_i) = 
  try Mv.find (L.unloc x) pmap
  with Not_found -> assert false

let get_var_kind pmap x = 
  if (L.unloc x).v_kind = Reg Direct then None
  else Some (get_pk pmap x)
  
let ptr_of_pk pk = 
  match pk with
  | Pmem mp -> mp.mp_p
  | Pregptr p -> p

(* ----------------------------------------------------------------- *)

let pp_var fmt x =
  Format.fprintf fmt "%a" (Printer.pp_var ~debug:false) (L.unloc x)

let pp_iloc = Printer.pp_iloc

(* ----------------------------------------------------------------- *)


module Region = struct

  type regions = {
      var_region  : mem_pos Mv.t;
      region_var : Sv.t Mmp.t;
    }

  let empty = {
      var_region = Mv.empty;
      region_var = Mmp.empty; 
    }

  let check_valid rmap (x:var_i) =
    let xv = L.unloc x in
    let mp = 
      try Mv.find xv rmap.var_region
      with Not_found ->
        hierror "no associated region for %a" pp_var x in
    let xs = 
      try Mmp.find mp rmap.region_var
      with Not_found ->
        hierror "invalid variable %a (check alias)" pp_var x in
    if not (Sv.mem xv xs) then 
      hierror "no associated region for %a" pp_var x;
    mp

  let set_align (x:var_i) mp ws =
    let xws = info mp.mp_align in
    if wsize_lt xws ws then 
      try update ws mp.mp_align 
      with NotModifiable ->
        hierror "the alignment of %a is forced to %s, and %s is required" 
          pp_var x (string_of_ws xws) (string_of_ws ws)

  let set_writable (x:var_i) mp = 
    if not (info mp.mp_writable) then
      try update true mp.mp_writable
      with NotModifiable ->
        hierror "%a is not writable" pp_var x

  let rset_word rmap x mp = 
    { var_region = Mv.add x mp rmap.var_region;
      region_var = Mmp.add mp (Sv.singleton x) rmap.region_var }

  let set_word rmap x ws mp =
    set_writable x mp;
    set_align x mp ws;
    rset_word rmap (L.unloc x) mp

  let set rmap x mp = 
    let x = L.unloc x in
    let xs = Mmp.find_default Sv.empty mp rmap.region_var in
    { var_region = Mv.add x mp rmap.var_region;
      region_var = Mmp.add mp (Sv.add x xs) rmap.region_var }

  let set_move rmap x y = 
    let mp = check_valid rmap y in
    set rmap x mp

  let set_init rmap x pk = 
    match pk with
    | Pmem mp   -> set rmap x mp
    | Pregptr _ -> rmap

  let incl r1 r2 = 
    Mv.for_all (fun x mp -> 
        try mp_equal (Mv.find x r2.var_region) mp 
        with Not_found -> false) r1.var_region &&
    Mmp.for_all (fun x xs ->
        Sv.subset xs (Mmp.find_default Sv.empty x r2.region_var)) r1.region_var 
        
  let merge r1 r2 = 
    let merge_mp _ o1 o2 = 
      match o1, o2 with
      | Some mp1, Some mp2 -> if mp_equal mp1 mp2 then Some mp1 else None
      | _, _ -> None in
    let merge_xs _ o1 o2 =
      match o1, o2 with
      | Some xs1, Some xs2 -> Some (Sv.inter xs1 xs2)
      | _, _               -> None in
    { var_region = Mv.merge merge_mp r1.var_region r2.var_region;
      region_var = Mmp.merge merge_xs r1.region_var r2.region_var; }

end

(* ---------------------------------------------------------- *)

let mk_addr x pk = 
  L.mk_loc (L.loc x) (ptr_of_pk pk)

(* ---------------------------------------------------------- *)

let alloc_e pmap rmap e =
  let rec alloc_e e = 
    match e with
    | Pconst _ | Pbool _ | Parr_init _ -> e
    | Pvar x ->
      let x = x.gv in
      begin match get_var_kind pmap x with
      | None -> e
      | Some pk -> 
        let mp = Region.check_valid rmap x in
        let ws = ws_of_ty (L.unloc x).v_ty in
        Region.set_align x mp ws;
        let p = mk_addr x pk in
        Pload(ws, p, icnst 0) (* not well typed, but not important *)
      end
    | Pget(_, ws, x, e1) ->
      let x = x.gv in
      let e1 = alloc_e e1 in
      begin match get_var_kind pmap x with
      | None -> e
      | Some pk -> 
        let mp = Region.check_valid rmap x in
        Region.set_align x mp ws;
        let p = mk_addr x pk in
        Pload(ws, p, e1) (* not well typed, but not important *)
      end
    | Pload(ws, x, e)  -> Pload(ws, x, alloc_e e)
    | Papp1(o,e)       -> Papp1(o, alloc_e e) 
    | Papp2(o,e1,e2)   -> Papp2(o, alloc_e e1, alloc_e e2)
    | PappN(o,es)      -> PappN(o, List.map alloc_e es)
    | Pif(ty,e1,e2,e3) -> Pif(ty, alloc_e e1, alloc_e e2, alloc_e e3) in
  alloc_e e

let alloc_es pmap rmap es = List.map (alloc_e pmap rmap) es

(* ---------------------------------------------------------- *)

let alloc_lval pmap rmap (r:lval) =
  match r with
  | Lnone _ -> (rmap, r) 
  | Lvar x  -> 
    begin match get_var_kind pmap x with
    | None -> (rmap, r) 
    | Some (Pregptr _) -> assert false (* pointer to word *)
    | Some (Pmem mp as pk) ->
      let ws = ws_of_ty (L.unloc x).v_ty in
      let rmap = Region.set_word rmap x ws mp in
      let r = Lmem(ws, mk_addr x pk, icnst 0) in (* not well typed, but ... *)
      (rmap, r)
    end

  | Laset (_,ws,x,e1) -> 
    let e1 = alloc_e pmap rmap e1 in
    begin match get_var_kind pmap x with
    | None -> (rmap, r)
    | Some pk ->
      let mp = Region.check_valid rmap x in
      let rmap = Region.set_word rmap x ws mp in
      let r = Lmem (ws, mk_addr x pk, e1) in
      (rmap, r)
    end
     
  | Lmem(ws, x, e1) -> 
    let e1 = alloc_e pmap rmap e1 in
    (rmap, Lmem(ws, x, e1))

let alloc_lvals pmap rmap rs = List.map_fold (alloc_lval pmap) rmap rs

(* ---------------------------------------------------------- *)
let nop = Copn([], AT_none, Expr.Onop, [])

let lea_ptr x ptr = 
  Copn([x], AT_none, Expr.Ox86 (LEA U64), [Pvar (gkvar ptr)])

let mov_ptr x ptr =
  Copn([x], AT_none, Expr.Ox86 (MOV U64), [ptr])

let get_addr rmap x dx y = 
  let yv = y.gv in
  let mpy = Region.check_valid rmap y.gv in
  let rmap = Region.set rmap x mpy in 
  let py = L.mk_loc (L.loc yv) mpy.mp_p in
  let i = 
    if is_gkvar y then
      match (L.unloc yv).v_kind with
      | Stack Direct  -> lea_ptr dx py
      | Stack Pointer -> mov_ptr dx (Pload(U64, py,icnst 0))
      | Reg Pointer   -> mov_ptr dx (Pvar (gkvar py))
      | _ -> assert false 
    else lea_ptr dx py in
  (rmap, i)

let alloc_array_move pmap rmap r e = 
  match r, e with
  | Lvar x, Pvar y ->
    begin match get_var_kind pmap x with
    | None -> hierror "register array remains %a, please report" pp_var x
    | Some pk -> 
      begin match (L.unloc x).v_kind with
      | Stack Direct ->
        if not (is_gkvar y) then 
          hierror "can not move global to stack";
        let y = y.gv in
        let mpy = Region.check_valid rmap y in
        if not (V.equal (L.unloc x) mpy.mp_s) then 
          hierror "invalid move: check alias";
        let rmap = Region.set rmap x mpy in
        (rmap, nop)
      | Stack Pointer ->
        get_addr rmap x (Lmem(U64, mk_addr x pk, icnst 0)) y
      | Reg Pointer ->
        get_addr rmap x (Lvar (mk_addr x pk)) y
      | _ -> assert false 
      end          
    end
  | _, _ -> hierror "can not reconnize an array move" 

(* ---------------------------------------------------------- *)

type param_info = { 
  pi_ptr      : var;
  pi_writable : bool;
  pi_align    : wsize;
}

type stk_alloc_oracle_t =
  { sao_has_stack : bool;
    sao_params : param_info option list (* Allocation of pointer params *)
  ; sao_return : int option list        (* Where to find the param input region *)
  ; sao_alloc  : pmap                   (* info to finalize stack_alloc *)
  }

let alloc_call_arg pmap rmap sao_param e = 
  match e with 
  | Pvar x -> 
    if not (is_gkvar x) then 
      hierror "global variable (%a) in argument of a call" pp_var x.gv;
    let xv = x.gv in
    let k = (L.unloc xv).v_kind in
    begin match sao_param, get_var_kind pmap xv with
    | None, None ->
      (None, e)

    | None, Some _ ->
      hierror "%a should be a register" pp_var xv
    | Some _, None ->
      hierror "%a should be a reg ptr" pp_var xv;

    | Some pi, Some pk -> 
      if k <> Reg Pointer then
         hierror "%a should be a reg ptr" pp_var xv;
      let mp = Region.check_valid rmap xv in
      Region.set_align xv mp pi.pi_align;
      if pi.pi_writable then Region.set_writable xv mp;
      (Some (mp,L.unloc xv), Pvar (gkvar (mk_addr xv pk)))
    end
  | _ -> 
    hierror "the expression %a is not a variable" 
      (Printer.pp_expr ~debug:false) e

(* Remark we did not check disjointness here *)
let alloc_call_args pmap rmap soa_params es = 
  List.map2 (alloc_call_arg pmap rmap) soa_params es 


(* ---------------------------------------------------------- *)
exception CallRetReg of lval

let check_lval_reg_call (r:lval) = 
  match r with
  | Lnone _ -> ()
  | Lvar x ->
    if (L.unloc x).v_kind <> Reg Direct then
      hierror "%a should be a register" pp_var x
  | _ -> raise (CallRetReg r)

let check_is_Lvar r (x:var) =
  match r with
  | Lvar x' -> V.equal (L.unloc x') x
  | _       -> false

let alloc_lval_call mps rmap r i =
  match i with
  | None -> 
    check_lval_reg_call r;
    (rmap, Some r)
  | Some i ->
    match List.nth mps i with
    | (Some (mp,x),_) ->
      let rmap = Region.rset_word rmap x mp in
      rmap, None
    | (None,_) -> assert false

let alloc_call_res rmap mps ret_pos rs = 
  let (rmap, rs) = List.map_fold2 (alloc_lval_call mps) rmap rs ret_pos in
  rmap, List.filter_map (fun x -> x) rs 


(* ---------------------------------------------------------- *)

let alloc_call local_alloc pmap rmap ini rs fn es = 
  let sao = local_alloc fn in
  let es  = alloc_call_args pmap rmap sao.sao_params es in
  let (rmap,rs)  = alloc_call_res  rmap es sao.sao_return rs in
  let es  = List.map snd es in
  (rmap, Ccall(ini, rs, fn, es))


let rec alloc_i local_alloc pmap rmap i =
  let (rmap, i_desc) = 
    try 
      begin match i.i_desc with
      | Cassgn(r, t, ty, e) ->
        if is_ty_arr ty then alloc_array_move pmap rmap r e
        else
          let e = alloc_e pmap rmap e in
          let rmap, r = alloc_lval pmap rmap r in
          rmap, Cassgn(r, t, ty, e)
      | Copn(rs, t, o, e) -> 
        let e  = alloc_es pmap rmap e in
        let rmap, rs = alloc_lvals pmap rmap rs in
        rmap, Copn(rs, t, o, e)               
  
      | Cif(e, c1, c2) -> 
        let e  = alloc_e pmap rmap e in
        let rmap1, c1 = alloc_c local_alloc pmap rmap c1 in
        let rmap2, c2 = alloc_c local_alloc pmap rmap c2 in
        let rmap = Region.merge rmap1 rmap2 in
        rmap, Cif(e,c1,c2)
  
      | Cwhile(a, c1, e, c2) -> 
        let rec check_body rmap = 
          let rmap1, c1 = alloc_c local_alloc pmap rmap c1 in
          let e = alloc_e pmap rmap1 e in
          let rmap2, c2 = alloc_c local_alloc pmap rmap1 c2 in
          if Region.incl rmap rmap2 then
            rmap1, Cwhile(a, c1, e, c2)
          else check_body (Region.merge rmap rmap2) in
        check_body rmap 

      | Ccall(ini, rs, fn, es) ->
          alloc_call local_alloc pmap rmap ini rs fn es

      | Cfor _  -> assert false 
      end
    with HiError s ->
      hierror "At %a: %s" Printer.pp_iloc i.i_loc s
  in
  rmap, { i with i_desc = i_desc }

and alloc_c local_alloc pmap rmap c =
  List.map_fold (alloc_i local_alloc pmap) rmap c

(* ---------------------------------------------------------- *)
let initial_alignment x = 
  if is_ty_arr x.v_ty then U8
  else ws_of_ty x.v_ty 

let init_globals globs =
  let pmap = ref Mv.empty in
  let rmap = ref Region.empty in
  let add (x,_) = 
    let mp = 
      { mp_s = x;
        mp_p = Prog.rip;
        mp_align = Info.init (initial_alignment x) true;
        mp_writable = Info.init false false; } in
    pmap := Mv.add x (Pmem mp) !pmap;
    rmap := Region.rset_word !rmap x mp
  in
  List.iter add globs;
  !pmap, !rmap

(* ---------------------------------------------------------- *)

let init_locals pmap rmap fd = 
  let fv = locals fd in
  let params = fd.f_args in
  let fv = Sv.diff fv (Sv.of_list params) in
  let pmap = ref pmap in
  let rmap = ref rmap in
  let posi = ref Mv.empty in
  let add_param i x =
    match x.v_kind with
    | Reg Pointer ->
      assert (is_ty_arr x.v_ty);
      let xp = V.mk x.v_name (Reg Direct) (tu uptr) x.v_dloc in
      let mp = {
        mp_s = x;
        mp_p = xp;
        mp_align = Info.init U8 true;
        mp_writable = Info.init false true; } in
      pmap := Mv.add x (Pmem mp) !pmap;
      rmap := Region.rset_word !rmap x mp;
      posi := Mv.add x i !posi;
      Some mp
    | Reg Direct -> 
      None
    | _ -> hierror "kind of %a should be reg of reg ptr" 
             (Printer.pp_var ~debug:false) x in

  let paramsi = List.mapi add_param params in

  let has_stack = ref false in
  let add_local x = 
    match x.v_kind with
    | Stack Direct ->
      let mp = {
        mp_s = x;
        mp_p = rsp;
        mp_align = Info.init (initial_alignment x) true;
        mp_writable = Info.init true true;
      } in 
      has_stack := true;
      pmap := Mv.add x (Pmem mp) !pmap;
      rmap := Region.rset_word !rmap x mp
    | Stack Pointer ->
      let mp = {
        mp_s = x;
        mp_p = rsp;
        mp_align = Info.init uptr false;
        mp_writable = Info.init true false;
      } in 
      has_stack := true;
      pmap := Mv.add x (Pmem mp) !pmap
    | Reg Direct ->
      ()
    | Reg Pointer -> 
      let xp = V.mk x.v_name (Reg Direct) (tu uptr) x.v_dloc in
      pmap := Mv.add x (Pregptr xp) !pmap
    | _ -> assert false
  in
  Sv.iter add_local fv;
  !posi, paramsi, !pmap, !rmap, fv, !has_stack

(* ---------------------------------------------------------- *)

let alloc_fd local_alloc pmap rmap fd =
  try 
  let posi, paramsi, pmap, rmap, locals, sao_has_stack = 
    init_locals pmap rmap fd in
  let rmap, f_body = alloc_c local_alloc pmap rmap fd.f_body in
  
  let do_res x =
    let xv = L.unloc x in
    match xv.v_kind with
    | Reg Direct -> 
      None, Some x
    | Reg Pointer ->
      let mp = Region.check_valid rmap x in
      if not (V.equal xv mp.mp_s) then
        hierror "invalid reg ptr %a" pp_var x;
      let i = 
        try Mv.find xv posi 
        with Not_found -> assert false in
      Some i, None
    | _ -> assert false in

  let sao_return, ret = List.split (List.map do_res fd.f_ret) in
  let f_ret = List.filter_map (fun x -> x) ret in
  
  let do_arg o x = 
    match o with
    | None -> None, x
    | Some mp -> 
      let pi = {
        pi_ptr = mp.mp_p;
        pi_writable = Info.info mp.mp_writable;
        pi_align    = Info.info mp.mp_align;
      } in
      Some pi, mp.mp_p in
        
  let sao_params, f_args = List.split (List.map2 do_arg paramsi fd.f_args) in

  let do_tyargs o ty =
    match o with
    | Some pi -> pi.pi_ptr.v_ty
    | None    -> ty in
  
  let do_tyres o ty = 
    match o with
    | Some _ -> None
    | None   -> Some ty in

  let f_tyin = List.map2 do_tyargs sao_params fd.f_tyin in
  let f_tyout = 
    List.filter_map (fun x -> x) 
      (List.map2 do_tyres sao_return fd.f_tyout) in

  let fd = 
    {fd with
      f_tyin; f_args; f_body; f_tyout; f_ret } in

  let sao_alloc = Mv.filter (fun x _mp -> Sv.mem x locals) pmap in

  let sao = 
    { sao_has_stack; sao_params; sao_return; sao_alloc } in

  sao, fd
  
  with HiError s ->
    hierror "(stack alloc) In function %s: %s"
      fd.f_name.fn_name s 

let alloc_prog (globs, fds) = 
  let pmap, rmap = init_globals globs in
  let tbl = Hf.create 100 in
  let local_alloc fn = 
    try Hf.find tbl fn 
    with Not_found -> 
      hierror "unknown function %s" fn.fn_name in

  let do_fd fd =
    let sao, fd = alloc_fd local_alloc pmap rmap fd in
    Hf.add tbl fd.f_name sao;
    sao, fd in

  let fds = List.map do_fd fds in
  pmap, fds


(* ---------------------------------------------------------- *)

type pos_kind =
  | Pstack of int * Wsize.wsize
  | Pregptr of var 
  | Pstkptr of int

let alloc_stackmem xmem pmap = 
  let vars = ref [] in
  let alloc = ref [] in
  let add_var x mp =
    match mp with
    | Pmem mp ->
      assert (V.equal mp.mp_p xmem);
      let ws, s = 
        if x.v_kind = Stack Pointer then uptr, size_of_ws uptr
        else
          let ws = Info.info mp.mp_align in
          let s = 
            match x.v_ty with
            | Bty (U ws) -> size_of_ws ws
            | Arr (ws', n) -> arr_size ws' n 
            | t -> 
              Format.eprintf "%a@." Printer.pp_ty t;
              assert false in
          ws, s in
      vars := (x,ws,s) :: !vars
    | Pregptr p -> 
      alloc := (x, Pregptr p) :: !alloc 
  in
  Mv.iter add_var pmap;
  let cmp (_,ws1,_) (_,ws2,_) = 
    match Wsize.wsize_cmp ws1 ws2 with
    | Lt -> -1
    | Eq -> 0
    | Gt -> 1 
  in
  let vars = List.sort cmp !vars in
  
  let mk_pos x pos ws = 
    let dest = 
      if x.v_kind = Stack Pointer then Pstkptr pos
      else Pstack(pos, ws) in
    alloc := (x, dest) :: !alloc in

  let size = ref 0 in
  let init_var (x,ws,n) =
    let s = size_of_ws ws in
    let pos = !size in
    let pos = 
      if pos mod s = 0 then pos
      else (pos/s + 1) * s in
    size := pos + n;
    mk_pos x pos ws in

  List.iter init_var vars;

  List.rev !alloc

let alloc_stack pmap = 
  alloc_stackmem rsp pmap

let alloc_mem pmap = 
  let alloc = alloc_stackmem rip pmap in
  let to_mem = function
    | (x,Pstack(i,ws)) -> (x,(i,ws))
    | _ -> assert false in
  List.map to_mem alloc


  
  
    
    



  





    

    





    

