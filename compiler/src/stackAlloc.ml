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
  
module MpCmp = struct 
  type t = mem_pos   
  let compare (x:t) (y:t) = V.compare x.mp_s y.mp_s
end
module Mmp = Map.Make (MpCmp)
module Smp = Set.Make (MpCmp)

(* ------------------------------------------------------------------ *)
type sub_mp = {
    smp_ofs : int;
    smp_len : int;
  }

module SMpCmp = struct 
  type t = sub_mp   
  let compare (x:t) (y:t) = compare x y
end
module Msmp = Map.Make (SMpCmp)
module Ssmp = Set.Make (SMpCmp)
 
let disjoint_sub_mp smp1 smp2 = 
  smp1.smp_ofs + smp1.smp_len <= smp2.smp_ofs || 
  smp2.smp_ofs + smp2.smp_len <= smp1.smp_ofs

(* ------------------------------------------------------------------ *)
type mem_pos_sub = {
    mps_mp : mem_pos;
    mps_sub: sub_mp option;
  }

let mps_equal mps1 mps2 = 
  mp_equal mps1.mps_mp mps2.mps_mp && 
    mps1.mps_sub = mps2.mps_sub

module MpsCmp = struct
  type t = mem_pos_sub
  let compare x y = 
    let c = MpCmp.compare x.mps_mp y.mps_mp in
    if c = 0 then 
      match x.mps_sub, y.mps_sub with
      | None, None -> 0
      | Some _, None -> 1
      | None, Some _ -> -1
      | Some xsmp, Some ysmp -> SMpCmp.compare xsmp ysmp
    else c
end

module Mmps = Map.Make(MpsCmp)
module Smps = Set.Make(MpsCmp)

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
  Format.fprintf fmt "%a" (Printer.pp_var ~debug:true) (L.unloc x)

let pp_iloc = Printer.pp_iloc

(* ----------------------------------------------------------------- *)


module Region : 
sig
  type regions 
  val empty        : regions
(*  val pp_rmap      : Format.formatter -> regions -> unit *)
  val check_valid  : regions -> var_i -> mem_pos_sub
  val get_mp_opt   : regions -> var_i -> mem_pos_sub option
  val set_align    : var_i -> mem_pos_sub -> Wsize.wsize -> unit
  val set_writable : var_i -> mem_pos_sub -> unit
  val remove       : regions -> mem_pos_sub -> regions 
  val rset_word    : regions -> var -> int option -> int -> mem_pos_sub -> regions
  val rset_full    : regions -> var -> mem_pos -> regions
  val set_word     : regions -> var_i -> int option -> Wsize.wsize -> mem_pos_sub -> regions
  val set          : regions -> var_i -> mem_pos_sub -> regions
  val set_init     : regions -> var_i -> ptr_kind -> regions
  val incl         : regions -> regions -> bool
  val merge        : regions -> regions -> regions
  val has_stack    : regions -> bool 
  val calls        : regions -> Sf.t
  val set_call     : regions -> funname -> bool -> regions  
  val set_stack    : regions -> regions
end 
= struct

  type internal_mem_pos = 
    | IMP of mem_pos_sub
    | IMP_error of Smps.t option 

  type sub_map = {
      sm_base : Sv.t;
      sm_sub  : Sv.t Msmp.t;
    }
  type regions = {
      calls      : Sf.t;
      has_stack  : bool;
      var_region : internal_mem_pos Mv.t;
      region_var : sub_map Mmp.t;
    }

  let empty = {
      calls      = Sf.empty;
      has_stack  = false;
      var_region = Mv.empty;
      region_var = Mmp.empty; 
    }

  let set_call rmap fn has_stack = 
    {rmap with 
      has_stack = has_stack || rmap.has_stack;
      calls     = Sf.add fn rmap.calls;
    }

  let set_stack rmap = {rmap with has_stack = true }

  let has_stack rmap = rmap.has_stack

  let calls rmap = rmap.calls

(*  let pp_rmap fmt rmap = 
    let pp_var = (Printer.pp_var ~debug:true) in
    Format.fprintf fmt "@[<v>%a@ ------@ %a@]"
      (Printer.pp_list "@ " (fun fmt (x,mp) -> 
           Format.fprintf fmt "%a -> %a" pp_var x pp_var mp.mp_s))
      (Mv.bindings rmap.var_region)
      (Printer.pp_list "@ " (fun fmt (mp,xs) ->
           Format.fprintf fmt "%a -> {@[%a@]}" pp_var mp.mp_s
            (Printer.pp_list ",@ " pp_var) (Sv.elements xs)))
      (Mmp.bindings rmap.region_var) *)
    
  let get_mp_opt rmap (x:var_i) =
    let xv = L.unloc x in
    match Mv.Exceptionless.find xv rmap.var_region with
    | Some (IMP mp) -> Some mp
    | _ -> None

  let get_mp rmap (x:var_i) = 
    let xv = L.unloc x in
    let imp = 
      try Mv.find xv rmap.var_region
      with Not_found ->
        hierror "no associated region for %a (the pointer may be not initialized)" 
          (Printer.pp_var ~debug:true) xv in
    match imp with
    | IMP mp -> mp 
    | IMP_error None ->
      hierror "@[At %a: some path do not initialize the variable %a@]" 
        L.pp_loc (L.loc x) (Printer.pp_var ~debug:true) xv 
    | IMP_error (Some smp) ->
      let pp_from fmt mps = 
        let y = mps.mps_mp.mp_s in
        Format.fprintf fmt "%a declared at %a" (Printer.pp_var ~debug:true) y L.pp_loc y.v_dloc in
      hierror "@[the variable %a is bound to different regions: %a@]"
        (Printer.pp_var ~debug:true) xv 
        (pp_list ",@ " pp_from) (Smps.elements smp)
      
   
  let empty_sub_map = {
      sm_base = Sv.empty;
      sm_sub  = Msmp.empty;
    }

  let get_sub_map mp rmap  = 
    Mmp.find_default empty_sub_map mp rmap.region_var 
    
  let get_xs mps rmap = 
    let sub_map = get_sub_map mps.mps_mp rmap in
    match mps.mps_sub with
    | None -> sub_map.sm_base
    | Some sub -> Msmp.find_default Sv.empty sub sub_map.sm_sub

  let check_valid rmap (x:var_i) =
(*    Format.eprintf "check_valid@.";
    Format.eprintf "%a@." pp_rmap rmap; *)
    let mp = get_mp rmap x in
    let pp_error xs = 
      hierror
      "@[<v>(check alias) the variable %a points to the region of %a,@ which only contains the values of variables {@[%a@]}@]"
      (Printer.pp_var ~debug:true) (L.unloc x) (Printer.pp_var ~debug:true) mp.mps_mp.mp_s
      (pp_list ",@ " (Printer.pp_var ~debug:true)) (Sv.elements xs) in
    let xs = get_xs mp rmap in
    if not (Sv.mem (L.unloc x) xs) then pp_error xs;
    mp

  let set_align (x:var_i) {mps_mp = mp; mps_sub = _sub} ws =
    (* FIXME: should we check that sub.mps_ofs is agree with the alignment *)
    let xws = info mp.mp_align in   
    if wsize_lt xws ws then 
      try update ws mp.mp_align 
      with NotModifiable ->
        hierror "the alignment of %a is forced to %s, and %s is required" 
          pp_var x (string_of_ws xws) (string_of_ws ws)
           

  let set_writable (x:var_i) {mps_mp = mp} = 
    if not (info mp.mp_writable) then
      try update true mp.mp_writable
      with NotModifiable ->
        hierror "%a is not writable" pp_var x

  
  let remove_sub sub sub_map = 
    { sm_base = Sv.empty;
      sm_sub  = Msmp.filter (fun sub' _xs -> disjoint_sub_mp sub sub') sub_map.sm_sub; }

  let remove rmap {mps_mp = mp; mps_sub = sub } = 
    let region_var = 
      match sub with
      | None -> Mmp.remove mp rmap.region_var
      | Some sub ->
        let sub_map = get_sub_map mp rmap in
        let sub_map = remove_sub sub sub_map in
        Mmp.add mp sub_map rmap.region_var in
    { rmap with region_var }


  let remove_sub sub sub_map = 
    { sm_base = Sv.empty;
      sm_sub  = Msmp.filter (fun sub' _xs -> disjoint_sub_mp sub sub') sub_map.sm_sub; }

  let set_sub_map x sub sub_map = 
    { sub_map with sm_sub = Msmp.add sub (Sv.singleton x) sub_map.sm_sub }
  (* [ofs:len] is assumed to be a sub region of mps.mps_sub *)
  let rset_word rmap x ofs len ({mps_mp = mp; mps_sub = sub} as mps) =
    let sub_map = 
      match sub, ofs with
      | None, None -> 
        { sm_base = Sv.singleton x;
          sm_sub  = Msmp.empty }
      | None, Some ofs ->
        let subr = { smp_ofs = ofs; smp_len = len } in
        let sub_map = remove_sub subr (get_sub_map mp rmap) in
        { sub_map with sm_base = Sv.singleton x }
      | Some sub, None ->
        let subr = sub in
        let sub_map = remove_sub subr (get_sub_map mp rmap) in
        set_sub_map x sub sub_map
      | Some sub, Some ofs -> 
        let subr = { smp_ofs = sub.smp_ofs + ofs; smp_len = len } in
        let sub_map = remove_sub subr (get_sub_map mp rmap) in
        set_sub_map x sub sub_map
    in
 
    { rmap with 
      var_region = Mv.add x (IMP mps) rmap.var_region;
      region_var = Mmp.add mp sub_map rmap.region_var }

  let rset_full rmap x mp = 
    rset_word rmap x None 0 {mps_mp = mp; mps_sub = None}

  let set_word rmap x ofs ws mp =
    set_writable x mp;
    set_align x mp ws;
    rset_word rmap (L.unloc x) ofs (size_of_ws ws) mp

  let set_sub x sub sub_map = 
    match sub with
    | None -> { sub_map with sm_base = Sv.add x sub_map.sm_base }
    | Some sub ->
      { sub_map with 
        sm_sub = 
          let xs = Msmp.find_default Sv.empty sub sub_map.sm_sub in
          Msmp.add sub (Sv.add x xs) sub_map.sm_sub }

  let set rmap x ({mps_mp = mp; mps_sub = sub} as mps) = 
    let x = L.unloc x in
    let sub_map = set_sub x sub (get_sub_map mp rmap) in
    { rmap with 
      var_region = Mv.add x (IMP mps) rmap.var_region;
      region_var = Mmp.add mp sub_map rmap.region_var }

  let set_init rmap x pk = 
    match pk with
    | Pmem mp   -> set rmap x {mps_mp = mp; mps_sub = None}
    | Pregptr _ -> rmap

  let imp_incl imp1 imp2 = 
    match imp1, imp2 with
    | IMP mp1, IMP mp2 -> mps_equal mp1 mp2
    | IMP _,  IMP_error _ -> false
    | IMP_error _, _ -> true
    
  let incl_sub_map sub_map1 sub_map2 = 
    Sv.subset sub_map1.sm_base sub_map2.sm_base &&
      Msmp.for_all (fun sub xs ->
          Sv.subset xs (Msmp.find_default Sv.empty sub sub_map2.sm_sub)) sub_map1.sm_sub

  let incl r1 r2 = 
    ( Sf.subset r1.calls r2.calls) && 
    (* r1.has_stack => r2.has_stack *)
    ( not r1.has_stack || r2.has_stack ) && 
    Mv.for_all (fun x imp1 -> 
        try imp_incl imp1 (Mv.find x r2.var_region) 
        with Not_found -> 
          match imp1 with
          | IMP _ -> false
          | IMP_error _  -> true) r1.var_region &&
    Mmp.for_all (fun mp sub_map1 ->
        incl_sub_map sub_map1 (get_sub_map mp r2)) r1.region_var
        
  let merge_sub_map _ osm1 osm2 =
    match osm1, osm2 with
    | Some sm1, Some sm2 ->
      let merge_xs _ o1 o2 =
        match o1, o2 with
        | Some xs1, Some xs2 -> Some (Sv.inter xs1 xs2)
        | _, _               -> None in
      Some { sm_base = Sv.inter sm1.sm_base sm2.sm_base;
             sm_sub  = Msmp.merge merge_xs sm1.sm_sub sm2.sm_sub }
    | _, _ -> None
    
  let merge r1 r2 = 
    let merge_mp _ o1 o2 = 
      match o1, o2 with
      | Some (IMP mp1), Some (IMP mp2) -> 
        if mps_equal mp1 mp2 then o1 else Some (IMP_error (Some (Smps.of_list [mp1;mp2])))
      | Some imp1, Some imp2 ->
        let get_error = function
          | IMP mp1 -> Some (Smps.singleton mp1)
          | IMP_error e -> e in
        let os = match get_error imp1, get_error imp2 with 
        | Some s1, Some s2 -> Some (Smps.union s1 s2)
        | _, _ -> None
        in
        Some (IMP_error os)
      | None, Some _ | Some _, None -> Some (IMP_error None) 
      | None, None -> None 
    in
    { 
      calls      = Sf.union r1.calls r2.calls;
      has_stack  = r1.has_stack  || r2.has_stack;
      var_region = Mv.merge merge_mp r1.var_region r2.var_region;
      region_var = Mmp.merge merge_sub_map r1.region_var r2.region_var; }

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
    | Psub _ -> assert false
    | Pload(ws, x, e)  -> Pload(ws, x, alloc_e e)
    | Papp1(o,e)       -> Papp1(o, alloc_e e) 
    | Papp2(o,e1,e2)   -> Papp2(o, alloc_e e1, alloc_e e2)
    | PappN(o,es)      -> PappN(o, List.map alloc_e es)
    | Pif(ty,e1,e2,e3) -> Pif(ty, alloc_e e1, alloc_e e2, alloc_e e3) in
  alloc_e e

let alloc_es pmap rmap es = List.map (alloc_e pmap rmap) es

(* ---------------------------------------------------------- *)
let get_ofs aa ws e = 
  match e with
  | Pconst i ->
    Some (if aa = Warray_.AAdirect then B.to_int i else size_of_ws ws * (B.to_int i))
  | _ -> None 

let alloc_lval pmap rmap (r:lval) =
  match r with
  | Lnone _ -> (rmap, r) 
  | Lvar x  -> 
    begin match get_var_kind pmap x with
    | None -> (rmap, r) 
    | Some (Pregptr _) -> assert false (* pointer to word *)
    | Some (Pmem mp as pk) ->
      let ws = ws_of_ty (L.unloc x).v_ty in
      let rmap = Region.set_word rmap x None ws { mps_mp = mp; mps_sub = None } in
      let r = Lmem(ws, mk_addr x pk, icnst 0) in (* not well typed, but ... *)
      (rmap, r)
    end

  | Laset (aa,ws,x,e1) -> 
    let e1 = alloc_e pmap rmap e1 in
    begin match get_var_kind pmap x with
    | None -> (rmap, r)
    | Some pk ->
      let mp = Region.check_valid rmap x in
      let rmap = Region.set_word rmap x (get_ofs aa ws e1) ws mp in
      let r = Lmem (ws, mk_addr x pk, e1) in
      (rmap, r)
    end
  | Lasub _ -> assert false
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

let get_addr is_spilling rmap x dx y = 
  let yv = y.gv in
  let mpy = Region.check_valid rmap y.gv in
  let py = L.mk_loc (L.loc yv) mpy.mps_mp.mp_p in
  let i = 
    match Region.get_mp_opt rmap x with
    | Some mpx when is_spilling && mps_equal mpx mpy -> nop
    | _ ->
      if is_gkvar y then
        match (L.unloc yv).v_kind with
        | Stack Direct  -> lea_ptr dx py
        | Stack (Pointer _) -> mov_ptr dx (Pload(U64, py,icnst 0))
        | Reg (Pointer _)  -> mov_ptr dx (Pvar (gkvar py))
        | _ -> assert false 
      else lea_ptr dx py in
  let rmap = Region.set rmap x mpy in 
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
        (* FIXME CHECK SUB REGION = None *)
        if not (V.equal (L.unloc x) mpy.mps_mp.mp_s) then 
          hierror "(check alias) invalid move, the variable %a points to the region of %a instead of %a"
             pp_var y (Printer.pp_var ~debug:true) mpy.mps_mp.mp_s pp_var x;
        let rmap = Region.set rmap x mpy in
        (rmap, nop)
      | Stack (Pointer _)->
        get_addr true rmap x (Lmem(U64, mk_addr x pk, icnst 0)) y
      | Reg (Pointer _) ->
        get_addr false rmap x (Lvar (mk_addr x pk)) y
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
  { sao_has_stack : bool
  ; sao_calls  : Sf.t
  ; sao_params : param_info option list (* Allocation of pointer params *)
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
      if not (is_reg_ptr_kind k) then
         hierror "%a should be a reg ptr" pp_var xv;
      let mp = Region.check_valid rmap xv in
      Region.set_align xv mp pi.pi_align;
      if pi.pi_writable then Region.set_writable xv mp;
      (Some (pi.pi_writable, mp), Pvar (gkvar (mk_addr xv pk)))
    end
  | _ -> 
    hierror "the expression %a is not a variable" 
      (Printer.pp_expr ~debug:false) e

let mp_in mps = 
  List.exists (fun mps' ->
      mp_equal mps.mps_mp mps'.mps_mp && 
        match mps.mps_sub, mps'.mps_sub with
        | None, _ | _, None -> true
        | Some sub, Some sub' -> not (disjoint_sub_mp sub sub')) 

let rec check_all_disj (notwritables:mem_pos_sub list) (writables:mem_pos_sub list)
                       (mps: ((bool * mem_pos_sub) option * expr) list) = 
  match mps with
  | [] -> true
  | (None, _) :: mps -> check_all_disj notwritables writables mps
  | (Some (writable, mp), _) :: mps -> 
    if mp_in mp writables then false
    else
      if writable then 
        if mp_in mp notwritables then false
        else check_all_disj notwritables (mp::writables) mps
      else   check_all_disj (mp::notwritables) writables mps
  


(* Remark we did not check disjointness here *)
let alloc_call_args pmap rmap soa_params es = 
  let mps = List.map2 (alloc_call_arg pmap rmap) soa_params es in
  if not (check_all_disj [] [] mps) then
    hierror "the pointers arguments are not disjoints";
  mps
  


(* ---------------------------------------------------------- *)
exception CallRetReg of lval

let check_lval_reg_call (r:lval) = 
  match r with
  | Lnone _ -> ()
  | Lvar x ->
    if (L.unloc x).v_kind <> Reg Direct then
      hierror "%a should be a register" pp_var x
  | _ -> raise (CallRetReg r)

let alloc_lval_call mps pmap rmap r i =
  match i with
  | None -> 
    check_lval_reg_call r;
    (rmap, r)
  | Some i ->
    match List.nth mps i with
    | (None,_) -> assert false
    | (Some (_,mp),_) ->
      match r with
      | Lvar x ->
        if not (is_reg_ptr_kind (L.unloc x).v_kind) then
          hierror "%a should be a reg ptr" pp_var x;
        let pk = get_pk pmap x in
        let xv = L.unloc x in
        let len = size_of xv.v_ty in
        let rmap = Region.rset_word rmap xv (Some 0) len mp in
        rmap, Lvar (mk_addr x pk)
      | _ -> hierror "%a should be a reg ptr" (Printer.pp_lval ~debug:false) r


let remove_writable_arg rmap (mp,_e) = 
  match mp with
  | Some (writable, mp) -> if writable then Region.remove rmap mp else rmap
  | _ -> rmap 

let alloc_call_res pmap rmap mps ret_pos rs = 
  let rmap = List.fold_left remove_writable_arg rmap mps in
  let (rmap, rs) = List.map_fold2 (alloc_lval_call mps pmap) rmap rs ret_pos in
  rmap, rs 


(* ---------------------------------------------------------- *)

let alloc_call local_alloc pmap rmap ini rs fn es = 
  let sao = local_alloc fn in
  let rmap = Region.set_call rmap fn sao.sao_has_stack in
  let es  = alloc_call_args pmap rmap sao.sao_params es in
  let (rmap,rs)  = alloc_call_res pmap rmap es sao.sao_return rs in
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
      hierror "@[<v>At %a:@ %s@]" Printer.pp_iloc i.i_loc s
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
    rmap := Region.rset_full !rmap x mp
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
  let add_param x =
    match x.v_kind with
    | Reg (Pointer writable) ->
      assert (is_ty_arr x.v_ty);
      let xp = V.mk x.v_name (Reg Direct) (tu uptr) x.v_dloc in
      let mp = {
        mp_s = x;
        mp_p = xp;
        mp_align = Info.init U8 true;
        mp_writable = Info.init (writable=Writable) false; } in
      pmap := Mv.add x (Pmem mp) !pmap;
      rmap := Region.rset_full !rmap x mp;
      Some mp
    | Reg Direct -> 
      None
    | _ -> hierror "kind of %a should be reg of reg ptr" 
             (Printer.pp_var ~debug:false) x in

  let paramsi = List.map add_param params in

  let add_local x = 
    match x.v_kind with
    | Stack Direct ->
      let mp = {
        mp_s = x;
        mp_p = rsp;
        mp_align = Info.init (initial_alignment x) true;
        mp_writable = Info.init true true;
      } in 
      rmap := Region.set_stack !rmap;
      pmap := Mv.add x (Pmem mp) !pmap;
      rmap := Region.rset_full !rmap x mp;
    | Stack (Pointer _) ->
      let mp = {
        mp_s = x;
        mp_p = rsp;
        mp_align = Info.init uptr false;
        mp_writable = Info.init true false;
      } in 
      rmap := Region.set_stack !rmap;
      pmap := Mv.add x (Pmem mp) !pmap
    | Reg Direct ->
      ()
    | Reg (Pointer _) -> 
      let xp = V.mk x.v_name (Reg Direct) (tu uptr) x.v_dloc in
      pmap := Mv.add x (Pregptr xp) !pmap
    | _ -> assert false
  in
  Sv.iter add_local fv;
  paramsi, !pmap, !rmap, fv

(* ---------------------------------------------------------- *)

let alloc_fd local_alloc pmap rmap fd =
  try 
  let sao_return = 
    match fd.f_cc with
    | Export -> List.map (fun _ -> None) fd.f_ret 
    | Subroutine {returned_params} -> returned_params
    | Internal -> assert false in

  let paramsi, pmap, rmap, locals = init_locals pmap rmap fd in
  let rmap, f_body = alloc_c local_alloc pmap rmap fd.f_body in

  let sao_has_stack = Region.has_stack rmap || fd.f_annot.retaddr_kind = Some OnStack in

  let do_res x oi=
    let xv = L.unloc x in
    match xv.v_kind, oi with
    | Reg Direct, None -> x
    | Reg (Pointer _), Some i ->
      let mp = Region.check_valid rmap x in
      let mpi = oget (List.nth paramsi i) in
      if not (V.equal mpi.mp_s mp.mps_mp.mp_s && mp.mps_sub = None ) then
        hierror "invalid reg ptr %a" pp_var x;
      let pk = get_pk pmap x in
      mk_addr x pk
    | _ -> assert false in

  let f_ret = List.map2 do_res fd.f_ret sao_return in
  
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

  let sao_calls = Region.calls rmap in
  let sao = 
    { sao_calls; sao_has_stack; sao_params; sao_return; sao_alloc } in

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

  let fds = List.map do_fd (List.rev fds) in
  pmap, (List.rev fds)


(* ---------------------------------------------------------- *)

type pos_kind =
  | Pstack of int * Wsize.wsize
  | Pregptr of var 
  | Pstkptr of int

let set_align align ws = 
  if wsize_lt !align ws then align := ws 

let init_alloc xmem pmap = 
  let vars = ref [] in
  let alloc = ref [] in
  let align = ref U8 in

  let add_var x mp =
    match mp with
    | Pmem mp ->
      assert (V.equal mp.mp_p xmem);
      let ws, s = 
        if is_stk_ptr_kind x.v_kind then uptr, size_of_ws uptr
        else
          let ws = Info.info mp.mp_align in
          let s  = size_of x.v_ty in
          ws, s in
      set_align align ws;
      vars := (false,x,ws,s) :: !vars
    | Pregptr p -> 
      alloc := (x, Pregptr p) :: !alloc 
  in
  Mv.iter add_var pmap;
  vars, alloc, align

let cmp (_,_,ws1,_) (_,_,ws2,_) = 
  match Wsize.wsize_cmp ws1 ws2 with
  | Lt -> -1
  | Eq -> 0
  | Gt -> 1 
 
let alloc_stack pmap extra = 
  let vars, alloc, align = init_alloc rsp pmap in

  let add_extra x = 
    let ws = ws_of_ty x.v_ty in
    let s  = size_of_ws ws in
    set_align align ws;
    vars := (true,x,ws,s)::!vars in
  List.iter add_extra extra;

  let vars = List.sort cmp !vars in
  let etbl = Hv.create 17 in

  let mk_pos x pos ws = 
    let dest = 
      if is_stk_ptr_kind x.v_kind then Pstkptr pos
      else Pstack(pos, ws) in
    alloc := (x, dest) :: !alloc in

  let size = ref 0 in
  let init_var (isextra,x,ws,n) =
    let s = size_of_ws ws in
    let pos = !size in
    let pos = 
      if pos mod s = 0 then pos
      else (pos/s + 1) * s in
    size := pos + n;
    if isextra then Hv.add etbl x pos
    else mk_pos x pos ws in

  List.iter init_var vars;
  let extra = List.map (fun x -> Hv.find etbl x) extra in

  List.rev !alloc, !size, !align, extra

let alloc_mem pmap globs = 
  (* FIXME: propagate the alignment of globs *)
  let vars, _alloc, _ = init_alloc rip pmap in
  let vars = List.sort cmp !vars in

  let size = ref 0 in
  let data = ref [] in
  let get x = 
    try List.assoc x globs with Not_found -> assert false in

  let init_var (_, v, ws, n) =
    let pos = !size in
    let pos = 
      let s = size_of_ws ws in
      if pos mod s = 0 then pos
      else 
        let new_pos = (pos/s + 1) * s in
        (* fill data with 0 *)
        for i = 0 to new_pos - pos - 1 do
          data := Word0.wrepr U8 (Conv.z_of_int 0) :: !data
        done;
        new_pos in
    (* fill data with the corresponding values *)
    begin match get v with
    | Global.Gword(ws, w) ->
      let w = Memory_model.LE.encode ws w in
      data := List.rev_append w !data 
    | Global.Garr(p, t) ->
      let ip = Conv.int_of_pos p in
      for i = 0 to ip - 1 do
        let w = 
          match Warray_.WArray.get p Warray_.AAdirect U8 t (Conv.z_of_int i) with
          | Ok w -> w
          | _    -> assert false in
        data := w :: !data
      done 
    end;
    size := pos + n;
    (v,(pos,ws)) in
  let alloc = List.map init_var vars in
  let data = List.rev !data in
  data, alloc



  
  
    
    



  





    

    





    

