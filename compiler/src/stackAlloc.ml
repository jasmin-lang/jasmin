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
    mps_sub: sub_mp;
  }

let mps_equal mps1 mps2 = 
  mp_equal mps1.mps_mp mps2.mps_mp && 
    mps1.mps_sub = mps2.mps_sub

module MpsCmp = struct
  type t = mem_pos_sub
  let compare x y = 
    let c = MpCmp.compare x.mps_mp y.mps_mp in
    if c = 0 then SMpCmp.compare x.mps_sub y.mps_sub
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

module ByteSet : sig
  type interval = { min : int; max : int }

  type t
  val empty  : t
  val is_empty : t -> bool

  val memi   : int -> t -> bool
  val mem    : interval -> t -> bool
  val subset : t -> t -> bool

  val full   : interval -> t
  val add    : interval -> t -> t
  val remove : interval -> t -> t
  val inter  : t -> t -> t 

end = struct

  (* Represents the interval [min, max) *)
  type interval = { min : int; max:int }
  
  type t = interval list (* sorted in increasing order, no overlap *)

  let empty = []
  let is_empty t = t == []

  let full n = [n]

  let memi_inter i inter = inter.min <= i && i < inter.max

  let rec memi i t = 
    match t with
    | [] -> false
    | n::t -> memi_inter i n || (n.max <= i && memi i t)

  let is_empty_inter n = n.max <= n.min
            
  let subset_inter n1 n2 = n2.min <= n1.min && n1.max <= n2.max

  let rec mem n t = 
    match t with
    | [] -> false
    | n'::t -> subset_inter n n' || (n'.max <= n.min) && mem n t

  let rec add n t = 
    match t with
    | [] -> [n]
    | n'::t' ->
      if n.max < n'.min then n :: t
      else if n'.max < n.min then n' :: add n t'
      else 
        let n = { min = min n.min n'.min; 
                  max = max n.max n'.max } in
        add n t'

  let push n t = if is_empty_inter n then t else n :: t

  let rec remove excl t = 
    match t with
    | [] -> t
    | n' :: t' ->
      let n1 = { min = n'.min; max = min n'.max excl.min } in
      let n2 = { min = max n'.min excl.max; max = n'.max } in
      let excl = {min = max n'.max excl.min; max = excl.max } in
      let t' = if is_empty_inter excl then t' else remove excl t' in
      push n1 (push n2 t')

  let rec subset t1 t2 = 
    match t1, t2 with
    | [], _ -> true
    | _::_, [] -> false
    | n1::t1', n2::t2' ->
      if subset_inter n1 n2 then subset t1' t2
      else 
        if n2.max <= n1.min then subset t1 t2'
        else false

  let rec inter t1 t2 = 
    match t1, t2 with
    | _, [] | [], _ -> []
    | n1::t1', n2 :: t2' ->
      if n1.max <= n2.min then inter t1' t2
      else if n2.max <= n1.min then inter t1 t2'
      else 
        let n = { min = max n1.min n2.min;
                  max = min n1.max n2.max; } in
        let n1' = { min = max n2.max n1.min; max = n1.max } in
        let n2' = { min = max n1.max n2.min; max = n2.max } in
        n :: inter (push n1' t1') (push n2' t2') 
        
  let pp_inter fmt t = 
    List.iter (fun n -> Format.fprintf fmt "[%i..%i) " n.min n.max) t

end

module Region  : 
sig
  type regions 
  val empty        : regions
(*  val pp_rmap      : Format.formatter -> regions -> unit *)
  val check_valid  : regions -> var_i -> int option -> int -> mem_pos_sub
  val get_mp_opt   : regions -> var_i -> mem_pos_sub option 
  val set_align    : var_i -> mem_pos_sub -> Wsize.wsize -> unit
  val set_writable : var_i -> mem_pos_sub -> unit
  val set_arr_init : regions -> var -> mem_pos_sub -> regions
  val set_full     : regions -> var -> mem_pos -> regions 
  val set_word     : regions -> var_i -> mem_pos -> wsize -> regions
  val set_arr_word : regions -> var_i -> int option -> wsize -> regions
  val set_arr_sub  : regions -> var_i -> int -> int -> mem_pos_sub -> regions 
  val set_move     : regions -> var_i -> mem_pos_sub -> regions
  val set_arr_call : regions -> var_i -> mem_pos_sub -> regions 

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

  type subspace = {
      xs    : Sv.t;          (* All the variable that are known to point to that region *)
      bytes : ByteSet.t; (* Set of valid positions *)
    }

  type sub_map = subspace Msmp.t

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

  let pp_mps fmt mps = 
    Format.fprintf fmt "%a[%i:%i]"
      (Printer.pp_var ~debug:true) mps.mps_mp.mp_s 
      mps.mps_sub.smp_ofs mps.mps_sub.smp_len

  let pp_rmap fmt rmap = 
    let pp_var = (Printer.pp_var ~debug:true) in
    let pp_sub_map mp fmt sub_map =
      (Printer.pp_list "@ "
         (fun fmt (sub,ss) ->
           Format.fprintf fmt "%a -> {@[%a@]}"
             pp_mps {mps_mp = mp; mps_sub = sub}
             (Printer.pp_list ",@ " pp_var) (Sv.elements ss.xs)))
        fmt (Msmp.bindings sub_map) in
             
    Format.fprintf fmt "@[<v>%a@ ------@ %a@]"
      (Printer.pp_list "@ " (fun fmt (x,mps) -> 
        match mps with
        | IMP mps ->
           Format.fprintf fmt "%a -> %a" pp_var x 
             pp_mps mps
        | IMP_error _ -> Format.fprintf fmt "error"))
      (Mv.bindings rmap.var_region)
      (Printer.pp_list "@ " 
         (fun fmt (mp,sub_map) -> pp_sub_map mp fmt sub_map))
      (Mmp.bindings rmap.region_var) 
    
  let get_mp_opt rmap (x:var_i) =
    let xv = L.unloc x in
    match Mv.Exceptionless.find xv rmap.var_region with
    | Some (IMP mp) -> Some mp
    | _ -> None

  let get_mps rmap (x:var_i) = 
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
      
  let empty_subspace = {
      xs = Sv.empty;
      bytes = ByteSet.empty;
    }

  let empty_sub_map = Msmp.empty

  let get_sub_map mp rmap  = 
    Mmp.find_default empty_sub_map mp rmap.region_var 
    
  let get_subspace mps rmap = 
    let sub_map = get_sub_map mps.mps_mp rmap in
    Msmp.find_default empty_subspace mps.mps_sub sub_map

  let xs_error x mps xs = 
    hierror
      "@[<v>(check alias) the variable %a points to the region of %a,@ which only contains the values of variables {@[%a@]}@]"
      (Printer.pp_var ~debug:true) (L.unloc x) (Printer.pp_var ~debug:true) mps.mps_mp.mp_s
      (pp_list ",@ " (Printer.pp_var ~debug:true)) (Sv.elements xs)

  (* FIXME improve error message *)
  let partial_error () =
    hierror "@[try to read a region that is partially known@]"
    
  let interval_of_sub sub = ByteSet.({min = sub.smp_ofs; max = sub.smp_ofs + sub.smp_len})
 
  let sub_ofs sub ofs len = 
    match ofs with
    | None -> sub
    | Some ofs -> { smp_ofs = sub.smp_ofs + ofs; smp_len = len } 

  let check_valid rmap (x:var_i) ofs len =
    let mps = get_mps rmap x in
    let ss = get_subspace mps rmap in
    if not (Sv.mem (L.unloc x) ss.xs) then xs_error x mps ss.xs;
    let sub_ofs = sub_ofs mps.mps_sub ofs len in
    let isub_ofs = interval_of_sub sub_ofs in
    if not (ByteSet.mem isub_ofs ss.bytes) then partial_error ();
    { mps with mps_sub = sub_ofs }

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
      
  let set_word rmap x mp ws =
    let sub = { smp_ofs = 0; smp_len = size_of_ws ws} in
    let mps = { mps_mp = mp; mps_sub = sub } in
    set_writable x mps;
    set_align x mps ws;
    let full = ByteSet.full (interval_of_sub sub) in
    let x = L.unloc x in
    let sub_map = 
      Msmp.add sub { xs = Sv.singleton x; bytes = full } Msmp.empty in
    { rmap with 
      var_region = Mv.add x (IMP mps) rmap.var_region;
      region_var = Mmp.add mps.mps_mp sub_map rmap.region_var }
 
  (* [ofs:len] is assumed to be a sub region of mps.mps_sub *)
  let set_arr_word rmap x ofs ws =
    let len = size_of_ws ws in
    (* part of check_valid, but do not check validity of bytes *)
    let mps = get_mps rmap x in
    let ss = get_subspace mps rmap in
    if not (Sv.mem (L.unloc x) ss.xs) then xs_error x mps ss.xs;
    (* end check_valid *)
    set_writable x mps;
    set_align x mps ws;
    let sub_map = get_sub_map mps.mps_mp rmap in
    let sub = mps.mps_sub in
    let inter_ofs = interval_of_sub (sub_ofs sub ofs len) in
    let xv = L.unloc x in
    let doit sub' subspace =
      if sub = sub' then 
        let bytes = 
          match ofs with 
          | None -> subspace.bytes 
          | Some i -> ByteSet.add { min = i; max = i + len } subspace.bytes in
        { xs = Sv.singleton xv; bytes }
      else { subspace with bytes = ByteSet.remove inter_ofs subspace.bytes } in
    let sub_map = Msmp.mapi doit sub_map in
    { rmap with 
      var_region = Mv.add xv (IMP mps) rmap.var_region;
      region_var = Mmp.add mps.mps_mp sub_map rmap.region_var }

  (* [ofs:len] is assumed to be a sub region of mps.mps_sub *)
  let set_arr_call rmap x mps =
    let sub = mps.mps_sub in
    let inter_ofs = interval_of_sub sub  in
    let sub_map = get_sub_map mps.mps_mp rmap in
    let xv = L.unloc x in
    let ss =  
      { xs = Sv.singleton xv; 
        bytes = ByteSet.full inter_ofs } in
    let sub_map = Msmp.add sub ss sub_map in
    let doit sub' subspace =
      if sub = sub' then subspace 
      else { subspace with bytes = ByteSet.remove inter_ofs subspace.bytes } in
    let sub_map = Msmp.mapi doit sub_map in
    { rmap with 
      var_region = Mv.add xv (IMP mps) rmap.var_region;
      region_var = Mmp.add mps.mps_mp sub_map rmap.region_var }

  let set_arr_sub rmap x ofs len mps_from = 
    let mps = get_mps rmap x in
    let ss = get_subspace mps rmap in
    if not (Sv.mem (L.unloc x) ss.xs) then xs_error x mps ss.xs;
    let sub = mps.mps_sub in
    let sub_ofs = { smp_ofs = sub.smp_ofs + ofs; smp_len = len } in
    if not (mp_equal mps.mps_mp mps_from.mps_mp && sub_ofs = mps_from.mps_sub) then
      hierror "set array: source and destination are not equal";
    let sub_map = get_sub_map mps.mps_mp rmap in
    let xv = L.unloc x in
    let ss =        
      { xs = Sv.singleton xv; 
        bytes = ByteSet.add (interval_of_sub sub_ofs) ss.bytes } in
    let sub_map = Msmp.add sub ss sub_map in
    { rmap with 
      var_region = Mv.add xv (IMP mps) rmap.var_region;
      region_var = Mmp.add mps.mps_mp sub_map rmap.region_var }
    
  let set_move rmap x mps =
    let sub_map = get_sub_map mps.mps_mp rmap in
    let xv = L.unloc x in
    let ss = 
      try Msmp.find mps.mps_sub sub_map
      with Not_found -> 
        { xs = Sv.empty; bytes = ByteSet.full (interval_of_sub mps.mps_sub) } in
    let ss = { ss with xs = Sv.add xv ss.xs } in
    let sub_map = Msmp.add mps.mps_sub ss sub_map in
    { rmap with 
      var_region = Mv.add xv (IMP mps) rmap.var_region;
      region_var = Mmp.add mps.mps_mp sub_map rmap.region_var }

  let set_arr_init rmap x mps = 
    let mp  = mps.mps_mp in
    let sub = mps.mps_sub in
    let isub = interval_of_sub sub in
    let ss = get_subspace mps rmap in
    let ss = 
      if ByteSet.mem isub ss.bytes then 
        { xs = Sv.add x ss.xs; bytes = ss.bytes}
      else 
        { xs = Sv.singleton x; bytes = ByteSet.full isub } in
    let sub_map = get_sub_map mp rmap in
    let sub_map = Msmp.add sub ss sub_map in
    { rmap with
      var_region = Mv.add x (IMP mps) rmap.var_region;
      region_var = Mmp.add mp sub_map rmap.region_var}

  let set_full rmap x mp = 
    let len = size_of x.v_ty in
    let sub = { smp_ofs = 0; smp_len = len } in
    let mps = { mps_mp = mp; mps_sub = sub } in
    let ss = 
      {xs = Sv.singleton x; bytes= ByteSet.full (interval_of_sub sub) } in
    let sub_map = Msmp.add sub ss Msmp.empty in
    { rmap with 
      var_region = Mv.add x (IMP mps) rmap.var_region;
      region_var = Mmp.add mp sub_map rmap.region_var }
 
  let imp_incl imp1 imp2 = 
    match imp1, imp2 with
    | IMP mp1, IMP mp2 -> mps_equal mp1 mp2
    | IMP _,  IMP_error _ -> false
    | IMP_error _, _ -> true
    

  let incl_sub_map sm1 sm2 = 
    Msmp.for_all (fun sub ss1 ->
      match Msmp.find sub sm2 with 
      | ss2 -> Sv.subset ss1.xs ss2.xs && ByteSet.subset ss1.bytes ss2.bytes 
      | exception Not_found -> Sv.is_empty ss1.xs && ByteSet.is_empty ss1.bytes) sm1 

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
    Mmp.for_all (fun mp sm1 -> incl_sub_map sm1 (get_sub_map mp r2)) r1.region_var
        
  let merge_subspace _ oss1 oss2 = 
    match oss1, oss2 with
    | Some ss1, Some ss2 ->
      Some { xs    = Sv.inter ss1.xs ss2.xs;
             bytes = ByteSet.inter ss1.bytes ss2.bytes; }
    | _, _ -> None

  let merge_sub_map _ osm1 osm2 =
    match osm1, osm2 with
    | Some sm1, Some sm2 -> Some (Msmp.merge merge_subspace sm1 sm2)
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
        let ws = ws_of_ty (L.unloc x).v_ty in
        let mp = Region.check_valid rmap x (Some 0) (size_of_ws ws) in
        Region.set_align x mp ws;
        let p = mk_addr x pk in
        Pload(ws, p, icnst 0) (* not well typed, but not important *)
      end
    | Pget(aa, ws, x, e1) ->
      let x = x.gv in
      let e1 = alloc_e e1 in
      begin match get_var_kind pmap x with
      | None -> e
      | Some pk -> 
        let ofs = get_ofs aa ws e1 in
        let mp = Region.check_valid rmap x ofs (size_of_ws ws) in
        Region.set_align x mp ws;
        let p = mk_addr x pk in
        Pload(ws, p, e1) (* not well typed, but not important *)
      end
    | Psub _ -> 
      hierror "%a sub-array expression not allowed here" (Printer.pp_expr ~debug:true) e

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
      let rmap = Region.set_word rmap x mp ws        
in
      let r = Lmem(ws, mk_addr x pk, icnst 0) in (* not well typed, but ... *)
      (rmap, r)
    end

  | Laset (aa,ws,x,e1) -> 
    let e1 = alloc_e pmap rmap e1 in
    begin match get_var_kind pmap x with
    | None -> (rmap, r)
    | Some pk ->
      let ofs = get_ofs aa ws e1 in
      let rmap = Region.set_arr_word rmap x ofs ws in
      let r = Lmem (ws, mk_addr x pk, e1) in
      (rmap, r)
    end
  | Lasub _ -> 
    hierror "%a subarray not allowed here" (Printer.pp_lval ~debug:true) r
  | Lmem(ws, x, e1) -> 
    let e1 = alloc_e pmap rmap e1 in
    (rmap, Lmem(ws, x, e1))

let alloc_lvals pmap rmap rs = List.map_fold (alloc_lval pmap) rmap rs

(* ---------------------------------------------------------- *)
let nop = Copn([], AT_none, Expr.Onop, [])

let lea_ptr x ptr _ofs = 
  Copn([x], AT_none, Expr.Ox86 (LEA U64), [Pvar (gkvar ptr)])

let mov_ptr x ptr =
  Copn([x], AT_none, Expr.Ox86 (MOV U64), [ptr])


let get_addr is_spilling pmap rmap x dx y mpsy ofs = 
  let yv = y.gv in
  let i = 
    match Region.get_mp_opt rmap x with
    | Some mpsx when is_spilling && mps_equal mpsx mpsy && ofs = 0 -> nop
    | _ ->
      let py = 
        match get_var_kind pmap yv with
        | None -> hierror "register array remains %a, please report" pp_var x
        | Some pk -> ptr_of_pk pk
      in
      let py = L.mk_loc (L.loc yv) py in
      if is_gkvar y then
        match (L.unloc yv).v_kind with
        | Stack Direct  -> lea_ptr dx py ofs
        | Stack (Pointer _) -> 
          if ofs <> ofs then hierror "cannot take a subarray of a stack pointer";
          mov_ptr dx (Pload(U64, py, icnst 0))
        | Reg (Pointer _)  -> 
          if ofs = 0 then mov_ptr dx (Pvar (gkvar py))
          else lea_ptr dx py ofs
        | _ -> assert false 
      else lea_ptr dx py ofs in
  let rmap = Region.set_move rmap x mpsy in 
  (rmap, i)
 

let get_ofs_sub aa ws e1 = 
  match get_ofs aa ws e1 with
  | None -> hierror "cannot take/set a subarray on a unknown starting position" 
  | Some ofs -> ofs

let alloc_array_move pmap rmap r e = 
  let x, xsub = 
    match r with
    | Lvar x -> x, None
    | Lasub(aa,ws,len,x,e1) -> 
      let ofs = get_ofs_sub aa ws e1 in
      x, Some(ofs, arr_size ws len) 
    | _ -> hierror "cannot reconnize lvalue of an array move" in
  let y, mpsy, ofs = 
    match e with
    | Pvar y -> 
      let (ws,n) = array_kind (L.unloc y.gv).v_ty in
      let len = arr_size ws n in
      y,  Region.check_valid rmap y.gv (Some 0) len, 0
    | Psub(aa,ws,len,y,e1) -> 
      let ofs = get_ofs_sub aa ws e1 in
      let len = arr_size ws len in
      let mps = Region.check_valid rmap y.gv (Some ofs) len in
      y, mps, ofs 
    | _ -> hierror "cannot reconnize expression of an array move" in

  match xsub with
  | None ->
    begin match get_var_kind pmap x with
    | None -> hierror "register array remains %a, please report" pp_var x
    | Some pk -> 
      match (L.unloc x).v_kind with
      | Stack Direct ->
        if not (is_gkvar y) then 
          hierror "can not move global to stack";
        let y = y.gv in
        if not (V.equal (L.unloc x) mpsy.mps_mp.mp_s) then 
          hierror "(check alias) invalid move, the variable %a points to the region of %a instead of %a"
            pp_var y (Printer.pp_var ~debug:true) mpsy.mps_mp.mp_s pp_var x;
        if not (
            mpsy.mps_sub.smp_ofs = 0 && mpsy.mps_sub.smp_len = size_of (L.unloc x).v_ty &&
              ofs = 0) then 
          hierror "invalid source";
        let rmap = Region.set_move rmap x mpsy in
        (rmap, nop)
      | Stack (Pointer _)->
        get_addr true pmap rmap x (Lmem(U64, mk_addr x pk, icnst 0)) y mpsy ofs
      | Reg (Pointer _) ->
        get_addr false pmap rmap x (Lvar (mk_addr x pk)) y mpsy ofs
      | _ -> assert false 
    end
  | Some (ofs, len) ->
    begin match get_var_kind pmap x with
    | None -> hierror "register array remains %a, please report" pp_var x
    | Some _ -> Region.set_arr_sub rmap x ofs len mpsy, nop
    end
 

let is_array_init e = 
  match e with
  | Parr_init _ -> true
  | _ -> false
 
let alloc_array_move_init pmap rmap r e =
  if is_array_init e then
    let x,ofs,len = 
      match r with
      | Lvar x -> 
        x, 0, size_of (L.unloc x).v_ty 
      | Lasub(aa,ws,len,x,e1) -> 
        let ofs = get_ofs_sub aa ws e1 in
        x, ofs, arr_size ws len
      | _ -> hierror "cannot reconnize lvalue of an array move" in
    let mps = 
      match (L.unloc x).v_kind with
      | Stack Direct ->
        begin match get_var_kind pmap x with
        | Some (Pmem mp) -> 
          {mps_mp = mp; mps_sub = {smp_ofs = ofs; smp_len = len }}
        | _              -> assert false 
        end
      | _ -> 
        match Region.get_mp_opt rmap x with
        | Some mps -> 
          { mps with mps_sub = { smp_ofs = mps.mps_sub.smp_ofs + ofs; smp_len = len}}
        | _ -> hierror "no region associated to %a" pp_var x in

    let rmap = Region.set_arr_init rmap (L.unloc x) mps in
    (rmap, nop)
  else alloc_array_move pmap rmap r e
 

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
      let mps = Region.check_valid rmap xv (Some 0) (size_of (L.unloc x.gv).v_ty) in
      Region.set_align xv mps pi.pi_align;
      if pi.pi_writable then Region.set_writable xv mps;
      (Some (pi.pi_writable, mps), Pvar (gkvar (mk_addr xv pk)))
    end
  | _ -> 
    hierror "the expression %a is not a variable" 
      (Printer.pp_expr ~debug:false) e

let mp_in mps = 
  List.exists (fun mps' ->
      mp_equal mps.mps_mp mps'.mps_mp && 
         not (disjoint_sub_mp mps.mps_sub mps'.mps_sub))

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
    | (Some (_,mps),_) ->
      match r with
      | Lvar x ->
        if not (is_reg_ptr_kind (L.unloc x).v_kind) then
          hierror "%a should be a reg ptr" pp_var x;
        let pk = get_pk pmap x in
        let rmap = Region.set_arr_call rmap x mps in
        rmap, Lvar (mk_addr x pk)
      | _ -> hierror "%a should be a reg ptr" (Printer.pp_lval ~debug:false) r

let alloc_call_res pmap rmap mps ret_pos rs = 
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
        if is_ty_arr ty then alloc_array_move_init pmap rmap r e
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
    rmap := Region.set_full !rmap x mp
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
      rmap := Region.set_full !rmap x mp;
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
      rmap := Region.set_full !rmap x mp;
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
      let mp = Region.check_valid rmap x (Some 0) (size_of xv.v_ty) in
      let mpi = oget (List.nth paramsi i) in
      if not (V.equal mpi.mp_s mp.mps_mp.mp_s) then
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

(* Bigger since first *)
let cmp (_,_,ws1,_) (_,_,ws2,_) = 
  match Wsize.wsize_cmp ws1 ws2 with
  | Lt -> 1
  | Eq -> 0
  | Gt -> -1 
 
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
  let extra = List.map (fun x -> x, Hv.find etbl x) extra in

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
