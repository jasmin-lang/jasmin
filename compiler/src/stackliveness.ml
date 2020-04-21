open Utils
open Prog



type live_elem = 
  | NotArray (* the full variable is in live *)
  | Array of ByteSet.t (* The set of bytes in live *)

module Live : sig
  type t
  val empty : t 
  val incl  : t -> t -> bool
  val union : t -> t -> t 
  val get   : var -> t -> live_elem 
  val set   : var -> live_elem -> t -> t
  val remove : var -> t -> t

  val pp : Format.formatter -> t -> unit

end = struct 

  (* Invariant : if [Array bs] in [m] then bs is not empty *)
  type t = live_elem Mv.t

  let empty = Mv.empty 

  exception NotIncl 

  let incl (il1:t) (il2:t) =
    let merge_elem _x oe1 oe2 = 
      match oe1, oe2 with
      | None, _ -> None
      | Some _, None -> raise NotIncl
      | Some elem1, Some elem2 ->
        begin match elem1, elem2 with
        | NotArray, NotArray -> None
        | Array bs1, Array bs2 -> 
          if not (ByteSet.subset bs1 bs2) then raise NotIncl;
          None
        | _, _ -> assert false
        end in
    try ignore (Mv.merge merge_elem il1 il2); true
    with NotIncl -> false

  let union il1 il2 = 
    let merge_elem _x oe1 oe2 = 
      match oe1, oe2 with
      | None, oe | oe, None -> oe
      | Some NotArray, Some NotArray -> oe1
      | Some (Array bs1), Some (Array bs2) -> 
        let bs = ByteSet.union bs1 bs2 in
        Some(Array bs) 
      | Some _, Some _ -> assert false in
    Mv.merge merge_elem il1 il2

  let get x t = Mv.find x t
   
  let set x e t = 
    match e with
    | NotArray -> 
      assert (not (is_ty_arr x.v_ty));
      Mv.add x e t
    | Array bs ->
      assert (is_ty_arr x.v_ty);
      if ByteSet.is_empty bs then Mv.remove x t 
      else Mv.add x e t

  let remove x t = Mv.remove x t

  let pp fmt t = 
    let pp_elem fmt (x,e) = 
      match e with
      | NotArray -> Printer.pp_var ~debug:true fmt x
      | Array bs -> 
        Format.fprintf fmt "%a%a" 
          (Printer.pp_var ~debug:true) x
          ByteSet.pp bs in
    Format.fprintf fmt "{@[%a@]}" 
      (Printer.pp_list ",@ " pp_elem) (Mv.bindings t)
      
end  

type live_info = {
    before : Live.t;
    after  : Live.t;
  }

let pp_live_info fmt li = 
 Format.fprintf fmt "@[<v>%a@ @]"
    Live.pp li.before 
(*
  Format.fprintf fmt "@[<v> before = %a@ after = %a@ @]"
    Live.pp li.before Live.pp li.after *)

(* FIXME word_of_int *)
let get_index e = 
  match e with
  | Pconst i -> Some i
  | _        -> None

let full_array x = 
  ByteSet.full Interval.{ min = 0 ; max = size_of x.v_ty }

let get_live_array x (s:Live.t) =
  try 
    match Live.get x s with
    | NotArray -> assert false
    | Array bs -> bs 
  with Not_found -> ByteSet.empty 
    
let set_live_array x bs s = Live.set x (Array bs) s

let set_live x s = 
  let elem = 
    if is_ty_arr x.v_ty then Array (full_array x)
    else NotArray in
  Live.set x elem s

let get_ofs aa ws i = 
  if aa = Warray_.AAdirect then B.to_int i 
  else size_of_ws ws * (B.to_int i)

let set_live_index aa ws x e s = 
  match get_index e with
  | None -> set_live x s 
  | Some i ->
    let i = get_ofs aa ws i in
    let bs = get_live_array x s in
    let iv = Interval.{ min = i; max = i + size_of_ws ws } in
    let bs = ByteSet.add iv bs in
    set_live_array x bs s 

let set_live_sub aa ws x e len s = 
  match get_index e with 
  | None -> hierror "unknow subindex %a" (Printer.pp_expr ~debug:true) e
  | Some i -> 
    let i = get_ofs aa ws i in
    let bs = get_live_array x s in
    let iv = Interval.{ min = i; max = i + len * size_of_ws ws } in
    let bs = ByteSet.add iv bs in
    set_live_array x bs s

let rec live_e s e = 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ -> s 
  | Pvar x           -> set_live (L.unloc x.gv) s 
  | Pget (aa,ws,x,e) -> 
    let s = set_live_index aa ws (L.unloc x.gv) e s in
    live_e s e 
  | Psub (aa,ws,len,x,e) -> 
    let s = set_live_sub aa ws (L.unloc x.gv) e len s in
    live_e s e 
  | Pload(_,x,e) -> live_e (set_live (L.unloc x) s) e
  | Papp1(_,e) -> live_e s e 
  | Papp2(_,e1,e2) -> live_e (live_e s e1) e2
  | PappN(_,es) -> live_es s es
  | Pif(_, e1, e2, e3) -> live_es s [e1;e2;e3]

and live_es s es = List.fold_left live_e s es

let dep_lv x s_o = 
  match x with
  | Lnone _ -> s_o 

  | Lmem(_,x,e) -> live_e (set_live (L.unloc x) s_o) e 

  | Lvar x -> Live.remove (L.unloc x) s_o

  | Laset (aa, ws, x, e) ->
    let x = L.unloc x in
    let bs = get_live_array x s_o in
    let bs = 
      match get_index e with
      | Some i -> 
        let i = get_ofs aa ws i in
        let iv = Interval.{ min = i ; max = i + size_of_ws ws } in
        ByteSet.remove iv bs
      | None -> bs in
    let s = set_live_array x bs s_o in
    live_e s e 

  | Lasub(aa, ws, len, x, e) ->
    let x = L.unloc x in
    let bs = get_live_array x s_o in
    let bs = 
      match get_index e with
      | Some i -> 
        let i = get_ofs aa ws i in
        let iv = Interval.{ min = i ; max = i + len * size_of_ws ws } in
        ByteSet.remove iv bs 
      | None ->  hierror "unknow subindex %a" (Printer.pp_expr ~debug:true) e in
    let s = set_live_array x bs s_o in
    live_e s e 

let dep_lvs xs s_o = List.fold_right dep_lv xs s_o

let rec live_i i s_o = 
  let s_i, d = live_d i.i_desc s_o in
  s_i, { i_desc = d; i_loc = i.i_loc; i_info = { before = s_i; after = s_o }}

and live_d d s_o = 
  match d with
  | Cassgn(x,tg,ty,e) ->
    let s = dep_lv x s_o in
    live_e s e, Cassgn(x,tg,ty,e)

  | Copn(xs,t,o,es) ->
    let s = dep_lvs xs s_o in
    live_es s es, Copn(xs,t,o,es)

  | Cif(e,c1,c2) -> 
    let s1, c1 = live_c c1 s_o in
    let s2, c2 = live_c c2 s_o in
    live_e (Live.union s1 s2) e, Cif(e,c1,c2)

  | Cfor _ -> assert false (* Should have been removed before *)

  | Cwhile(a,c,e,c') ->
    let rec loop s_o =
      (* loop (c; if e then c' else exit) *)
      let s_o' = live_e s_o e in
      let s_i, c = live_c c s_o' in
      let s_i', c' = live_c c' s_i in
      if Live.incl s_i' s_o then s_i, (c,c')
      else loop (Live.union s_i' s_o) in
    let s_i, (c,c') = loop s_o in
    s_i, Cwhile(a, c, e, c')

  | Ccall(ii,xs,f,es) ->
    let s =  dep_lvs xs s_o in
    live_es s es, Ccall(ii,xs,f,es)

and live_c c s_o = 
  List.fold_right (fun i (s_o, c) ->
      let s_i, i = live_i i s_o in
      s_i, i::c) c (s_o, [])

let live_fd fd =
  let s_o = 
    List.fold_left (fun s x -> set_live (L.unloc x) s) Live.empty fd.f_ret in
  let _, c = live_c fd.f_body s_o in
  { fd with f_body = c }



    
