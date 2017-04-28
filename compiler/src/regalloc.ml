open Utils
open Prog

let fill_in_missing_names (f: 'info func) : 'info func =
  let fresh_name : L.t -> ty gvar_i =
    let count = ref 0 in
    fun loc ->
      let n = Printf.sprintf " %d" !count in
      incr count;
      L.mk_loc loc (V.mk n Reg (Bty Bool) L._dummy)
  in
  let fill_lv =
    function
    | Lnone p -> Lvar (fresh_name p)
    | x -> x in
  let fill_lvs lvs = List.map fill_lv lvs in
  let rec fill_instr_r =
    function
    | Cblock s -> Cblock (fill_stmt s)
    | Cassgn (lv, tg, e) -> Cassgn (fill_lv lv, tg, e)
    | Copn (lvs, op, es) -> Copn (fill_lvs lvs, op, es)
    | Cif (e, s1, s2) -> Cif (e, fill_stmt s1, fill_stmt s2)
    | Cfor _ -> assert false
    | Cwhile (s, e, s') -> Cwhile (fill_stmt s, e, fill_stmt s')
    | Ccall (i, lvs, f, es) -> Ccall (i, fill_lvs lvs, f, es)
  and fill_instr i = { i with i_desc = fill_instr_r i.i_desc }
  and fill_stmt s = List.map fill_instr s in
  let f_body = fill_stmt f.f_body in
  { f with f_body }

let x86_equality_constraints (tbl: (var, int) Hashtbl.t) (k: int -> int -> unit)
    (lvs: 'ty glvals) (op: op) (es: 'ty gexprs) : unit =
  let merge v w =
    try
      let i = Hashtbl.find tbl (L.unloc v) in
      let j = Hashtbl.find tbl (L.unloc w) in
      k i j
    with Not_found -> ()
  in
  match op, lvs, es with
  | Olnot, [ Lvar v ], [ Pvar w]
  | (Oxor | Oland | Olor | Olsr | Olsl), Lvar v :: _, Pvar w :: _
    (* TODO: add more constraints *)
    -> merge v w
  | _, _, _ -> ()

let collect_equality_constraints (tbl: (var, int) Hashtbl.t) (nv: int)
    (f: 'info func) : Puf.t =
  let p = ref (Puf.create nv) in
  let add x y = p := Puf.union !p x y in
  let rec collect_instr_r =
    function
    | Cblock s
    | Cfor (_, _, s)
      -> collect_stmt s
    | Copn (lvs, op, es) -> x86_equality_constraints tbl add lvs op es
    | Cassgn _
    | Ccall _
      -> ()
    | Cwhile (s1, _, s2)
    | Cif (_, s1, s2) -> collect_stmt s1; collect_stmt s2
  and collect_instr { i_desc } = collect_instr_r i_desc
  and collect_stmt s = List.iter collect_instr s in
  collect_stmt f.f_body;
  !p

module C =
struct
  type t = V.t * V.t

  let norm ((u, v) as x : t) : t =
    if V.compare u v < 0 then (v, u) else x

  let compare x x' =
    let (u, v) = norm x in
    let (u', v') = norm x' in
    match V.compare u u' with
    | 0 -> V.compare v v'
    | n -> n

end

module Sc = Set.Make (C)

let conflicts_in (i: Sv.t) (k: C.t -> 'a -> 'a) : 'a -> 'a =
  let e = Sv.elements i |> List.sort V.compare in
  let rec loop a =
    function
    | [] -> a
    | x :: xs ->
      let rec inner a =
        function
        | [] -> a
        | y :: ys -> inner (k (x, y) a) ys
      in
      loop (inner a xs) xs
  in
  fun a -> loop a e

let collect_conflicts (f: (Sv.t * Sv.t) func) : Sc.t =
  let add (c: Sc.t) ((i, _): (Sv.t * Sv.t)) : Sc.t =
    conflicts_in i Sc.add c in
  let rec collect_instr_r c =
    function
    | Cblock s
    | Cfor (_, _, s)  
      -> collect_stmt c s
    | Cassgn _
    | Copn _
    | Ccall _
      -> c
    | Cwhile (s1, _, s2)
    | Cif (_, s1, s2)
      -> collect_stmt (collect_stmt c s1) s2
  and collect_instr c { i_desc ; i_info } = collect_instr_r (add c i_info) i_desc
  and collect_stmt c s = List.fold_left collect_instr c s in
  collect_stmt Sc.empty f.f_body

let collect_variables (f: 'info func) : (var, int) Hashtbl.t * int =
  let fresh, total =
    let count = ref 0 in
    (fun () ->
    let n = !count in
    incr count;
    n),
    (fun () -> !count)
  in
  let tbl : (var, int) Hashtbl.t = Hashtbl.create 97 in
  let get (v: var) : unit =
    if v.v_kind = Reg then
    if not (Hashtbl.mem tbl v)
    then
      let n = fresh () in
      Hashtbl.add tbl v n
  in
  let collect_sv = Sv.iter get in
  let collect_lv lv = rvars_lv Sv.empty lv |> collect_sv in
  let collect_lvs lvs = List.fold_left rvars_lv Sv.empty lvs |> collect_sv in
  let collect_expr e = vars_e e |> collect_sv in
  let collect_exprs es = vars_es es |> collect_sv in
  let rec collect_instr_r =
    function
    | Cblock s -> collect_stmt s
    | Cassgn (lv, _, e) -> collect_lv lv; collect_expr e
    | Ccall (_, lvs, _, es)
    | Copn (lvs, _, es) -> collect_lvs lvs; collect_exprs es
    | Cwhile (s1, e, s2)
    | Cif (e, s1, s2) -> collect_expr e; collect_stmt s1; collect_stmt s2
    | Cfor _ -> assert false
  and collect_instr { i_desc } = collect_instr_r i_desc
  and collect_stmt s = List.iter collect_instr s in
  collect_stmt f.f_body;
  tbl, total ()

module X64 =
struct

  let rax = V.mk "RAX" Reg (Bty (U W64)) L._dummy
  let rbx = V.mk "RBX" Reg (Bty (U W64)) L._dummy
  let rcx = V.mk "RCX" Reg (Bty (U W64)) L._dummy
  let rdx = V.mk "RDX" Reg (Bty (U W64)) L._dummy
  let rsp = V.mk "RSP" Reg (Bty (U W64)) L._dummy
  let rbp = V.mk "RBP" Reg (Bty (U W64)) L._dummy
  let rsi = V.mk "RSI" Reg (Bty (U W64)) L._dummy
  let rdi = V.mk "RDI" Reg (Bty (U W64)) L._dummy
  let r8 = V.mk "R8" Reg (Bty (U W64)) L._dummy
  let r9 = V.mk "R9" Reg (Bty (U W64)) L._dummy
  let r10 = V.mk "R10" Reg (Bty (U W64)) L._dummy
  let r11 = V.mk "R11" Reg (Bty (U W64)) L._dummy
  let r12 = V.mk "R12" Reg (Bty (U W64)) L._dummy
  let r13 = V.mk "R13" Reg (Bty (U W64)) L._dummy
  let r14 = V.mk "R14" Reg (Bty (U W64)) L._dummy
  let r15 = V.mk "R15" Reg (Bty (U W64)) L._dummy

  let allocatable = [
      rax; rbx; rcx; rdx;
      rsp; rbp; rsi; rdi;
      r8; r9; r10; r11; r12; r13; r14; r15
    ]

  let f_c = V.mk "CF" Reg (Bty Bool) L._dummy
  let f_d = V.mk "DF" Reg (Bty Bool) L._dummy
  let f_o = V.mk "OF" Reg (Bty Bool) L._dummy
  let f_p = V.mk "PF" Reg (Bty Bool) L._dummy
  let f_s = V.mk "SF" Reg (Bty Bool) L._dummy
  let f_z = V.mk "ZF" Reg (Bty Bool) L._dummy

end

type allocation = (var, var) Hashtbl.t

let allocate_forced_registers (f: 'info func) (a: allocation) : allocation =
  a

let regalloc (f: 'info func) : 'info func =
  let f = fill_in_missing_names f in
  let lf = Liveness.live_fd f in
  let vars, nv = collect_variables f in
  let eqc = collect_equality_constraints vars nv f in
  let conflicts = collect_conflicts lf in
  f
