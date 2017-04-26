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
  let conflicts = collect_conflicts lf in
  f
