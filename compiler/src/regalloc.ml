open Utils
open Prog

let fill_in_missing_names (f: 'info func) : 'info func =
  let fresh_name : L.t -> ty -> ty gvar_i =
    let count = ref 0 in
    fun loc ty ->
      let n = Printf.sprintf " %d" !count in
      incr count;
      L.mk_loc loc (V.mk n Reg ty L._dummy)
  in
  let fill_lv =
    function
    | Lnone(p, ty) -> Lvar (fresh_name p ty)
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
  | (Oaddcarry | Osubcarry),
    [ _ ; Lvar v ], Pvar w :: _
  | (Ox86_ADD | Ox86_SUB | Ox86_ADC | Ox86_SBB
    | Ox86_SHL | Ox86_SHR | Ox86_SAR
    | Ox86_AND | Ox86_OR | Ox86_XOR),
    [ _ ; _ ; _ ; _ ; _ ; Lvar v ], Pvar w :: _
  | (Ox86_INC | Ox86_DEC),
    [ _ ; _ ; _ ; _ ; Lvar v ], Pvar w :: _
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

(* Conflicting variables: variables that may be live simultaneously
   and thus must be allocated to distinct registers.

   The set of conflicts is represented by a map from variables to
   the set of variables they are conflicting with.
   Variables are represented by their equivalence class
   (equality constraints mandated by the architecture).
*)
module IntSet = Sint
module IntMap = Mint

type conflicts = IntSet.t IntMap.t

let get_conflicts (v: int) (c: conflicts) : IntSet.t =
  IntMap.find_default IntSet.empty v c

let conflicts_in (i: Sv.t) (k: var -> var -> 'a -> 'a) : 'a -> 'a =
  let e = Sv.elements i in
  let rec loop a =
    function
    | [] -> a
    | x :: xs ->
      let rec inner a =
        function
        | [] -> a
        | y :: ys -> inner (k x y a) ys
      in
      loop (inner a xs) xs
  in
  fun a -> loop a e

let collect_conflicts (tbl: (var, int) Hashtbl.t) (f: (Sv.t * Sv.t) func) : conflicts =
  let add_one_aux (v: int) (w: int) (c: conflicts) : conflicts =
      let x = get_conflicts v c in
      IntMap.add v (IntSet.add w x) c
  in
  let add_one loc (v: var) (w: var) (c: conflicts) : conflicts =
    try
      let i = Hashtbl.find tbl v in
      let j = Hashtbl.find tbl w in
      if i = j then hierror "%a: bad conflict between %a and %a"
          L.pp_loc loc
          (Printer.pp_var ~debug:true) v
          (Printer.pp_var ~debug:true) w;
      c |> add_one_aux i j |> add_one_aux j i
    with Not_found -> c
  in
  let add (c: conflicts) loc ((i, _): (Sv.t * Sv.t)) : conflicts =
    conflicts_in i (add_one loc) c in
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
  and collect_instr c { i_desc ; i_loc ; i_info } = collect_instr_r (add c i_loc i_info) i_desc
  and collect_stmt c s = List.fold_left collect_instr c s in
  collect_stmt IntMap.empty f.f_body

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
  List.iter get f.f_args;
  tbl, total ()

let normalize_variables (tbl: (var, int) Hashtbl.t) (eqc: Puf.t) : (var, int) Hashtbl.t =
    let r = Hashtbl.create 97 in
    Hashtbl.iter (fun v n -> Hashtbl.add r v (Puf.find eqc n)) tbl;
    r

type allocation = var IntMap.t

exception AlreadyAllocated

let allocate_one (x: int) (r: var) (a: allocation) : allocation =
  match IntMap.find x a with
  | r' when r' = r -> a
  | _ -> raise AlreadyAllocated
  | exception Not_found -> IntMap.add x r a

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
      rax; rcx; rdx;
      rsi; rdi;
      r8; r9; r10; r11;
      rbp;
      rbx;
      r12; r13; r14; r15
    ]

  let arguments = [
    rdi; rsi; rdx; rcx;
    r8; r9
  ]

  let ret = [
    rax; rdx
  ]

  let reserved = [
    rsp
  ]

  let f_c = V.mk "CF" Reg (Bty Bool) L._dummy
  let f_d = V.mk "DF" Reg (Bty Bool) L._dummy
  let f_o = V.mk "OF" Reg (Bty Bool) L._dummy
  let f_p = V.mk "PF" Reg (Bty Bool) L._dummy
  let f_s = V.mk "SF" Reg (Bty Bool) L._dummy
  let f_z = V.mk "ZF" Reg (Bty Bool) L._dummy

  let flags = [f_c; f_d; f_o; f_p; f_s; f_z]

  let all_registers = reserved @ allocatable @ flags

  let forced_registers (vars: (var, int) Hashtbl.t)
      (lvs: 'ty glvals) (op: op) (es: 'ty gexprs)
      (a: allocation) : allocation =
    let f x = Hashtbl.find vars (L.unloc x) in
    let mallocate_one x y a =
      match x with Pvar x -> allocate_one (f x) y a | _ -> a
    in
    match op, lvs, es with
    | (Ox86_ADD | Ox86_SUB | Ox86_AND | Ox86_OR | Ox86_XOR | Ox86_CMP
      | Ox86_SHL | Ox86_SHR | Ox86_SAR),
      Lvar oF :: Lvar cF :: Lvar sF :: Lvar pF :: Lvar zF :: _, _ ->
      a |>
      allocate_one (f oF) f_o |>
      allocate_one (f cF) f_c |>
      allocate_one (f sF) f_s |>
      allocate_one (f pF) f_p |>
      allocate_one (f zF) f_z
    | (Ox86_ADC | Ox86_SBB),
      [ Lvar oF ; Lvar cF ; Lvar sF ; Lvar pF ; Lvar zF ; _ ], [ _ ; _ ; cF' ] ->
      a |>
      mallocate_one cF' f_c |>
      allocate_one (f oF) f_o |>
      allocate_one (f cF) f_c |>
      allocate_one (f sF) f_s |>
      allocate_one (f pF) f_p |>
      allocate_one (f zF) f_z
    | (Ox86_INC | Ox86_DEC),
      [ Lvar oF ; Lvar sF ; Lvar pF ; Lvar zF ; _ ], _ ->
      a |>
      allocate_one (f oF) f_o |>
      allocate_one (f sF) f_s |>
      allocate_one (f pF) f_p |>
      allocate_one (f zF) f_z
    | (Oaddcarry | Osubcarry), Lvar cf  :: _, _ :: _ :: x :: _ ->
      a |>
      mallocate_one x f_c |>
      allocate_one (f cf) f_c
    | Ox86_MUL,
      [ Lvar oF ; Lvar cF ; Lvar sF ; Lvar pF ; Lvar zF ; Lvar hi ; Lvar lo ], x :: _ ->
      a |>
      mallocate_one x rax |>
      allocate_one (f oF) f_o |>
      allocate_one (f cF) f_c |>
      allocate_one (f sF) f_s |>
      allocate_one (f pF) f_p |>
      allocate_one (f zF) f_z |>
      allocate_one (f hi) rdx |>
      allocate_one (f lo) rax
    | Ox86_IMUL64,
      [ Lvar oF ; Lvar cF ; Lvar sF ; Lvar pF ; Lvar zF ; _ ], _ ->
      a |>
      allocate_one (f oF) f_o |>
      allocate_one (f cF) f_c |>
      allocate_one (f sF) f_s |>
      allocate_one (f pF) f_p |>
      allocate_one (f zF) f_z
    | _, _, _ -> a (* TODO *)

end

let allocate_forced_registers (vars: (var, int) Hashtbl.t)
    (f: 'info func) (a: allocation) : allocation =
  let alloc_from_list rs q a vs =
    let f x = Hashtbl.find vars (q x) in
    List.fold_left (fun (vs, a) p ->
        match f p with
        | r ->
          begin match vs with
          | v :: vs -> (vs, allocate_one r v a)
          | [] -> failwith "Regalloc: dame…"
          end
        | exception Not_found -> (vs, a))
      (rs, a)
      vs
    |> snd
  in
  let alloc_args = alloc_from_list X64.arguments identity in
  let alloc_ret = alloc_from_list X64.ret L.unloc in
  let rec alloc_instr_r a =
    function
    | Cblock s
    | Cfor (_, _, s)
      -> alloc_stmt a s
    | Copn (lvs, op, es) -> X64.forced_registers vars lvs op es a
    | Cwhile (s1, _, s2)
    | Cif (_, s1, s2)
        -> alloc_stmt (alloc_stmt a s1) s2
    | Cassgn _
      -> a
    | Ccall _ -> a (* TODO *)
  and alloc_instr a { i_desc } = alloc_instr_r a i_desc
  and alloc_stmt a s = List.fold_left alloc_instr a s
  in
  let a = alloc_args a f.f_args in
  let a = alloc_ret a f.f_ret in
  alloc_stmt a f.f_body

let find_vars (vars: (var, int) Hashtbl.t) (n: int) : var list =
  Hashtbl.fold (fun v m i -> if n = m then v :: i else i) vars []

let greedy_allocation
    (vars: (var, int) Hashtbl.t)
    (nv: int) (cnf: conflicts)
    (a: allocation) : allocation =
  let a = ref a in
  for i = 0 to nv - 1 do
    if not (IntMap.mem i !a) then (
      let c =
        get_conflicts i cnf |>
        IntSet.elements |>
        List.map (fun k -> try Some (IntMap.find k !a) with Not_found -> None)
      in
      let has_no_conflict v = not (List.mem (Some v) c) in
      match List.filter has_no_conflict X64.allocatable with
      | x :: _ -> a := IntMap.add i x !a
      | _ -> hierror "Register allocation: no more register to allocate %a" Printer.(pp_list "; " (pp_var ~debug:true)) (find_vars vars i)
    )
  done;
  !a

let subst_of_allocation (vars: (var, int) Hashtbl.t)
    (a: allocation) (v: var_i) : expr =
  let m = L.loc v in
  let v = L.unloc v in
  let q x = L.mk_loc m x in
  try
    let i = Hashtbl.find vars v in
    let w = IntMap.find i a in
    Pvar (q w)
  with Not_found -> Pvar (q v)

let regalloc (f: 'info func) : 'info func =
  let f = fill_in_missing_names f in
  let lf = Liveness.live_fd f in
  let vars, nv = collect_variables f in
  let eqc = collect_equality_constraints vars nv f in
  let vars = normalize_variables vars eqc in
  let conflicts = collect_conflicts vars lf in
  let a =
    allocate_forced_registers vars f IntMap.empty |>
    greedy_allocation vars nv conflicts |>
    subst_of_allocation vars
  in Subst.gsubst_func (fun ty -> ty) a f
