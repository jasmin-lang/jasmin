open Utils
open Expr
open Prog
open X86_decl

module IntSet = Sint
module IntMap = Mint

let fill_in_missing_names (f: 'info func) : 'info func =
  let fresh_name : L.t -> ty -> var_i =
    let count = ref 0 in
    fun loc ty ->
      let n = Printf.sprintf " _%d" !count in
      incr count;
      L.mk_loc loc (V.mk n (Reg Direct) ty L._dummy)
  in
  let fill_lv =
    function
    | Lnone(p, ty) -> Lvar (fresh_name p ty)
    | x -> x in
  let fill_lvs lvs = List.map fill_lv lvs in
  let rec fill_instr_r =
    function
    | Cassgn (lv, tg, ty, e) -> Cassgn (fill_lv lv, tg, ty, e)
    | Copn (lvs, tg, op, es) -> Copn (fill_lvs lvs, tg, op, es)
    | Cif (e, s1, s2) -> Cif (e, fill_stmt s1, fill_stmt s2)
    | Cfor (i, r, s) -> Cfor (i, r, fill_stmt s)
    | Cwhile (a, s, e, s') -> Cwhile (a, fill_stmt s, e, fill_stmt s')
    | Ccall (i, lvs, f, es) -> Ccall (i, fill_lvs lvs, f, es)
  and fill_instr i = { i with i_desc = fill_instr_r i.i_desc }
  and fill_stmt s = List.map fill_instr s in
  let f_body = fill_stmt f.f_body in
  { f with f_body }

type arg_position = APout of int | APin of int

let int_of_nat n =
  let rec loop acc =
    function
    | Datatypes.O -> acc
    | Datatypes.S n -> loop (1 + acc) n
  in loop 0 n

let find_equality_constraints (id: instruction) : arg_position list list =
  let tbl : (int, arg_position list) Hashtbl.t = Hashtbl.create 17 in
  let set n p =
    let old = try Hashtbl.find tbl n with Not_found -> [] in
    Hashtbl.replace tbl n (p :: old)
  in
  List.iteri (fun n ->
      function
      | ADImplicit _ -> ()
      | ADExplicit (p, _) -> set (int_of_nat p) (APout n)) id.i_out;
  List.iteri (fun n ->
      function
      | ADImplicit _ -> ()
      | ADExplicit (p, _) -> set (int_of_nat p) (APin n)) id.i_in;
  Hashtbl.fold
    (fun _ apl res ->
       match apl with
       | [] | [ _ ] -> res
       | _ -> apl :: res)
    tbl []

let find_var outs ins ap : _ option =
  match ap with
  | APout n -> (List.nth outs n |> function Lvar v -> Some v | _ -> None)
  | APin n ->
     (List.nth ins n |>
        function
        | Pvar v -> if is_gkvar v then Some v.gv else None
        | _ -> None)

let x86_equality_constraints (int_of_var: var_i -> int option) (k: int -> int -> unit)
    (k': int -> int -> unit)
    (lvs: 'ty glvals) (op: sopn) (es: 'ty gexprs) : unit =
  let merge k v w =
    match int_of_var v with
    | None -> ()
    | Some i ->
       match int_of_var w with
       | None -> ()
       | Some j -> k i j
  in
  begin match op, lvs, es with
  | Ox86 (MOV _), [ Lvar x ], [ Pvar y ] when is_gkvar y &&
                                              kind_i x = kind_i y.gv ->
    merge k' x y.gv
  | _, _, _ ->
    let id = get_instr op in
      find_equality_constraints id |>
      List.iter (fun constr ->
          constr |>
          List.filter_map (find_var lvs es) |> function
          | [] | [ _ ] -> ()
          | x :: m ->
            List.iter (merge k x) m
        )
  end

(* Set of instruction information for each variable equivalence class. *)
type 'info trace = (int, 'info instr list) Hashtbl.t

let pp_trace (i: int) fmt (tr: 'info trace) =
  let j = try Hashtbl.find tr i with Not_found -> [] in
  let pp_i fmt i =
    Format.fprintf fmt "@[%a at@ %a@]"
      (Printer.pp_instr ~debug:true) i
      Printer.pp_iloc i.i_loc in
  Format.fprintf fmt "@[<v>%a@]" (Printer.pp_list "@ " pp_i) j

let normalize_trace (eqc: Puf.t) (tr: 'info instr list array) : 'info trace =
  let tbl = Hashtbl.create 97 in
  let old i = try Hashtbl.find tbl i with Not_found -> [] in
  let union x y = List.sort_uniq compare (List.rev_append x y) in
  Array.iteri (fun i s ->
      let j = Puf.find eqc i in
      Hashtbl.replace tbl j (union s (old j))
  ) tr;
  tbl

type friend = IntSet.t IntMap.t

let get_friend (i: int) (f: friend) : IntSet.t =
  IntMap.find_default IntSet.empty i f

let set_friend i j (f: friend) : friend =
  f
  |> IntMap.modify_def (IntSet.singleton j) i (IntSet.add j)
  |> IntMap.modify_def (IntSet.singleton i) j (IntSet.add i)

type 'info collect_equality_constraints_state =
  { mutable cac_friends : friend; mutable cac_eqc: Puf.t ; cac_trace: 'info instr list array }

let collect_equality_constraints_in_func
      ~(with_call_sites: (funname -> 'info func) option)
      (msg: string)
      (int_of_var: var_i -> int option)
      copn_constraints
      (s: 'info collect_equality_constraints_state)
      (f: 'info func)
    : unit
  =
  let get_var x =
    match int_of_var x with
    | Some i -> i
    | None -> hierror "%s: unknown variable %a" msg (Printer.pp_var ~debug:true) (L.unloc x)
  in
  let add ii x y =
    s.cac_trace.(x) <- ii :: s.cac_trace.(x);
    s.cac_eqc <- Puf.union s.cac_eqc x y
  in
  let addv ii x y =
    let i = get_var x in
    let j = get_var y in
    add ii i j
  in
  let addf i j = s.cac_friends <- set_friend i j s.cac_friends in
  let rec collect_instr_r ii =
    function
    | Cfor (_, _, s) -> collect_stmt s
    | Copn (lvs, _, op, es) -> copn_constraints int_of_var (add ii) addf lvs op es
    | Cassgn (Lvar x, (AT_rename | AT_phinode), _, Pvar y) when
          is_gkvar y && kind_i x = kind_i y.gv ->
       addv ii x y.gv
    | Cassgn (Lvar x, _, _, Pvar y) when is_gkvar y && kind_i x = kind_i y.gv ->
       begin match int_of_var x, int_of_var y.gv with
       | Some i, Some j -> addf i j
       | (None, _) | (_, None) -> ()
       end
    | Cassgn _ -> ()
    | Ccall (_, xs, fn, es) ->
      let get_Pvar a =
        match a with
        | Pvar { gs = Expr.Slocal ; gv } -> gv
        | _ -> hierror "%s: argument is not a local variable" msg in
      let get_Lvar x =
        match x with
        | Lvar v -> v
        | _ -> hierror "%s: return destination is not a variable" msg in
      begin match with_call_sites with
      | None -> ()
      | Some get_func ->
        let g = get_func fn in
        List.iter2 (fun a p -> addv ii (get_Pvar a) Location.(mk_loc _dummy p))
          es g.f_args;
        List.iter2 (fun r x -> addv ii r (get_Lvar x))
          g.f_ret xs
      end
    | (Cwhile (_, s1, _, s2) | Cif (_, s1, s2)) -> collect_stmt s1; collect_stmt s2
  and collect_instr ({ i_desc } as i) = collect_instr_r i i_desc
  and collect_stmt s = List.iter collect_instr s in
  collect_stmt f.f_body

let collect_equality_constraints
    (msg: string)
    copn_constraints
    (tbl: int Hv.t)
    (nv: int)
    (f: 'info func) : Puf.t * 'info trace * friend =
  let int_of_var x = Hv.find_option tbl (L.unloc x) in
  let s = { cac_friends = IntMap.empty ; cac_eqc = Puf.create nv ; cac_trace = Array.make nv [] } in
  collect_equality_constraints_in_func ~with_call_sites:None msg int_of_var copn_constraints s f;
  let eqc = s.cac_eqc in
  eqc, normalize_trace eqc s.cac_trace, s.cac_friends

let collect_equality_constraints_in_prog
      (msg: string)
      copn_constraints
      (tbl: int Hv.t)
      (nv: int)
      (f: 'info func list) : Puf.t * 'info trace * friend =
  let int_of_var x = Hv.find_option tbl (L.unloc x) in
  let s = { cac_friends = IntMap.empty ; cac_eqc = Puf.create nv ; cac_trace = Array.make nv [] } in
  let tbl = Hf.create 17 in
  let get_var n = Hf.find tbl n in
  let () = List.fold_right (fun f () ->
               Hf.add tbl f.f_name f;
               collect_equality_constraints_in_func ~with_call_sites:(Some get_var) msg int_of_var copn_constraints s f)
             f ()
  in
  let eqc = s.cac_eqc in
  eqc, normalize_trace eqc s.cac_trace, s.cac_friends

(* Conflicting variables: variables that may be live simultaneously
   and thus must be allocated to distinct registers.

   The set of conflicts is represented by a map from variables to
   the set of variables they are conflicting with.
   Variables are represented by their equivalence class
   (equality constraints mandated by the architecture).
*)

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

let conflicts_add_one tbl tr loc (v: var) (w: var) (c: conflicts) : conflicts =
  let add_one_aux (v: int) (w: int) (c: conflicts) : conflicts =
    let x = get_conflicts v c in
    IntMap.add v (IntSet.add w x) c
  in
  try
    let i = Hv.find tbl v in
    let j = Hv.find tbl w in
    if i = j then hierror "%a: conflicting variables %a and %a must be merged due to:@.%a"
                    Printer.pp_iloc loc
                    (Printer.pp_var ~debug:true) v
                    (Printer.pp_var ~debug:true) w
                    (pp_trace i) tr;
    c |> add_one_aux i j |> add_one_aux j i
  with Not_found -> c

let collect_conflicts
      (tbl: int Hv.t) (tr: 'info trace) (f: (Sv.t * Sv.t) func) (c: conflicts) : conflicts =
  let add_one = conflicts_add_one tbl tr in
  let add (c: conflicts) loc ((i, j): (Sv.t * Sv.t)) : conflicts =
    c
    |> conflicts_in i (add_one loc)
    |> conflicts_in j (add_one loc)
  in
  let rec collect_instr_r c =
    function
    | Cfor (_, _, s)
      -> collect_stmt c s
    | Cassgn _
    | Copn _
    | Ccall _
      -> c
    | Cwhile (_, s1, _, s2)
    | Cif (_, s1, s2)
      -> collect_stmt (collect_stmt c s1) s2
  and collect_instr c { i_desc ; i_loc ; i_info } =
    collect_instr_r (add c i_loc i_info) i_desc
  and collect_stmt c s = List.fold_left collect_instr c s in
  collect_stmt c f.f_body

(** May-conflicts: local variables of function f may-conflict with variables
that are live at some call-site *)
let collect_may_conflicts tbl tr (live: Sv.t) (f: 'info func) (cnf: conflicts) : conflicts =
  let add_conflicts s x = Sv.fold (conflicts_add_one tbl tr (Location._dummy, []) x) s in
  let vars, _ = written_vars_fc f in
  cnf |> Sv.fold (add_conflicts vars) live |> Sv.fold (add_conflicts live) vars

let iter_variables (cb: var -> unit) (f: 'info func) : unit =
  let iter_sv = Sv.iter cb in
  let iter_lv lv = rvars_lv Sv.empty lv |> iter_sv in
  let iter_lvs lvs = List.fold_left rvars_lv Sv.empty lvs |> iter_sv in
  let iter_expr e = vars_e e |> iter_sv in
  let iter_exprs es = vars_es es |> iter_sv in
  let rec iter_instr_r =
    function
    | Cassgn (lv, _, _, e) -> iter_lv lv; iter_expr e
    | (Ccall (_, lvs, _, es) | Copn (lvs, _, _, es)) -> iter_lvs lvs; iter_exprs es
    | (Cwhile (_, s1, e, s2) | Cif (e, s1, s2)) -> iter_expr e; iter_stmt s1; iter_stmt s2
    | Cfor _ -> assert false
  and iter_instr { i_desc } = iter_instr_r i_desc
  and iter_stmt s = List.iter iter_instr s in
  iter_stmt f.f_body;
  List.iter cb f.f_args

let make_counter () =
  let count = ref 0 in
  (fun () ->
    let n = !count in
    incr count;
    n),
  (fun () -> !count)

let collect_variables_aux ~(allvars: bool) (excluded: Sv.t) (fresh: unit -> int) (tbl: int Hv.t) (f: 'info func) : unit =
  (* Remove sp and rip *)
  let get (v: var) : unit =
    if allvars || (is_reg_kind v.v_kind && not (Sv.mem v excluded)) then
      if not (Hv.mem tbl v)
      then
        let n = fresh () in
        Hv.add tbl v n
  in
  iter_variables get f

let collect_variables ~(allvars: bool) (excluded:Sv.t) (f: 'info func) : int Hv.t * int =
  let fresh, total = make_counter () in
  let tbl : int Hv.t = Hv.create 97 in
  collect_variables_aux ~allvars excluded fresh tbl f;
  tbl, total ()

let collect_variables_in_prog ~(allvars: bool) (excluded:Sv.t) (f: 'info func list) : int Hv.t * int =
  let fresh, total = make_counter () in
  let tbl : int Hv.t = Hv.create 97 in
  List.iter (collect_variables_aux ~allvars excluded fresh tbl) f;
  tbl, total ()

let normalize_variables (tbl: int Hv.t) (eqc: Puf.t) : int Hv.t =
    let r = Hv.create 97 in
    Hv.iter (fun v n -> Hv.add r v (Puf.find eqc n)) tbl;
    r

module A : sig
  type allocation
  val empty: int -> allocation
  val find: int -> allocation -> var option
  val rfind : var -> allocation -> IntSet.t
  val set: int -> var -> allocation -> unit
  val mem: int -> allocation -> bool
end = struct
type allocation = var option array * IntSet.t Hv.t
let empty nv = Array.create nv None, Hv.create nv
let find n (a, _) = a.(n)
let rfind x (_, r) = Hv.find_default r x IntSet.empty
let set n x (a, r) =
  Hv.modify_def (IntSet.singleton n) x (IntSet.add n) r;
  a.(n) <- Some x
let mem n (a, _) = a.(n) <> None
end

exception AlreadyAllocated

let does_not_conflict i (cnf: conflicts) (a: A.allocation) (x: var) : bool =
  IntSet.inter (get_conflicts i cnf) (A.rfind x a) |> IntSet.is_empty

let allocate_one loc (cnf: conflicts) (x_:var) (x: int) (r: var) (a: A.allocation) : unit =
  match A.find x a with
  | Some r' when r' = r -> ()
  | Some r' ->
     let pv = Printer.pp_var ~debug: true in
     hierror "at line %a: can not allocate %a into %a, the variable is already allocated in %a"
       Printer.pp_iloc loc
       pv x_
       pv r
       pv r'

  | None ->
     if does_not_conflict x cnf a r
     then A.set x r a
     else
       let pv = Printer.pp_var ~debug:true in
       hierror "Register allocation at line %a: variable %a must be allocated to conflicting register %a" Printer.pp_iloc loc pv x_ pv r

module X64 =
struct

  let reg_k = Prog.Reg Prog.Direct

  let rax = V.mk "RAX" reg_k (Bty (U U64)) L._dummy
  let rbx = V.mk "RBX" reg_k (Bty (U U64)) L._dummy
  let rcx = V.mk "RCX" reg_k (Bty (U U64)) L._dummy
  let rdx = V.mk "RDX" reg_k (Bty (U U64)) L._dummy
  let rsp = Prog.rsp
  let rbp = V.mk "RBP" reg_k (Bty (U U64)) L._dummy
  let rsi = V.mk "RSI" reg_k (Bty (U U64)) L._dummy
  let rdi = V.mk "RDI" reg_k (Bty (U U64)) L._dummy
  let r8 = V.mk "R8" reg_k (Bty (U U64)) L._dummy
  let r9 = V.mk "R9" reg_k (Bty (U U64)) L._dummy
  let r10 = V.mk "R10" reg_k (Bty (U U64)) L._dummy
  let r11 = V.mk "R11" reg_k (Bty (U U64)) L._dummy
  let r12 = V.mk "R12" reg_k (Bty (U U64)) L._dummy
  let r13 = V.mk "R13" reg_k (Bty (U U64)) L._dummy
  let r14 = V.mk "R14" reg_k (Bty (U U64)) L._dummy
  let r15 = V.mk "R15" reg_k (Bty (U U64)) L._dummy

  let xmm0 = V.mk "XMM0" reg_k (Bty (U U256)) L._dummy
  let xmm1 = V.mk "XMM1" reg_k (Bty (U U256)) L._dummy
  let xmm2 = V.mk "XMM2" reg_k (Bty (U U256)) L._dummy
  let xmm3 = V.mk "XMM3" reg_k (Bty (U U256)) L._dummy
  let xmm4 = V.mk "XMM4" reg_k (Bty (U U256)) L._dummy
  let xmm5 = V.mk "XMM5" reg_k (Bty (U U256)) L._dummy
  let xmm6 = V.mk "XMM6" reg_k (Bty (U U256)) L._dummy
  let xmm7 = V.mk "XMM7" reg_k (Bty (U U256)) L._dummy
  let xmm8 = V.mk "XMM8" reg_k (Bty (U U256)) L._dummy
  let xmm9 = V.mk "XMM9" reg_k (Bty (U U256)) L._dummy
  let xmm10 = V.mk "XMM10" reg_k (Bty (U U256)) L._dummy
  let xmm11 = V.mk "XMM11" reg_k (Bty (U U256)) L._dummy
  let xmm12 = V.mk "XMM12" reg_k (Bty (U U256)) L._dummy
  let xmm13 = V.mk "XMM13" reg_k (Bty (U U256)) L._dummy
  let xmm14 = V.mk "XMM14" reg_k (Bty (U U256)) L._dummy
  let xmm15 = V.mk "XMM15" reg_k (Bty (U U256)) L._dummy

  let allocatable = [
      rax; rcx; rdx;
      rsi; rdi;
      r8; r9; r10; r11;
      rbp;
      rbx;
      r12; r13; r14; r15
    ]

  let allocatables = Sv.of_list allocatable

  let xmm_allocatable = [
    xmm0; xmm1; xmm2; xmm3; xmm4; xmm5; xmm6; xmm7;
    xmm8; xmm9; xmm10; xmm11; xmm12; xmm13; xmm14; xmm15
  ]

  let arguments = [
    rdi; rsi; rdx; rcx;
    r8; r9
  ]

  let xmm_arguments = [
    xmm0; xmm1; xmm2; xmm3; xmm4; xmm5; xmm6; xmm7
  ]

  let ret = [
    rax; rdx
  ]

  let xmm_ret = [
    xmm0; xmm1
  ]

  let reserved = [
    rsp
  ]

  (* rsp does not need to be saved since it is an invariant
     of jasmin program *)
  let callee_save = Sv.of_list [ rbp; rbx; r12; r13; r14; r15 ]

  let f_c = V.mk "CF" reg_k (Bty Bool) L._dummy
  let f_d = V.mk "DF" reg_k (Bty Bool) L._dummy
  let f_o = V.mk "OF" reg_k (Bty Bool) L._dummy
  let f_p = V.mk "PF" reg_k (Bty Bool) L._dummy
  let f_s = V.mk "SF" reg_k (Bty Bool) L._dummy
  let f_z = V.mk "ZF" reg_k (Bty Bool) L._dummy

  let flags = [f_d ;f_o; f_c; f_s; f_p; f_z]

  let all_registers = reserved @ allocatable @ xmm_allocatable @ flags

  let forced_registers translate_var loc (vars: int Hv.t) (cnf: conflicts)
      (lvs: 'ty glvals) (op: sopn) (es: 'ty gexprs)
      (a: A.allocation) : unit =
    let f x = Hv.find vars (L.unloc x) in
    let allocate_one x y a =
      let i = f x in
      allocate_one loc cnf (L.unloc x) i y a
    in
    let mallocate_one x y a =
      match x with Pvar x when is_gkvar x -> allocate_one x.gv y a | _ -> ()
    in
    let id = get_instr op in
    List.iter2 (fun ad lv ->
        match ad with
        | ADImplicit v ->
           begin match lv with
           | Lvar w -> allocate_one w (translate_var (Asmgen.var_of_implicit v)) a
           | _ -> assert false
           end
        | ADExplicit _ -> ()) id.i_out lvs;
    List.iter2 (fun ad e ->
        match ad with
        | ADImplicit v ->
           mallocate_one e (translate_var (Asmgen.var_of_implicit v)) a
        | ADExplicit (_, Some r) ->
           mallocate_one e (translate_var (X86_variables.var_of_register r)) a
        | ADExplicit (_, None) -> ()) id.i_in es

end

type kind = Word | Vector | Unknown of ty

let kind_of_type =
  function
  | Bty (U (U8 | U16 | U32 | U64)) -> Word
  | Bty (U (U128 | U256)) -> Vector
  | ty -> Unknown ty

let allocate_forced_registers translate_var (vars: int Hv.t) (cnf: conflicts)
    (f: 'info func) (a: A.allocation) : unit =
  let alloc_from_list loc rs xs q vs : unit =
    let f x = Hv.find vars x in
    List.fold_left (fun (rs, xs) p ->
        let p = q p in
        match f p with
        | i ->
          let split =
            function
            | a :: b -> (a, b)
            | [] -> hierror "Register allocation: dame…"
          in
          let d, rs, xs =
            match kind_of_type p.v_ty with
            | Word -> let d, rs = split rs in d, rs, xs
            | Vector -> let d, xs = split xs in d, rs, xs
            | Unknown ty ->
              hierror "Register allocation: unknown type %a for forced register %a"
                Printer.pp_ty ty (Printer.pp_var ~debug:true) p
          in
          allocate_one loc cnf p i d a;
          (rs, xs)
        | exception Not_found -> (rs, xs))
      (rs, xs)
      vs
    |> (ignore : var list * var list -> unit)
  in
  let alloc_args loc = alloc_from_list loc X64.arguments X64.xmm_arguments identity in
  let alloc_ret loc = alloc_from_list loc X64.ret X64.xmm_ret L.unloc in
  let rec alloc_instr_r loc =
    function
    | Cfor (_, _, s)
      -> alloc_stmt s
    | Copn (lvs, _, op, es) -> X64.forced_registers translate_var loc vars cnf lvs op es a
    | Cwhile (_, s1, _, s2)
    | Cif (_, s1, s2)
        -> alloc_stmt s1; alloc_stmt s2
    | Cassgn _
      -> ()
    | Ccall (_, lvs, _, es) ->
       (* TODO: check this *)
       (*
       let args = List.map (function Pvar { gv ; gs = Slocal } -> (L.unloc gv) | _ -> assert false) es in
       let dsts = List.map (function Lvar gv -> gv | _ -> assert false) lvs in
       let a = alloc_args loc a args in
       alloc_ret loc a dsts
        *)
       ignore lvs;
       ignore es;
       ()
  and alloc_instr { i_loc; i_desc } = alloc_instr_r i_loc i_desc
  and alloc_stmt s = List.iter alloc_instr s
  in
  let loc = (f.f_loc, []) in
  if f.f_cc = Export then alloc_args loc f.f_args;
  if f.f_cc = Export then alloc_ret loc f.f_ret;
  alloc_stmt f.f_body

(* Returns a variable from [regs] that is allocated to a friend variable of [i]. Defaults to [dflt]. *)
let get_friend_registers (dflt: var) (fr: friend) (a: A.allocation) (i: int) (regs: var list) : var =
  let fregs =
    get_friend i fr
    |> IntSet.elements
    |> List.map (fun k -> A.find k a)
  in
  try
    List.find (fun r -> List.mem (Some r) fregs) regs
  with Not_found -> dflt

(* Gets the type of all variables in the list.
   Fails if the list has variables of different types. *)
let type_of_vars (vars: var list) : ty =
  match List.sort_unique Pervasives.compare (List.map (fun x -> x.v_ty) vars) with
  | [ty] -> ty
  | _ :: _ ->
    hierror "Register allocation: heterogeneous class %a"
      Printer.(pp_list "; " (pp_var ~debug: true)) vars
  | [] -> assert false

let greedy_allocation
    (vars: int Hv.t)
    (nv: int) (cnf: conflicts) (may_cnf: conflicts)
    (fr: friend)
    (a: A.allocation) : unit =
  let classes : var list array = Array.make nv [] in
  Hv.iter (fun v i -> classes.(i) <- v :: classes.(i)) vars;
  for i = 0 to nv - 1 do
    if not (A.mem i a) then (
      let vi = classes.(i) in
      if vi <> [] then (
      let has_no_conflict v = does_not_conflict i cnf a v in
      let has_no_may_conflict v = does_not_conflict i may_cnf a v in
      let bank =
        match kind_of_type (type_of_vars vi) with
        | Word -> X64.allocatable
        | Vector -> X64.xmm_allocatable
        | Unknown ty -> hierror "Register allocation: no register bank for type %a" Printer.pp_ty ty
      in
      match List.filter has_no_conflict bank with
      | (x :: regs) as bank ->
         begin match List.filter has_no_may_conflict bank with
         | x :: regs ->
            let y = get_friend_registers x fr a i regs in
            A.set i y a
         | [] ->
            let y = get_friend_registers x fr a i regs in
            A.set i y a
         end
      | [] -> hierror "Register allocation: no more register to allocate %a" Printer.(pp_list "; " (pp_var ~debug:true)) vi
    )
    )
  done

let var_subst_of_allocation (vars: int Hv.t)
    (a: A.allocation) (v: var) : var =
  try
    let i = Hv.find vars v in
    oget ~exn:Not_found (A.find i a)
  with Not_found -> v

let subst_of_var_subst (s: var -> var) (v: var L.located) : expr =
  let m = L.loc v in
  let v = L.unloc v in
  Pvar (gkvar (L.mk_loc m (s v)))

let subst_of_allocation vars a =
  var_subst_of_allocation vars a |> subst_of_var_subst

let reverse_varmap nv (vars: int Hv.t) : A.allocation =
  let a = A.empty nv in
  Hv.iter (fun v i -> A.set i v a) vars;
  a

let split_live_ranges (fds: 'info func list) : unit func list =
  let doit f =
    let f = Ssa.split_live_ranges true f in
    Glob_options.eprint Compiler.Splitting  (Printer.pp_func ~debug:true) f;
    let vars, nv = collect_variables ~allvars:true Sv.empty f in
    let eqc, _tr, _fr =
      collect_equality_constraints
        "Split live range" (fun _ _ _ _ _ _ -> ()) vars nv f in
    let vars = normalize_variables vars eqc in
    let a =
      reverse_varmap nv vars |>
        subst_of_allocation vars
    in Subst.subst_func a f
       |> Ssa.remove_phi_nodes in
  List.map doit fds

let is_subroutine = function
  | Subroutine _ -> true
  | _            -> false

(** Returns extra information (k, rsp, ra) depending on the calling convention.

 - Subroutines:
   - ra: a free register for the return address of f (caveat: may be live at the call-site),
        unless the function is annotated with “returnaddress="stack"”
   - k: all registers overwritten by a call to f (including ra)
   - rsp: None

 - Export:
    - k: all callee-saved registers overwritten by this function (including rsp)
    - rsp: if ~stack_needed and if there is a free register, a free register to hold the stack pointer of the caller (aka environment)
    - ra: None

*)
let post_process ~stack_needed ~extra_free_registers (live: Sv.t) ~(killed: funname -> Sv.t) (f: _ func) : Sv.t * var option * var option =
  let killed_in_f =
    let fv, cg = written_vars_fc f in
    let killed_by_calls =
      Mf.fold (fun n locs acc ->
          let acc = Sv.union (killed n) acc in
          List.fold_left (fun acc loc ->
              match extra_free_registers loc with
              | None -> acc
              | Some r -> Sv.add r acc
            ) acc locs
        ) cg Sv.empty in
    Sv.union fv killed_by_calls
  in
  let allocatable = X64.allocatables in
  let used_in_f = List.fold_left (fun s x -> Sv.add x s) killed_in_f f.f_args in
  let free_regs = Sv.diff allocatable used_in_f in
  match f.f_cc with
  | Internal -> assert false
  | Subroutine _ ->
     begin
       assert (not stack_needed);
       let ra =
         if f.f_annot.retaddr_kind <> Some OnStack then 
           let globally_free_regs = Sv.diff free_regs live in
           begin match Sv.Exceptionless.any globally_free_regs with
           | None ->
             begin match Sv.any free_regs with
             | r -> Some r
             | exception Not_found ->
               hierror "There is no free register for the return address in function “%s”" f.f_name.fn_name
             end
           | r -> r
           end
         else None
       in
       killed_in_f, None, ra
     end
  | Export ->
     begin
       assert (Sv.is_empty live);
       let to_save = Sv.inter X64.callee_save killed_in_f in
       if stack_needed && Sv.is_empty to_save then
         to_save, Sv.Exceptionless.any (Sv.diff free_regs X64.callee_save), None
       else to_save, None, None
     end

(** Useful for error messages: maps each register (after allocation) to the set
of variables (before allocation) it implements *)
let reverse_allocation nv vars (a: A.allocation) : var -> Sv.t =
  let classes : Sv.t array lazy_t =
    lazy (
        let classes : var list array = Array.make nv [] in
        Hv.iter (fun v i -> classes.(i) <- v :: classes.(i)) vars;
        Array.map Sv.of_list classes
      )
  in
  fun x ->
  let s = A.rfind x a in
  IntSet.fold (fun i -> Sv.union (Lazy.force classes).(i)) s Sv.empty

(** Implementing the calling conventions (storing the return address on the stack) may need an extra register
      This chooses a free register for each call site (to a rastack). *)
let chose_extra_free_registers get_annot (live: Sv.t) (f: (Sv.t * Sv.t) func) (subst: var -> var) (tbl: (i_loc, var) Hashtbl.t) : unit =
  let live = Sv.map subst live in
  Liveness.iter_call_sites (fun i fn _xs s ->
      if (get_annot fn).retaddr_kind = Some OnStack then
        let all = X64.allocatable |> Sv.of_list in
        let locally_free = Sv.diff all (Sv.map subst s) in
        let globally_free = Sv.diff locally_free live in
        match Sv.Exceptionless.any globally_free with
        | Some r -> Hashtbl.add tbl i r
        | None ->
          match Sv.Exceptionless.any locally_free with
          | Some r -> Hashtbl.add tbl i r
          | None -> () (* TODO: warning? *))
    f

let global_allocation translate_var (funcs: 'info func list) : unit func list * (funname -> Sv.t) * (var -> var) * (var -> Sv.t) * (i_loc -> var option) =
  (* Preprocessing of functions:
    - ensure all variables are named (no anonymous assign)
    - split live ranges (caveat: do not forget to remove φ-nodes at the end)
    - compute liveness information

    Initial 'info are preserved in the result.
   *)
  let annot_table : f_annot Hf.t = Hf.create 17 in
  let get_annot fn = Hf.find_default annot_table fn f_annot_empty in
  let liveness_table : (Sv.t * Sv.t) func Hf.t = Hf.create 17 in
  let preprocess f =
    Hf.add annot_table f.f_name f.f_annot;
    let f = f |> fill_in_missing_names |> Ssa.split_live_ranges false in
    Hf.add liveness_table f.f_name (Liveness.live_fd true f);
    f
  in
  let funcs : unit func list = List.map preprocess funcs in
  (* Live variables at the end of each function, in addition to returned local variables *)
  let get_liveness =
    let live : Sv.t Hf.t = Hf.create 17 in
    let collect_call_sites _fn f =
      Liveness.iter_call_sites (fun _loc fn xs s ->
          let s = Liveness.dep_lvs s xs in
          Hf.modify_def s fn (Sv.union s) live) f
    in
    Hf.iter collect_call_sites liveness_table;
    fun fn -> Hf.find_default live fn Sv.empty
  in
  let excluded = Sv.of_list [Prog.rip; X64.rsp] in
  let vars, nv = collect_variables_in_prog ~allvars:false excluded funcs in
  let eqc, tr, fr = collect_equality_constraints_in_prog "Regalloc" x86_equality_constraints vars nv funcs in
  let vars = normalize_variables vars eqc in
  let conflicts =
    Hf.fold (fun _fn lf conflicts ->
        collect_conflicts vars tr lf conflicts
      )
      liveness_table
      IntMap.empty
  in
  let may_conflicts = List.fold_left (fun a f -> collect_may_conflicts vars tr (get_liveness f.f_name) f a) IntMap.empty funcs in
  let a = A.empty nv in
  List.iter (fun f -> allocate_forced_registers translate_var vars conflicts f a) funcs;
  greedy_allocation vars nv conflicts may_conflicts fr a;
  let subst = var_subst_of_allocation vars a in

  let extra_free_registers = Hashtbl.create 137 in
  Hf.iter (fun fn f ->
      chose_extra_free_registers get_annot (get_liveness fn) f subst extra_free_registers
    ) liveness_table;

  List.map (fun f -> f |> Subst.subst_func (subst_of_var_subst subst) |> Ssa.remove_phi_nodes) funcs,
  get_liveness,
  var_subst_of_allocation vars a,
  reverse_allocation nv vars a
  , Hashtbl.find_opt extra_free_registers

type reg_oracle_t = {
    ro_to_save: var list;  (* TODO: allocate them in the stack rather than push/pop *)
    ro_rsp: var option;
    ro_return_address: var option;
  }

let alloc_prog translate_var (has_stack: call_conv -> 'a -> bool) (dfuncs: ('a * 'info func) list)
    : ('a * reg_oracle_t * unit func) list * (var -> Sv.t) * (i_loc -> var option) =
  let extra : 'a Hf.t = Hf.create 17 in
  let funcs, get_liveness, subst, reva, extra_free_registers =
    dfuncs
    |> List.map (fun (a, f) -> Hf.add extra f.f_name a; f)
    |> global_allocation translate_var
  in
  let killed_map : Sv.t Hf.t = Hf.create 17 in
  let killed fn = Hf.find_default killed_map fn Sv.empty in
  funcs |> List.rev |>
  List.rev_map (fun f ->
      let e = Hf.find extra f.f_name in
      let stack_needed = has_stack f.f_cc e in
      let to_save, ro_rsp, ro_return_address = post_process ~stack_needed ~killed ~extra_free_registers (Sv.map subst (get_liveness f.f_name)) f in
      let to_save = match ro_return_address with Some ra -> Sv.add ra to_save | None -> to_save in
      Hf.add killed_map f.f_name to_save;
      e, { ro_to_save = Sv.elements to_save ; ro_rsp ; ro_return_address }, f
    )
  , reva
  , extra_free_registers
