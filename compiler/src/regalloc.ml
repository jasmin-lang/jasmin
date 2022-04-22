open Utils
open Sopn
open Prog

module IntSet = Sint
module IntMap = Mint

let hierror = hierror ~kind:"compilation error"
let hierror_reg = hierror ~sub_kind:"register allocation"

let make_counter () =
  let count = ref 0 in
  (fun () ->
    let n = !count in
    incr count;
    n),
  (fun () -> !count)

let fill_in_missing_names (f: ('info, 'asm) func) : ('info, 'asm) func =
  let fresh_name : L.t -> ty -> var_i =
    let fresh, _ = make_counter () in
    fun loc ty ->
      let n = Printf.sprintf " _%d" (fresh ()) in
      L.mk_loc loc (V.mk n (Reg Direct) ty L._dummy [])
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

type kind = Word | Vector | Unknown of ty

let kind_of_type =
  function
  | Bty (U (U8 | U16 | U32 | U64)) -> Word
  | Bty (U (U128 | U256)) -> Vector
  | ty -> Unknown ty

(* Only variables that will be allocated to the same “bank” may conflict. *)
let types_cannot_conflict x y : bool =
  match kind_of_type x, kind_of_type y with
  | Word, Word | Vector, Vector -> false
  | _, _ -> true

type arg_position = APout of int | APin of int

let int_of_nat n =
  let rec loop acc =
    function
    | Datatypes.O -> acc
    | Datatypes.S n -> loop (1 + acc) n
  in loop 0 n

let find_equality_constraints (id: instruction_desc) : arg_position list list =
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

let asm_equality_constraints ~loc asmOp is_move_op (int_of_var: var_i -> int option) (k: int -> int -> unit)
    (k': int -> int -> unit)
    (lvs: 'ty glvals) (op: 'asm sopn) (es: 'ty gexprs) : unit =
  let assert_compatible_types x y =
    if types_cannot_conflict (L.unloc x).v_ty (L.unloc y).v_ty then
      hierror_reg ~loc "Variables %a and %a must be merged due to architectural constraints but have incompatible types"
        (Printer.pp_var ~debug:true) (L.unloc x)
        (Printer.pp_var ~debug:true) (L.unloc y)
  in
  let merge k v w =
    assert_compatible_types v w;
    match int_of_var v with
    | None -> ()
    | Some i ->
       match int_of_var w with
       | None -> ()
       | Some j -> k i j
  in
  begin match op, lvs, es with
  | Oasm op, [ Lvar x ], [ Pvar y ] when is_move_op op && is_gkvar y &&
                                              kind_i x = kind_i y.gv ->
    merge k' x y.gv
  | _, _, _ ->
    let id = get_instr_desc asmOp op in
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
type ('info, 'asm) trace = (int, ('info, 'asm) instr list) Hashtbl.t

let pp_trace asmOp (i: int) fmt (tr: ('info, 'asm) trace) =
  let j = try Hashtbl.find tr i with Not_found -> [] in
  let pp_i fmt i =
    Format.fprintf fmt "@[<v>at %a:@;<1 2>%a@]"
      L.pp_iloc i.i_loc
      (Printer.pp_instr ~debug:true asmOp) i
  in
  Format.fprintf fmt "@[<v>%a@]" (pp_list "@ " pp_i) j

let normalize_trace (eqc: Puf.t) (tr: ('info, 'asm) instr list array) : ('info, 'asm) trace =
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
  |> IntMap.modify_def IntSet.empty i (IntSet.add j)
  |> IntMap.modify_def IntSet.empty j (IntSet.add i)

type ('info, 'asm) collect_equality_constraints_state =
  { mutable cac_friends : friend; mutable cac_eqc: Puf.t ; cac_trace: ('info, 'asm) instr list array }

let collect_equality_constraints_in_func
      (asmOp:'asm Sopn.asmOp)
      is_move_op
      ~(with_call_sites: (funname -> ('info, 'asm) func) option)
      (msg: string)
      (int_of_var: var_i -> int option)
      copn_constraints
      (s: ('info, 'asm) collect_equality_constraints_state)
      (f: ('info, 'asm) func)
    : unit
  =
  let add ii x y =
    s.cac_trace.(x) <- ii :: s.cac_trace.(x);
    s.cac_eqc <- Puf.union s.cac_eqc x y
  in
  let addv ii x y =
    match int_of_var x, int_of_var y with
    | Some i, Some j -> add ii i j
    | (None, _) | (_, None) -> ()
  in
  let addf i j = s.cac_friends <- set_friend i j s.cac_friends in
  let rec collect_instr_r ii =
    function
    | Cfor (_, _, s) -> collect_stmt s
    | Copn (lvs, _, op, es) ->
        copn_constraints
          ~loc:(Lmore ii.i_loc)
          asmOp
          is_move_op
          int_of_var
          (add ii)
          addf
          lvs
          op
          es
    | Cassgn (Lvar x, AT_phinode, _, Pvar y) when
          is_gkvar y && kind_i x = kind_i y.gv ->
       addv ii x y.gv
    | Cassgn (Lvar x, AT_rename, _, Pvar y) when is_gkvar y && kind_i x = kind_i y.gv &&
                                                   not (is_stack_array x) ->
      addv ii x y.gv

    | Cassgn (Lvar x, _, _, Pvar y) when is_gkvar y && kind_i x = kind_i y.gv && 
                                          not (is_stack_array x) ->
       begin match int_of_var x, int_of_var y.gv with
       | Some i, Some j -> addf i j
       | (None, _) | (_, None) -> ()
       end
    | Cassgn _ -> ()
    | Ccall (_, xs, fn, es) ->
      let get_Pvar a =
        match a with
        | Pvar { gs = Expr.Slocal ; gv } -> gv
        | _ -> hierror ~loc:(Lmore ii.i_loc) ~sub_kind:msg ~internal:true "argument is not a local variable" in
      let get_Lvar x =
        match x with
        | Lvar v -> v
        | _ -> hierror ~loc:(Lmore ii.i_loc) ~sub_kind:msg ~internal:true "return destination is not a variable" in
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

let normalize_friend (eqc: Puf.t) (fr: friend) : friend =
  IntMap.filter_map (
      fun k f ->
      if Stdlib.Int.equal k (Puf.find eqc k)
      then Some (IntSet.map (Puf.find eqc) f)
      else None
    ) fr

let collect_equality_constraints
    asmOp
    is_move_op
    (msg: string)
    copn_constraints
    (tbl: int Hv.t)
    (nv: int)
    (f: ('info, 'asm) func) : Puf.t * ('info, 'asm) trace * friend =
  let int_of_var x = Hv.find_option tbl (L.unloc x) in
  let s = { cac_friends = IntMap.empty ; cac_eqc = Puf.create nv ; cac_trace = Array.make nv [] } in
  collect_equality_constraints_in_func asmOp is_move_op ~with_call_sites:None msg int_of_var copn_constraints s f;
  let eqc = s.cac_eqc in
  eqc, normalize_trace eqc s.cac_trace, normalize_friend eqc s.cac_friends

let collect_equality_constraints_in_prog
      asmOp
      is_move_op
      (msg: string)
      copn_constraints
      (tbl: int Hv.t)
      (nv: int)
      (f: ('info, 'asm) func list) : Puf.t * ('info, 'asm) trace * friend =
  let int_of_var x = Hv.find_option tbl (L.unloc x) in
  let s = { cac_friends = IntMap.empty ; cac_eqc = Puf.create nv ; cac_trace = Array.make nv [] } in
  let tbl = Hf.create 17 in
  let get_var n = Hf.find tbl n in
  let () = List.fold_right (fun f () ->
               Hf.add tbl f.f_name f;
               collect_equality_constraints_in_func asmOp is_move_op ~with_call_sites:(Some get_var) msg int_of_var copn_constraints s f)
             f ()
  in
  let eqc = s.cac_eqc in
  eqc, normalize_trace eqc s.cac_trace, normalize_friend eqc s.cac_friends

(* Conflicting variables: variables that may be live simultaneously
   and thus must be allocated to distinct registers.

   The set of conflicts is represented by a map from variables to
   the set of variables they are conflicting with.
   Variables are represented by their equivalence class
   (equality constraints mandated by the architecture).
*)

module Conflicts :
  sig
    type conflicts
    val empty_conflicts : conflicts
    val get_conflicts : int -> conflicts -> IntSet.t
    val add_conflicts : int -> int -> conflicts -> conflicts
  end
=
struct
  type conflicts = IntSet.t IntMap.t

  let empty_conflicts = IntMap.empty

  let get_conflicts (v: int) (c: conflicts) : IntSet.t =
    IntMap.find_default IntSet.empty v c

  let add_conflicts (v: int) (w: int) (c: conflicts) : conflicts =
    IntMap.modify_opt v (function
        | None -> Some (IntSet.singleton w)
        | Some x -> Some (IntSet.add w x)
      ) c
end
open Conflicts

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

let conflicts_add_one asmOp tbl tr loc (v: var) (w: var) (c: conflicts) : conflicts =
  if types_cannot_conflict v.v_ty w.v_ty then c else
  try
    let i = Hv.find tbl v in
    let j = Hv.find tbl w in
    if i = j then hierror_reg ~loc:loc "conflicting variables “%a” and “%a” must be merged due to:@;<1 2>%a"
                    (Printer.pp_var ~debug:true) v
                    (Printer.pp_var ~debug:true) w
                    (pp_trace asmOp i) tr;
    c |> add_conflicts i j |> add_conflicts j i
  with Not_found -> c

let collect_conflicts asmOp
      (tbl: int Hv.t) (tr: ('info, 'asm) trace) (f: (Sv.t * Sv.t, 'asm) func) (c: conflicts) : conflicts =
  let add_one = conflicts_add_one asmOp tbl tr in
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
    collect_instr_r (add c (Lmore i_loc) i_info) i_desc
  and collect_stmt c s = List.fold_left collect_instr c s in
  collect_stmt c f.f_body

let iter_variables (cb: var -> unit) (f: ('info, 'asm) func) : unit =
  let iter_sv = Sv.iter cb in
  let iter_lv lv = vars_lv Sv.empty lv |> iter_sv in
  let iter_lvs lvs = List.fold_left vars_lv Sv.empty lvs |> iter_sv in
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
  List.iter cb f.f_args;
  List.iter (fun x -> cb (L.unloc x)) f.f_ret

let collect_variables_cb ~(allvars: bool) (excluded: Sv.t) (fresh: unit -> int) (tbl: int Hv.t) (v: var) : unit =
  (* Remove sp and rip *)
  if allvars || (is_reg_kind v.v_kind && not (Sv.mem v excluded)) then
    if not (Hv.mem tbl v)
    then
      let n = fresh () in
      Hv.add tbl v n

let collect_variables_aux ~(allvars: bool) (excluded: Sv.t) (fresh: unit -> int) (tbl: int Hv.t) (extra: var option) (f: ('info, 'asm) func) : unit =
  let get v = collect_variables_cb ~allvars excluded fresh tbl v in
  iter_variables get f;
  match extra with Some x -> get x | None -> ()

let collect_variables ~(allvars: bool) (excluded:Sv.t) (f: ('info, 'asm) func) : int Hv.t * int =
  let fresh, total = make_counter () in
  let tbl : int Hv.t = Hv.create 97 in
  collect_variables_aux ~allvars excluded fresh tbl None f;
  tbl, total ()

let collect_variables_in_prog ~(allvars: bool) (excluded:Sv.t) (extra: var Hf.t) (extras: ('k, var) Hashtbl.t) (f: ('info, 'asm) func list) : int Hv.t * int =
  let fresh, total = make_counter () in
  let tbl : int Hv.t = Hv.create 97 in
  List.iter (fun f -> collect_variables_aux ~allvars excluded fresh tbl (Hf.Exceptionless.find extra f.f_name) f) f;
  Hashtbl.iter (fun _ v -> collect_variables_cb ~allvars excluded fresh tbl v) extras;
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
let empty nv = Array.make nv None, Hv.create nv
let find n (a, _) = a.(n)
let rfind x (_, r) = Hv.find_default r x IntSet.empty
let set n x (a, r) =
  Hv.modify_def IntSet.empty x (IntSet.add n) r;
  a.(n) <- Some x
let mem n (a, _) = a.(n) <> None
end

let reverse_classes nv vars : Sv.t array =
  let classes : var list array = Array.make nv [] in
  Hv.iter (fun v i -> classes.(i) <- v :: classes.(i)) vars;
  Array.map Sv.of_list classes

let get_conflict_set i (cnf: conflicts) (a: A.allocation) (x: var) : IntSet.t =
  IntSet.inter (get_conflicts i cnf) (A.rfind x a)

let does_not_conflict i (cnf: conflicts) (a: A.allocation) (x: var) : bool =
  get_conflict_set i cnf a x |> IntSet.is_empty

let allocate_one nv vars loc (cnf: conflicts) (x_:var) (x: int) (r: var) (a: A.allocation) : unit =
  match A.find x a with
  | Some r' when r' = r -> ()
  | Some r' ->
     let pv = Printer.pp_var ~debug:true in
     hierror_reg ~loc:(Lmore loc) "cannot allocate %a into %a, the variable is already allocated in %a"
       pv x_
       pv r
       pv r'

  | None ->
     let c = get_conflict_set x cnf a r in
     if IntSet.is_empty c
     then A.set x r a
     else
       let pv = Printer.pp_var ~debug:true in
       let regs = reverse_classes nv vars in
       hierror_reg ~loc:(Lmore loc) "variable %a must be allocated to conflicting register %a { %a }"
         pv x_
         (Printer.pp_var ~debug:false) r
         (pp_list "; " pv)
         (IntSet.fold (fun i -> Sv.union regs.(i)) c Sv.empty |> Sv.elements)

type reg_oracle_t = {
    ro_to_save: var list;
    ro_rsp: var option;
    ro_return_address: var option;
  }

module type Regalloc = sig
  type extended_op

  val split_live_ranges : (unit, extended_op) func -> (unit, extended_op) func
  val renaming : (unit, extended_op) func -> (unit, extended_op) func
  val remove_phi_nodes : (unit, extended_op) func -> (unit, extended_op) func

  val alloc_prog :
    (Var0.Var.var -> var) -> ((unit, extended_op) func -> 'a -> bool) ->
    ('a * (unit, extended_op) func) list ->
    ('a * reg_oracle_t * (unit, extended_op) func) list
    * (L.i_loc -> var option)
end

module Regalloc (Arch : Arch_full.Arch)
  : Regalloc with type extended_op := (Arch.reg, Arch.xreg, Arch.rflag, Arch.cond, Arch.asm_op, Arch.extra_op) Arch_extra.extended_op = struct

  let forced_registers translate_var loc nv (vars: int Hv.t) (cnf: conflicts)
      (lvs: 'ty glvals) (op: 'asm sopn) (es: 'ty gexprs)
      (a: A.allocation) : unit =
    let allocate_one x y a =
      let x = L.unloc x in
      let i =
        try Hv.find vars x
        with Not_found ->
          hierror_reg ~loc:(Lmore loc) "variable %a (declared at %a as “%a”) must be allocated to register %a but is unknown to the register allocator%s"
            (Printer.pp_var ~debug:true) x
            L.pp_sloc x.v_dloc
            Printer.pp_kind x.v_kind
            (Printer.pp_var ~debug:false) y
            (if is_reg_kind x.v_kind then "" else " (consider declaring this variable as “reg”)")
      in
      allocate_one nv vars loc cnf x i y a
    in
    let mallocate_one x y a =
      match x with Pvar x when is_gkvar x -> allocate_one x.gv y a | _ -> ()
    in
    let id = get_instr_desc Arch.asmOp op in
    (* TODO: move !! *)
    let var_of_implicit v =
      match v with
      | IArflag v -> v
      | IAreg v -> v
    in
    List.iter2 (fun ad lv ->
        match ad with
        | ADImplicit v ->
           begin match lv with
           | Lvar w -> allocate_one w (translate_var (var_of_implicit v)) a
           | _ -> assert false
           end
        | ADExplicit _ -> ()) id.i_out lvs;
    List.iter2 (fun ad e ->
        match ad with
        | ADImplicit v ->
           mallocate_one e (translate_var (var_of_implicit v)) a
        | ADExplicit (_, Some v) ->
           mallocate_one e (translate_var v) a
        | ADExplicit (_, None) -> ()) id.i_in es

let allocate_forced_registers translate_var nv (vars: int Hv.t) (cnf: conflicts)
    (f: ('info, 'asm) func) (a: A.allocation) : unit =
  let split ~ctxt =
    function
    | hd :: tl -> hd, tl
    | [] ->
       hierror_reg ~loc:(Lone f.f_loc) ~funname:f.f_name.fn_name "too many %s according to the ABI"
         ctxt
  in
  let alloc_from_list loc ~ctxt rs xs q vs : unit =
    let f x = Hv.find vars x in
    List.fold_left (fun (rs, xs) p ->
        let p = q p in
        match f p with
        | i ->
          let d, rs, xs =
            match kind_of_type p.v_ty with
            | Word -> let d, rs = split ~ctxt rs in d, rs, xs
            | Vector -> let d, xs = split ~ctxt xs in d, rs, xs
            | Unknown ty ->
              hierror_reg ~loc:(Lmore loc) "unknown type %a for forced register %a"
                Printer.pp_ty ty (Printer.pp_var ~debug:true) p
          in
          allocate_one nv vars loc cnf p i d a;
          (rs, xs)
        | exception Not_found -> (rs, xs))
      (rs, xs)
      vs
    |> (ignore : var list * var list -> unit)
  in
  let alloc_args loc = alloc_from_list loc ~ctxt:"parameters" Arch.argument_vars Arch.xmm_argument_vars identity in
  let alloc_ret loc = alloc_from_list loc ~ctxt:"return values" Arch.ret_vars Arch.xmm_ret_vars L.unloc in
  let rec alloc_instr_r loc =
    function
    | Cfor (_, _, s)
      -> alloc_stmt s
    | Copn (lvs, _, op, es) -> forced_registers translate_var loc nv vars cnf lvs op es a
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
  let loc = L.i_loc0 f.f_loc in
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

let schedule_coloring (size: int) (variables: (int, var list) Hashtbl.t) (cnf: conflicts) (a: A.allocation) : int list =
  let module G = struct type t = (int, IntSet.t) Hashtbl.t end in
  (* Sets of uncolored nodes of degree below than size, and whether there are uncolored nodes. *)
  let nodes_of_low_degree (g: G.t) : IntSet.t * bool =
    Hashtbl.fold (fun i c ((m, _) as acc) ->
        if A.mem i a then acc
        else (if IntSet.cardinal c < size then IntSet.add i m else m), true)
      g (IntSet.empty, false)
  in
  (* Remove from g all nodes in v *)
  let prune (g: G.t) (v: IntSet.t) : unit =
    Hashtbl.filter_map_inplace
      (fun i c -> if IntSet.mem i v then None else Some (IntSet.diff c v)) g
  in
  (* Heuristic to pick an uncolored node in g *)
  (* Any uncolored node is valid: the choice made here is arbitrary. *)
  let pick (g: G.t) : int =
    let (r, _), _ =
      Hashtbl.fold (fun i c m -> if A.mem i a then m else (i, c) :: m) g []
      |> List.map (fun (i, c) -> i, c |> IntSet.filter (fun j -> not (A.mem j a)) |> IntSet.cardinal)
      |> List.min_max ~cmp:(fun (_, x) (_, y) -> Stdlib.Int.compare y x)
    in
    r
  in
  let pick_if_empty (g: G.t) (v: IntSet.t) : IntSet.t =
    if IntSet.is_empty v then pick g |> IntSet.singleton else v
  in
  let g = Hashtbl.create 97 in
  Hashtbl.iter (fun i _ -> Hashtbl.add g i (get_conflicts i cnf)) variables;
  let rec loop (g: G.t) (order: int list) : int list =
    let v, continue = nodes_of_low_degree g in
    if not continue
    then (assert (IntSet.is_empty v); order)
    else
      let v = pick_if_empty g v in
      prune g v;
      loop g (IntSet.elements v @ order)
  in
  loop g []

let lazy_scheduling (variables: (int, var list) Hashtbl.t) (a: A.allocation) : int list =
  []
  |> Hashtbl.fold (fun i _c m -> if A.mem i a then m else i :: m) variables
  |> List.sort Stdlib.Int.compare

let two_phase_coloring
    (registers: var list)
    (variables: (int, var list) Hashtbl.t)
    (cnf: conflicts)
    (fr: friend)
    (a: A.allocation) : unit =
  let size = List.length registers in
  let schedule =
    if !Glob_options.lazy_regalloc then lazy_scheduling variables a
    else schedule_coloring size variables cnf a in
  List.iter (fun i ->
      let has_no_conflict v = does_not_conflict i cnf a v in
      match List.filter has_no_conflict registers with
      | [] -> hierror_reg ~loc:Lnone "no more register to allocate “%a”" Printer.(pp_list "; " (pp_var ~debug:true)) (Hashtbl.find variables i)
      | x :: regs ->
        (* Any register in [x; regs] is valid: the choice made here is arbitrary. *)
        let y = get_friend_registers x fr a i regs in
        A.set i y a
    ) schedule

let greedy_allocation
    (vars: int Hv.t)
    (nv: int) (cnf: conflicts)
    (fr: friend)
    (a: A.allocation) : unit =
  let scalars : (int, var list) Hashtbl.t = Hashtbl.create nv in
  let vectors : (int, var list) Hashtbl.t = Hashtbl.create nv in
  let push_var tbl i v =
    match Hashtbl.find tbl i with
    | old -> Hashtbl.replace tbl i (v :: old)
    | exception Not_found -> Hashtbl.add tbl i [ v ]
  in
  Hv.iter (fun v i ->
      match kind_of_type v.v_ty with
      | Word -> push_var scalars i v
      | Vector -> push_var vectors i v
      | Unknown _ -> ()
      ) vars;
  two_phase_coloring Arch.allocatable_vars scalars cnf fr a;
  two_phase_coloring Arch.xmm_allocatable_vars vectors cnf fr a;
  ()

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

let split_live_ranges (f: ('info, 'asm) func) : (unit, 'asm) func =
  Ssa.split_live_ranges Arch.aparams.ap_is_move_op true f

let renaming (f: ('info, 'asm) func) : (unit, 'asm) func =
  let vars, nv = collect_variables ~allvars:true Sv.empty f in
  let eqc, _tr, _fr =
    collect_equality_constraints
      Arch.asmOp
      Arch.aparams
      "Split live range"
      (fun ~loc:_ _ _ _ _ _ _ _ _ -> ())
      vars
      nv
      f
  in
  let vars = normalize_variables vars eqc in
  let a = reverse_varmap nv vars |> subst_of_allocation vars in
  Subst.subst_func a f

let remove_phi_nodes (f: ('info, 'asm) func) : (unit, 'asm) func =
  Ssa.remove_phi_nodes f

let is_subroutine = function
  | Subroutine _ -> true
  | _            -> false

(** Returns extra information (k, rsp) depending on the calling convention.

 - Subroutines:
   - k: all registers overwritten by a call to f (including ra)
   - rsp: None

 - Export:
    - k: all callee-saved registers overwritten by this function (including rsp)
    - rsp: if ~stack_needed and if there is a free register, a free register to hold the stack pointer of the caller (aka environment)

*)
let post_process ~stack_needed (subst: var -> var) (live: Sv.t) ~(killed: funname -> Sv.t) (f: _ func) : Sv.t * var option =
  let killed_in_f = killed f.f_name |> Sv.map subst in
  match f.f_cc with
  | Internal -> assert false
  | Subroutine _ ->
     begin
       assert (not stack_needed);
       killed_in_f, None
     end
  | Export ->
     begin
       assert (Sv.is_empty live);
       (* TODO: should we call Sv.of_list once and for all, or is it ok to call each time we enter this function? *)
       let allocatable = Sv.of_list Arch.allocatable_vars in
       let used_in_f = List.fold_left (fun s x -> Sv.add (subst x) s) killed_in_f f.f_args in
       let free_regs = Sv.diff allocatable used_in_f in
       (* TODO: should we call Sv.of_list once and for all, or is it ok to call each time we enter this function? *)
       let to_save = Sv.inter (Sv.of_list Arch.callee_save_vars) killed_in_f in
       if stack_needed && Sv.is_empty to_save then
         to_save, Sv.Exceptionless.any (Sv.diff free_regs (Sv.of_list Arch.callee_save_vars))
       else to_save, None
     end

let global_allocation translate_var (funcs: ('info, 'asm) func list) : (unit, 'asm) func list * (funname -> Sv.t) * (var -> var) * (funname -> Sv.t) * (L.i_loc, var) Hashtbl.t * var Hf.t =
  (* Preprocessing of functions:
    - ensure all variables are named (no anonymous assign)
    - generate a fresh variable to hold the return address (if needed)
    - generate fresh variables to hold extra-free-registers
    - split live ranges (caveat: do not forget to remove φ-nodes at the end)
    - compute liveness information
    - compute variables that are killed by a call to a function (including return addresses and extra registers)

    Initial 'info are preserved in the result.
   *)
  let count, _ = make_counter () in
  let annot_table : f_annot Hf.t = Hf.create 17 in
  let get_annot fn = Hf.find_default annot_table fn f_annot_empty in
  let liveness_table : (Sv.t * Sv.t, 'asm) func Hf.t = Hf.create 17 in
  let return_addresses : var Hf.t = Hf.create 17 in
  let extra_free_registers : (L.i_loc, var) Hashtbl.t = Hashtbl.create 137 in
  let killed_map : Sv.t Hf.t = Hf.create 17 in
  let killed fn = Hf.find killed_map fn in
  let preprocess f =
    Hf.add annot_table f.f_name f.f_annot;
    let f = f |> fill_in_missing_names |> Ssa.split_live_ranges Arch.aparams.ap_is_move_op false in
    Hf.add liveness_table f.f_name (Liveness.live_fd Arch.aparams.ap_is_move_op true f);
    let written =
      let written, cg = written_vars_fc f in
      let written =
        if
          match f.f_cc with
          | (Export | Internal) -> false
          | Subroutine _ ->
             match f.f_annot.retaddr_kind with
             | Some OnStack -> false
             | (None | Some OnReg) -> true
        then
          let r = V.mk " ra" (Reg Direct) (Bty (U U64)) L._dummy [] in
          if !Glob_options.debug then
            Format.eprintf "Fresh variable “%a” for the return address of function “%s”.@."
              (Printer.pp_var ~debug:true) r f.f_name.fn_name;
          Hf.add return_addresses f.f_name r;
          Sv.add r written
        else written
      in
      let killed_by_calls =
        Mf.fold (fun fn locs acc ->
            let acc = Sv.union (killed fn) acc in
            if (get_annot fn).retaddr_kind = Some OnStack then
              List.fold_left (fun acc loc ->
                  let r = V.mk (Format.sprintf " ra%d" (count())) (Reg Direct) (Bty (U U64)) loc.L.base_loc [] in
                  Hashtbl.add extra_free_registers loc r;
                  Sv.add r acc
                ) acc locs
            else acc
          ) cg Sv.empty in
      Sv.union written killed_by_calls
    in
    Hf.add killed_map f.f_name written;
    f
  in
  let funcs : (unit, 'asm) func list = funcs |> List.rev |> List.rev_map preprocess in
  if !Glob_options.debug then
    Format.printf "Before REGALLOC:@.%a@."
      Printer.(pp_list "@ @ " (pp_func ~debug:true Arch.asmOp)) (List.rev funcs);
  (* Live variables at the end of each function, in addition to returned local variables *)
  let get_liveness =
    let live : Sv.t Hf.t = Hf.create 17 in
    List.iter (fun f ->
        let f_with_liveness = Hf.find liveness_table f.f_name in
        let live_when_calling_f = Hf.find_default live f.f_name Sv.empty in
        Liveness.iter_call_sites (fun _loc fn xs (_, s) ->
            let s = Sv.union live_when_calling_f s in
            let s = Liveness.dep_lvs s xs in
            Hf.modify_def Sv.empty fn (Sv.union s) live) f_with_liveness
      ) funcs;
    fun fn -> Hf.find_default live fn Sv.empty
  in
  let excluded = Sv.of_list [Arch.rip; Arch.rsp_var] in
  let vars, nv = collect_variables_in_prog ~allvars:false excluded return_addresses extra_free_registers funcs in
  let eqc, tr, fr = collect_equality_constraints_in_prog Arch.asmOp Arch.aparams.ap_is_move_op "Regalloc" asm_equality_constraints vars nv funcs in
  let vars = normalize_variables vars eqc in
  (* Intra-procedural conflicts *)
  let conflicts =
    Hf.fold (fun _fn lf conflicts ->
        collect_conflicts Arch.asmOp vars tr lf conflicts
      )
      liveness_table
      empty_conflicts
  in
  (* Extra free registers at call-sites conflict with live variables *)
  let conflicts =
    let cnf = ref conflicts in
    Hf.iter (fun _fn f ->
        Liveness.iter_call_sites (fun loc _fn' _xs (s, _) ->
            match Hashtbl.find extra_free_registers loc with
            | exception Not_found -> ()
            | r -> cnf := Sv.fold (conflicts_add_one Arch.asmOp vars tr (Lmore loc) r) s !cnf
          ) f
      ) liveness_table;
    !cnf
  in
  (* In-register return address conflicts with function arguments *)
  let conflicts =
    List.fold_left (fun a f ->
        match Hf.find return_addresses f.f_name with
        | ra ->
           List.fold_left (fun cnf x -> conflicts_add_one Arch.asmOp vars tr Lnone ra x cnf) a f.f_args
        | exception Not_found -> a )
      conflicts funcs in
  (* Inter-procedural conflicts *)
  let conflicts =
    let add_conflicts s x = Sv.fold (conflicts_add_one Arch.asmOp vars tr Lnone x) s in
    List.fold_right (fun f cnf ->
        let live = get_liveness f.f_name in
        let vars = killed f.f_name in
        let cnf =
          match Hf.find return_addresses f.f_name with
          | ra -> cnf |> add_conflicts (Sv.remove ra vars) ra
          | exception Not_found -> cnf
        in
        cnf |> Sv.fold (add_conflicts vars) live
      ) funcs conflicts in
  let a = A.empty nv in
  List.iter (fun f -> allocate_forced_registers translate_var nv vars conflicts f a) funcs;
  greedy_allocation vars nv conflicts fr a;
  let subst = var_subst_of_allocation vars a in

  List.map (fun f -> f |> Subst.subst_func (subst_of_var_subst subst) |> Ssa.remove_phi_nodes) funcs,
  get_liveness,
  subst
  , killed
  , extra_free_registers
  , return_addresses

let alloc_prog translate_var (has_stack: ('info, 'asm) func -> 'a -> bool) (dfuncs: ('a * ('info, 'asm) func) list)
    : ('a * reg_oracle_t * (unit, 'asm) func) list * (L.i_loc -> var option) =
  (* Ensure that instruction locations are really unique,
     so that there is no confusion on the position of the “extra free register”. *)
  let dfuncs =
    List.map (fun (a,f) -> a, Prog.refresh_i_loc_f f) dfuncs in
  let extra : 'a Hf.t = Hf.create 17 in
  let funcs, get_liveness, subst, killed, extra_free_registers, return_addresses =
    dfuncs
    |> List.map (fun (a, f) -> Hf.add extra f.f_name a; f)
    |> global_allocation translate_var
  in
  if !Glob_options.debug then
    begin
      Format.eprintf "Extra free regs: ";
      Hashtbl.iter (fun loc r -> Format.eprintf "(%a → %a: %a)" L.pp_iloc loc (Printer.pp_var ~debug:true) r (Printer.pp_var ~debug:false) (subst r)) extra_free_registers;
      Format.eprintf "@."
    end;
  funcs |>
  List.map (fun f ->
      let e = Hf.find extra f.f_name in
      let stack_needed = has_stack f e in
      let to_save, ro_rsp = post_process ~stack_needed ~killed subst (get_liveness f.f_name) f in
      let ro_return_address =
        match Hf.find return_addresses f.f_name with
        | exception Not_found -> None
        | ra -> Some (subst ra)
      in
      let to_save = match ro_return_address with Some ra -> Sv.add ra to_save | None -> to_save in
      e, { ro_to_save = Sv.elements to_save ; ro_rsp ; ro_return_address }, f
    )
  , (fun loc -> Hashtbl.find_opt extra_free_registers loc |> Option.map subst)

end
