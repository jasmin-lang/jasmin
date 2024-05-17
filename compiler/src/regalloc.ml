open Utils
open Wsize
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
      L.mk_loc loc (V.mk n (Reg(Normal, Direct)) ty L._dummy [])
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
    | Csyscall (lvs, op, es) -> Csyscall(fill_lvs lvs, op, es)
    | Cif (e, s1, s2) -> Cif (e, fill_stmt s1, fill_stmt s2)
    | Cfor (i, r, s) -> Cfor (i, r, fill_stmt s)
    | Cwhile (a, s, e, s') -> Cwhile (a, fill_stmt s, e, fill_stmt s')
    | Ccall (lvs, f, es) -> Ccall (fill_lvs lvs, f, es)
  and fill_instr i = { i with i_desc = fill_instr_r i.i_desc }
  and fill_stmt s = List.map fill_instr s in
  let f_body = fill_stmt f.f_body in
  { f with f_body }

type kind = Word | Extra | Vector | Flag | Unknown of ty

let string_of_kind =
  function
  | Word -> "general purpose"
  | Extra -> "extra (aka mmx)"
  | Vector -> "vector"
  | Flag -> "flag"
  | Unknown ty -> Format.asprintf "(unknown of type %a)" PrintCommon.pp_ty ty

let kind_of_type reg_size k =
  function
  | Bty (U sz) ->
     if Wsize.wsize_cmp sz reg_size = Datatypes.Gt then Vector
     else if reg_kind k = Normal then Word else Extra
  | Bty Bool -> Flag
  | ty -> Unknown ty

(* Only variables that will be allocated to the same “bank” may conflict. *)
let types_cannot_conflict reg_size kx x ky y : bool =
  match kind_of_type reg_size kx x, kind_of_type reg_size ky y with
  | Word, Word | Extra, Extra | Vector, Vector | Flag, Flag -> false
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

let asm_equality_constraints ~loc pd reg_size asmOp is_move_op (int_of_var: var_i -> int option) (k: int -> int -> unit)
    (k': int -> int -> unit)
    (lvs: 'ty glvals) (op: 'asm sopn) (es: 'ty gexprs) : unit =
  let assert_compatible_types x y =
    let x = L.unloc x and y = L.unloc y in
    if types_cannot_conflict reg_size x.v_kind x.v_ty y.v_kind y.v_ty then
      hierror_reg ~loc "Variables %a and %a must be merged due to architectural constraints but must be allocated to incompatible banks “%s” and “%s” (respectively)"
        (Printer.pp_var ~debug:true) x
        (Printer.pp_var ~debug:true) y
        (string_of_kind (kind_of_type reg_size x.v_kind x.v_ty))
        (string_of_kind (kind_of_type reg_size y.v_kind y.v_ty))
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
    let id = get_instr_desc pd asmOp op in
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

let pp_trace pd asmOp (i: int) fmt (tr: ('info, 'asm) trace) =
  let j = try Hashtbl.find tr i with Not_found -> [] in
  let pp_i fmt i =
    Format.fprintf fmt "@[<v>at %a:@;<1 2>%a@]"
      L.pp_iloc i.i_loc
      (Printer.pp_instr ~debug:true pd asmOp) i
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

(* Renaming assignments can be removed between variables of compatible kinds,
where “compatibility” is defined below and allows the promotion of mutable
pointers to constant pointers. *)
let pointer_compatible (x: reference) (y: reference) : bool =
  match x, y with
  | Direct, Direct
  | Pointer Writable, Pointer Writable
  | Pointer Constant, Pointer _
      -> true
  | Direct, Pointer _
  | Pointer _, Direct
  | Pointer Writable, Pointer Constant
    -> false

let kind_compatible (x: v_kind) (y: v_kind) : bool =
  match x, y with
  | Const, Const
  | Inline, Inline
  | Global, Global
    -> true
  | Stack a, Stack b
  | Reg (Normal, a), Reg (Normal, b)
  | Reg (Extra, a), Reg (Extra, b)
    -> pointer_compatible a b
  | _, _ -> false

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
    | Csyscall (_lvs, _op, _es) -> ()
    | Cassgn (Lvar x, AT_phinode, _, Pvar y) when
          is_gkvar y && kind_i x = kind_i y.gv ->
       addv ii x y.gv
    | Cassgn (Lvar x, AT_rename, _, Pvar y) when
       is_gkvar y
       && kind_compatible (kind_i x) (kind_i y.gv)
       && not (is_stack_array x) ->
      addv ii x y.gv

    | Cassgn (Lvar x, _, _, Pvar y) when is_gkvar y && kind_i x = kind_i y.gv &&
                                          not (is_stack_array x) ->
       begin match int_of_var x, int_of_var y.gv with
       | Some i, Some j -> addf i j
       | (None, _) | (_, None) -> ()
       end
    | Cassgn _ -> ()
    | Ccall (xs, fn, es) ->
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
    (f: ('info, 'asm) func) : Puf.t =
  let int_of_var x = Hv.find_option tbl (L.unloc x) in
  let s = { cac_friends = IntMap.empty ; cac_eqc = Puf.create nv ; cac_trace = Array.make nv [] } in
  collect_equality_constraints_in_func asmOp is_move_op ~with_call_sites:None msg int_of_var copn_constraints s f;
  s.cac_eqc

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

let conflicts_add_one pd reg_size asmOp tbl tr loc (v: var) (w: var) (c: conflicts) : conflicts =
  if types_cannot_conflict reg_size v.v_kind v.v_ty w.v_kind w.v_ty then c else
  try
    let i = Hv.find tbl v in
    let j = Hv.find tbl w in
    if i = j then hierror_reg ~loc:loc "conflicting variables “%a” and “%a” must be merged due to:@;<1 2>%a"
                    (Printer.pp_var ~debug:true) v
                    (Printer.pp_var ~debug:true) w
                    (pp_trace pd asmOp i) tr;
    c |> add_conflicts i j |> add_conflicts j i
  with Not_found -> c

let collect_conflicts pd reg_size asmOp
      (tbl: int Hv.t) (tr: ('info, 'asm) trace) (f: (Sv.t * Sv.t, 'asm) func) (c: conflicts) : conflicts =
  let add_one = conflicts_add_one pd reg_size asmOp tbl tr in
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
    | Csyscall _
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
    | (Ccall (lvs, _, es) | Copn (lvs, _, _, es)) | Csyscall(lvs, _ , es) -> iter_lvs lvs; iter_exprs es
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

type retaddr =
  | StackDirect
  | StackByReg of var * var option
  | ByReg of var * var option

let collect_variables_in_prog
      ~(allvars: bool)
      (excluded: Sv.t)
      (return_adresses: retaddr Hf.t)
      (all_reg: var list)
      (f: ('info, 'asm) func list) : int Hv.t * int =
  let fresh, total = make_counter () in
  let tbl : int Hv.t = Hv.create 97 in
  List.iter (fun f ->
      let extra, tmp =
        match Hf.find return_adresses f.f_name with
        | StackByReg (v, tmp) | ByReg (v, tmp) -> Some v, tmp
        | StackDirect -> None, None in
        collect_variables_aux ~allvars excluded fresh tbl extra f;
        Option.may (collect_variables_cb ~allvars excluded fresh tbl) tmp) f;
  List.iter (collect_variables_cb ~allvars excluded fresh tbl) all_reg;
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
       let other = IntSet.fold (fun i -> Sv.union regs.(i)) c Sv.empty |> Sv.elements in
       hierror_reg ~loc:(Lmore loc) "variable %a must be allocated to register %a due to architectural constaints; this register already holds conflicting variable%s: %a"
         pv x_
         (Printer.pp_var ~debug:false) r
         (match other with [ _ ] -> "" | _ -> "s")
         (pp_list "; " pv)
         other

type reg_oracle_t = {
    (* The list of callee save registers that are modified by
      a call to the export function *)
    ro_to_save: var list;
    (* A register that can be used to save the rsp of export function *)
    ro_rsp: var option;
    (* How the return address is pass to the function *)
    ro_return_address: retaddr;
  }

module type Regalloc = sig
  type extended_op

  val split_live_ranges : (unit, extended_op) func -> (unit, extended_op) func
  val renaming : (unit, extended_op) func -> (unit, extended_op) func
  val remove_phi_nodes : (unit, extended_op) func -> (unit, extended_op) func

  val subroutine_ra_by_stack : (unit, extended_op) func -> bool

  val alloc_prog :
    (Var0.Var.var -> var) ->
    ((unit, extended_op) func -> 'a -> bool) ->
    ((unit, extended_op) func -> 'a -> Z.t) ->
    ('a * (unit, extended_op) func) list ->
    ('a * reg_oracle_t * (unit, extended_op) func) list
end

module Regalloc (Arch : Arch_full.Arch)
  : Regalloc with type extended_op := (Arch.reg, Arch.regx, Arch.xreg, Arch.rflag, Arch.cond, Arch.asm_op, Arch.extra_op) Arch_extra.extended_op = struct

  let forced_registers translate_var loc nv (vars: int Hv.t) (cnf: conflicts)
      (lvs: 'ty glvals) (op: 'asm sopn) (es: 'ty gexprs)
      (a: A.allocation) : unit =
    let allocate_one x y a =
      let x = L.unloc x in
      if types_cannot_conflict Arch.reg_size x.v_kind x.v_ty y.v_kind y.v_ty
      then hierror_reg ~loc:(Lmore loc) "variable %a (declared at %a with type “%a”) must be allocated to register %a from an incompatible bank"
          (Printer.pp_var ~debug:true) x
          L.pp_sloc x.v_dloc
          PrintCommon.pp_ty x.v_ty
          (Printer.pp_var ~debug:false) y;
      let i =
        try Hv.find vars x
        with Not_found ->
          hierror_reg ~loc:(Lmore loc) "variable %a (declared at %a as “%a”) must be allocated to register %a but is unknown to the register allocator%s"
            (Printer.pp_var ~debug:true) x
            L.pp_sloc x.v_dloc
            PrintCommon.pp_kind x.v_kind
            (Printer.pp_var ~debug:false) y
            (if is_reg_kind x.v_kind then "" else " (consider declaring this variable as “reg”)")
      in
      allocate_one nv vars loc cnf x i y a
    in
    let mallocate_one x y a =
      match x with Pvar x when is_gkvar x -> allocate_one x.gv y a | _ -> ()
    in
    let id = get_instr_desc Arch.reg_size Arch.asmOp op in
    List.iter2 (fun ad lv ->
        match ad with
        | ADImplicit v ->
           begin match lv with
           | Lvar w -> allocate_one w (translate_var v) a
           | _ -> assert false
           end
        | ADExplicit _ -> ()) id.i_out lvs;
    List.iter2 (fun ad e ->
        match ad with
        | ADImplicit v ->
           mallocate_one e (translate_var v) a
        | ADExplicit (_, Some v) ->
           mallocate_one e (translate_var v) a
        | ADExplicit (_, None) -> ()) id.i_in es

let allocate_forced_registers return_addresses translate_var nv (vars: int Hv.t) (cnf: conflicts)
    (f: ('info, 'asm) func) (a: A.allocation) : unit =
  let split ~ctxt ~num =
    function
    | hd :: tl -> hd, tl
    | [] ->
       hierror_reg ~loc:(Lone f.f_loc) ~funname:f.f_name.fn_name "too many %s according to the ABI (only %d available on this architecture)"
         ctxt num
  in
  let alloc_from_list loc ~ctxt rs xs q vs : unit =
    let f x = Hv.find vars x in
    let num_rs = List.length rs in
    let num_xs = List.length xs in
    List.fold_left (fun (rs, xs) p ->
        let p = q p in
        match f p with
        | i ->
          let d, rs, xs =
            match kind_of_type Arch.reg_size p.v_kind p.v_ty with
            | Word -> let d, rs = split ~ctxt ~num:num_rs rs in d, rs, xs
            | Vector ->
                let ctxt = "large " ^ ctxt in
                let d, xs = split ~ctxt ~num:num_xs xs in d, rs, xs
            | Extra ->
               hierror_reg ~loc:(Lmore loc) "unexpected extra register %a" (Printer.pp_var ~debug:true) p
            | Flag ->
               hierror_reg ~loc:(Lmore loc) "unexpected flag register %a" (Printer.pp_var ~debug:true) p
            | Unknown ty ->
              hierror_reg ~loc:(Lmore loc) "unknown type %a for forced register %a"
                PrintCommon.pp_ty ty (Printer.pp_var ~debug:true) p
          in
          allocate_one nv vars loc cnf p i d a;
          (rs, xs)
        | exception Not_found -> (rs, xs))
      (rs, xs)
      vs
    |> (ignore : var list * var list -> unit)
  in
  let alloc_args loc get = alloc_from_list loc ~ctxt:"parameters" Arch.argument_vars Arch.xmm_argument_vars get in
  let alloc_ret loc get = alloc_from_list loc ~ctxt:"return values" Arch.ret_vars Arch.xmm_ret_vars get in
  let rec alloc_instr_r loc =
    function
    | Cfor (_, _, s)
      -> alloc_stmt s
    | Copn (lvs, _, op, es) -> forced_registers translate_var loc nv vars cnf lvs op es a
    | Csyscall(lvs, _, es) ->
       let get_a = function Pvar { gv ; gs = Slocal } -> L.unloc gv | _ -> assert false in
       let get_r = function Lvar gv -> L.unloc gv | _ -> assert false in
       alloc_args loc get_a es;
       alloc_ret loc get_r lvs

    | Cwhile (_, s1, _, s2)
    | Cif (_, s1, s2)
        -> alloc_stmt s1; alloc_stmt s2
    | Cassgn _
      -> ()
    | Ccall (lvs, _, es) ->
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
  if FInfo.is_export f.f_cc then alloc_args loc identity f.f_args;
  if FInfo.is_export f.f_cc then alloc_ret loc L.unloc f.f_ret;
  alloc_stmt f.f_body;
  match Hf.find return_addresses f.f_name, Arch.callstyle with
  | (StackByReg (ra,_) | ByReg (ra, _)), Arch_full.ByReg (Some r) ->
      let i = Hv.find vars ra in
      allocate_one nv vars (Location.i_loc f.f_loc []) cnf ra i r a
  | _ -> ()

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
  (* Give a specific error message if the bank is empty: there is no way the
     variables can be allocated. We pick one of the variables to illustrate
     the error message. *)
  begin match schedule, registers with
  | i :: _, [] ->
      let x = List.hd (Hashtbl.find variables i) in
      hierror_reg ~loc:Lnone "unable to allocate %a: bank “%s” is empty on this architecture"
        (Printer.pp_dvar ~debug:true) x
        (string_of_kind (kind_of_type Arch.reg_size x.v_kind x.v_ty))
  | _, _ -> ()
  end;
  List.iter (fun i ->
      let has_no_conflict v = does_not_conflict i cnf a v in
      match List.filter has_no_conflict registers with
      | [] ->
         let pv = Printer.pp_dvar ~debug:true in
         let ppvl fmt = List.iter @@ Format.fprintf fmt "\n    %a" pv in
         let pp_conflicts fmt c =
           let unallocated =
             IntSet.fold (fun i xs ->
                 match A.find i a with
                 | Some r ->
                   Format.fprintf fmt " - register %a%a\n"
                     (Printer.pp_var ~debug:false) r
                     ppvl (Hashtbl.find variables i);
                   xs
                 | None -> i :: xs)
               c
               []
           in
           if unallocated <> [] then begin
             Format.fprintf fmt " - variables not allocated yet";
             List.iter (fun i -> ppvl fmt (Hashtbl.find variables i)) unallocated
           end
         in
         let c = get_conflicts i cnf in
         hierror_reg ~loc:Lnone "no more free register to allocate variable:%a\nConflicts with:\n%a"
           ppvl (Hashtbl.find variables i)
           pp_conflicts c
      | x :: regs ->
        (* Any register in [x; regs] is valid: the choice made here is arbitrary. *)
        let y = get_friend_registers x fr a i regs in
        A.set i y a
    ) schedule

let check_allocated
      (vars: (int, var list) Hashtbl.t)
      (a: A.allocation) : unit =
  match Hashtbl.fold (fun i x m -> if A.mem i a then m else x @ m) vars [] with
  | [] -> ()
  | m ->
     hierror_reg ~loc:Lnone "variables { %a } remain unallocated"
       (pp_list "; " (Printer.pp_var ~debug:true)) m

let greedy_allocation
    (vars: int Hv.t)
    (nv: int) (cnf: conflicts)
    (fr: friend)
    (a: A.allocation) : unit =
  let scalars : (int, var list) Hashtbl.t = Hashtbl.create nv in
  let extra_scalars : (int, var list) Hashtbl.t = Hashtbl.create nv in
  let vectors : (int, var list) Hashtbl.t = Hashtbl.create nv in
  let flags : (int, var list) Hashtbl.t = Hashtbl.create nv in
  let push_var tbl i v =
    match Hashtbl.find tbl i with
    | old -> Hashtbl.replace tbl i (v :: old)
    | exception Not_found -> Hashtbl.add tbl i [ v ]
  in
  Hv.iter (fun v i ->
      match kind_of_type Arch.reg_size v.v_kind v.v_ty with
      | Word -> push_var scalars i v
      | Extra -> push_var extra_scalars i v
      | Vector -> push_var vectors i v
      | Flag -> push_var flags i v
      | Unknown ty ->
          hierror_reg ~loc:Lnone "unable to allocate variable %a: no register bank for type %a"
            (Printer.pp_dvar ~debug:true) v PrintCommon.pp_ty ty
      ) vars;
  two_phase_coloring Arch.allocatable_vars scalars cnf fr a;
  two_phase_coloring Arch.extra_allocatable_vars extra_scalars cnf fr a;
  two_phase_coloring Arch.xmm_allocatable_vars vectors cnf fr a;
  check_allocated flags a;
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
  Ssa.split_live_ranges true f

let renaming (f: ('info, 'asm) func) : (unit, 'asm) func =
  let vars, nv = collect_variables ~allvars:true Sv.empty f in
  let eqc =
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
  let a = reverse_varmap nv vars in
  (* The variable that is added last is the representative of its class.
     This makes sure that each argument is the representative of its class,
     meaning that it will be preserved. *)
  List.iter (fun arg -> A.set (Hv.find vars arg) arg a) f.f_args;
  let subst = subst_of_allocation vars a in
  Subst.subst_func subst f

let remove_phi_nodes (f: ('info, 'asm) func) : (unit, 'asm) func =
  Ssa.remove_phi_nodes f

(** Returns extra information (k, rsp) depending on the calling convention.

 - Subroutines:
   - k: all registers overwritten by a call to f (including ra)
   - rsp: None

 - Export:
    - k: all callee-saved registers overwritten by this function (including rsp)
    - rsp: if ~stack_needed and if there is a free register, a free register to hold the stack pointer of the caller (aka environment)

*)
let post_process
  ~allocatable_vars
  ~callee_save_vars
  ~not_saved_stack
  ~stack_needed
  (subst: var -> var)
  (live: Sv.t)
  ~(killed: funname -> Sv.t)
  (f: _ func) :
  Sv.t * var option =
  let killed_in_f = killed f.f_name |> Sv.map subst in
  match f.f_cc with
  | Internal -> assert false
  | Subroutine _ ->
     begin
       assert (not stack_needed);
       killed_in_f, None
     end
  | Export _ ->
     begin
       assert (Sv.is_empty live);
       let used_in_f = List.fold_left (fun s x -> Sv.add (subst x) s) killed_in_f f.f_args in
       let free_regs = Sv.diff allocatable_vars used_in_f in
       let to_save = Sv.inter callee_save_vars killed_in_f in
       if stack_needed && Sv.is_empty to_save then
         to_save, Sv.Exceptionless.any (Sv.diff free_regs not_saved_stack)
       else to_save, None
     end

let subroutine_ra_by_stack f =
  match f.f_cc with
  | Export _ | Internal -> assert false
  | Subroutine _ ->
      match Arch.callstyle with
      | Arch_full.StackDirect -> true
      | Arch_full.ByReg oreg ->
        let dfl = oreg <> None && has_call_or_syscall f.f_body in
        match f.f_annot.retaddr_kind with
        | None -> dfl
        | Some k -> dfl || k = OnStack

module Miloc = Map.Make (struct
  open Location
  type t = i_loc
  let compare x y = Stdlib.Int.compare x.uid_loc y.uid_loc
end)

type callsite_tree =
  { sv : Sv.t option; sub : callsite_tree Miloc.t }

let empty_callsite =
  { sv = None; sub = Miloc.empty }

let rec insert_callsite t (locs, sv) =
  match locs with
  | [] -> assert (t.sv = None); { t with sv = Some sv }
  | loc::locs ->
    { t with sub =
      Miloc.modify_def empty_callsite loc
        (fun t -> insert_callsite t (locs, sv))
       t.sub }

let callsite_tree (s : (Location.i_loc list * Sv.t) list) =
  List.fold_left insert_callsite empty_callsite s




let pp_liveness vars liveness_per_callsite liveness_table conflicts a =
  (* Prints the program with forced registers, equivalence classes, and liveness information *)
  let open Format in
  let open PrintCommon in
  let open Printer in
  let pp_variable fmt i = fprintf fmt "v%d" i in
  let pp_reg fmt r = pp_var fmt ~debug:false r in
  let pp_nonreg fmt x = pp_var fmt ~debug:true x in
  let pp_decl_type fmt x = fprintf fmt "%a %a" pp_kind x.v_kind pp_ty x.v_ty in
  let pp_var fmt x =
    match Hv.find vars x with
    | exception Not_found -> pp_nonreg fmt x
    | i -> match A.find i a with
           | Some r -> pp_reg fmt r
           | None -> pp_variable fmt i
  in
  let pp_locals fmt s =
    let tbl = ref IntMap.empty in
    Sv.iter (fun x ->
        match Hv.find vars x with
        | exception Not_found -> fprintf fmt "%a %a@ " pp_decl_type x pp_nonreg x
        | i -> if A.find i a = None then tbl := IntMap.modify_def [] i (List.cons x) !tbl
      ) s;
    IntMap.iter (fun i -> function
        | [] -> ()
        | x :: _ as xs -> fprintf fmt "%a %a /* %a */@ " pp_decl_type x pp_variable i (pp_list ", " pp_nonreg) xs
      ) !tbl
  in
  let m_word, m_extra, m_vector, m_flag = ref 0, ref 0, ref 0, ref 0 in
  let reset_max () =
    m_word := 0; m_extra := 0; m_vector := 0; m_flag := 0
  in

  let set_max k n =
    match k with
    | Word   -> m_word   := max !m_word   n
    | Extra  -> m_extra  := max !m_extra  n
    | Vector -> m_vector := max !m_vector n
    | Flag   -> m_flag   := max !m_flag   n
    | Unknown _ -> assert false
  in

  let string_of_k = function
    | Word   -> "word"
    | Extra  -> "extra"
    | Vector -> "vector"
    | Flag   -> "flag"
    | Unknown _ -> assert false
  in

  let pp_liveset fmt s =
    let subset k = Sv.elements (Sv.filter (fun x -> k (kind_of_type Arch.reg_size x.v_kind x.v_ty)) s) in
    let words = subset (fun k -> k = Word) in
    let extras = subset (fun k -> k = Extra) in
    let vectors = subset (fun k -> k = Vector) in
    let flags = subset (fun k -> k = Flag) in
    let pp fmt (k, xs) =
      let n = List.length xs in
      set_max k n;
      fprintf fmt "@[<h> %d %s%s (%a)@]" n (string_of_k k) (if n > 1 then "s" else "") (pp_list "@ " pp_var) xs in
    let l =
      (List.filter (fun (_, m) -> List.length m > 0)
         [ Word, words; Extra, extras; Vector, vectors; Flag, flags]) in
    fprintf fmt "%a" (pp_list "@ " pp) l

  in

  let pp_info fmt (loc, (i, o)) =
    fprintf fmt "/* %a */@ " L.pp_iloc_short loc;
    fprintf fmt "@[<v>/* Live-in:@ %a */@]@ " pp_liveset i;
    fprintf fmt "@[<v>/* Live-out:@ %a */@]@ " pp_liveset o
  in

  let pp_callsites fmt fn =
    let s = Hf.find_default liveness_per_callsite fn [] in
    let rec pp_callsite i fmt t =
      match t.sv with
      | Some sv ->
          assert (Miloc.is_empty t.sub);
          fprintf fmt "@[<v>%a@]" pp_liveset sv;
      | None ->
        if Miloc.is_empty t.sub then ()
        else
          let pp_site fmt (loc, t) =
            fprintf fmt "(%i)%a@   %a" i L.pp_iloc loc (pp_callsite (i+1)) t
          in
         fprintf fmt "@[<v>%a@]" (pp_list "@ " pp_site) (Miloc.bindings t.sub)
    in
    if s <> [] then
      fprintf fmt "@[<v>/* Live when calling %s:@ %a*/@]" fn.fn_name (pp_callsite 0) (callsite_tree s)
  in

  let pp_recap fmt fn (i_w, i_e, i_v, i_f) (e_w, e_e, e_v, e_f) =
    let pp fmt (k, i, e) =
      fprintf fmt  "(intern : %d, extern : %d, total : %d) %s%s" i e (i+e)
        (string_of_k k) (if (i+e) > 1 then "s" else "")
    in
    fprintf fmt "@[<v>/* Maximal register usage for %s:@ %a@ */@]@.@."
      fn.fn_name
      (pp_list "@ " pp)
      (List.filter (fun (_, i , e) -> i + e > 0)
         [ Word, i_w, e_w; Extra, i_e, e_e; Vector, i_v, e_v; Flag, i_f, e_f])
  in

  printf "/* Ready to allocate variables to registers: */@.";
  liveness_table |> Hf.iter (fun fn fd ->
    reset_max();
    printf "%a@." (pp_fun ~pp_locals ~pp_info (pp_opn Arch.reg_size Arch.asmOp) pp_var) fd;
    let intern = !m_word, !m_extra, !m_vector, !m_flag in
    reset_max();
    printf "%a@." pp_callsites fn;
    let extern = !m_word, !m_extra, !m_vector, !m_flag in
    pp_recap Format.std_formatter fn intern extern)

let global_allocation translate_var get_internal_size (funcs: ('info, 'asm) func list) :
  (unit, 'asm) func list * (funname -> Sv.t) * (var -> var) * (funname -> Sv.t) * retaddr Hf.t =
  (* Preprocessing of functions:
    - ensure all variables are named (no anonymous assign)
    - generate a fresh variable to hold the return address (if needed)
    - split live ranges (caveat: do not forget to remove φ-nodes at the end)
    - compute liveness information
    - compute variables that are killed by a call to a function (including return addresses and extra registers)

    Initial 'info are preserved in the result.
   *)
  let liveness_table : (Sv.t * Sv.t, 'asm) func Hf.t = Hf.create 17 in
  let return_addresses : retaddr Hf.t = Hf.create 17 in
  let killed_map : Sv.t Hf.t = Hf.create 17 in
  let killed fn = Hf.find killed_map fn in
  let preprocess f =
    let f = f |> fill_in_missing_names |> Ssa.split_live_ranges false in
    Hf.add liveness_table f.f_name (Liveness.live_fd true f);
    (* compute where will be store the return address *)
    let ra =
       match f.f_cc with
       | Export _ -> StackDirect
       | Internal -> assert false
       | Subroutine _ ->
         match Arch.callstyle with
         | Arch_full.StackDirect -> StackDirect
         | Arch_full.ByReg oreg ->
           let dfl = oreg <> None && has_call_or_syscall f.f_body in
           let r = V.mk ("ra_"^f.f_name.fn_name) (Reg(Normal,Direct)) (tu Arch.reg_size) f.f_loc [] in
           (* Fixme: Add an option in Arch to say when the tmp reg is needed *)
           let tmp_needed = Arch.alloc_stack_need_extra (get_internal_size f) in
           let tmp =
             if tmp_needed then
               let tmp = V.mk ("tmp_"^f.f_name.fn_name) (Reg(Normal,Direct)) (tu Arch.reg_size) f.f_loc [] in
               Some tmp
             else None in
           let rastack =
             match f.f_annot.retaddr_kind with
             | None -> dfl
             | Some k -> dfl || k = OnStack in
           if rastack then StackByReg (r, tmp)
           else ByReg (r, tmp) in
    Hf.add return_addresses f.f_name ra;
    let written =
      let written, cg = written_vars_fc f in
      let written =
        match f.f_cc with
        | (Export _ | Internal) -> written
        | Subroutine _ ->
          match ra with
          | StackDirect -> written
          | StackByReg (r, None) | ByReg (r, None) -> Sv.add r written
          | StackByReg (r, Some t) | ByReg (r, Some t) -> Sv.add t (Sv.add r written)
      in
      let killed_by_calls =
        Mf.fold (fun fn _locs acc -> Sv.union (killed fn) acc)
          cg Sv.empty in
      let killed_by_syscalls = if has_syscall f.f_body then Arch.syscall_kill else Sv.empty in
      Sv.union (Sv.union written killed_by_calls) killed_by_syscalls
    in
    Hf.add killed_map f.f_name written;
    f
  in
  let funcs : (unit, 'asm) func list = funcs |> List.rev |> List.rev_map preprocess in
  if !Glob_options.debug then
    Format.printf "Before REGALLOC:@.%a@."
      Printer.(pp_list "@ @ " (pp_func ~debug:true Arch.reg_size Arch.asmOp)) (List.rev funcs);
  (* Live variables at the end of each function, in addition to returned local variables *)
  let get_liveness, slive, liveness_per_callsite =
    let live : (L.i_loc list * Sv.t) list Hf.t = Hf.create 17 in
    let slive : (BinNums.positive Syscall_t.syscall_t, Sv.t) Hashtbl.t = Hashtbl.create 17 in
    List.iter (fun f ->
        let f_with_liveness = Hf.find liveness_table f.f_name in
        let live_when_calling_f = Hf.find_default live f.f_name [[], Sv.empty] in
        let cbf loc fn xs (_, s) =
          let s = Liveness.dep_lvs s xs in
          let s = List.map (fun (ctx, ls) -> loc :: ctx, Sv.union s ls) live_when_calling_f in
          Hf.modify_def [] fn (List.rev_append s) live in
        let cbs _loc o xs (_, s) =
            let s = Liveness.dep_lvs s xs in
            match Hashtbl.find slive o with
            | s0 -> Hashtbl.replace slive o (Sv.union s s0)
            | exception Not_found -> Hashtbl.add slive o s in

        Liveness.iter_call_sites cbf cbs f_with_liveness
      ) funcs;
    (let tbl = Hf.map (fun _ -> List.fold_left (fun acc (_, s) -> Sv.union acc s) Sv.empty) live in
     fun fn -> Hf.find_default tbl fn Sv.empty),
    slive,
    live
  in
  let excluded = Sv.of_list [Arch.rip; Arch.rsp_var] in
  let vars, nv = collect_variables_in_prog ~allvars:false excluded return_addresses Arch.all_registers funcs in
  let eqc, tr, fr =
    collect_equality_constraints_in_prog
      Arch.asmOp
      Arch.aparams.ap_is_move_op
      "Regalloc"
      (asm_equality_constraints Arch.pointer_data Arch.reg_size)
      vars
      nv
      funcs
  in
  let vars = normalize_variables vars eqc in
  (* Intra-procedural conflicts *)
  let conflicts =
    Hf.fold (fun _fn lf conflicts ->
        collect_conflicts Arch.pointer_data Arch.reg_size Arch.asmOp vars tr lf conflicts
      )
      liveness_table
      empty_conflicts
  in

  (* In-register return address conflicts with function arguments *)
  let conflicts =
    let doit ra =
      List.fold_left (fun cnf x -> conflicts_add_one Arch.pointer_data Arch.reg_size Arch.asmOp vars tr Lnone ra x cnf) in
    List.fold_left (fun a f ->
        match Hf.find return_addresses f.f_name with
        | ByReg (ra, None) | StackByReg(ra,None) ->
           doit ra a f.f_args
        | ByReg (ra, Some tmp) | StackByReg(ra,Some tmp) ->
          let a = doit ra a f.f_args in
          (* tmp register used to increment the stack conflicts with function arguments and results *)
          let a = doit tmp a f.f_args in
          doit tmp a (List.map L.unloc f.f_ret)
        | StackDirect -> a)
      conflicts funcs in
  (* Inter-procedural conflicts *)
  let conflicts =
    let add_conflicts s x = Sv.fold (conflicts_add_one Arch.pointer_data Arch.reg_size Arch.asmOp vars tr Lnone x) s in
    List.fold_right (fun f cnf ->
        let live = get_liveness f.f_name in
        let vars = killed f.f_name in
        let cnf =
          match Hf.find return_addresses f.f_name with
          | ByReg (ra, _) -> cnf |> add_conflicts (Sv.remove ra vars) ra
          | StackDirect | StackByReg _ -> cnf
        in
        cnf |> Sv.fold (add_conflicts vars) live
      ) funcs conflicts in

  (* syscall conflicts *)
  let conflicts =
    let add_conflicts x = Sv.fold (conflicts_add_one Arch.pointer_data Arch.reg_size Arch.asmOp vars tr Lnone x) Arch.syscall_kill in
    Hashtbl.fold (fun _o live cnf -> cnf |> Sv.fold add_conflicts live) slive conflicts in

  let a = A.empty nv in

  (* Allocate all_vars *)
  let allocate_one x =
    match Hv.find vars x with
    | i -> allocate_one nv vars L.i_dummy conflicts x i x a
    | exception Not_found -> ()
  in
  List.iter allocate_one Arch.all_registers;

  List.iter (fun f -> allocate_forced_registers return_addresses translate_var nv vars conflicts f a) funcs;

  if !Glob_options.print_liveness then pp_liveness vars liveness_per_callsite liveness_table conflicts a;

  greedy_allocation vars nv conflicts fr a;
  let subst = var_subst_of_allocation vars a in

  List.map (fun f -> f |> Subst.subst_func (subst_of_var_subst subst) |> Ssa.remove_phi_nodes) funcs,
  get_liveness,
  subst
  , killed
  , return_addresses

let alloc_prog translate_var (has_stack: ('info, 'asm) func -> 'a -> bool) get_internal_size (dfuncs: ('a * ('info, 'asm) func) list)
    : ('a * reg_oracle_t * (unit, 'asm) func) list =
  (* Ensure that instruction locations are really unique,
     so that there is no confusion on the position of the “extra free register”. *)
  let dfuncs =
    List.map (fun (a,f) -> a, Prog.refresh_i_loc_f f) dfuncs in

  let extra : 'a Hf.t = Hf.create 17 in
  let allocatable_vars = Sv.of_list Arch.allocatable_vars in
  let callee_save_vars = Sv.of_list Arch.callee_save_vars in
  let not_saved_stack =
    Sv.of_list (Arch.not_saved_stack @ Arch.callee_save_vars)
  in

  let funcs, get_liveness, subst, killed, return_addresses =
    dfuncs
    |> List.map (fun (a, f) -> Hf.add extra f.f_name a; f)
    |> global_allocation translate_var (fun f -> get_internal_size f (Hf.find extra f.f_name))
  in
  funcs |>
  List.map (fun f ->
      let e = Hf.find extra f.f_name in
      let stack_needed = has_stack f e in
      let to_save, ro_rsp =
         post_process
          ~allocatable_vars
          ~callee_save_vars
          ~not_saved_stack
          ~stack_needed
          ~killed
          subst
          (get_liveness f.f_name)
          f in
      let ro_return_address =
        match Hf.find return_addresses f.f_name with
        | StackDirect -> StackDirect
        | StackByReg(r, tmp) -> StackByReg (subst r, Option.map subst tmp)
        | ByReg(r, tmp) -> ByReg (subst r, Option.map subst tmp) in
      let ro_to_save = if FInfo.is_export f.f_cc then Sv.elements to_save else [] in
      e, { ro_to_save ; ro_rsp ; ro_return_address }, f
    )

end
