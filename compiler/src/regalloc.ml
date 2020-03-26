open Utils
open Expr
open Prog
open X86_decl

module IntSet = Sint
module IntMap = Mint

let fill_in_missing_names (f: 'info func) : 'info func =
  let fresh_name : L.t -> ty -> ty gvar_i =
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

let x86_equality_constraints (tbl: int Hv.t) (k: int -> int -> unit)
    (k': int -> int -> unit)
    (lvs: 'ty glvals) (op: sopn) (es: 'ty gexprs) : unit =
  let merge k v w =
    try
      let i = Hv.find tbl (L.unloc v) in
      let j = Hv.find tbl (L.unloc w) in
      k i j
    with Not_found -> ()
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

let collect_equality_constraints
    (msg: string)
    copn_constraints
    (tbl: int Hv.t) (nv: int)
    (f: 'info func) : Puf.t * 'info trace * friend =
  let p = ref (Puf.create nv) in
  let tr = Array.make nv [] in
  let fr = ref IntMap.empty in
  let add ii x y =
      tr.(x) <- ii :: tr.(x);
      p := Puf.union !p x y
  in
  let addf x y = fr := set_friend x y !fr in
  let rec collect_instr_r ii =
    function
    | Cfor (_, _, s)
      -> collect_stmt s
    | Copn (lvs, _, op, es) -> copn_constraints tbl (add ii) addf lvs op es
    | Cassgn (Lvar x, (AT_rename | AT_phinode), _, Pvar y) when is_gkvar y ->
      let i = try Hv.find tbl (L.unloc x) with
        Not_found ->
          hierror "%s: unknown variable %a"
            msg
            (Printer.pp_var ~debug:true) (L.unloc x)
      in
      let j = Hv.find tbl (L.unloc y.gv) in
      add ii  i j
    | Cassgn (Lvar x, _, _, Pvar y) when is_gkvar y && kind_i x = kind_i y.gv ->
      begin try
        let i = Hv.find tbl (L.unloc x) in
        let j = Hv.find tbl (L.unloc y.gv) in
        fr := set_friend i j !fr
      with Not_found -> ()
    end
    | Cassgn _
    | Ccall _
      -> ()
    | Cwhile (_, s1, _, s2)
    | Cif (_, s1, s2) -> collect_stmt s1; collect_stmt s2
  and collect_instr ({ i_desc } as i) = collect_instr_r i i_desc
  and collect_stmt s = List.iter collect_instr s in
  collect_stmt f.f_body;
  let eqc = !p in
  eqc, normalize_trace eqc tr, !fr

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

let collect_conflicts (tbl: int Hv.t) (tr: 'info trace) (f: (Sv.t * Sv.t) func) : conflicts =
  let add_one_aux (v: int) (w: int) (c: conflicts) : conflicts =
      let x = get_conflicts v c in
      IntMap.add v (IntSet.add w x) c
  in
  let add_one loc (v: var) (w: var) (c: conflicts) : conflicts =
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
  in
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
  collect_stmt IntMap.empty f.f_body

let collect_variables (allvars: bool) (excluded:Sv.t) (f: 'info func) : int Hv.t * int =
  let fresh, total =
    let count = ref 0 in
    (fun () ->
    let n = !count in
    incr count;
    n),
    (fun () -> !count)
  in
  let tbl : int Hv.t = Hv.create 97 in
  (* Remove sp and rip *)
  let get (v: var) : unit =
    if allvars || (is_reg_kind v.v_kind && not (Sv.mem v excluded)) then
    if not (Hv.mem tbl v)
    then
      let n = fresh () in
      Hv.add tbl v n
  in
  let collect_sv = Sv.iter get in
  let collect_lv lv = rvars_lv Sv.empty lv |> collect_sv in
  let collect_lvs lvs = List.fold_left rvars_lv Sv.empty lvs |> collect_sv in
  let collect_expr e = vars_e e |> collect_sv in
  let collect_exprs es = vars_es es |> collect_sv in
  let rec collect_instr_r =
    function
    | Cassgn (lv, _, _, e) -> collect_lv lv; collect_expr e
    | Ccall (_, lvs, _, es)
    | Copn (lvs, _, _, es) -> collect_lvs lvs; collect_exprs es
    | Cwhile (_, s1, e, s2)
    | Cif (e, s1, s2) -> collect_expr e; collect_stmt s1; collect_stmt s2
    | Cfor _ -> assert false
  and collect_instr { i_desc } = collect_instr_r i_desc
  and collect_stmt s = List.iter collect_instr s in
  collect_stmt f.f_body;
  List.iter get f.f_args;
  tbl, total ()

let normalize_variables (tbl: int Hv.t) (eqc: Puf.t) : int Hv.t =
    let r = Hv.create 97 in
    Hv.iter (fun v n -> Hv.add r v (Puf.find eqc n)) tbl;
    r

type allocation = var IntMap.t

exception AlreadyAllocated

let allocate_one loc (cnf: conflicts) (x_:var) (x: int) (r: var) (a: allocation) : allocation =
  match IntMap.find x a with
  | r' when r' = r -> a
  | r' ->
     let pv = Printer.pp_var ~debug: true in
     hierror "at line %a: can not allocate %a into %a, the variable is already allocated in %a"
       Printer.pp_iloc loc
       pv x_
       pv r
       pv r'

  | exception Not_found ->
     let c = get_conflicts x cnf in
     IntMap.iter (fun i r' ->
         if V.equal r r' && IntSet.mem i c
         then let pv = Printer.pp_var ~debug:true in
              hierror "Register allocation at line %a: variable %a must be allocated to conflicting register %a" Printer.pp_iloc loc pv x_ pv r
       ) a;
     IntMap.add x r a

let conflicting_registers (i: int) (cnf: conflicts) (a: allocation) : var option list =
  get_conflicts i cnf |>
  IntSet.elements |>
  List.map (fun k -> try Some (IntMap.find k a) with Not_found -> None)

module X64 =
struct

  let reg_k = Prog.Reg Prog.Direct

  let rax = V.mk "RAX" reg_k (Bty (U U64)) L._dummy
  let rbx = V.mk "RBX" reg_k (Bty (U U64)) L._dummy
  let rcx = V.mk "RCX" reg_k (Bty (U U64)) L._dummy
  let rdx = V.mk "RDX" reg_k (Bty (U U64)) L._dummy
  let rsp = V.mk "RSP" reg_k (Bty (U U64)) L._dummy
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

  let flags = [f_c; f_d; f_o; f_p; f_s; f_z]

  let all_registers = reserved @ allocatable @ xmm_allocatable @ flags

  let forced_registers translate_var loc (vars: int Hv.t) (cnf: conflicts)
      (lvs: 'ty glvals) (op: sopn) (es: 'ty gexprs)
      (a: allocation) : allocation =
    let f x = Hv.find vars (L.unloc x) in
    let allocate_one x y a =
      let i = f x in
      allocate_one loc cnf (L.unloc x) i y a
    in
    let mallocate_one x y a =
      match x with Pvar x when is_gkvar x -> allocate_one x.gv y a | _ -> a
    in
    let id = get_instr op in 
    let a =
      List.fold_left2 (fun acc ad lv ->
          match ad with
          | ADImplicit v ->
            begin match lv with 
            | Lvar w -> allocate_one w (translate_var (Asmgen.var_of_implicit v)) acc 
            | _ -> assert false 
            end
          | ADExplicit _ -> acc) a id.i_out lvs
    in
    List.fold_left2 (fun acc ad e ->
        match ad with
        | ADImplicit v -> 
          mallocate_one e (translate_var (Asmgen.var_of_implicit v)) acc
        | ADExplicit (_, Some r) -> 
          mallocate_one e (translate_var (X86_variables.var_of_register r)) acc
        | ADExplicit (_, None) -> acc) a id.i_in es

end

type kind = Word | Vector | Unknown of ty

let kind_of_type =
  function
  | Bty (U (U8 | U16 | U32 | U64)) -> Word
  | Bty (U (U128 | U256)) -> Vector
  | ty -> Unknown ty

let allocate_forced_registers translate_var (vars: int Hv.t) (cnf: conflicts)
    (f: 'info func) (a: allocation) : allocation =
  let alloc_from_list loc rs xs q a vs =
    let f x = Hv.find vars x in
    List.fold_left (fun (rs, xs, a) p ->
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
          (rs, xs, allocate_one loc cnf p i d a)
        | exception Not_found -> (rs, xs, a))
      (rs, xs, a)
      vs
    |> fun (_, _, a) -> a
  in
  let alloc_args loc = alloc_from_list loc X64.arguments X64.xmm_arguments identity in
  let alloc_ret loc = alloc_from_list loc X64.ret X64.xmm_ret L.unloc in
  let rec alloc_instr_r loc a =
    function
    | Cfor (_, _, s)
      -> alloc_stmt a s
    | Copn (lvs, _, op, es) -> X64.forced_registers translate_var loc vars cnf lvs op es a
    | Cwhile (_, s1, _, s2)
    | Cif (_, s1, s2)
        -> alloc_stmt (alloc_stmt a s1) s2
    | Cassgn _
      -> a
    | Ccall _ -> a (* TODO *)
  and alloc_instr a { i_loc; i_desc } = alloc_instr_r i_loc a i_desc
  and alloc_stmt a s = List.fold_left alloc_instr a s
  in
  let loc = (f.f_loc, []) in
  let a = alloc_args loc a f.f_args in
  let a = alloc_ret loc a f.f_ret in
  alloc_stmt a f.f_body

let find_vars (vars: int Hv.t) (n: int) : var list =
  Hv.fold (fun v m i -> if n = m then v :: i else i) vars []

(* Returns a variable from [regs] that is allocated to a friend variable of [i]. Defaults to [dflt]. *)
let get_friend_registers (dflt: var) (fr: friend) (a: allocation) (i: int) (regs: var list) : var =
  let fregs =
    get_friend i fr
    |> IntSet.elements
    |> List.map (fun k -> try Some (IntMap.find k a) with Not_found -> None)
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
    (nv: int) (cnf: conflicts)
    (fr: friend)
    (a: allocation) : allocation =
  let a = ref a in
  for i = 0 to nv - 1 do
    if not (IntMap.mem i !a) then (
      let vi = find_vars vars i in
      if vi <> [] then (
      let c = conflicting_registers i cnf !a in
      let has_no_conflict v = not (List.mem (Some v) c) in
      let bank =
        match kind_of_type (type_of_vars vi) with
        | Word -> X64.allocatable
        | Vector -> X64.xmm_allocatable
        | Unknown ty -> hierror "Register allocation: no register bank for type %a" Printer.pp_ty ty
      in
      match List.filter has_no_conflict bank with
      | x :: regs ->
        let y = get_friend_registers x fr !a i regs in
        a := IntMap.add i y !a
      | _ -> hierror "Register allocation: no more register to allocate %a" Printer.(pp_list "; " (pp_var ~debug:true)) vi
    )
    )
  done;
  !a

let subst_of_allocation (vars: int Hv.t)
    (a: allocation) (v: var_i) : expr =
  let m = L.loc v in
  let v = L.unloc v in
  let q x = gkvar (L.mk_loc m x) in
  try
    let i = Hv.find vars v in
    let w = IntMap.find i a in
    Pvar (q w)
  with Not_found -> Pvar (q v)

let reverse_varmap (vars: int Hv.t) : var IntMap.t =
  Hv.fold (fun v i m -> IntMap.add i v m) vars IntMap.empty

let split_live_ranges (f: 'info func) : unit func =
  let f = Ssa.split_live_ranges true f in
  Glob_options.eprint Compiler.Splitting  (Printer.pp_func ~debug:true) f;
  let vars, nv = collect_variables true Sv.empty f in
  let eqc, _tr, _fr = collect_equality_constraints "Split live range" (fun _ _ _ _ _ _ -> ()) vars nv f in
  let vars = normalize_variables vars eqc in
  let a =
    reverse_varmap vars |>
    subst_of_allocation vars
  in Subst.subst_func a f
   |> Ssa.remove_phi_nodes


let reg_alloc translate_var (f: 'info func) : unit func =
  let excluded = Sv.of_list [Prog.rip; X64.rsp] in
  let f = fill_in_missing_names f in
  let f = Ssa.split_live_ranges false f in
  Glob_options.eprint Compiler.Splitting  (Printer.pp_func ~debug:true) f;
  let lf = Liveness.live_fd true f in
  let vars, nv = collect_variables false excluded f in
  let eqc, tr, fr = collect_equality_constraints "Regalloc" x86_equality_constraints vars nv f in
  let vars = normalize_variables vars eqc in
  let conflicts = collect_conflicts vars tr lf in
  let a =
    allocate_forced_registers translate_var vars conflicts f IntMap.empty |>
    greedy_allocation vars nv conflicts fr |>
    subst_of_allocation vars
  in Subst.subst_func a f
   |> Ssa.remove_phi_nodes

let regalloc translate_var stack_needed (f: 'info func) = 
  let f = reg_alloc translate_var f in
  let fv = vars_fc f in
  let allocatable = X64.allocatables in
  let free_regs = Sv.diff allocatable fv in
  let to_save = Sv.inter X64.callee_save fv in
  let to_save, stk = 
    if stack_needed then
      if Sv.is_empty free_regs then
        to_save, None
      else
        let r = 
          let s = Sv.diff free_regs X64.callee_save in
          if Sv.is_empty s then Sv.any free_regs
          else Sv.any s in
        let to_save = Sv.inter X64.callee_save (Sv.add r fv) in
        to_save, Some r
    else 
      to_save, None in
  f, to_save, stk
                  



