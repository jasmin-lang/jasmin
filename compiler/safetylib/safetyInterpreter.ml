open Jasmin
open Utils
open Prog
open Apron
open Wsize

open SafetyProf
open SafetyPreanalysis
open SafetyInterfaces
open SafetyUtils
open SafetyExpr
open SafetyVar
open SafetyConstr
open SafetySymEq
open SafetyPointsTo
open SafetyBoolean
open SafetyAbsExpr    
  
(*------------------------------------------------------------*)
(* REM *)
(* Printexc.record_backtrace true *)

let hndl_apr_exc e = match e with
  | Manager.Error exclog as e ->
    Printexc.print_backtrace stderr;
    Format.eprintf "@[<v>Apron error message:@;@[%a@]@;@]@."
      Manager.print_exclog exclog;
    raise e
  | _ as e -> raise e


(*------------------------------------------------------------*)
(* Typing Environment *)

type s_env = { s_glob : Sv.t;
               m_locs : mem_loc list }

let pp_s_env fmt env =
  Format.printf fmt "@[<v>global variables:@;%a@]"
    (pp_list (fun fmt (_,(x,sw)) ->
         Format.fprintf fmt "@[%s: %a@]@,"
           x PrintCommon.pp_ty (Conv.ty_of_cty sw)))
    (Sv.to_list env.s_glob)
    (pp_list (fun fmt i -> Format.fprintf fmt "%d" i))

let add_glob_var env (v : var) =
  { env with s_glob = Sv.add v env.s_glob }

(* let add_glob_gvar env (v : int ggvar) = match v.gs with
 *   | Expr.Slocal -> env
 *   | Expr.Sglob  -> add_glob_var env (L.unloc v.gv) 
 * 
 * let rec add_glob_expr env = function
 *   | Pconst _ | Pbool _ | Parr_init _ -> env
 *   | Pvar x          -> add_glob_gvar env x
 *   | Pget  (_,_,x,e)
 *   | Psub(_,_,_,x,e) -> add_glob_expr (add_glob_gvar env x) e
 *   | Pload(_,x,e)    -> add_glob_expr (add_glob_var env (L.unloc x)) e
 *   | Papp1(_, e)     -> add_glob_expr env e
 *   | Papp2(_,e1,e2)  -> add_glob_expr (add_glob_expr env e1) e2
 *   | PappN (_,es)    -> List.fold_left add_glob_expr env es
 *   | Pif(_,e,e1,e2)  ->
 *     add_glob_expr (add_glob_expr (add_glob_expr env e) e1) e2
 * 
 * let add_glob_exprs env es = List.fold_left add_glob_expr env es
 * 
 * let rec add_glob_lv env = function
 *   | Lnone _      -> env
 *   | Lvar x       -> add_glob_var env (L.unloc x)
 *   | Lmem      (_,x,e)
 *   | Laset   (_,_,x,e) 
 *   | Lasub (_,_,_,x,e)  -> add_glob_expr (add_glob_var env (L.unloc x)) e
 * 
 * let add_glob_lvs env lvs = List.fold_left add_glob_lv env lvs
 * 
 * let rec add_glob_instr env i =
 *   match i.i_desc with
 *   | Cassgn(x, _, _, e) -> add_glob_expr (add_glob_lv env x) e
 *   | Copn(x,_,_,e) -> add_glob_exprs (add_glob_lvs env x) e
 *   | Cif(e,c1,c2) -> add_glob_body (add_glob_body (add_glob_expr env e) c1) c2
 *   | Cfor(x,(_,e1,e2), c) ->
 *     add_glob_body
 *       (add_glob_expr (add_glob_expr (add_glob_var env (L.unloc x)) e1) e2) c
 *   | Cwhile(_,c,e,c') ->
 *     add_glob_body (add_glob_expr (add_glob_body env c') e) c
 *   | Ccall(_,x,_,e) -> add_glob_exprs (add_glob_lvs env x) e
 * 
 * and add_glob_body env c =  List.fold_left add_glob_instr env c *)


(*------------------------------------------------------------*)
(* Safety conditions *)

type arr_slice = { as_arr    : var;
                   as_wsize  : wsize;
                   as_len    : int;
                   as_access : Warray_.arr_access;
                   as_offset : Prog.expr; }
                     
type safe_cond =
  | Initv of var
      
  | Initai  of arr_slice
  | InBound of int * arr_slice
  | InRange of expr * expr * expr (* InRange a b c ≡ c ∈ [a; b] *)

  | Valid       of wsize * var * expr (* allocated memory region *)
  | AlignedPtr  of wsize * var * expr (* aligned pointer *)                   
  | AlignedExpr of wsize * expr       (* aligned expression *)
               
  | NotZero of wsize * expr
  | Termination of bool (* the boolean signals whether this is a severe violation *)

let severe_violation =
  function
  | Termination b -> b
  | _ -> true

let alignment_violation =
  function
  | (AlignedPtr _ | AlignedExpr _) -> true
  | _ -> false

let pp_var = Printer.pp_var ~debug:false
let pp_expr = Printer.pp_expr ~debug:false
let pp_ws fmt ws = Format.fprintf fmt "%i" (int_of_ws ws)

let pp_access fmt = function
  | Warray_.AAdirect -> Format.fprintf fmt "direct"
  | Warray_.AAscale -> Format.fprintf fmt "scale"

let pp_arr_slice fmt slice =
  let pp_len fmt i = 
    if i = 1 then ()
    else Format.fprintf fmt " : %d" i in
  Format.fprintf fmt "%a%s[U%d %a %a]"
    (Printer.pp_var ~debug:false) slice.as_arr
    (if slice.as_access = Warray_.AAdirect then "." else "")
    (int_of_ws slice.as_wsize)
    (Printer.pp_expr ~debug:false) slice.as_offset
    pp_len slice.as_len
  
let pp_safety_cond fmt = function
  | Initv x -> Format.fprintf fmt "is_init %a" pp_var x
  | Initai (slice) ->
    Format.fprintf fmt "is_init %a"
      pp_arr_slice slice
      
  | NotZero(sz,e) -> Format.fprintf fmt "%a <>%a zero" pp_expr e pp_ws sz
  | InRange(lo, hi, e) -> Format.fprintf fmt "%a ∈ [%a; %a]" pp_expr e pp_expr lo pp_expr hi
  | InBound(n,slice)  ->
    Format.fprintf fmt "in_bound: %a (length %i U8)"      
      pp_arr_slice slice n
      
  | Valid (sz, x, e) ->
    Format.fprintf fmt "is_valid %s + %a u%a" x.v_name pp_expr e pp_ws sz
  | AlignedPtr (sz, x, e) ->
    Format.fprintf fmt "aligned pointer %s + %a u%a" x.v_name pp_expr e pp_ws sz
  | AlignedExpr (sz, e) ->
    Format.fprintf fmt "aligned %a u%a" pp_expr e pp_ws sz
            
  | Termination b -> Format.fprintf fmt "termination%s" (if b then "" else " has not been checked")

type violation_loc =
  | InProg of Prog.L.i_loc
  | InReturn of funname

type violation = violation_loc * safe_cond

let pp_violation_loc fmt = function
  | InProg loc -> Format.fprintf fmt "%a" L.pp_iloc loc
  | InReturn fn -> Format.fprintf fmt "%s return" fn.fn_name

let pp_violation fmt (loc,cond) =
  Format.fprintf fmt "%a: %a"
    pp_violation_loc loc
    pp_safety_cond cond

let pp_violations fmt violations =
  if violations = [] then
    Format.fprintf fmt "@[<v>*** No Safety Violation@;@]"
  else
    Format.fprintf fmt "@[<v 2>*** Possible Safety Violation(s):@;@[<v>%a@]@]"
      (pp_list pp_violation) violations

let pp_assumptions fmt =
  function
  | [] -> ()
  | m -> Format.fprintf fmt "@[<v>*** Safety Assumptions:@;@[<v>%a@]@]"
           (pp_list pp_violation) m

let pp_alignment fmt =
  function
  | [] -> ()
  | m -> Format.fprintf fmt "@[<v>*** Possible alignment issue(s):@;@[<v>%a@]@]"
        (pp_list pp_violation) m

let vloc_compare v v' = match v, v' with
  | InReturn fn, InReturn fn' -> Stdlib.compare fn fn'
  | InProg _, InReturn _ -> 1
  | InReturn _, InProg _ -> -1
  | InProg l, InProg l' ->
    Stdlib.Int.compare l.L.uid_loc l'.L.uid_loc

let rec lex f = match f with
  | f_cmp :: f_t ->
    let c = f_cmp () in
    if c = 0
    then lex f_t
    else c
  | _ -> 0

let v_compare (loc,c) (loc',c') =
  lex [(fun () -> vloc_compare loc loc');
       (fun () ->  Stdlib.compare c c')]

let add64 x e = Papp2 (E.Oadd ( E.Op_w U64), Pvar x, e)


(*------------------------------------------------------------*)
(* checks for arrays and sub-arrays *)
    
let in_bound x access ws e len =
  let ux = L.unloc x in
  match ux.v_ty with
  | Arr(ws',n) -> [InBound ( n * size_of_ws ws',
                             { as_arr = ux;
                               as_len = len;
                               as_wsize = ws;
                               as_offset = e;
                               as_access = access; } )]
  (* | Bty (U _)-> []  *)    
  | _ -> assert false

let init_get x access ws e len =
  if x.gs = Expr.Sglob then []
  else
    let ux = L.unloc x.gv in
    match ux.v_ty with
    | Arr _ -> [Initai { as_arr = ux;
                         as_len = len;
                         as_wsize = ws;
                         as_offset = e;
                         as_access = access; }]

    (* | Bty (U _)-> [Initv (L.unloc x)] *)
    | _ -> assert false

let arr_aligned access ws e = match access with
  | Warray_.AAscale  -> []
  | Warray_.AAdirect ->
     begin match e with
     | Papp1 (Oint_of_word U64, e) -> [AlignedExpr (ws, e)]
     | _ -> [AlignedExpr (ws, Papp1 (Oword_of_int U64, e))]
     end

(*------------------------------------------------------------*)
let safe_op2 e2 = function
  | E.Obeq | E.Oand | E.Oor | E.Oadd _ | E.Omul _ | E.Osub _
  | E.Oland _ | E.Olor _ | E.Olxor _
  | E.Olsr _ | E.Olsl _ | E.Oasr _
  | E.Oror _ | E.Orol _
  | E.Oeq _ | E.Oneq _ | E.Olt _ | E.Ole _ | E.Ogt _ | E.Oge _ -> []

  | E.Odiv E.Cmp_int -> []
  | E.Omod Cmp_int  -> []
  | E.Odiv (E.Cmp_w(_, s)) -> [NotZero (s, e2)]
  | E.Omod (E.Cmp_w(_, s)) -> [NotZero (s, e2)]

  | E.Ovadd _ | E.Ovsub _ | E.Ovmul _
  | E.Ovlsr _ | E.Ovlsl _ | E.Ovasr _ -> []

let safe_var x = match (L.unloc x).v_ty with
    | Arr _ -> []
    | _ -> [Initv(L.unloc x)]

let safe_gvar x = match x.gs with
  | Expr.Sglob  -> []
  | Expr.Slocal -> safe_var x.gv

let optional_alignment_check al ws x e acc =
  match al with
  | Memory_model.Unaligned -> acc
  | _ -> AlignedPtr (ws, x, e) :: acc

let rec safe_e_rec safe = function
  | Pconst _ | Pbool _ | Parr_init _ -> safe
  | Pvar x -> safe_gvar x @ safe

  | Pload (al, ws,x,e) ->
     let x = L.unloc x in
    Valid (ws, x, e) ::
    optional_alignment_check al ws x e
    (safe_e_rec safe e)
      
  | Pget (al, access, ws, x, e) ->
    in_bound    x.gv access ws e 1 @
    init_get    x access ws e 1 @
    (if al = Aligned then arr_aligned (* x.gv *) access ws e else []) @
    safe

  | Psub (access, ws, len, x, e) ->
    in_bound    x.gv access ws e len @
    (* Remark that we do not have to check initialization for sub-arrays. *)
    (* Note that the length is scaled with the word-size, so we only
       need to check that the offset w.r.t. the base is aligned. *)
    arr_aligned (* x.gv *) access ws e @
    safe
    
  | Papp1 (_, e) -> safe_e_rec safe e
  | Papp2 (op, e1, e2) -> safe_op2 e2 op @ safe_e_rec (safe_e_rec safe e1) e2
  | PappN (_,es) -> List.fold_left safe_e_rec safe es

  | Pif  (_,e1, e2, e3) ->
    (* We do not check "is_defined e1 && is_defined e2" since
        (safe_e_rec (safe_e_rec safe e1) e2) implies it *)
    safe_e_rec (safe_e_rec (safe_e_rec safe e1) e2) e3

let safe_e = safe_e_rec []

let safe_es = List.fold_left safe_e_rec []

let safe_lval = function
  | Lnone _ | Lvar _ -> []

  | Lmem(al, ws, x, e) ->
    let x = L.unloc x in
    Valid (ws, x, e) ::
    optional_alignment_check al ws x e
    (safe_e_rec [] e)

  | Laset(al, access,ws, x,e) ->
    in_bound x access ws e 1 @
    (if al = Aligned then arr_aligned (* x *) access ws e else []) @
    safe_e_rec [] e

  | Lasub(access,ws,len,x,e) ->
    in_bound x access ws e len @
    arr_aligned (* x  *) access ws e @
    safe_e_rec [] e

let safe_lvals = List.fold_left (fun safe x -> safe_lval x @ safe) []

let pow2 = Z.pow (Z.of_int 2)
let half_modulus ws = pow2 (int_of_ws ws - 1)
let modulus ws = pow2 (int_of_ws ws)

let int_of_word sg ws e =
  match sg with
  | Unsigned -> Papp1 (E.Oint_of_word ws, e)
  | Signed ->
     let m = Pconst (half_modulus ws) in
     Papp2 (E.Osub Op_int,
            Papp1 (E.Oint_of_word ws, Papp2 (E.Oadd (E.Op_w ws), e, Papp1 (E.Oword_of_int ws, m))),
            m)

let int_of_words sg ws hi lo =
  Papp2 (E.Oadd E.Op_int, Papp2 (E.Omul E.Op_int, Pconst (modulus ws), int_of_word sg ws hi), int_of_word Unsigned ws lo)

let split_div sg ws es =
  let hi, lo, d = as_seq3 es in
  int_of_words sg ws hi lo,
  int_of_word sg ws d

let safe_opn safe opn es = 
  let id =
    Sopn.get_instr_desc
      X86_decl.x86_decl.reg_size
      (Arch_extra.asm_opI X86_arch_full.X86_core.asm_e)
      opn
  in
  List.flatten (List.map (fun c ->
      match c with
      | Wsize.X86Division(sz, sg) ->
         let n, d = split_div sg sz es in
         [ NotZero(sz, List.nth es 2)
         ; match sg with
           | Unsigned ->
             InRange(Pconst Z.zero, Papp2 (E.Osub E.Op_int, Papp2 (E.Omul E.Op_int, Pconst (modulus sz), d), Pconst Z.one), n)
          | Signed ->
             InRange (Pconst (Z.neg (half_modulus sz)), Pconst (Z.pred (half_modulus sz)), Papp2 (E.Odiv E.Cmp_int, n, d))
        ]
      | Wsize.InRange(sz, lo, hi, n) ->
         [ InRange(Pconst (Conv.z_of_cz lo), Pconst (Conv.z_of_cz hi), Papp1 (Oint_of_word sz, List.nth es (Conv.int_of_nat n)))]
      | Wsize.AllInit(ws, p, i) -> 
        let e = List.nth es (Conv.int_of_nat i) in
        let y = match e with Pvar y -> y | _ -> assert false in
        List.flatten 
          (List.init (Conv.int_of_pos p) (fun i -> init_get y Warray_.AAscale ws (Pconst (Z.of_int i)) 1)))
     id.i_safe) @ safe

let safe_instr ginstr = match ginstr.i_desc with
  | Cassgn (lv, _, _, e) -> safe_e_rec (safe_lval lv) e
  | Copn (lvs,_,opn,es) -> safe_opn (safe_lvals lvs @ safe_es es) opn es
  | Cif(e, _, _) -> safe_e e
  | Cwhile(_,_, _, _) -> []       (* We check the while condition later. *)
  | Ccall(lvs, _, es) | Csyscall(lvs, _, es) -> safe_lvals lvs @ safe_es es
  | Cfor (_, (_, e1, e2), _) -> safe_es [e1;e2]

let safe_return main_decl =
  List.fold_left (fun acc v -> safe_var v @ acc) [] main_decl.f_ret


(*------------------------------------------------------------*)
let rec add_offsets assigns = match assigns with
  | [] -> []
  | (Mlocal (Avar v)) :: tail when v.v_ty <> Bty (Prog.Bool) ->       
    (Mlocal (Avar v)) :: (MvarOffset v) :: add_offsets tail
  | u :: tail -> u :: add_offsets tail

let rec add_offsets3 assigns = match assigns with
  | [] -> []
  | (ty, Mlocal (Avar v),es) :: tail when v.v_ty <> Bty (Prog.Bool) ->
    (ty, Mlocal (Avar v),es)
    :: (ty, MvarOffset v,es)
    :: add_offsets3 tail
  | u :: tail -> u :: add_offsets3 tail

let fun_locals ~expand_arrays f_decl =
  let locals = Sv.elements (locals f_decl) in
  let vars =
    List.map (mvar_of_scoped_var Expr.Slocal) locals
    |> add_offsets in

  if expand_arrays
  then expand_arr_vars vars
  else vars

let fun_args_no_offset f_decl =
  List.map (mvar_of_scoped_var Expr.Slocal) f_decl.f_args

let fun_args ~expand_arrays f_decl =
  let args = fun_args_no_offset f_decl
             |> add_offsets in
  if expand_arrays
  then expand_arr_vars args
  else args

let in_cp_var v = match v with
  | Mlocal (Avar v) -> Some (MinLocal v)
  | _ -> None

let fun_in_args_no_offset f_decl =
  fun_args_no_offset f_decl |> List.pmap in_cp_var

let get_mem_range env = List.map (fun x -> MmemRange x) env.m_locs

let prog_globals ~expand_arrays env =
  let vars =
    List.map (fun x -> mvar_of_scoped_var Expr.Sglob x)
      (Sv.to_list env.s_glob)
    @ get_mem_range env
    |> add_offsets in

  if expand_arrays
  then expand_arr_vars vars
  else vars

let fun_vars ~expand_arrays f_decl env =
  fun_args ~expand_arrays:expand_arrays f_decl
  @ prog_globals ~expand_arrays:expand_arrays env
  @ fun_locals ~expand_arrays:expand_arrays f_decl


(************************)
(* Abstract Interpreter *)
(************************)

type warnings = (Format.formatter -> unit) list
    
type analyse_res =
  { violations : violation list;
    print_var_interval : (Format.formatter -> mvar -> unit);
    mem_ranges_printer : (Format.formatter -> unit -> unit);
    warnings : warnings; }
                     
module AbsInterpreter (PW : ProgWrap) : sig
  val analyze : Wsize.wsize -> X86_extra.x86_extended_op Sopn.asmOp -> unit -> analyse_res
end = struct

  let source_main_decl = PW.main_source
  let main_decl,prog = PW.main, PW.prog

  let () = Prof.reset_all ()

  (*---------------------------------------------------------------*)
  module AbsDom = AbsBoolNoRel (AbsNumTMake (PW)) (PointsToImpl) (SymExprImpl)

  module AbsExpr = AbsExpr (AbsDom)

  (*---------------------------------------------------------------*)
  type side_effects = mem_loc list

  (* Function abstraction.
     This is a bit messy because the same function abstraction can be used
     with different call-stacks, but the underlying disjunctive domain we 
     use is sensitive to the call-stack. *)
  module FAbs : sig
    type t

    (* [make abs_in abs_out f_effects] *)
    val make    : AbsDom.t -> AbsDom.t -> side_effects -> t

    (* [ apply in fabs = (f_in, f_out, effects) ]:
       Return the abstraction of the initial states that was used, the
       abstract final state, and the side-effects of the function (if the
       abstraction applies in state [in]).
       Remarks: 
       - the final state abstraction [f_out] uses the disjunctions of [in]. *)
    val apply : AbsDom.t -> t -> (AbsDom.t * side_effects) option

    val get_in : t -> AbsDom.t
  end = struct
    (* Sound over-approximation of a function 'f' behavior:
       for any initial state in [it_in], the state after executing the function
       'f' is over-approximated by [it_out], the function's side-effects are at
       most [it_s_effects]. *)
    type t = { fa_in        : AbsDom.t;
               fa_out       : AbsDom.t;
               fa_s_effects : mem_loc list; }

    let make abs_in abs_out f_effects =
      { fa_in        = AbsDom.remove_disj abs_in;
        fa_out       = AbsDom.remove_disj abs_out;
        fa_s_effects = f_effects; }

    let apply abs_in fabs =
      if AbsDom.is_included abs_in (AbsDom.to_shape fabs.fa_in abs_in) 
      then begin
        debug (fun () -> 
            Format.eprintf "Reusing previous analysis of the body ...@.@.");
        Some (AbsDom.to_shape fabs.fa_out abs_in, fabs.fa_s_effects)
      end
      else None

    let get_in t = t.fa_in
  end


  (*---------------------------------------------------------------*)
  type astate = { it : FAbs.t ItMap.t;
                  abs : AbsDom.t; 
                  cstack : funname list;
                  env : s_env;
                  prog : (minfo, X86_extra.x86_extended_op) prog;
                  s_effects : side_effects;
                  violations : violation list }

  let init_state_init_args f_args state =
    List.fold_left (fun state v -> match v with
        | Mlocal at ->
          { state with abs = AbsDom.is_init state.abs at; }
        | _ -> state )
      state f_args

  let init_env : ('info, 'asm) prog -> mem_loc list -> s_env =
    fun (glob_decls, _fun_decls) mem_locs ->
    let env = { s_glob = Sv.empty; m_locs = mem_locs } in
    let env =
      List.fold_left (fun env (x, _) -> add_glob_var env x)
        env glob_decls in

    (* This is not necessary *)
    (* List.fold_left (fun env f_decl ->
     *     { env with s_glob = List.fold_left (fun s_glob ginstr ->
     *           add_glob_instr s_glob ginstr)
     *           env.s_glob f_decl.f_body })
     *   env fun_decls *)
    env

  let init_state : (unit, 'asm) func -> (minfo, 'asm) func -> (minfo, 'asm) prog -> astate * warnings =
    fun main_source main_decl (glob_decls, fun_decls) ->
      let mem_locs = List.map (fun x -> MemLoc x) main_decl.f_args in
      let env = init_env (glob_decls, fun_decls) mem_locs in
      let it = ItMap.empty in

      (* We add the initial variables *)
      let comp_f_args decl =
        let f_args = fun_args ~expand_arrays:true decl in
        (* If f_args is empty, we add a dummy variable to avoid having an
           empty relational abstraction *)
        if f_args = [] then [dummy_mvar] else f_args
      in
      let f_args        = comp_f_args main_decl in
      let source_f_args = comp_f_args main_source in
      
      let f_in_args = List.map in_cp_var f_args
      and m_locs = List.map (fun mloc -> MmemRange mloc ) env.m_locs in

      (* We set the offsets and ranges to zero, and bound the variables using
         their types. E.g. register of type U 64 is in [0;2^64]. *)
      let abs, warns = AbsDom.make (f_args @ m_locs) mem_locs
                |> AbsExpr.set_zeros (f_args @ m_locs)
                (* We use the function location as location of the initial 
                   assignment of the main procedure's arguments. *)
                |> AbsExpr.set_bounds f_args source_f_args in

      (* We apply the global declarations *)
      let abs = AbsExpr.apply_glob glob_decls abs in

      (* We extend the environment to its local variables *)
      let f_vars = (List.pmap (fun x -> x) f_in_args)
                   @ fun_vars ~expand_arrays:true main_decl env in

      let abs = AbsDom.change_environment abs f_vars in

      (* We keep track of the initial values. *)
      let ves = List.fold_left2 (fun ves x oy -> match oy with
          | None -> ves
          | Some y ->
            let sexpr = sexpr_from_simple_expr (Mtexpr.var x) in
            (y, sexpr) :: ves)
          [] f_args f_in_args in
      let abs = AbsDom.assign_sexpr abs None ves in

      let state = { it = it;
                    abs = abs;
                    cstack = [main_decl.f_name];
                    env = env;
                    prog = (glob_decls, fun_decls);
                    s_effects = [];
                    violations = []; } in

      (* We initialize the arguments. Note that for exported function, we 
         know that input arrays are initialized. *)
      ( init_state_init_args (fun_args ~expand_arrays:true main_decl) state,
        warns )


  (*-------------------------------------------------------------------------*)
  (* Checks that all safety conditions hold, except for valid memory access. *)
  let is_safe state = function
    | Initv v -> begin match mvar_of_scoped_var Expr.Slocal v with
        | Mlocal at -> AbsDom.check_init state.abs at
        | _ -> assert false end

    | Initai slice -> 
      let is =
        AbsExpr.abs_sub_arr_range
          state.abs
          (slice.as_arr,Expr.Slocal) slice.as_access
          slice.as_wsize slice.as_len slice.as_offset in
      let is = List.map (function Mlocal at -> at | _ -> assert false) is in
      List.for_all (AbsDom.check_init state.abs) is

    | InBound (n, slice) ->
      (* We check that:
         - offset * ws/8 + len * ws/8   
           is no larger than n if the slice is Scaled 
         - offset        + len * ws/8   
           is no larger than n if the slice is Direct *)
      let scaled_offset = match slice.as_access with
        | Warray_.AAscale ->
          Papp2 (E.Omul E.Op_int,
                 slice.as_offset,
                 Pconst (Z.of_int (size_of_ws slice.as_wsize)))
        | Warray_.AAdirect -> slice.as_offset in

      let bnd = Papp2 (E.Oadd E.Op_int,
                       scaled_offset,
                       Pconst (Z.of_int (size_of_ws slice.as_wsize *
                                         slice.as_len))) in
            
      let simple_check = match AbsExpr.linearize_smpl_iexpr state.abs bnd with
        | None -> false
        | Some lin_e -> 
          let int = AbsDom.bound_texpr state.abs lin_e in
          Scalar.cmp_int int.sup n <= 0 in

      if simple_check then true
      else
        let be = Papp2 (E.Ogt E.Cmp_int, bnd, Pconst (Z.of_int n)) in

        begin match AbsExpr.bexpr_to_btcons be state.abs with
          | None -> false
          | Some c -> 
            AbsDom.is_bottom (AbsDom.meet_btcons state.abs c) end

    | InRange(lo, hi, e) ->
       begin
         let out_of_range =
           Papp2(Oor,
                 Papp2 (Olt E.Cmp_int, e, lo),
                 Papp2 (Olt E.Cmp_int, hi, e)) in
         let s = state.abs in
         match AbsExpr.bexpr_to_btcons out_of_range s with
         | None -> false
         | Some c -> AbsDom.is_bottom (AbsDom.meet_btcons s c) end

    | NotZero (ws,e) ->
      (* We check that e is never 0 *)
      let be = Papp2 (E.Oeq (E.Op_w ws), e, pcast ws (Pconst (Z.of_int 0))) in
      begin match AbsExpr.bexpr_to_btcons be state.abs with
        | None -> false
        | Some c -> 
          AbsDom.is_bottom (AbsDom.meet_btcons state.abs c) end

    (* These are checked elsewhere *)
    | AlignedPtr _ | AlignedExpr _ | Valid _ | Termination _ -> true

  let is_safe state cond =
    let res = is_safe state cond in
    let () = debug (fun () ->
        Format.eprintf "Checked condition: %a@."
          pp_safety_cond cond)
    in
    res

  (* Update abs with the abstract memory range and alignment
     constraint for memory accesses. *)
  let mem_safety_apply (abs, violations, s_effect) = function
    | Valid (ws,x,e) as pv ->
      begin
        match AbsDom.var_points_to abs (mvar_of_scoped_var Expr.Slocal x) with
        | Ptrs pts ->
          if List.length pts = 1 then
            let pt = List.hd pts in

            (* We update the accessed memory range in [abs]. *)
            let x_o = Mtexpr.var (MvarOffset x) in
            let lin_e = oget (AbsExpr.linearize_smpl_wexpr abs e) in
            let c_ws =
              (size_of_ws ws) 
              |> Coeff.s_of_int
              |> Mtexpr.cst in
            let ws_plus_e = Mtexpr.binop Texpr1.Add c_ws lin_e in
            let sexpr = Mtexpr.binop Texpr1.Add x_o ws_plus_e
                        |> sexpr_from_simple_expr in
            let abs = AbsDom.assign_sexpr abs None [MmemRange pt, sexpr] in
            
            ( abs,
              violations,
              if List.mem pt s_effect then s_effect else pt :: s_effect)
          else (abs, pv :: violations, s_effect)
        | TopPtr -> (abs, pv :: violations, s_effect)
      end

    | AlignedPtr (ws,x,e) as pv ->
      begin
        match AbsDom.var_points_to abs (mvar_of_scoped_var Expr.Slocal x) with
        | Ptrs pts ->
          if List.length pts = 1 then
            let pt = List.hd pts in

            (* We update the base alignment constraints. *)
            let abs = AbsDom.base_align abs pt ws in

            (* And we check that the offset is correctly aligned. *)
            let x_o = Mtexpr.var (MvarOffset x) in
            let lin_e = oget (AbsExpr.linearize_smpl_wexpr abs e) in            
            let o_plus_e = Mtexpr.binop Texpr1.Add x_o lin_e in
            let violations =
              if AbsDom.check_align abs o_plus_e ws
              then violations
              else pv :: violations in

            ( abs, violations, s_effect)
          else (abs, pv :: violations, s_effect)
        | TopPtr -> (abs, pv :: violations, s_effect) end

    | AlignedExpr (ws,e) as pv ->
      (* We check that the offset is correctly aligned. *)
      let lin_e = oget (AbsExpr.linearize_smpl_wexpr abs e) in 
      let violations =
        if AbsDom.check_align abs lin_e ws
        then violations
        else pv :: violations
      in
      ( abs, violations, s_effect)

    | _ -> (abs, violations, s_effect)


  (*-------------------------------------------------------------------------*)
  let rec check_safety_rec state unsafe = function
    | [] -> unsafe
    | c :: t ->
      let unsafe = if is_safe state c then unsafe else c :: unsafe in
      check_safety_rec state unsafe t 
        
  let rec mem_safety_rec a = function
    | [] -> a
    | c :: t ->       
      mem_safety_rec (mem_safety_apply a c) t

  let add_violations : astate -> violation list -> astate = fun state ls ->
    if ls <> [] then debug (fun () -> Format.eprintf "%a@." pp_violations ls);
    { state with violations = List.sort_uniq v_compare (ls @ state.violations) }
    
  let rec check_safety state loc conds =
    let vsc = check_safety_rec state [] conds in
    let abs, mvsc, s_effects =
      mem_safety_rec (state.abs, [], state.s_effects) conds in
    
    let state = { state with abs = abs;
                             s_effects = s_effects } in
    
    let unsafe = vsc @ mvsc
                 |> List.map (fun x -> (loc,x)) in
    add_violations state unsafe

      
  (*-------------------------------------------------------------------------*)
  (* Initialize variable or array elements lvalues. *)
  let init_mlv_no_array mlv state = 
    { state with abs = AbsExpr.a_init_mlv_no_array mlv state.abs; }
      

  let offsets_of_mvars l = List.map ty_gvar_of_mvar l
                           |> List.filter (fun x -> x <> None)
                           |> List.map (fun x -> MvarOffset (oget x))

  (* Prepare the caller for a function call. Returns the state with the
     arguments es evaluated in f input variables. *)
  let aeval_f_args f es state =
    let f_decl = get_fun_def state.prog f |> oget in

    let f_args = fun_args_no_offset f_decl
    and exp_in_tys = f_decl.f_tyin in

    let assigns = combine3 exp_in_tys f_args es
                  |> List.map (fun (x,y,z) ->
                      (* The info on the [mlval] does not matter here,
                         since the flow-sensitive packing heuristic we use 
                         only makes sense for fully inlined Jasmin programs *)
                      let y = MLvar ({ i_instr_number = -1 }, y) in
                      (x, y, z)) in

    let abs = List.fold_left (fun abs (in_ty, mvar, e) ->
        AbsExpr.abs_assign abs in_ty mvar e ) 
        state.abs assigns in

    { state with abs = abs }

  (* Remark: handles variable initialization. *)
  let aeval_f_return abs ret_assigns =
    (* TODO: check that [_out_ty] can be ignored here. *)
    List.fold_left (fun abs (_out_ty,rexpr,(ty_lv,mlvo)) ->
        AbsExpr.abs_assign abs ty_lv mlvo rexpr)
      
      abs ret_assigns

  let forget_f_vars f state =
    let f_decl = get_fun_def state.prog f |> oget in
    let f_vs = fun_args ~expand_arrays:true f_decl
               @ fun_locals ~expand_arrays:true f_decl in

    (* We remove f variables *)
    { state with abs = AbsDom.remove_vars state.abs f_vs }

  let forget_stack_vars state = match state.cstack with
    | [_] | [] -> state
    | _ :: cf :: _ -> forget_f_vars cf state


  (* Forget the values of all variables with have been modified by side-effect
     during a function call.
     Remark: we only log side effects on memory locations, hence we always
     forget global variables. *)
  let forget_side_effect state s_effects =
    let vs_globs = prog_globals ~expand_arrays:true state.env
                   |> List.filter (function
                       | MmemRange pt -> List.mem pt s_effects
                       | _ -> true) in
    {state with abs = AbsDom.forget_list state.abs vs_globs }

  (* Forget the values of memory locations that have *not* been modified. *)
  let forget_no_side_effect fstate s_effects =
    let nse_vs = get_mem_range fstate.env
                 |> List.filter (function
                     | MmemRange pt -> not (List.mem pt s_effects)
                     | _ -> true) in
    { fstate with abs = AbsDom.forget_list fstate.abs nse_vs }

  (* Prepare a function call. Returns the state where:
     - The arguments of f have been evaluated.
     - The variables of the caller's caller have been *removed*.
     - s_effects is empty. *)
  let prepare_call state callsite f es =
    debug (fun () -> Format.eprintf "evaluating arguments ...@.");
    let state = aeval_f_args f es state in

    debug (fun () -> Format.eprintf "forgetting variables ...@.");
    let state = forget_stack_vars state in

    let state = { state with 
                  abs = AbsDom.new_cnstr_blck state.abs callsite; } in

    { state with cstack = f :: state.cstack;
                 s_effects = [] }


  (* Profiling *)
  let () = Prof.record "prepare_call"
  let prepare_call abs callsite f es =
    let t = Sys.time () in
    let r = prepare_call abs callsite f es in
    let t' = Sys.time () in
    let sf = "prepare_call_" ^ f.fn_name in
    let () = 
      if Prof.is_recorded sf
      then ()
      else Prof.record sf in
    let () = Prof.call "prepare_call" (t' -. t) in
    let () = Prof.call sf (t' -. t) in
    r

  let get_ret_assgns abs f_decl lvs =
    let f_rets_no_offsets = 
      List.map (fun x ->
          Pvar { gv = x; gs = Expr.Slocal; }
        ) f_decl.f_ret in
    let out_tys = f_decl.f_tyout in
    let mlvs = List.map (fun x ->
        (* The info of [mlv] does not matter here,
           since the flow-sensitive packing heuristic we use 
           only makes sense for fully inlined Jasmin programs *)
        (ty_lval x,
         AbsExpr.mvar_of_lvar abs { i_instr_number = -1 }  x)
      ) lvs in

    combine3 out_tys f_rets_no_offsets mlvs


  let return_call state callsite fstate lvs =
    (* We forget side effects of f in the caller *)
    let state = forget_side_effect state fstate.s_effects in

    (* We pop the top-most block of constraints in the callee *)
    let fabs = AbsDom.pop_cnstr_blck fstate.abs callsite in
    let fstate = { fstate with abs = fabs; } in

    (* We forget variables untouched by f in the callee *)
    let fstate = forget_no_side_effect fstate fstate.s_effects in
    let fname = List.hd fstate.cstack in

    debug(fun () ->
        Format.eprintf "@[<v 0>side effects of %s: @[<hov 2>%a@]@]@."
          fname.fn_name
          (pp_list pp_mvar) (List.map (fun x -> MmemRange x) fstate.s_effects));

    (* We join the alignment constraints, as we want the union of
       previous and new constraints. 
       Also, every variable (of the callee or caller) which was initalized
       remains so. *)   
    let abs = AbsDom.meet
        ~join_align:true
        state.abs fstate.abs in
    let state = { abs = abs;
                  it = fstate.it;
                  env = state.env;
                  prog = state.prog;
                  s_effects = List.unique (state.s_effects @ fstate.s_effects);
                  cstack = state.cstack;
                  violations = List.sort_uniq v_compare
                      (state.violations @ fstate.violations) } in

    debug(fun () -> Format.eprintf "evaluating returned values ...@.");
    (* Finally, we assign the returned values in the corresponding lvalues *)
    let f_decl = get_fun_def fstate.prog fname |> oget in
    let r_assgns = get_ret_assgns state.abs f_decl lvs in      
    
    let state = { state with abs = aeval_f_return state.abs r_assgns } in

    debug(fun () -> 
        Format.eprintf "forgetting %s local variables ...@.@." fname.fn_name);
    (* We forget the variables of f to get a smaller abstract element. *)
    forget_f_vars fname state

  let simpl_obtcons = function
    | Some (BLeaf c) -> Some c
    | _ -> None


  (* -------------------------------------------------------------------- *)
  (* Return flags for the different operations.
     This covers a subset of the x86 flags, as described in the Coq
     semantics (x86_instr_decl.v). *)

  (* Carry flag is true if [w] and [vu] are not equal. *)
  let cf_of_word sz w vu =
    Some (Papp2 (E.Oneq (E.Op_int),
                 Papp1(E.Oint_of_word sz,w),
                 vu))

  (* FIXME *)
  let sf_of_word _sz _w = None
  (* msb w. *)

  (* FIXME *)
  let pf_of_word _sz _w = None
  (* lsb w. *) 

  let zf_of_word sz w =
    Some (Papp2 (E.Oeq (E.Op_w sz),
                 w,
                 pcast sz (Pconst (Z.of_int 0))))

  let rflags_of_aluop sz w vu _vs = 
    let of_f = None               (* FIXME *)
    and cf   = cf_of_word sz w vu 
    and sf   = sf_of_word sz w
    and pf   = pf_of_word sz w
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  (* For the SUB (without carry) and CMP operation, we manually set
     the flags to have simpler and more precise expressions for the 
     carry and zero flags. *)
  let rflags_of_sub sz w1 w2 =
    let sub = Papp2 (E.Osub (E.Op_w sz), w1, w2) in 
    let of_f = None               (* FIXME *)
    and cf   = Some (Papp2 (E.Olt (E.Cmp_w (Unsigned, sz)), w1,w2))
    and sf   = sf_of_word sz sub
    and pf   = pf_of_word sz sub
    and zf   = Some (Papp2 (E.Oeq (E.Op_w sz), w1,w2))
    in
    [of_f;cf;sf;pf;zf]

  let rflags_of_bwop sz w =
    let of_f = Some (Pbool false)
    and cf   = Some (Pbool false)
    and sf   = sf_of_word sz w
    and pf   = pf_of_word sz w
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  let rflags_of_neg sz w _vs = 
    let of_f = None               (* FIXME, same than for rflags_of_aluop *)
    and cf   = None               (* FIXME, must be (w != 0)*)
    and sf   = sf_of_word sz w
    and pf   = pf_of_word sz w
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  let rflags_of_mul (ov : bool option) =
    (*  OF; CF; SF; PF; ZF *)
    [Some ov; Some ov; None; None; None]

  let rflags_unknwon =
    (*  OF; CF; SF; PF; ZF *)
    [None; None; None; None; None]

  let rflags_of_div =
    (*  OF; CF; SF; PF; ZF *)
    rflags_unknwon

  let rflags_of_andn sz w =
    let of_f = Some (Pbool false)
    and cf   = Some (Pbool false)
    and sf   = sf_of_word sz w
    and pf   = None
    and zf   = zf_of_word sz w in
    [of_f;cf;sf;pf;zf]

  (* Remove the carry flag *)
  let nocf = function
    | [of_f;_;sf;pf;zf] -> [of_f;sf;pf;zf]
    | _ -> assert false

  let opn_dflt n = List.init n (fun _ -> None)

  let opn_bin_gen f_flags ws op op_int es =
    let el,er = as_seq2 es in
    let w = Papp2 (op, el, er) in
    let vu = Papp2 (op_int,
                    Papp1(E.Oint_of_word ws,el),
                    Papp1(E.Oint_of_word ws,er)) in
    let vs = () in              (* FIXME *)
    let rflags = f_flags ws w vu vs in
    rflags @ [Some w]

  let opn_bin_alu = opn_bin_gen rflags_of_aluop

  let opn_sub sz es =
    let el,er = as_seq2 es in
    let w = Papp2 (E.Osub (E.Op_w sz), el, er) in
    let rflags = rflags_of_sub sz el er in
    rflags @ [Some w]

  (* -------------------------------------------------------------------- *)
  (* FIXME: redo using the generic flags definition above *)
  let mk_addcarry ws es =
    let el,er,eb = as_seq3 es in    
    let w_no_carry = Papp2 (E.Oadd (E.Op_w ws), el, er) in
    let w_carry = Papp2 (E.Oadd (E.Op_w ws),
                         w_no_carry,
                         pcast ws (Pconst (Z.of_int 1))) in

    let eli = Papp1 (E.Oint_of_word ws, el)    (* (int)el *)
    and eri = Papp1 (E.Oint_of_word ws, er) in (* (int)er *)
    let w_i =
      Papp2 (E.Oadd E.Op_int, eli, eri) in (* (int)el + (int)er *)
    let pow_ws = Pconst (Z.pow (Z.of_int 2) (int_of_ws ws)) in (* 2^ws *)

    (* cf_no_carry is true <=> 2^ws <= el + er      (addition without modulo) *)
    let cf_no_carry = Papp2 (E.Ole E.Cmp_int, pow_ws, w_i ) in
    (* cf_carry    is true <=> 2^ws <= el + er + 1  (addition without modulo) *)
    let cf_carry = Papp2 (E.Ole E.Cmp_int,
                          pow_ws,
                          Papp2 (E.Oadd E.Op_int,
                                 w_i,
                                 Pconst (Z.of_int 1))) in

    match eb with
    | Pbool false ->         (* No carry *)
      [Some cf_no_carry; Some w_no_carry] 

    | Pbool true ->          (* Carry *)
      [Some cf_carry; Some w_carry] 

    | _ ->                   (* General case, potential carry *)
      let _w = Pif (Bty (U ws), eb, w_carry, w_no_carry) in
      let _cf = Pif (Bty Bool, eb, cf_carry, cf_no_carry) in

      (* FIXME: make this optional ?*)
      [None; None]
      (* [Some cf; Some w]  *)

  (* FIXME: idem *)
  let mk_subcarry ws es =
    let el,er,eb = as_seq3 es in    
    let w_no_carry = Papp2 (E.Osub (E.Op_w ws), el, er) in
    let w_carry = Papp2 (E.Osub (E.Op_w ws),
                         w_no_carry,
                         pcast ws (Pconst (Z.of_int 1))) in

    let eli = Papp1 (E.Oint_of_word ws, el)    (* (int)el *)
    and eri = Papp1 (E.Oint_of_word ws, er) in (* (int)er *)

    (* cf_no_carry is true <=> el < er *)
    let cf_no_carry = Papp2 (E.Olt E.Cmp_int, eli, eri ) in
    (* cf_carry    is true <=> el < er + 1  (sub without modulo) *)
    let cf_carry = Papp2 (E.Ole E.Cmp_int,
                          eli,
                          Papp2 (E.Oadd E.Op_int, eri, Pconst (Z.of_int 1))) in

    match eb with
    | Pbool false ->         (* No carry *)
      [Some cf_no_carry; Some w_no_carry] 

    | Pbool true ->          (* Carry *)
      [Some cf_carry; Some w_carry] 

    | _ ->                   (* General case, potential carry *)
      let _w = Pif (Bty (U ws), eb, w_carry, w_no_carry) in
      let _cf = Pif (Bty Bool, eb, cf_carry, cf_no_carry) in

      (* FIXME: make this optional ?*)
      [None; None]
      (* [Some cf; Some w]  *)

  
  (* -------------------------------------------------------------------- *)
  (* Remark: the assignments must be done in the correct order.
     Bitwise operators are ignored for now (result is soundly set to top).
     See x86_instr_decl.v for a desciption of the operators. *)
  let split_opn pd asmOp n opn es = match opn with
    | Sopn.Oasm (Arch_extra.ExtOp X86_extra.Oset0 ws) ->
       let zero = Some (pcast ws (Pconst (Z.of_int 0))) in
       begin match wsize_cmp U64 ws with
       | Lt -> [ zero ]
       | _ -> [ None; None; None; None; None; zero ]
       end

    | Sopn.Opseudo_op (Osubcarry ws) -> mk_subcarry ws es

    | Sopn.Opseudo_op (Oaddcarry ws) -> mk_addcarry ws es

    | Sopn.Opseudo_op (Oswap ty) ->
       let x, y = as_seq2 es in
       [ Some y; Some x]

    | Sopn.Oasm (Arch_extra.ExtOp X86_extra.Ox86MOVZX32) ->
      let e = as_seq1 es in
      (* Cast [e], seen as an U32, to an integer, and then back to an U64. *)
      [Some (Papp1(E.Oword_of_int U64, Papp1(E.Oint_of_word U32, e)))]

    (* Idem than Ox86MOVZX32, but with different sizes. *)      
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.MOVZX (sz_o, sz_i))) ->
      assert (x = None); (* FIXME *)
      assert (int_of_ws sz_o >= int_of_ws sz_i);
      let e = as_seq1 es in
      [Some (Papp1(E.Oword_of_int sz_o, Papp1(E.Oint_of_word sz_i, e)))]

    (* CMP flags are identical to SUB flags. *)
    | Sopn.Oasm (Arch_extra.BaseOp (_, X86_instr_decl.CMP ws)) ->
      (* Input types: ws, ws *)
      let el,er = as_seq2 es in
      rflags_of_sub ws el er

    (* add unsigned / signed *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.ADD ws)) ->
      assert (x = None);
      opn_bin_alu ws (E.Oadd (E.Op_w ws)) (E.Oadd E.Op_int) es

    (* sub unsigned / signed *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.SUB ws)) ->
      assert (x = None);
      opn_sub ws es

    (* mul unsigned *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.MUL ws))

    (* mul signed *)
    (* since, for now, we ignore the upper-bits, 
       we do the same thing than for unsigned multiplication. *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.IMUL ws)) ->
      assert (x = None);
      let el,er = as_seq2 es in
      let w = Papp2 (E.Omul (E.Op_w ws), el, er) in
      (* FIXME: overflow bit to have the precise flags *)
      (* let ov = ?? in
       * let rflags = rflags_of_mul ov in *)
      let rflags = [None; None; None; None; None] in
      (*          high, low   *)
      rflags @ [  None; Some w]

    (* mul signed, no higher-bits *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.IMULr ws))
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.IMULri ws)) ->
      assert (x = None);
      let el,er = as_seq2 es in
      let w = Papp2 (E.Omul (E.Op_w ws), el, er) in
      (* FIXME: overflow bit to have the precise flags *)
      (* let ov = ?? in
       * let rflags = rflags_of_mul ov in *)
      let rflags = [None; None; None; None; None] in
      (*        low   *)
      rflags @ [Some w]

    (* div unsigned *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.DIV ws)) ->
      assert (x = None);
      let n, d = split_div Unsigned ws es in
      let w = Papp1 (E.Oword_of_int ws, Papp2 (E.Odiv E.Cmp_int, n, d)) in
      let rflags = rflags_of_div in
      rflags @ [None; Some w]

    (* div signed *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.IDIV ws)) ->
       assert (x = None);
       let n, d = split_div Signed ws es in
      let w = Papp1 (E.Oword_of_int ws, Papp2 (E.Odiv E.Cmp_int, n, d)) in
      let rflags = rflags_of_div in
      rflags @ [None; Some w]

    (* increment *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.INC ws)) ->
      assert (x = None);
      let e = as_seq1 es in
      let w = Papp2 (E.Oadd (E.Op_w ws), e,
                     Papp1(E.Oword_of_int ws, Pconst (Z.of_int 1))) in
      let vu = Papp2 (E.Oadd E.Op_int,
                      Papp1(E.Oint_of_word ws,e),
                      Pconst (Z.of_int 1)) in
      let vs = () in
      let rflags = nocf (rflags_of_aluop ws w vu vs) in
      rflags @ [Some w]

    (* decrement *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.DEC ws)) ->
      assert (x = None);
      let e = as_seq1 es in
      let w = Papp2 (E.Osub (E.Op_w ws), e,
                     Papp1(E.Oword_of_int ws,Pconst (Z.of_int 1))) in
      let vu = Papp2 (E.Osub E.Op_int,
                      Papp1(E.Oint_of_word ws,e),
                      Pconst (Z.of_int 1)) in
      let vs = () in
      let rflags = nocf (rflags_of_aluop ws w vu vs) in
      rflags @ [Some w]

    (* negation *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.NEG ws)) ->
      assert (x = None);
      let e = as_seq1 es in
      let w = Papp1 (E.Oneg (E.Op_w ws), e) in
      let vs = () in
      let rflags = rflags_of_neg ws w vs in
      rflags @ [Some w]

    (* copy *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.MOV _)) ->
      assert (x = None);
      let e = as_seq1 es in 
      [Some e]

    (* shift, unsigned / left  *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.SHL ws)) ->
      assert (x = None);
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Olsl (E.Op_w ws), e1, e2) in
      rflags_unknwon @ [Some e]

    (* shift, unsigned / right  *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.SHR ws)) ->
      assert (x = None);
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Olsr ws, e1, e2) in
      rflags_unknwon @ [Some e]

    (* shift, signed / right  *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.SAR ws)) ->
      assert (x = None);
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Oasr (E.Op_w ws), e1, e2) in
      rflags_unknwon @ [Some e]

    (* FIXME: adding bit shift with flags *)
    (* 
    | ROR    of wsize    (* rotation / right *)
    | ROL    of wsize    (* rotation / left  *)
    | RCR    of wsize    (* rotation / right with carry *)
    | RCL    of wsize    (* rotation / left  with carry *)
    | SHL    of wsize    (* unsigned / left  *)
    | SHR    of wsize    (* unsigned / right *)
    | SAL    of wsize    (*   signed / left; synonym of SHL *)
    | SAR    of wsize    (*   signed / right *)
    | SHLD   of wsize    (* unsigned (double) / left *)
    | SHRD   of wsize    (* unsigned (double) / right *)
    | MULX    of wsize  (* mul unsigned, doesn't affect arithmetic flags *)
    | ADCX    of wsize  (* add with carry flag, only writes carry flag *)
    | ADOX    of wsize  (* add with overflow flag, only writes overflow flag *)
    *)

    (* conditional copy *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.CMOVcc sz)) ->
      assert (x = None);
      let c,el,er = as_seq3 es in
      let e = Pif (Bty (U sz), c, el, er) in
      [Some e] 

    (* bitwise operators *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.AND ws)) ->
      assert (x = None);
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Oland ws, e1, e2) in
      rflags_unknwon @ [Some e]

    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.OR ws)) ->
      assert (x = None);
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Olor ws, e1, e2) in
      rflags_unknwon @ [Some e]

    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.XOR ws)) ->
      assert (x = None);
      let e1, e2 = as_seq2 es in
      let e = Papp2 (E.Olxor ws, e1, e2) in
      rflags_unknwon @ [Some e]

    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.NOT ws)) ->
      assert (x = None);
      let e1 = as_seq1 es in
      let e = Papp1 (E.Olnot ws, e1) in
      [Some e]

    | Sopn.Oslh op ->
       begin match op with
       | SLHinit -> [ Some (pcast U64 (Pconst (Z.of_int 0))) ]
       | SLHupdate ->
          let b, msf = as_seq2 es in
          let msf = Pif (Bty (U U64), b, msf, pcast U64 (Pconst (Z.of_int (-1)))) in
          [ Some msf ]
       | SLHmove -> let msf = as_seq1 es in [ Some msf ]
       | SLHprotect _ | SLHprotect_ptr _ ->
          let x, _msf = as_seq2 es in
          [ Some x ]
       | SLHprotect_ptr_fail _ -> assert false
       end
    | _ ->
      debug (fun () ->
          Format.eprintf "Warning: unknown opn %a, default to ⊤.@."
            (PrintCommon.pp_opn pd asmOp) opn);
      opn_dflt n


  (* -------------------------------------------------------------------- *)
  (* Ugly handling of flags to build. 
     When adding new flags, update [find_heur]. *)
  type flags_heur = { fh_zf : Mtexpr.t option;
                      fh_cf : Mtexpr.t option; }

  let pp_flags_heur fmt fh =
    Format.fprintf fmt "@[<hv 0>zf: %a;@ cf %a@]"
      (pp_opt Mtexpr.print) (fh.fh_zf)
      (pp_opt Mtexpr.print) (fh.fh_cf)
  
  
  (* [v] is the variable receiving the assignment. *)
  let opn_heur pd asmOp opn v es =
    match opn with 
    (* sub carry *) 
    | Sopn.Opseudo_op (Osubcarry _) ->
      (* FIXME: improve precision by allowing decrement by something else 
         than 1 here. *)
      Some { fh_zf = None;
             fh_cf = Some (Mtexpr.binop Texpr1.Add
                             (Mtexpr.var v)
                             (Mtexpr.cst (Coeff.s_of_int 1))); }
        
    (* decrement *) 
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.DEC _)) ->
      assert (x = None);
      Some { fh_zf = Some (Mtexpr.var v);
             fh_cf = Some (Mtexpr.binop Texpr1.Add
                             (Mtexpr.var v)
                             (Mtexpr.cst (Coeff.s_of_int 1))); }

    (* compare *)
    | Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.CMP _)) ->
      assert (x = None);
      let exception Opn_heur_failed in
      let rec to_mvar = function
        | Pvar x ->
          check_is_word x;
          Mtexpr.var (mvar_of_var x)
        | Papp1 (E.Oword_of_int _, e) -> to_mvar e
        | Papp1 (E.Oint_of_word _, e) -> to_mvar e 
        | _ -> raise Opn_heur_failed in
      let el, er = as_seq2 es in
      begin try
        let el, er = to_mvar el, to_mvar er in
        Some { fh_zf = Some (Mtexpr.binop Texpr1.Sub el er);
               fh_cf = Some (Mtexpr.binop Texpr1.Sub el er); }
        with Opn_heur_failed -> None end
      
    (* (\* sub with borrow *\)
     * | Sopn.Oasm (Arch_extra.BaseOp (X86_instr_decl.SBB _)) *)
    | _ ->
      debug (fun () ->
          Format.eprintf "No heuristic for the return flags of %a@."
            (PrintCommon.pp_opn pd asmOp) opn);
      None

  exception Heuristic_failed

  (* Ugly, just tries to match the string name to a flag name. *)
  let find_heur bv = function
    | None -> raise Heuristic_failed
    | Some heur ->     
      let s = Bvar.var_name bv in
      let s = String.lowercase_ascii s in
      if String.starts_with s "v_cf"
      then Utils.oget ~exn:Heuristic_failed heur.fh_cf
      else if String.starts_with s "v_zf"
      then Utils.oget ~exn:Heuristic_failed heur.fh_zf
      else raise Heuristic_failed

  (* Heuristic for the (candidate) decreasing quantity to prove while
     loop termination. *)  
  let dec_qnty_heuristic pd asmOp loop_body loop_cond =
    let heur_leaf leaf = match Mtcons.get_typ leaf with
      | Lincons0.SUPEQ | Lincons0.SUP -> Mtcons.get_expr leaf

      (* We handle the exit condition "x <> 0" as if it was "x > 0" *)
      | Lincons0.DISEQ -> Mtcons.get_expr leaf

      | _ -> raise Heuristic_failed in

    match loop_cond with
    (* If the exit condition is a constraint (i.e. a leaf boolean term),
       then we try to retrieve the expression inside. *)
    | Some (BLeaf sc) -> heur_leaf sc

    (* For boolean variables, we look whether it is a return flag. If that is
       the case, we look for the instruction that set the flag, and use a
       heuristic depending on the operation. *)
    | Some (BVar bv) ->
      let brev = List.rev loop_body in 
      begin try
          List.find_map (fun ginstr -> match ginstr.i_desc with 
              | Copn(lvs,_,opn,es) ->
                List.find_map_opt (fun lv ->
                    match lv with
                    | Lvar x -> 
                      let x_mv = Mlocal (Avar (L.unloc x)) in
                      if Bvar.make x_mv true = Bvar.positive bv 
                      (* We found the assignment where the flag is set *)
                      then
                        (* Register for which the flags are computed. *)
                        let reg_assgn = match List.last lvs with
                          | Lvar r -> Mlocal (Avar (L.unloc r))
                          | Lnone _ -> raise Heuristic_failed
                          | _ -> assert false in

                        let heur = opn_heur pd asmOp opn reg_assgn es in
                        Some (find_heur bv heur)
                      else None
                    | _ -> None) lvs

              | _ -> None                
            ) brev
        with Not_found -> raise Heuristic_failed
      end

    | _ -> raise Heuristic_failed


  (* -------------------------------------------------------------------- *)
  (* Check that there are no memory stores and loads. *)
  let check_memory_access_aux f_decl = 

    (* vs_for: integer variable from for loops, which will be inlined to
       a constant integer value. *)
    let rec nm_i vs_for i = match i.i_desc with
      | Cassgn (lv, _, _, e)    -> nm_lv vs_for lv && nm_e vs_for e
      | Copn (lvs, _, _, es)    -> nm_lvs vs_for lvs && nm_es vs_for es
      | Csyscall(lvs, _ ,es)    -> nm_lvs vs_for lvs && nm_es vs_for es
      | Cif (e, st, st')        -> 
        nm_e vs_for e && nm_stmt vs_for st && nm_stmt vs_for st'
      | Cfor (i, _, st)         -> nm_stmt (i :: vs_for) st
      | Cwhile (_, st1, e, st2) -> 
        nm_e vs_for e && nm_stmt vs_for st1 && nm_stmt vs_for st2
      | Ccall (lvs, fn, es)  -> 
        let f' = get_fun_def prog fn |> oget in
        nm_lvs vs_for lvs && nm_es vs_for es && nm_fdecl f'

    and nm_fdecl f = nm_stmt [] f.f_body

    and nm_stmt vs_for stmt = List.for_all (nm_i vs_for) stmt

    and nm_e vs_for = function
      | Pconst _ | Pbool _ | Parr_init _ | Pvar _ -> true
      | Pget (_,_,_,_,  e)
      | Psub (_,_,_, _, e) -> know_offset vs_for e && nm_e vs_for e
      | Pload _            -> false
      | Papp1 (_, e)       -> nm_e vs_for e
      | Papp2 (_, e1, e2)  -> nm_es vs_for [e1; e2]
      | PappN (_,es)       -> nm_es vs_for es
      | Pif (_, e, el, er) -> nm_es vs_for [e; el; er]

    and nm_es vs_for es = List.for_all (nm_e vs_for) es

    and nm_lv vs_for = function
      | Lnone _ | Lvar _ -> true
      | Laset (_,_,_,_,e) | Lasub (_,_,_,_,e) -> know_offset vs_for e
      | Lmem _ -> false

    and nm_lvs vs_for lvs = List.for_all (nm_lv vs_for) lvs 

    and know_offset vs_for = function
      | Pconst _ -> true
      | Pvar v ->
        begin
          match v.gs with
          | Expr.Sglob -> true
          | Expr.Slocal -> List.mem v.gv vs_for
        end
        
      | Papp1 (E.Oneg Op_int, e) -> know_offset vs_for e

      | Papp2 ((Osub Op_int | Omul Op_int | Oadd Op_int), e1, e2) ->
        know_offset vs_for e1 && know_offset vs_for e2

      | _ -> false
    in

    nm_fdecl f_decl 


  (* Memoisation *)
  let nm_memo = Hf.create 16
  let check_memory_access f_decl =
    try Hf.find nm_memo f_decl.f_name with Not_found ->
      let res = check_memory_access_aux f_decl in
      Hf.add nm_memo f_decl.f_name res;
      res

  
  (* The function must not use memory loads/stores, array accesses must be 
     fixed, and arrays in arguments must be fully initialized
     (i.e. cells must be initialized). *)
  let check_valid_call_top st f_decl = 
    let cells_init = 
      List.for_all (fun v -> match mvar_of_scoped_var Expr.Slocal v with
          | Mlocal (Aarray _) as mv -> 
            let vs = u8_blast_var ~blast_arrays:true mv in
            List.for_all (function 
                | Mlocal at -> AbsDom.check_init st.abs at
                | _ -> assert false (* initialization of other arguments
                                       should already have been checked
                                       by the analyzer. *)
              ) vs
          | _ -> true
        ) f_decl.f_args in

    cells_init && check_memory_access f_decl


  (* -------------------------------------------------------------------- *)
  let num_instr_evaluated = ref 0

  let print_ginstr pd asmOp ginstr abs_vals =
    Format.eprintf "@[<v>@[<v>%a@]@;*** %d Instr: nb %d, %a %a@;@;@]%!"
      (AbsDom.print ~full:true) abs_vals
      (let a = !num_instr_evaluated in incr num_instr_evaluated; a)
      ginstr.i_info.i_instr_number
      L.pp_sloc ginstr.i_loc.L.base_loc
      (Printer.pp_instr ~debug:false pd asmOp) ginstr

  let print_binop fmt (cpt_instr,abs1,abs2,abs3) =
    Format.fprintf fmt "@[<v 2>Of %d:@;%a@]@;\
                        @[<v 2>And %d:@;%a@]@;\
                        @[<v 2>Yield:@;%a@]"
      cpt_instr
      (AbsDom.print ~full:true) abs1
      (!num_instr_evaluated - 1)
      (AbsDom.print ~full:true) abs2
      (AbsDom.print ~full:true) abs3

  let print_if_join pd asmOp cpt_instr ginstr labs rabs abs_r =
    Format.eprintf "@;@[<v 2>If join %a for Instr:@;%a @;@;%a@]@."
      L.pp_sloc ginstr.i_loc.L.base_loc
      (Printer.pp_instr ~debug:false pd asmOp) ginstr
      (print_binop) (cpt_instr,
                     labs,
                     rabs,
                     abs_r)

  let print_while_join cpt_instr abs abs_o abs_r =
    Format.eprintf "@;@[<v 2>While Join:@;%a@]@."
      (print_binop) (cpt_instr,
                             abs,
                             abs_o,
                             abs_r)

  let print_while_widening cpt_instr abs abs' abs_r =
    Format.eprintf "@;@[<v 2>While Widening:@;%a@]@."
      (print_binop) (cpt_instr,
                             abs,
                             abs',
                             abs_r)

  let print_return ginstr fabs fname =
    Format.eprintf "@[<v>@[<v>%a@]@;Returning %s (called line %a):@;@]%!"
      (AbsDom.print ~full:true) fabs
      fname
      L.pp_iloc ginstr.i_loc

  let cells_of_array x ofs n =
    let x = L.unloc x in
    List.init (Conv.int_of_pos n) (fun i -> SafetyVar.AarraySlice (x, U8, ofs + i))

  let aeval_syscall state sc lvs _es =
    match sc with
    | Syscall_t.RandomBytes n ->
       let cells = match lvs with
         | [ Lnone _ ] -> []
         | [ Lvar x ] -> cells_of_array x 0 n
         | [ Lasub(aa, ws, _len, x, ofs) ] ->
            begin match AbsExpr.aeval_cst_int state.abs ofs with
            | Some j -> cells_of_array x (access_offset aa ws j) n
            | None ->
               debug (fun () ->
                   Format.eprintf "Warning: cannot compute the offset of the destination of #randombytes@.");
               []
            end
         | _ -> assert false
       in
       let abs = List.fold_left AbsDom.is_init state.abs cells in
       { state with abs }

  let log = timestamp ()

  let rec aeval_ginstr pd asmOp : ('ty,minfo,'asm) ginstr -> astate -> astate =
    fun ginstr state ->
      debug (fun () ->
        print_ginstr pd asmOp ginstr state.abs);

      (* We stop if the abstract state is bottom *)
      if AbsDom.is_bottom state.abs
      then state
      else
        (* We check the safety conditions *)
        let conds = safe_instr ginstr in
        let state = check_safety state (InProg ginstr.i_loc) conds in
        aeval_ginstr_aux pd asmOp ginstr state

  and aeval_ginstr_aux pd asmOp : ('ty,minfo,'asm) ginstr -> astate -> astate =
    fun ginstr state ->
    match ginstr.i_desc with 
      | Cassgn (lv,tag,ty1, Pif (ty2, c, el, er))
        when Config.sc_pif_movecc_as_if () ->
        assert (ty1 = ty2);
        let cl = { ginstr with i_desc = Cassgn (lv, tag, ty1, el) } in
        let cr = { ginstr with i_desc = Cassgn (lv, tag, ty2, er) } in
        aeval_if pd asmOp ginstr c [cl] [cr] state

      | Copn (lvs,tag,Sopn.Oasm (Arch_extra.BaseOp (x, X86_instr_decl.CMOVcc sz)),es)
        when Config.sc_pif_movecc_as_if () ->
        assert (x = None);
        let c,el,er = as_seq3 es in
        let lv = as_seq1 lvs in
        let cl = { ginstr with i_desc = Cassgn (lv, tag, Bty (U sz), el) } in
        let cr = { ginstr with i_desc = Cassgn (lv, tag, Bty (U sz), er) } in
        aeval_if pd asmOp ginstr c [cl] [cr] state

      | Cassgn (lv, _, _, Parr_init _) ->
        let abs = AbsExpr.abs_forget_array_contents state.abs ginstr.i_info lv in
        { state with abs }

      | Copn ([ lv ], _, Opseudo_op (Ocopy _), [ e ])
      | Cassgn (lv, _, _, e) ->
        let abs = AbsExpr.abs_assign
            state.abs 
            (ty_lval lv)
            (AbsExpr.mvar_of_lvar state.abs ginstr.i_info lv) 
            e in
        { state with abs = abs; }

      | Copn (lvs,_,opn,es) ->
        (* Remark: the assignments must be done in the correct order. *)
        let assgns = split_opn pd asmOp (List.length lvs) opn es in
        let abs = AbsExpr.abs_assign_opn state.abs ginstr.i_info lvs assgns in

        { state with abs = abs; }

      | Csyscall(lvs, sc, es) ->
         aeval_syscall state sc lvs es

      | Cif(e,c1,c2) ->
        aeval_if pd asmOp ginstr e c1 c2 state

      | Cwhile(_, c1, e, c2) when has_annot "bounded" ginstr ->
         let prog_pt = ginstr.i_loc in
         let body = c2 @ c1 in
         let rec fully_unroll out state =
           let state = check_safety state (InProg prog_pt) (safe_e e) in
           let continue = Option.get (AbsExpr.bexpr_to_btcons e state.abs) in
           let exit = Option.get (flip_btcons continue) in
           let left = AbsDom.meet_btcons state.abs continue in
           let right = AbsDom.meet_btcons state.abs exit in
           let out = AbsDom.join out right in
           if AbsDom.is_bottom left
           then { state with abs = out }
           else { state with abs = left } |> aeval_gstmt pd asmOp body |> fully_unroll out
         in
         let state = { state with abs = AbsDom.new_cnstr_blck state.abs prog_pt } in
         let state = aeval_gstmt pd asmOp c1 state in
         let bot = AbsDom.meet_btcons state.abs (BLeaf (false_tcons1)) in
         let state = fully_unroll bot state in
         { state with abs = AbsDom.pop_cnstr_blck state.abs prog_pt }

      | Cwhile(_,c1, e, c2) ->
        let prog_pt = ginstr.i_loc in

        (* We add a disjunctive constraint block. *)
        let abs = AbsDom.new_cnstr_blck state.abs prog_pt in
        let state = { state with abs = abs; } in

        let cpt = ref 0 in
        let state = aeval_gstmt pd asmOp c1 state in

        (* We now check that e is safe *)
        let conds = safe_e e in
        let state = check_safety state (InProg prog_pt) conds in

        (* Given an abstract state, compute the loop condition expression. *)
        let oec abs = AbsExpr.bexpr_to_btcons e abs in

        (* Candidate decreasing quantity *)
        let ni_e =
          try Some (dec_qnty_heuristic pd asmOp (c2 @ c1) (oec state.abs))
          with Heuristic_failed -> None in
        (* Variable where we store its value before executing the loop body. *)
        let mvar_ni = MNumInv prog_pt in

        (* We check that if the loop does not exit, then ni_e decreased by
             at least one. *)
        let check_ni_dec state = 
          if AbsDom.is_bottom state.abs then state
          else
            match ni_e with
            | None -> (* Here, we cannot prove termination *)
              let violation = (InProg prog_pt, Termination true) in
              add_violations state [violation]

            | Some nie ->
              (* (initial nie) - nie *)
              let e = Mtexpr.(binop Sub (var mvar_ni) nie) in

              (* We assume the loop does not exit, and check whether the 
                 candidate decreasing quantity indeed decreased. *)
              let state_in = match oec state.abs with
                | Some ec -> 
                  { state with 
                    abs = AbsDom.meet_btcons state.abs ec }
                | None -> state in

              debug(fun () -> 
                  Format.eprintf "@[<v 2>Checking the numerical quantity in:@;\
                                  %a@]@."
                    (AbsDom.print ~full:true)
                    state_in.abs);

              let int = AbsDom.bound_texpr state_in.abs e
              and zint = AbsDom.bound_variable state_in.abs mvar_ni
              and test_intz =
                Interval.of_scalar (Scalar.of_int 0) (Scalar.of_infty 1)
              and test_into =
                Interval.of_scalar (Scalar.of_int 1) (Scalar.of_infty 1) in

              debug(fun () ->
                  Format.eprintf "@[<v>@;Candidate decreasing numerical \
                                  quantity:@;\
                                  @[%a@]@;\
                                  Numerical quantity decreasing by:@;\
                                  @[%a@]@;\
                                  Initial numerical quantity in interval:@;\
                                  @[%a@]@;@]"
                    (pp_opt Mtexpr.print) ni_e
                    Interval.print int
                    Interval.print zint;);

              if (Interval.is_leq int test_into) &&
                 (Interval.is_leq zint test_intz) then state
              else
                let violation = (InProg prog_pt, Termination true) in
                add_violations state [violation] in


        (* ⟦body⟧state_i ∪ state *)
        let eval_body state_i state =
          let cpt_instr = !num_instr_evaluated - 1 in

          let state_o = aeval_gstmt pd asmOp (c2 @ c1) state_i in

          (* We check that if the loop does not exit, then ni_e decreased by
             at least one, unless the loop is specially annotated *)
          let state_o =
            if has_annot "no_termination_check" ginstr
            then add_violations state_o [(InProg prog_pt, Termination false)]
            else check_ni_dec state_o in

          (* We forget the variable storing the initial value of the 
             candidate decreasing quantity. *)
          let state_o = { state_o with 
                          abs = AbsDom.forget_list state_o.abs [mvar_ni] } in

          let abs_r = AbsDom.join state.abs state_o.abs in
          debug (fun () ->
              print_while_join cpt_instr state.abs state_o.abs abs_r);
          { state_o with abs = abs_r; } in

        let enter_loop state =
          debug (fun () -> Format.eprintf "Loop %d@;" !cpt);
          cpt := !cpt + 1;
          let state = match oec state.abs with
            | Some ec ->
              debug (fun () -> Format.eprintf "Meet with %a@;" pp_btcons ec);
              { state with abs = AbsDom.meet_btcons state.abs ec }
            | None ->
              debug (fun () -> Format.eprintf "No meet");
              state in

          (* We evaluate a quantity that we try to prove is decreasing. *)
          debug (fun () ->
              Format.eprintf "@[<v>Candidate decreasing numerical quantity:@;\
                              @[%a@]@;@;@]"
                (pp_opt Mtexpr.print) ni_e);

          (* We evaluate the initial value of the candidate decreasing
             quantity. *)
          match ni_e with
            | None -> state
            | Some nie ->
              let sexpr = sexpr_from_simple_expr nie in
              let abs = AbsDom.assign_sexpr state.abs None [mvar_ni, sexpr] in
              { state with abs = abs } in

        (* Unroll one time the loop. *)
        let unroll_once state = eval_body (enter_loop state) state in

        let rec unroll_times i state pre_state =
          if i = 0 then (state,pre_state)
          else unroll_times (i - 1) (unroll_once state) (Some state) in

        let is_stable state pre_state =
          (pre_state <> None) &&
          (AbsDom.is_included state.abs (oget pre_state).abs) in

        let exit_loop state =
          debug (fun () -> Format.eprintf "Exit loop@;");
          match Option.bind (oec state.abs) flip_btcons with
          | Some neg_ec ->
            debug (fun () -> Format.eprintf "Meet with %a@;" pp_btcons neg_ec);
            { state with abs = AbsDom.meet_btcons state.abs neg_ec }
          | None -> state in

        (* Simple heuristic for the widening threshold.
           Basically, if the loop condition is a return flag, we use the 
           candidate decreasing numerical quantity to make the threshold. *)
        let smpl_thrs abs = match simpl_obtcons (oec abs) with
          | Some _ as constr -> constr
          | None -> Option.map (fun e -> Mtcons.make e Lincons1.SUP) ni_e in
            
        let rec stabilize state pre_state =
          if is_stable state pre_state then exit_loop state
          else
            let cpt_instr = !num_instr_evaluated - 1 in
            let state' = unroll_once state in
            let w_abs =
              AbsDom.widening
                (smpl_thrs state.abs) (* this is used as a threshold *)
                state.abs state'.abs in

            debug(fun () ->
                print_while_widening
                  cpt_instr state.abs state'.abs w_abs);
            stabilize { state' with abs = w_abs; } (Some state) in

        let rec stabilize_b state_i pre_state =
          let cpt_i = !num_instr_evaluated - 1 in
          let state = eval_body state_i pre_state in

          if is_stable state (Some pre_state) then exit_loop state
          else
            let state_i' = enter_loop state in

            let w_abs =
              AbsDom.widening
                (smpl_thrs state_i.abs) (* this is used as a threshold *)
                state_i.abs state_i'.abs in
            debug(fun () ->
                print_while_widening cpt_i
                  state_i.abs state_i'.abs w_abs);
            stabilize_b { state_i' with abs = w_abs; } state in

        (* We first unroll the loop k_unroll times. 
           (k_unroll is a parameter of the analysis) *)
        let state, pre_state = unroll_times (Config.sc_k_unroll ()) state None in

        (* We stabilize the abstraction (in finite time) using widening. *)
        let state =
          if Config.sc_widening_out ()
          then stabilize state pre_state
          else stabilize_b (enter_loop state) state in

        (* We pop the disjunctive constraint block *)
        let abs = AbsDom.pop_cnstr_blck state.abs prog_pt in
        { state with abs = abs; } 


      | Ccall(lvs, f, es) ->
        let f_decl = get_fun_def state.prog f |> oget in
        let fn = f_decl.f_name in

        log f_decl (`Call ginstr.i_loc);
        debug (fun () -> Format.eprintf "@[<v>Call %s:@;@]%!" fn.fn_name);
        let callsite = ginstr.i_loc in

        let state_i = prepare_call state callsite f es in

        let fstate = aeval_call pd asmOp f f_decl callsite state_i in

        (* We check the safety conditions of the return *)
        let conds = safe_return f_decl in
        let fstate = check_safety fstate (InReturn fn) conds in

        log f_decl `Ret;
        debug(fun () ->
            print_return ginstr fstate.abs fn.fn_name);

        return_call state callsite fstate lvs

      | Cfor(i, (d,e1,e2), c) ->
        let prog_pt = ginstr.i_loc in
        (match AbsExpr.aeval_cst_int state.abs e1, 
              AbsExpr.aeval_cst_int state.abs e2 with
        | Some z1, Some z2 ->
          if z1 = z2 then state else
            let init_i, final_i, op = match d with
              | UpTo -> assert (z1 < z2); (z1, z2 - 1, fun x -> x + 1)
              | DownTo -> assert (z1 < z2); (z2, z1 + 1, fun x -> x - 1) in

            let rec mk_range i f op =
              if i = f then [i] else i :: mk_range (op i) f op in

            let range = mk_range init_i final_i op
            and mvari = Mlocal (Avar (L.unloc i)) in

            List.fold_left ( fun state ci ->
                (* We add a disjunctive constraint block. *)
                let std = AbsDom.new_cnstr_blck state.abs prog_pt in
                let state = { state with abs = std; } in

                (* We set the integer variable i to ci. *)
                let expr_ci = Mtexpr.cst (Coeff.s_of_int ci)
                                  |> sexpr_from_simple_expr in
                let abs = 
                  AbsDom.assign_sexpr
                    state.abs (Some ginstr.i_info) [mvari, expr_ci] in

                let state =
                  { state with
                    abs = AbsDom.is_init abs (Avar (L.unloc i)); }
                  |> aeval_gstmt pd asmOp c in

                (* We pop the disjunctive constraint block. *)
                let abs = AbsDom.pop_cnstr_blck state.abs prog_pt in
                { state with abs = abs; } 
              ) state range

        | _ ->
          Format.eprintf "@[<v>For loop: \
                          I was expecting a constant integer expression.@;\
                          Expr1:@[%a@]@;Expr2:@[%a@]@;@."
            (Printer.pp_expr ~debug:true) e1
            (Printer.pp_expr ~debug:true) e2;
          assert false
        )

  and aeval_call pd asmOp : funname -> (minfo, 'asm) func -> L.i_loc -> astate -> astate =
    fun f f_decl callsite st_in ->
    let itk = ItFunIn (f,callsite) in

    match aeval_call_strategy callsite f_decl st_in with 
    | Config.Call_Direct -> aeval_body pd asmOp f_decl.f_body st_in

    (* Precond: [check_valid_call_top st_in] must hold:
       the function must not use memory loads/stores, array accesses must be 
       fixed, and arrays in arguments must be fully initialized
       (i.e. cells must be initialized). *)
    | Config.Call_TopByCallSite ->
      (* f has been abstractly evaluated at this callsite before *)
      if ItMap.mem itk st_in.it then 
        let fabs = ItMap.find itk st_in.it in
        match FAbs.apply st_in.abs fabs with
        | Some (f_abs_out, f_effects) ->
          { st_in with abs = f_abs_out;
                       s_effects = f_effects; } 

        | None -> assert false    (* that should not be possible *)

      (* We abstractly evaluate f for the first time *)
      else
        (* Set the abstract state to top (and remove all disjunction).
             Moreover, all arguments of [f_decl] are assumed
             initialized (including array cells). *)
        let st_in_ndisj = 
          let mvars =
            List.map (fun x -> mvar_of_scoped_var Expr.Slocal x) f_decl.f_args
            |> u8_blast_vars ~blast_arrays:true in
          let abs = AbsDom.top_ni st_in.abs in
          let abs = List.fold_left (fun abs mv -> match mv with
              | Mlocal at -> AbsDom.is_init abs at
              | _ -> assert false
            ) abs mvars in
          
          { st_in with abs = abs } 
        in

        let st_out_ndisj = aeval_body pd asmOp f_decl.f_body st_in_ndisj in

        (* We make a new function abstraction for f. Roughly, it is of the form:
           input |--> (output,effects) *)
        let fabs = FAbs.make 
            st_in_ndisj.abs
            st_out_ndisj.abs
            st_out_ndisj.s_effects in

        let st_out_ndisj = { st_out_ndisj with
                             it = ItMap.add itk fabs st_out_ndisj.it } in

        (* It remains to add the disjunctions of the call_site to st_out *)
        { st_out_ndisj with 
          abs = AbsDom.to_shape st_out_ndisj.abs st_in.abs }
        
  and aeval_if pd asmOp ginstr e c1 c2 state =
    let eval_cond state = function
      | Some ec -> AbsDom.meet_btcons state.abs ec
      | None -> state.abs in
    let oec = AbsExpr.bexpr_to_btcons e state.abs in

    let labs, rabs =
      if Config.sc_if_disj () && Option.is_some (simpl_obtcons oec) then
        let ec = simpl_obtcons oec |> oget in
        AbsDom.add_cnstr state.abs ~meet:true ec ginstr.i_loc
      else
        (* FIXME: check that the fact that we do not introduce a 
           disjunction node does not create issues. *)
        let noec = Option.bind oec flip_btcons in
        ( eval_cond state oec, eval_cond state noec ) in

    (* Branches evaluation *)
    let lstate = aeval_gstmt pd asmOp c1 { state with abs = labs; } in

    let cpt_instr = !num_instr_evaluated - 1 in

    (* We abstractly evaluate the right branch
       Be careful the start from lstate, as we need to use the
       updated abstract iterator. *)
    let rstate = aeval_gstmt pd asmOp c2 { lstate with abs = rabs; } in

    let abs_res = AbsDom.join lstate.abs rstate.abs in
    debug (fun () ->
        print_if_join pd asmOp cpt_instr ginstr lstate.abs rstate.abs abs_res);
    { rstate with abs = abs_res; }

  and aeval_body pd asmOp f_body state =
    debug (fun () -> Format.eprintf "Evaluating the body ...@.@.");
    aeval_gstmt pd asmOp f_body state

  and aeval_gstmt pd asmOp : ('ty,'i,'asm) gstmt -> astate -> astate =
    fun gstmt state ->
    let state = List.fold_left (fun state ginstr ->
        aeval_ginstr pd asmOp ginstr state)
        state gstmt in
    let () = if gstmt <> [] then
        debug (fun () ->            
            Format.eprintf "%a%!" (AbsDom.print ~full:true) state.abs) in
    state

  (* Select the call strategy for [f_decl] in [st_in] *)
  and aeval_call_strategy callsite f_decl st_in =
    let strat = match Config.sc_call_policy () with
    | Config.CallDirectAll -> Config.Call_Direct
    (* | CallWideningAll -> Call_WideningByCallSite *)
    | Config.CallTopHeuristic ->
      if check_valid_call_top st_in f_decl
      then Config.Call_TopByCallSite 
      else Config.Call_Direct in

    debug(fun () -> Format.eprintf "Call strategy for %s at %a: %a@." 
             f_decl.f_name.fn_name
             L.pp_iloc callsite
             pp_call_strategy strat);
    strat
  
  (*------------------------------------------------------------------------*)
  let print_mem_ranges state =
    debug(fun () -> Format.eprintf
             "@[<v 0>@;Final offsets full abstract value:@;@[%a@]@]@."
             (AbsDom.print ~full:true)
             state.abs)

  let print_var_interval state fmt mvar =
    let int = AbsDom.bound_variable state.abs mvar in
    Format.fprintf fmt "@[%a: %a@]"
      pp_mvar mvar
      Interval.print int

  let mem_ranges_printer state f_decl fmt () =
    let in_vars = fun_in_args_no_offset f_decl in
    let vars_to_keep = in_vars @ get_mem_range state.env in
    let vars = in_vars @ fun_vars ~expand_arrays:false f_decl state.env in
    let rem_vars = List.fold_left (fun acc v ->
        if (List.mem v vars_to_keep) then acc else v :: acc )
        [] vars in

    let abs_proj = 
      AbsDom.pop_cnstr_blck
        (AbsDom.forget_list state.abs rem_vars) 
        L.i_dummy                (* We use L.i_dummy for the initial block *)
    in

    let sb = !only_rel_print in (* Not very clean *)
    only_rel_print := true;
    Format.fprintf fmt "@[%a@]" (AbsDom.print ~full:true) abs_proj;
    only_rel_print := sb

  let analyze pd asmOp () =
    (* Stats *)
    let exception UserInterupt in

    let t_start = Sys.time () in
    let print_stats () =      
      Format.eprintf "@[<v 0>Duration: %1f@;%a@]"
        (Sys.time () -. t_start)
        Prof.print () in

    try
      (* We print stats before exciting *)
      let hndl = Sys.Signal_handle (fun _ ->
          let () = if SafetyConfig.sc_print_stats () then print_stats () in
          raise UserInterupt) in
      let old_handler = Sys.signal Sys.sigint hndl in

      let state, warnings = init_state source_main_decl main_decl prog in

      (* We abstractly evaluate the main function *)
      let final_st = aeval_gstmt pd asmOp main_decl.f_body state in

      (* We check the safety conditions of the return *)
      let conds = safe_return main_decl in
      let final_st = check_safety final_st (InReturn main_decl.f_name) conds in

      debug(fun () -> Format.eprintf "%a" pp_violations final_st.violations);
      print_mem_ranges final_st;

      let () = if SafetyConfig.sc_print_stats () then print_stats () in
      let () = Sys.set_signal Sys.sigint old_handler in

      { violations = final_st.violations;
        mem_ranges_printer = mem_ranges_printer final_st main_decl;
        print_var_interval = print_var_interval final_st;
        warnings = warnings; }
    with
    | Manager.Error _ as e -> hndl_apr_exc e
end


module type ExportWrap = sig
  (* main function, before any compilation pass *)
  val main_source : (unit, X86_extra.x86_extended_op) Prog.func
      
  val main : (unit, X86_extra.x86_extended_op) Prog.func
  val prog : (unit, X86_extra.x86_extended_op) Prog.prog
end

module AbsAnalyzer (EW : ExportWrap) = struct
  
  module EW = struct
    let main_source = EW.main_source
    
    (* We ensure that all variable names are unique *)
    let main,prog = MkUniq.mk_uniq EW.main EW.prog
  end

  let parse_pt_rel s = match String.split_on_char ';' s with
    | [pts;rels] ->
      let relationals =
        if rels = ""
        then Some []
        else String.split_on_char ',' rels |> Option.some in
      let pointers =
        if pts = ""
        then Some []
        else String.split_on_char ',' pts |> Option.some in
      { relationals = relationals;
        pointers = pointers; }
      
    | [_] ->
      raise (Failure "-safetyparam ill-formed (maybe you forgot a ';' ?)")
    | _ ->
      raise (Failure "-safetyparam ill-formed (too many ';' ?)")

  let parse_pt_rels s = String.split_on_char ':' s |> List.map parse_pt_rel

  let parse_params : string -> (string option * analyzer_param list) list =
    fun s ->
      String.split_on_char '|' s
      |> List.map (fun s -> match String.split_on_char '>' s with
          | [fn;ps] -> (Some fn, parse_pt_rels ps)
          | [ps] -> (None, parse_pt_rels ps)
          | _ -> raise (Failure "-safetyparam ill-formed (too many '>' ?)"))

  let analyze pd asmOp () =
    try     
    let ps_assoc = Option.map_default parse_params
        [ None, [ { relationals = None; pointers = None } ]]
        !Glob_options.safety_param in

    let ps = try List.assoc (Some EW.main.f_name.fn_name) ps_assoc with
      | Not_found -> try List.assoc None ps_assoc with
        | Not_found -> [ { relationals = None; pointers = None } ] in

    let pt_vars =
      List.fold_left (fun acc p -> match p.pointers with
          | None -> acc
          | Some l -> l @ acc) [] ps
      |> List.sort_uniq Stdlib.compare
      |> List.map (fun pt ->
          try List.find (fun x -> x.v_name = pt) EW.main.f_args with
          | Not_found ->
            raise (Failure ("-safetyparam ill-formed (" ^ pt ^ " unknown)"))) in

    let npt = List.filter (fun x -> not (List.mem x pt_vars)) EW.main.f_args
              |> List.map (fun x -> MmemRange (MemLoc x)) in
    
    let l_res = List.map (fun p ->
        let module AbsInt = AbsInterpreter (struct
            include EW
            let param = p
          end) in
        AbsInt.analyze pd asmOp ()) ps in

    match l_res with
    | [] -> raise (Failure "-safetyparam ill-formed (empty list of params)")
    | res :: _->
      let pp_mem_range fmt = match npt with
        | [] -> Format.fprintf fmt ""
        | _ ->          
          Format.eprintf "@[<v 2>Memory ranges:@;%a@]@;"
            (pp_list res.print_var_interval) npt in

      let violations, assumptions = List.partition (fun (_, v) -> severe_violation v) res.violations in
      let alignment, violations =
        if !Glob_options.trust_aligned
        then List.partition (fun (_, v) -> alignment_violation v) violations
        else [], violations in

      let pp_warnings fmt warns =
        if warns <> [] then
          Format.fprintf fmt "@[<v 2>Warnings:@;%a@]@;"
            (pp_list (fun fmt x -> x fmt)) warns in
      
      Format.eprintf "@?@[<v>%a@;\
                      %a@;\
                      %a@;\
                      %a@;\
                      %t\
                      %a@]@."
        pp_warnings res.warnings
        pp_assumptions assumptions
        pp_alignment alignment
        pp_violations violations
        pp_mem_range
        (pp_list (fun fmt res -> res.mem_ranges_printer fmt ())) l_res;

      if violations <> [] then begin
        Format.eprintf "@[<v>Program is not safe!@;@]@.";
        exit(2)
      end;
    with | Manager.Error _ as e -> hndl_apr_exc e
end
