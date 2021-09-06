open Utils
open Prog

module S = Syntax
module Pt = Pretyping

(* ----------------------------------------------------------- *)
(* Variable level                                              *)
module Vl : sig 
  type t
  val compare : t -> t -> int
  val is_flex : t -> bool
  val is_poly : t -> bool
  val mk_uni  : unit -> t
  val mk_poly : string -> t
  val pp      : Format.formatter -> t -> unit
end = struct

  (* vl_flex = true means that the variable can be instanciate with public
     vl_flex = false means that the variable cannot be instanciate *) 
  type t = 
    { vl_name : string
    ; vl_flex : bool }

  let compare = compare 

  let is_flex vl = vl.vl_flex
  let is_poly vl = not vl.vl_flex

  let count = ref 0

  let mk_uni () = 
    let name = string_of_int !count in
    incr count;
    { vl_name = name; vl_flex = true }

  let mk_poly name = { vl_name = name; vl_flex = false }
       
  let pp fmt vl = Format.fprintf fmt "%s" vl.vl_name 
end 

module Svl : Set.S with type elt = Vl.t = Set.Make(Vl)
module Mvl : Map.S with type key = Vl.t = Map.Make(Vl)

type level = 
  | Secret
  | Poly of Svl.t (* The min of the polymorphic variable *)
  | Public

module Lvl : sig
  type t = level

  val poly1 : Vl.t -> t
 
  val min : t -> t -> t

  val mins : t list -> t

  val le : t -> t -> bool

  val pp : Format.formatter -> t -> unit

  val parse : single:bool -> S.annotations -> t option
end = struct

  type t = level 

  let poly1 vl = Poly (Svl.singleton vl)

  let min l1 l2 = 
    match l1, l2 with
    | Public, _ | _, Public -> Public
    | Secret, l | l, Secret -> l
    | Poly l1, Poly l2 -> Poly (Svl.union l1 l2)

  let mins ls = List.fold_left min Secret ls 
              
  let le l1 l2 = 
    match l1, l2 with
    | Public, _ -> true
    | _, Secret -> true
    | Poly l1, Poly l2 -> Svl.subset l1 l2
    | _, _      -> false 

  let ssecret = "secret" 
  let spoly   = "poly" 
  let spublic = "public" 

  let pp fmt = function 
    | Secret -> Format.fprintf fmt "@@%s" ssecret 
    | Poly s -> 
      let l = Svl.elements s in
      begin match l with
      | [vl] -> Format.fprintf fmt "@@%s=%a" spoly Vl.pp vl
      | _ -> Format.fprintf fmt "@@%s={@[%a@]}" spoly (pp_list ",@ " Vl.pp) l 
      end
    | Public -> Format.fprintf fmt "@@%s" spublic

  let parse ~(single:bool) (annot: S.annotations) = 
    let module A = Pt.Annot in
    let on_struct loc (s:S.annotations) = 
      List.iter A.none s;
      let s = List.fold_left (fun s (id, _) -> Svl.add (Vl.mk_poly (L.unloc id)) s) Svl.empty s in
      if single && Svl.cardinal s <> 1 then 
        Pt.rs_tyerror ~loc 
          (Pt.string_error "= ident or = { ident } is expected after “%s”" spoly);
      Poly s in
    let on_id _loc id = poly1 (Vl.mk_poly id) in
    let error loc =
      Pt.rs_tyerror ~loc 
        (Pt.string_error "= ident or = { ident, ..., ident } is expected after “%s”" spoly) in
    let poly arg = A.on_attribute ~on_id ~on_struct error arg in
    let filters = 
      [spublic, (fun a -> A.none a; Public);
       ssecret, (fun a -> A.none a; Secret);
       spoly  , poly] in
    A.ensure_uniq filters annot 

end

(* -----------------------------------------------------------*)
type ty_fun = {
    tyin : Lvl.t list; (* Poly are ensured to be singleton *)
    tyout: Lvl.t list; 
  }

type 'info fenv = {
    ensure_annot : bool;
    env_ty       : ty_fun Hf.t;
    env_def      : 'info func list;
  }

(* -----------------------------------------------------------*)

module Env : sig 
  type env
  val empty : env

  val set  : env -> var -> Lvl.t -> env
  val seti : env -> var_i -> Lvl.t -> env

  val min : env -> env -> env
  val le  : env -> env -> bool

  val get : public:bool -> env -> var_i -> env * Lvl.t 
  val gget : public:bool -> env -> int ggvar -> env * Lvl.t 

  val pp : Format.formatter -> env -> unit 
end = struct

  type env = Lvl.t Mv.t

  let empty = Mv.empty

  let set env x lvl = Mv.add x lvl env
  let seti env x lvl = set env (L.unloc x) lvl

  let get_var ~public env x = 
    let x = L.unloc x in
    try env, Mv.find x env
    with Not_found -> 
      let lvl = 
        if public then Public 
        else Lvl.poly1 (Vl.mk_uni ()) in
      set env x lvl, lvl
            

  let min env1 env2 = 
    let merge_lvl _ lvl1 lvl2 = 
      match lvl1, lvl2 with
      | None, _ -> lvl2
      | _, None -> lvl1
      | Some lvl1, Some lvl2 -> Some (Lvl.min lvl1 lvl2)
    in
    Mv.merge merge_lvl env1 env2

  let le env1 env2 = 
    try 
      let _ = 
        Mv.merge (fun _ lvl1 lvl2 ->
            let lvl1 = (odfl Secret lvl1) in
            let lvl2 = (odfl Secret lvl2) in
            if Lvl.le lvl1 lvl2 then None
            else raise Not_found) env1 env2 in 
      true
    with Not_found -> false 

  let set_uni_public env s =
    Mv.map (fun lvl ->
        match lvl with
        | Public | Secret -> lvl
        | Poly s' -> 
          if Svl.is_empty (Svl.inter s s') then lvl
          else Public) env

  let get ~(public:bool) env x = 
    let loc = L.loc x in
    let env, lvl = get_var ~public env x in
    if public then
      match lvl with
      | Secret -> 
        Pt.rs_tyerror ~loc 
          (Pt.string_error "%a has type secret it needs to be public" 
             (Printer.pp_var ~debug:false) (L.unloc x))
      | Public -> env, Public
      | Poly s ->
        let poly = Svl.filter Vl.is_poly s in
        if Svl.is_empty poly then set_uni_public env s, Public
        else
          Pt.rs_tyerror ~loc 
            (Pt.string_error 
               "variable %a has type %a, it should be public. Replace the polymorphic variable(s) %a by public"
               (Printer.pp_var ~debug:false) (L.unloc x)
               Lvl.pp lvl
               (pp_list ",@ " Vl.pp) (Svl.elements poly))
    else env, lvl

  let gget ~(public:bool) env x = 
    if is_gkvar x then get ~public env x.gv
    else env, Public  

  let pp fmt env = 
    let pp_ty fmt (x, lvl) = 
      Format.fprintf fmt "@[%a : %a@]" (Printer.pp_var ~debug:false) x Lvl.pp lvl in
    Format.fprintf fmt "@[%a@]" (pp_list ";@ " pp_ty) (Mv.bindings env)

end
    
(* -----------------------------------------------------------*)

module UE = struct 

  type unienv = (Vl.t, level) Hashtbl.t 

  let create n = Hashtbl.create n

  let get (ue:unienv) vl = try Hashtbl.find ue vl with Not_found -> Secret 

  let set (ue:unienv) s ty = 
    assert (Svl.cardinal s = 1);
    let vl = Svl.choose s in
    Hashtbl.add ue vl (Lvl.min (get ue vl) ty) 

end (* UE *)

let unify uty ety : UE.unienv = 
  let ue = UE.create 31 in
  let doit uty ety =
    match uty, ety with
    | Public, Public -> ()
    | Poly s, _      -> UE.set ue s ety
    | Secret, _      -> ()
    | _, _           -> assert false in
  List.iter2 doit uty ety;
  ue

let instanciate ue ty = 
  match ty with
  | Secret | Public -> ty
  | Poly s -> Svl.fold (fun vl lvl -> Lvl.min (UE.get ue vl) lvl) s Public
  
let instanciates ue tyin = 
  List.map (instanciate ue) tyin
 
let instanciate_fty fty lvls  = 
  let ue = unify fty.tyin lvls in
  let tyout = instanciates ue fty.tyout in
  tyout
 
(* -----------------------------------------------------------*)

(* [ty_expr ~public env e] return [env', lvl] such that [env' |- e : lvl] 
   and [env' <= env] i.e for all x, [env'(x) <= env(x)].
   Furthermore [public => lvl = Public.
   Remark we need the property: [env' <= env => env |- e : lvl => env' |- e : lvl]
 *)

let rec ty_expr ~(public:bool) env (e:expr) = 
  match e with
  | Pconst _ | Pbool _  -> env, Public

  | Parr_init _ -> env, Lvl.poly1 (Vl.mk_uni ())

  | Pvar x -> Env.gget ~public env x

  | Pget (_, _, x, i) | Psub (_, _, _, x, i) ->
    let env, ty = Env.gget ~public env x in
    let env, _  = ty_expr ~public:true env i in
    env, ty

  | Pload (_, x, i) -> 
    let env, _ = Env.get ~public:true env x in
    let env, _ = ty_expr ~public:true env i in
    env, Secret 

  | Papp1(_, e)        -> ty_expr ~public env e 
  | Papp2(_, e1, e2)   -> ty_exprs_min ~public env [e1; e2]  
  | PappN(_, es)       -> ty_exprs_min ~public env es 
  | Pif(_, e1, e2, e3) -> ty_exprs_min ~public env [e1; e2; e3] 

and ty_exprs ~public env es = 
  List.map_fold (ty_expr ~public) env es 

and ty_exprs_min ~public env es =
  let env, lvls = ty_exprs ~public env es in
  env, Lvl.mins lvls

(* -----------------------------------------------------------*)
let ty_lval env x lvl = 
  match x with
  | Lnone _ -> env
  | Lvar x -> Env.seti env x lvl 
  | Lmem(_, x, i) ->
    let env, _ = Env.get ~public:true env x in
    let env, _ = ty_expr ~public:true env i in
    env
  | Laset(_, _, x, i) | Lasub(_, _, _, x, i) ->
    (* FIXME: is it really correct ? *)
    let env, xlvl = Env.get ~public:(lvl = Public) env x in
    let env, _    = ty_expr ~public:true env i in
    Env.seti env x (Lvl.min xlvl lvl)
 
let ty_lvals env xs lvls =
  List.fold_left2 ty_lval env xs lvls

let ty_lvals1 env xs lvl = 
  List.fold_left (fun env x -> ty_lval env x lvl) env xs 

(* -----------------------------------------------------------*)
    
let get_annot ensure_annot f = 
  let ain  = List.map (fun x -> Lvl.parse ~single:true x.v_annot) f.f_args in
  let aout = List.map (Lvl.parse ~single:false) f.f_outannot in

  let check_defined msg l = 
    if List.exists (fun a -> a = None) l then
      Pt.rs_tyerror ~loc:f.f_loc 
        (Pt.string_error 
           "export functions should be fully annotated, missing some security annotations on %s.@ User option “-infer” to infer them." 
           msg) in
  if ensure_annot && f.f_cc = Export then 
    (check_defined "result types" aout; check_defined "function parameters" ain);
  (* fill the missing input type *)
  let ain = 
    let doit o = 
      match o with 
      | None -> Lvl.poly1 (Vl.mk_uni ())
      | Some lvl -> lvl in
    List.map doit ain 
  in
  (* check that the output type only depend on variable level declared in the input type *)
  let known = 
    List.fold_left 
      (fun s lvl -> match lvl with Poly s' -> Svl.union s s' | _ -> s) Svl.empty ain in
  let check o = 
    match o with
    | Some (Poly s) ->
      let diff = Svl.diff known s in
      if not (Svl.is_empty diff) then
        Pt.rs_tyerror ~loc:f.f_loc 
          (Pt.string_error "variable(s) level %a should be used in the input security annotations"
             (pp_list ",@ " Vl.pp) (Svl.elements diff))
    | _ -> () in
  List.iter check aout;
  ain, aout
    
(* -----------------------------------------------------------*)

(* [ty_instr env i] return env' such that env |- i : env' *)

let rec ty_instr fenv env i = 
  let env1 = 
  match i.i_desc with
  | Cassgn(x, _, _, e) ->
    let env, lvl = ty_expr ~public:false env e in
    ty_lval env x lvl

  | Copn(xs, _, _, es) ->
    let env, lvl = ty_exprs_min ~public:false env es in
    ty_lvals1 env xs lvl 

  | Cif(e, c1, c2) ->
    let env, _ = ty_expr ~public:true env e in
    let env1 = ty_cmd fenv env c1 in
    let env2 = ty_cmd fenv env c2 in
    Env.min env1 env2

  | Cfor(x, (_, e1, e2), c) -> 
    let env, _ = ty_exprs ~public:true env [e1; e2] in
    let rec loop env = 
      let env1 = Env.seti env x Public in
      let env1 = ty_cmd fenv env1 c in
      if Env.le env1 env then env (* G <= G' G' |- c : G''   G |- c : G'' *)
      else loop (Env.min env1 env) in
    loop env 

  | Cwhile(_, c1, e, c2) -> 
    (* c1; while e do c2; c1 *)
    (* G |- c1 : G'   G' |- e : public   G' |- c2 : G
       -----------------------------------------------
       G |- while c1 e c2 : G'
     *)

    let rec loop env = 
      let env1 = ty_cmd fenv env c1 in
      let env1,_ = ty_expr ~public:true env1 e in
      let env2 = ty_cmd fenv env1 c2 in
      if Env.le env2 env then env1 
      else loop (Env.min env1 env) in
    loop env

  | Ccall (_, xs, f, es) -> 
    let fty = get_fun fenv f in
    (* Check the arguments *)
    let do_e env e lvl = ty_expr ~public:(lvl=Public) env e in
    let env, elvls = List.map_fold2 do_e env es fty.tyin in
    let olvls = instanciate_fty fty elvls in
    ty_lvals env xs olvls 
  in
  Format.eprintf "%a: @[<v>before %a@ after %a@]@." L.pp_loc (fst i.i_loc) Env.pp env Env.pp env1;
  env1

and ty_cmd fenv env c = 
  List.fold_left (fun env i -> ty_instr fenv env i) env c 

and get_fun fenv f = 
  try Hf.find fenv.env_ty f 
  with Not_found -> 
    let fty = ty_fun fenv f in
    Hf.add fenv.env_ty f fty;
    fty

and ty_fun fenv fn = 
  (* TODO: we should have this defined *)
  let f = List.find (fun f -> F.equal f.f_name fn) fenv.env_def in
  let tyin, aout = get_annot fenv.ensure_annot f in
  let env = List.fold_left2 Env.set Env.empty f.f_args tyin in
  let env = ty_cmd fenv env f.f_body in
  let do_r env x aout =
    let public = aout = Some Public in
    let env, lvl = Env.get ~public env x in
    let lvl = 
      match aout with
      | None -> lvl
      | Some alvl ->
        if Env.lvl_le env lvl alvl then alvl 
        else 
          Pt.rs_tyerror ~loc:(L.loc x) 
            (Pt.string_error "the variable %a has type %a instead of %a"
              (Printer.pp_var ~debug:false) (L.unloc x)
              Lvl.pp lvl Lvl.pp alvl) in
    env, lvl in
  let _, tyout = List.map_fold2 do_r env f.f_ret aout in
  let fty = {tyin; tyout} in
  let pp_arg fmt (x, lvl) = 
    Format.fprintf fmt "%a %a"
      Lvl.pp lvl (Printer.pp_var ~debug:false) x in
  Format.eprintf "security type for @[%s(@[%a@]) :@ @[%a@]@]@."
    f.f_name.fn_name
    (pp_list ",@ " pp_arg) (List.combine f.f_args tyin)
    (pp_list ",@ " Lvl.pp) tyout;
  fty


let ty_prog ~infer (prog:'info prog) fl =
  let prog = snd prog in
  let fenv = 
    { ensure_annot = not infer
    ; env_ty       = Hf.create 101
    ; env_def      = prog } in
  let fl = 
    if fl = [] then 
      List.rev_map (fun f -> f.f_name) prog 
    else 
      let get fn = 
        try (List.find (fun f -> f.f_name.fn_name = fn) prog).f_name 
        with Not_found -> raise (hierror "constant type checker: unknown function %s" fn) in
      List.map get fl in
  List.iter (fun fn -> ignore (get_fun fenv fn)) fl


  
  
    





 



    
    

  

