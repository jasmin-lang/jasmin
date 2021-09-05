open Utils
open Prog

module S = Syntax
module Pt = Pretyping

type vlevel = string
module Svl : Set.S with type elt = vlevel = Ss
module Mvl : Map.S with type key = vlevel = Ms

type level = 
  | Secret
  | MinLvl of Svl.t
  | Public

let ssecret = "secret" 
let spoly   = "poly" 
let spublic = "public" 


let pp_lvl fmt = function 
  | Secret -> Format.fprintf fmt "@@%s" ssecret 
  | MinLvl s -> 
    let l = Svl.elements s in
    begin match l with
    | [vl] -> Format.fprintf fmt "@@%s=%s" spoly vl
    | _ -> Format.fprintf fmt "@@%s={@[%a@]}" spoly (pp_list ",@ " Format.pp_print_string) l 
    end
  | Public -> Format.fprintf fmt "@@%s" spublic
 
let min l1 l2 = 
  match l1, l2 with
  | Secret, l | l, Secret -> l
  | Public, _ | _, Public -> Public
  | MinLvl l1, MinLvl l2 -> MinLvl (Svl.union l1 l2)

let mins tys = List.fold_left min Secret tys 

let le l1 l2 = 
  match l1, l2 with
  | Public, _ -> true
  | _, Secret -> true 
  | MinLvl l1, MinLvl l2 -> Svl.subset l2 l1
  | _, _      -> false 

(* -----------------------------------------------------------*)
type ty_fun = {
    tyin : level list;
    tyout: level list; (* MinLvl are ensured to be singleton *)
  }

type 'info fenv = {
    ensure_annot : bool;
    env_ty       : ty_fun Hf.t;
    env_def      : 'info func list;
  }

type env = {
    env_v  : level Mv.t;
    env_vl : Svl.t; (* vlevel that need to be secret *)
  }

let empty_env = { 
    env_v = Mv.empty;
    env_vl = Svl.empty;
  }

let min_env env1 env2 = 
  let merge_vlevel _ lvl1 lvl2 = 
    match lvl1, lvl2 with
    | None, _ -> lvl2
    | _, None -> lvl1
    | Some lvl1, Some lvl2 -> Some (min lvl1 lvl2)
  in
  { env_v  = Mv.merge merge_vlevel env1.env_v env2.env_v;
    env_vl = Svl.union env1.env_vl env2.env_vl }

let le_env env1 env2 = 
  let le =
    try 
      let _ = 
        Mv.merge (fun _ lvl1 lvl2 ->
            if le (odfl Secret lvl1) (odfl Secret lvl2) then None
            else raise Not_found) env1.env_v env2.env_v in 
      true
    with Not_found -> false in
  le && Svl.subset env2.env_vl env1.env_vl 

let get env x = 
  try Mv.find (L.unloc x) env.env_v 
  with Not_found -> Secret 

let get_vl env vl = 
  if Svl.mem vl env.env_vl then Secret 
  else MinLvl (Svl.singleton vl)

let norm_ty env = function
  | Secret -> Secret
  | Public -> Public
  | MinLvl l -> Svl.fold (fun lv ty -> min (get_vl env lv) ty) l Secret
   
let update env x ty = 
  let nty = norm_ty env (min ty (get env x)) in
  { env with env_v = Mv.add (L.unloc x) nty env.env_v }

let update_gvar env x ty =
  if is_gkvar x then (* Local variable *) update env x.gv ty
  else (* Global variable *) env 

let remove env x = 
  { env with env_v = Mv.remove (L.unloc x) env.env_v }

let add_secret_vl env s = 
  { env with env_vl = Svl.union s env.env_vl }

(* -----------------------------------------------------------*)

let set_secret_load loc env ty = 
  match norm_ty env ty with
  | Public -> Pt.rs_tyerror ~loc (Pt.string_error "a loaded value is secret, it should be public here") 
  | Secret -> env 
  | MinLvl s -> 
    (* Invariant: all vl in s are polymorph (i.e. not set to Secret or Public) *)
    add_secret_vl env s 
    
(* -----------------------------------------------------------*)

module UE = struct 

  type unienv = (vlevel, level) Hashtbl.t 

  let create n = Hashtbl.create n

  let get (ue:unienv) vl = try Hashtbl.find ue vl with Not_found -> Secret 

  let set (ue:unienv) s ty = 
    assert (Svl.cardinal s = 1);
    let vl = Svl.choose s in
    Hashtbl.add ue vl (min (get ue vl) ty) 

end (* UE *)

let unify_result loc f env oty ety : UE.unienv * env = 
  let ue = UE.create 31 in
  let env = ref env in
  let doit i oty ety =
    match oty, ety with
    | Public, _ -> ()
    | MinLvl s, _ -> UE.set ue s ety
    | Secret, Public -> 
      Pt.rs_tyerror ~loc 
        (Pt.string_error "the %ith return value of %s is secret while it should be public" i f.fn_name)
    | Secret, MinLvl s -> env := add_secret_vl !env s
    | Secret, Secret -> () in
  List.iter2i doit oty ety;
  ue, !env 

let instanciate ue ty = 
  match ty with
  | Secret | Public -> ty
  | MinLvl s -> Svl.fold (fun vl ty -> min (UE.get ue vl) ty) s Secret 
  
let instanciates ue tyin = 
  List.map (instanciate ue) tyin

(* -----------------------------------------------------------*)

(* [ty_expr env e ty] return env' such that env' |- e : ty and env' <= env i.e for all x, env'(x) <= env(x)
   Remark we need the property: env' <= env => env |- e : ty => env' |- e : ty
 *)
let rec ty_expr env (e:expr) ty = 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ -> env

  | Pvar x -> update_gvar env x ty 

  | Pget (_, _, x, i) ->
    let env = update_gvar env x ty in
    ty_expr env i Public

  | Psub (_, _, _, x, i) ->
    (* FIXME: did we realy need Public for i ? yes ...*)
    let env = update_gvar env x ty in
    ty_expr env i Public

  | Pload (_, x, i) -> 
    let env = set_secret_load (L.loc x) env ty in
    let env = update env x Public in
    ty_expr env i Public

  | Papp1(_, e)        -> ty_expr  env e ty
  | Papp2(_, e1, e2)   -> ty_exprs env [e1; e2] ty 
  | PappN(_, es)       -> ty_exprs env es ty 
  | Pif(_, e1, e2, e3) -> ty_exprs env [e1; e2; e3] ty


and ty_exprs env es ty = 
  List.fold_left (fun env e -> ty_expr env e ty) env es 

let ty_exprs1 env es tys =
  List.fold_left2 ty_expr env es tys

(* -----------------------------------------------------------*)
let ty_lval env x = 
  match x with
  | Lnone _ -> env, Secret
  | Lvar x -> remove env x, get env x
  | Lmem(_, x, i) -> 
    let env = update env x Public in
    let env = ty_expr env i Public in 
    env, Secret
  | Laset(_, _, x, i) | Lasub(_, _, _, x, i) ->
    let ty = get env x in
    let env = ty_expr env i Public in
    env, ty
 
let ty_lvals env xs = 
  List.map_fold ty_lval env xs

(* -----------------------------------------------------------*)
module A = Pt.Annot 

let parse_level ~(single:bool) (annot: S.annotations) = 
            
  let on_struct loc (s:S.annotations) = 
    List.iter A.none s;
    let s = List.fold_left (fun s (id, _) -> Svl.add (L.unloc id) s) Svl.empty s in
    if single && Svl.cardinal s <> 1 then 
      Pt.rs_tyerror ~loc 
        (Pt.string_error "= ident or = { ident } is expected after “%s”" spoly);
    MinLvl s in
  let on_id _loc id = MinLvl (Svl.singleton id) in
  let error loc =
    Pt.rs_tyerror ~loc 
      (Pt.string_error "= ident or = { ident, ..., ident } is expected after “%s”" spoly) in
  let poly arg = A.on_attribute ~on_id ~on_struct error arg in
  let filters = 
    [spublic, (fun a -> A.none a; Public);
     ssecret, (fun a -> A.none a; Secret);
     spoly  , poly] in
  A.ensure_uniq filters annot 
    
let get_annot ensure_annot f = 
  let aout = List.map (parse_level ~single:true) f.f_outannot in
  let ain  = List.map (fun x -> parse_level ~single:false x.v_annot) f.f_args in
  let check_defined msg l = 
    if List.exists (fun a -> a = None) l then
      Pt.rs_tyerror ~loc:f.f_loc (Pt.string_error "missing some security annotations on %s" msg) in
  if ensure_annot && f.f_cc = Export then 
    (check_defined "result types" aout; check_defined "function parameters" ain);
  (* fill the missing output type *)
  let aout = 
    let doit i o = 
      match o with 
      | None -> MinLvl (Svl.singleton (string_of_int i))
      | Some lvl -> lvl in
    List.mapi doit aout 
  in
  (* check that the input type only depend on vlevel use in the output type *)
  let known = 
    List.fold_left 
      (fun s lvl -> match lvl with MinLvl s' -> Svl.union s s' | _ -> s) Svl.empty aout in
  let check o = 
    match o with
    | Some (MinLvl s) ->
      let diff = Svl.diff known s in
      if not (Svl.is_empty diff) then
        Pt.rs_tyerror ~loc:f.f_loc 
          (Pt.string_error "variable(s) level %a should be used in return security annotations"
             (pp_list ",@ " Format.pp_print_string) (Svl.elements diff))
    | _ -> () in
  List.iter check ain;
  ain, aout

let check_tyin f ain tyin =
  let doit i o lvl = 
    match o with
    | None -> lvl
    | Some lvl' -> 
      if le lvl' lvl then lvl' 
      else 
        Pt.rs_tyerror ~loc:f.f_loc 
          (Pt.string_error "%ith parameter should have type %a but has declared type %a"
                           i pp_lvl lvl pp_lvl lvl') in
  List.map2i doit ain tyin 
        
      


(* -----------------------------------------------------------*)

(* [ty_instr env i] return env' such that env' |- i : env *)

let rec ty_instr fenv env i = 
  match i.i_desc with
  | Cassgn(x, _, _, e) ->
    let env, ty = ty_lval env x in
    ty_expr env e ty 

  | Copn(xs, _, _, es) ->
    let env, tys = ty_lvals env xs in
    let ty = mins tys in 
    ty_exprs env es ty 

  | Cif(e, c1, c2) ->
    let env1 = ty_cmd fenv env c1 in
    let env2 = ty_cmd fenv env c2 in
    let env = min_env env1 env2 in
    ty_expr env e Public

  | Cfor(x, (_, e1, e2), c) -> 
    let rec loop env = 
      let env1 = ty_cmd fenv env c in
      let env1 = remove env1 x in (* assign public value to x *)
      if le_env env1 env then env 
      else loop (min_env env1 env) in
    let env = loop env in
    ty_exprs env [e1;e2] Public 

  | Cwhile(_, c1, e, c2) -> 
    (* c1; while e do c2; c1 *)
    let rec loop env = 
      let env = ty_expr env e Public in
      let env1 = ty_cmd fenv env c1 in
      let env2 = ty_cmd fenv env1 c2 in
      if le_env env2 env then env1
      else loop (min_env env2 env) in
    loop env

  | Ccall (_, xs, f, es) -> 
    let env, tyout = ty_lvals env xs in
    let env, tyin = instanciate_fun (fst i.i_loc) fenv env f tyout in
    ty_exprs1 env es tyin 

and ty_cmd fenv env c = 
  List.fold_right (fun i env -> ty_instr fenv env i) c env

and instanciate_fun loc fenv env f tyout = 
  let fty = get_fun fenv f in
  let ue, env = unify_result loc f env fty.tyout tyout in
  let tyin = instanciates ue fty.tyin in
  env, tyin

and get_fun fenv f = 
  try Hf.find fenv.env_ty f 
  with Not_found -> 
    let fty = ty_fun fenv f in
    Hf.add fenv.env_ty f fty;
    fty

and ty_fun fenv fn = 
  (* TODO: we should have this defined *)
  let f = List.find (fun f -> F.equal f.f_name fn) fenv.env_def in
  let ain, tyout = get_annot fenv.ensure_annot f in
  let env = ty_exprs1 empty_env (List.map (fun x -> Pvar (gkvar x)) f.f_ret) tyout in
  let env = ty_cmd fenv env f.f_body in
  let tyin = List.map (fun x -> get env (L.mk_loc L._dummy x)) f.f_args in
  let tyin = check_tyin f ain tyin in
  {tyin; tyout}
  

  


    





 



    
    

  

