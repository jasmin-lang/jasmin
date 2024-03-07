open Utils
open Prog

module A = Annotations
module S = Syntax
module Pt = Pretyping

(* ----------------------------------------------------------- *)
(* Variable level                                              *)
module Vl : sig
  type t
  val compare : t -> t -> int
  val is_poly : t -> bool
  val mk_uni  : string -> t
  val mk_poly : string -> t
  val pp      : Format.formatter -> t -> unit
end = struct

  (* vl_flex = true means that the variable can be instanciate with public
     vl_flex = false means that the variable cannot be instanciate *)
  type t =
    { vl_name : string
    ; vl_flex : bool }

  let compare vl1 vl2 = String.compare vl1.vl_name vl2.vl_name

  let is_poly vl = not vl.vl_flex


  let mk_uni  name = { vl_name = name; vl_flex = true }
  let mk_poly name = { vl_name = name; vl_flex = false }

  let pp fmt vl = Format.fprintf fmt "%s" vl.vl_name
end

module Svl : Set.S with type elt = Vl.t = Set.Make(Vl)

type level =
  | Secret
  | Poly of Svl.t (* The min of the polymorphic variable *)
  | Public

(* [lvl_kind] indicate if the level of a program variable is allowed to varie
   at different point of the program *)
type lvl_kind =
  | Strict
  | Flexible

let string_of_lvl_kind = function
  | Strict -> "strict"
  | Flexible -> "flexible"

module Lvl : sig

  type t = level

  val sstrict   : string
  val sflexible : string

  val poly1 : Vl.t -> t

  val max : t -> t -> t

  val maxs : t list -> t

  val equal : t -> t -> bool

  val le : t -> t -> bool

  val pp : Format.formatter -> t -> unit

  val parse : single:bool -> kind_allowed:bool -> A.annotations ->
              lvl_kind option * t option

end = struct

  type t = level

  let poly1 vl = Poly (Svl.singleton vl)

  let max l1 l2 =
    match l1, l2 with
    | Secret, _ | _, Secret -> Secret
    | Public, l | l, Public -> l
    | Poly l1, Poly l2 -> Poly (Svl.union l1 l2)

  let maxs ls = List.fold_left max Public ls

  let equal l1 l2 =
    match l1, l2 with
    | Public, Public -> true
    | Secret, Secret -> true
    | Poly l1, Poly l2 -> Svl.equal l1 l2
    | _, _ -> false

  let le l1 l2 =
    match l1, l2 with
    | Public, _ -> true
    | _, Secret -> true
    | Poly l1, Poly l2 -> Svl.subset l1 l2
    | _, _      -> false

  let ssecret = "secret"
  let spoly   = "poly"
  let spublic = "public"

  let sflexible = "flex"
  let sstrict   = "strict"

  let pp fmt = function
    | Secret -> Format.fprintf fmt "#%s" ssecret
    | Poly s ->
      let l = Svl.elements s in
      begin match l with
      | [vl] -> Format.fprintf fmt "#%s=%a" spoly Vl.pp vl
      | _ -> Format.fprintf fmt "#%s={@[%a@]}" spoly (pp_list ",@ " Vl.pp) l
      end
    | Public -> Format.fprintf fmt "#%s" spublic

  let parse ~(single:bool) ~(kind_allowed:bool) (annot: A.annotations) =
    let module A = Annot in
    let on_struct loc _nid s =
      List.iter A.none s;
      let s = List.fold_left (fun s (id, _) -> Svl.add (Vl.mk_poly (L.unloc id)) s) Svl.empty s in
      if single && Svl.cardinal s <> 1 then
        A.error ~loc
          "= ident or = { ident } is expected after “%s”" spoly;
      Poly s in
    let on_id _loc _nid id = poly1 (Vl.mk_poly id) in
    let error loc _nid =
      A.error ~loc
        "= ident or = { ident, ..., ident } is expected after “%s”" spoly in
    let poly arg = A.on_attribute ~on_id ~on_struct error arg in
    let filters =
      [spublic, (fun a -> A.none a; Public);
       ssecret, (fun a -> A.none a; Secret);
       "transient", (fun a -> A.none a; Public);
       spoly  , poly] in
    let lvl = A.ensure_uniq filters annot in
    let kind =
      let check_allowed (id,_) =
        if not kind_allowed then
          A.error ~loc:(L.loc id)
            "%s not allowed here" (L.unloc id);
        if lvl = None then
          A.error ~loc:(L.loc id)
            "type level should be provided"
      in
      let filters =
        [ sflexible, (fun a -> check_allowed a; A.none a; Flexible);
          sstrict,   (fun a -> check_allowed a; A.none a; Strict)] in
      A.ensure_uniq filters annot in
    kind, lvl

end

(* -----------------------------------------------------------*)

type signature = {
    tyin : (lvl_kind * Lvl.t) list; (* Poly are ensured to be singleton *)
    tyout: Lvl.t list;
  }

type ('info, 'asm) fenv = {
    ensure_annot : bool;
    env_ty       : signature Hf.t;
    env_def      : ('info, 'asm) func list;
  }

(* -----------------------------------------------------------*)
let pp_kind fmt k =
  if k = Flexible then Format.fprintf fmt "#%s " (string_of_lvl_kind k)

let pp_arg fmt (x, (k, lvl)) =
  Format.fprintf fmt "%a%a %a" pp_kind k  Lvl.pp lvl (Printer.pp_var ~debug:false) x

let pp_signature prog fmt (fn, { tyin ; tyout }) =
  Format.fprintf fmt "@[<h>@[%s(@[%a@]) ->@ @[%a@]@]@]@."
    fn.fn_name
    (pp_list ",@ " pp_arg) (List.combine (List.find (fun f -> F.equal f.f_name fn) (snd prog)).f_args tyin)
    (pp_list ",@ " Lvl.pp) tyout

(* -----------------------------------------------------------*)
exception CtTypeError of Location.t * (Format.formatter -> unit)

let error ~loc =
  Format.kdprintf (fun msg ->
      raise (CtTypeError (loc, msg)))

(* -----------------------------------------------------------*)

module Env : sig

  type env
  val empty : env
  val norm_lvl : env -> Lvl.t -> Lvl.t

  val set  : env -> var_i -> Lvl.t -> env
  val add : env -> var -> (lvl_kind * Lvl.t) -> env

  val max : env -> env -> env
  val le  : env -> env -> bool

  val get : public:bool -> env -> var_i -> env * Lvl.t
  val gget : public:bool -> env -> int ggvar -> env * Lvl.t

  val pp : Format.formatter -> env -> unit
end = struct

  type env =
    { env_v  : (lvl_kind * Lvl.t) Mv.t
    ; env_vl : Svl.t (* vlevel that need to be public *) }

  let empty =
    { env_v  = Mv.empty
    ; env_vl = Svl.empty }

  let norm_lvl_aux env_vl = function
    | Secret -> Secret
    | Public -> Public
    | Poly s ->
      let s = Svl.diff s env_vl in
      if Svl.is_empty s then Public else Poly s

  let norm_lvl env lvl = norm_lvl_aux env.env_vl lvl

  let get_var env x =
    try
      let k, lvl = Mv.find (L.unloc x) env.env_v in
      k, norm_lvl env lvl
    with Not_found -> Flexible, Public

  let max env1 env2 =
    let env_vl = Svl.union env1.env_vl env2.env_vl in
    let merge_lvl _ klvl1 klvl2 =
      match klvl1, klvl2 with
      | None, _ -> klvl2
      | _, None -> klvl1
      | Some (k1, lvl1), Some (k2, lvl2) ->
        assert (k1 = k2 && (k1 = Flexible || Lvl.equal lvl1 lvl2));
        Some (k1, Lvl.max (norm_lvl_aux env_vl lvl1) (norm_lvl_aux env_vl lvl2))
    in
    { env_v  = Mv.merge merge_lvl env1.env_v env2.env_v;
      env_vl}

  let le env1 env2 =
    try
      let _ =
        Mv.merge (fun _ (klvl1) (klvl2) ->
            let k1, lvl1 = Option.default (Flexible, Public) klvl1 in
            let k2, lvl2 = Option.default (Flexible, Public) klvl2 in
            let lvl1 = norm_lvl env1 lvl1 in
            let lvl2 = norm_lvl env2 lvl2 in
            assert (k1 = k2 && (k1 = Flexible || Lvl.equal lvl1 lvl2));
            if Lvl.le lvl1 lvl2 then None
            else raise Not_found) env1.env_v env2.env_v in
      Svl.subset env1.env_vl env2.env_vl
    with Not_found -> false

  let set env x lvl =
    let lvl = norm_lvl env lvl in
    let k, lvlx = get_var env x in
    if k = Strict then
      if not (Lvl.equal lvl lvlx) then
        error ~loc:(L.loc x)
             "%a has type #%s %a it cannot receive a value of type %a"
             (Printer.pp_var ~debug:false) (L.unloc x)
             Lvl.sstrict Lvl.pp lvlx
             Lvl.pp lvl
      else env
    else { env with env_v = Mv.add (L.unloc x) (Flexible, lvl) env.env_v }

  let add env x (k, lvl) =
    assert (not (Mv.mem x env.env_v));
    { env with env_v = Mv.add x (k, lvl) env.env_v }

  let get ~(public:bool) env x =
    let loc = L.loc x in
    let _, lvl = get_var env x in
    if public then
      match lvl with
      | Secret ->
        error ~loc
          "%a has type secret it needs to be public"
             (Printer.pp_var ~debug:false) (L.unloc x)
      | Public -> env, Public
      | Poly s ->
        let poly = Svl.filter Vl.is_poly s in
        if Svl.is_empty poly then { env with env_vl = Svl.union s env.env_vl }, Public
        else
          error ~loc
               "variable %a has type %a, it should be public. Replace the polymorphic variable(s) %a by public"
               (Printer.pp_var ~debug:false) (L.unloc x)
               Lvl.pp lvl
               (pp_list ",@ " Vl.pp) (Svl.elements poly)
    else env, lvl

  let gget ~(public:bool) env x =
    if is_gkvar x then get ~public env x.gv
    else env, Public

  let pp fmt env =
    let pp_ty fmt (x, (k, lvl)) =
      Format.fprintf fmt "@[%a : %s %a@]" (Printer.pp_var ~debug:false) x
        (string_of_lvl_kind k) Lvl.pp lvl in
    Format.fprintf fmt "@[<v>type = @[%a@]@ vlevel= @[%a@]@]"
       (pp_list ";@ " pp_ty) (Mv.bindings env.env_v)
       (pp_list "@ " Vl.pp) (Svl.elements env.env_vl)

end

(* -----------------------------------------------------------*)

module UE = struct

  type unienv = (Vl.t, level) Hashtbl.t

  let create n = Hashtbl.create n

  let get (ue:unienv) vl =
    try Hashtbl.find ue vl with Not_found -> Public

  let set (ue:unienv) s lvl =
    assert (Svl.cardinal s = 1);
    let vl = Svl.choose s in
    Hashtbl.add ue vl (Lvl.max (get ue vl) lvl)

end (* UE *)

let unify uty ety : UE.unienv =
  let ue = UE.create 31 in
  let doit (_, uty) ety =
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
  | Poly s -> Svl.fold (fun vl lvl -> Lvl.max (UE.get ue vl) lvl) s Public

let instanciates ue tyin =
  List.map (instanciate ue) tyin

let instanciate_fty fty lvls  =
  let ue = unify fty.tyin lvls in
  let tyout = instanciates ue fty.tyout in
  tyout

(* -----------------------------------------------------------*)
let is_ct_op1 (_: Expr.sop1) = true

let is_ct_op2 (o: Expr.sop2) =
  match o with
  | Omod (Cmp_w _) | Odiv (Cmp_w _) -> false
  | _ -> true

let is_ct_opN (_ : Expr.opN) = true

let is_ct_sopn is_ct_asm (o : 'a Sopn.sopn) =
  match o with
  | Opseudo_op _ -> true
  | Oslh _ -> true
  | Oasm asm -> is_ct_asm asm

(* -----------------------------------------------------------*)
(* [ty_expr ~public env e] return [env', lvl] such that [env' |- e : lvl]
   and [env' <= env] i.e for all x, [env'(x) <= env(x)].
   Furthermore [public => lvl = Public.
   Remark we need the property: [env' <= env => env |- e : lvl => env' |- e : lvl]
 *)

let rec ty_expr ~(public:bool) env (e:expr) =
  match e with
  | Pconst _ | Pbool _ | Parr_init _ -> env, Public

  | Pvar x -> Env.gget ~public env x

  | Pget (_, _, _, x, i) | Psub (_, _, _, x, i) ->
    let env, ty = Env.gget ~public env x in
    let env, _  = ty_expr ~public:true env i in
    env, ty

  | Pload (_, _, x, i) ->
    let env, _ = Env.get ~public:true env x in
    let env, _ = ty_expr ~public:true env i in
    env, Secret

  | Papp1(o, e)        ->
    let public = public || not (is_ct_op1 o) in
    ty_expr ~public env e
  | Papp2(o, e1, e2)   ->
    let public = public || not (is_ct_op2 o) in
    ty_exprs_max ~public env [e1; e2]
  | PappN(o, es)       ->
    let public = public || not (is_ct_opN o) in
    ty_exprs_max ~public env es
  | Pif(_, e1, e2, e3) -> ty_exprs_max ~public env [e1; e2; e3]

and ty_exprs ~public env es =
  List.map_fold (ty_expr ~public) env es

and ty_exprs_max ~public env es =
  let env, lvls = ty_exprs ~public env es in
  env, Lvl.maxs lvls

(* -----------------------------------------------------------*)
let ty_lval env x lvl =
  match x with
  | Lnone _ -> env
  | Lvar x -> Env.set env x lvl
  | Lmem(_, _, x, i) ->
    let env, _ = Env.get ~public:true env x in
    let env, _ = ty_expr ~public:true env i in
    env
  | Laset(_, _, _, x, i) | Lasub(_, _, _, x, i) ->
    (* x[i] = e is x = x[i <- e] *)
    let env, xlvl = Env.get ~public:false env x in
    let env, _    = ty_expr ~public:true env i in
    Env.set env x (Lvl.max xlvl lvl)

let ty_lvals env xs lvls =
  List.fold_left2 ty_lval env xs lvls

let ty_lvals1 env xs lvl =
  List.fold_left (fun env x -> ty_lval env x lvl) env xs

(* -----------------------------------------------------------*)
let lvl_of_level =
  function
  | SecurityAnnotations.Public -> Public
  | Secret -> Secret
  | Named n -> Lvl.poly1 (Vl.mk_poly n)

let lvl_of_typ =
  function
  | SecurityAnnotations.Msf -> Public
  | Direct t | Indirect { value = t ; ptr = _ } -> lvl_of_level t.normal

let get_annot ensure_annot f =
  let sig_annot = SecurityAnnotations.get_sct_signature f.f_annot.f_user_annot in
  let process_argument i x =
    let lvl =
      match Lvl.parse ~single:true ~kind_allowed:true x.v_annot, Option.bind sig_annot (SecurityAnnotations.get_nth_argument i) with
      | lvl, None -> lvl
      | (_, Some _) as lvl, _ -> lvl
      | _, Some t -> Some Flexible, Some (lvl_of_typ t)
    in
    x.v_name, lvl
  in
  let process_result i a =
    match Lvl.parse ~single:false ~kind_allowed:false a, Option.bind sig_annot (SecurityAnnotations.get_nth_result i) with
    | (_, lvl), None -> lvl
    | (_, (Some _ as lvl)), _ -> lvl
    | _, Some t -> Some (lvl_of_typ t)
  in
  let ain  = List.mapi process_argument f.f_args in
  let ainlevels = List.map (fun (_, (_, x)) -> x) ain in
  let aout = List.mapi process_result f.f_outannot in

  let check_defined msg l =
    if List.exists (fun a -> a = None) l then
      error ~loc:f.f_loc
           "export functions should be fully annotated, missing some security annotations on %s.@ User option “-infer” to infer them."
           msg in
  if ensure_annot && FInfo.is_export f.f_cc then
    (check_defined "result types" aout;
     check_defined "function parameters" ainlevels);
  (* fill the missing input type *)
  (* we collect the existing levels, to avoid a name clash *)
  let used_lvls =
    let f acc lvl =
      match lvl with
      | Some (Poly s) -> Svl.union s acc
      | _ -> acc
    in
    let lvls = List.fold_left f Svl.empty ainlevels in
    List.fold_left f lvls aout
  in
  let used_lvls = ref used_lvls in
  let counter = ref (-1) in
  let rec fresh_lvl ?n () =
    let vl =
      let k =
      match n with
      | None -> incr counter; "l" ^ string_of_int !counter
      | Some x -> x
      in
      Vl.mk_uni k in
    if Svl.mem vl !used_lvls then fresh_lvl ()
    else (used_lvls := Svl.add vl !used_lvls; vl)
  in
  let ain =
    let doit (n, (k, o)) =
      match o with
      | None -> Flexible, Lvl.poly1 (fresh_lvl ~n ())
      | Some lvl -> Option.default Strict k, lvl in
    List.map doit ain
  in
  (* Compute the local variables info *)
  let do_local x decls =
    let (k, lvl) = Lvl.parse ~single:true ~kind_allowed:true x.v_annot in
    if k = Some Flexible then
      begin
        warning Always (L.i_loc0 x.v_dloc)
          "%s annotation will be ignored for local variable %a"
          Lvl.sflexible (Printer.pp_var ~debug:false) x;
        decls
      end
    else
      match lvl with
      | Some lvl -> (x,lvl) :: decls
      | None -> decls
  in
  let ldecls = Sv.fold do_local (Prog.locals f) [] in

  (* check that the output type only depend on variable level declared in the input type *)
  let known =
    List.fold_left
      (fun s (_, lvl) -> match lvl with Poly s' -> Svl.union s s' | _ -> s) Svl.empty ain in

  let check_lvl lvl =
    match lvl with
    | Poly s ->
      let diff = Svl.diff s known in
      if not (Svl.is_empty diff) then
        error ~loc:f.f_loc
          "variable(s) level %a should be used in the input security annotations"
             (pp_list ", " Vl.pp) (Svl.elements diff)
    | _ -> () in

  List.iter (Option.may check_lvl) aout;
  List.iter (fun (_, lvl) -> check_lvl lvl) ldecls;
  ain, aout, ldecls

(* -----------------------------------------------------------*)
let sdeclassify = "declassify"

let is_declassify annot =
  Annot.ensure_uniq1 sdeclassify Annot.none annot <> None

let declassify_lvl annot lvl =
  if is_declassify annot then Public
  else lvl

let declassify_lvls annot lvls =
  if is_declassify annot then List.map (fun _ -> Public) lvls
  else lvls

(* [ty_instr env i] return env' such that env |- i : env' *)

let rec ty_instr is_ct_asm fenv env i =
  let env1 =
  match i.i_desc with
  | Cassgn(x, _, _, e) ->
    let env, lvl = ty_expr ~public:false env e in
    ty_lval env x (declassify_lvl i.i_annot lvl)

  | Copn(xs, _, o, es) ->
    let public = not (is_ct_sopn is_ct_asm o) in
    let env, lvl = ty_exprs_max ~public env es in
    ty_lvals1 env xs (declassify_lvl i.i_annot lvl)

  | Csyscall(xs, RandomBytes _, es) ->
    let env, _ = ty_exprs_max ~public:true env es in
    ty_lvals1 env xs (declassify_lvl i.i_annot Secret)

  | Cif(e, c1, c2) ->
    let env, _ = ty_expr ~public:true env e in
    let env1 = ty_cmd is_ct_asm fenv env c1 in
    let env2 = ty_cmd is_ct_asm fenv env c2 in
    Env.max env1 env2

  | Cfor(x, (_, e1, e2), c) ->
    let env, _ = ty_exprs ~public:true env [e1; e2] in
    let rec loop env =
      let env1 = Env.set env x Public in
      let env1 = ty_cmd is_ct_asm fenv env1 c in (*  env |- x = p; c : env1 <= env  *)
      if Env.le env1 env then env      (* G <= G'  G' |- c : G''   G |- c : G'' *)
      else loop (Env.max env1 env) in  (* le env/env1 (max env1 env) Check *)
    loop env

  | Cwhile(_, c1, e, c2) ->
    (* c1; while e do c2; c1 *)
    (* G |- c1 : G'   G' |- e : public   G' |- c2 : G
       -----------------------------------------------
       G |- while c1 e c2 : G'
     *)

    let rec loop env =
      let env1 = ty_cmd is_ct_asm fenv env c1 in   (* env |- c1 : env1 *)
      let env1,_ = ty_expr ~public:true env1 e in
      let env2 = ty_cmd is_ct_asm fenv env1 c2 in  (* env1 |- c2 : env2 *)
      if Env.le env2 env then env1
      else loop (Env.max env2 env) in
    loop env

  | Ccall (xs, f, es) ->
    let fty = get_fun is_ct_asm fenv f in
    (* Check the arguments *)
    let do_e env e (_,lvl) = ty_expr ~public:(lvl=Public) env e in
    let env, elvls = List.map_fold2 do_e env es fty.tyin in
    let olvls = instanciate_fty fty elvls in
    ty_lvals env xs (declassify_lvls i.i_annot olvls)
  in
  if !Glob_options.debug then
    Format.eprintf "%a: @[<v>before %a@ after %a@]@." L.pp_loc (i.i_loc.base_loc) Env.pp env Env.pp env1;
  env1

and ty_cmd is_ct_asm fenv env c =
  List.fold_left (fun env i -> ty_instr is_ct_asm fenv env i) env c

and get_fun is_ct_asm fenv f =
  try Hf.find fenv.env_ty f
  with Not_found ->
    let fty = ty_fun is_ct_asm fenv f in
    Hf.add fenv.env_ty f fty;
    fty

and ty_fun is_ct_asm fenv fn =
  (* TODO: we should have this defined *)
  let f = List.find (fun f -> F.equal f.f_name fn) fenv.env_def in
  let tyin, aout, ldecls = get_annot fenv.ensure_annot f in
  let env = List.fold_left2 Env.add Env.empty f.f_args tyin in
  let env = List.fold_left (fun env (x,lvl) -> Env.add env x (Strict, lvl)) env ldecls in
  let env = ty_cmd is_ct_asm fenv env f.f_body in
  (* First ensure that all return that are required to be public are publics *)
  let set_pub env x aout =
    if aout = Some Public then
      let env, _ = Env.get ~public:true env x in
      env
    else env in
  let env = List.fold_left2 set_pub env f.f_ret aout in
  if !Glob_options.debug then Format.eprintf "env return %a@." Env.pp env;
  (* Compute the return type *)
  let do_r env x aout =
    let _, lvl = Env.get ~public:false env x in
    let lvl =
      match aout with
      | None -> lvl
      | Some alvl ->
        if Lvl.le lvl alvl then alvl
        else
          error ~loc:(L.loc x)
            "the variable %a has type %a instead of %a"
              (Printer.pp_var ~debug:false) (L.unloc x)
              Lvl.pp lvl Lvl.pp alvl in
    lvl in
  let tyout = List.map2 (do_r env) f.f_ret aout in
  (* Normalize the input type *)
  let tyin = List.map (fun (k, lvl) -> k, Env.norm_lvl env lvl) tyin in
  { tyin ; tyout }

let ty_prog (is_ct_asm: 'asm -> bool)  ~infer (prog: ('info, 'asm) prog) fl =
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
        with Not_found -> hierror ~loc:Lnone ~kind:"constant type checker" "unknown function %s" fn in
      List.map get fl in
  let status =
    match List.iter (fun fn -> ignore (get_fun is_ct_asm fenv fn : signature)) fl with
    | () -> None
    | exception Annot.AnnotationError (loc, msg)
    | exception CtTypeError (loc, msg)
      -> Some (loc, msg)
  in
  Hf.to_list fenv.env_ty, status
