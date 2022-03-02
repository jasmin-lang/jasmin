open Utils
open Prog

module S = Syntax
module Pt = Pretyping

let ssecret = "secret"
let spoly   = "poly"
let spublic = "public"
let stransient = "transient"
let smsf = "msf"

(* ----------------------------------------------------------- *)
(* Variable level                                              *)
module Vl : sig
  type t
  val compare : t -> t -> int
  (* Transient is a special variable that cannot be instantiate.
     It represent Transient type *)
  val transient : t
  val is_transient : t -> bool
  val mk_poly : string -> t
  val pp : Format.formatter -> t -> unit
end = struct

  type t = { vl_name : string }

  let compare = compare

  let mk_poly name = { vl_name = name }
  let transient = mk_poly stransient

  let is_transient vl = vl = transient

  let pp fmt vl = Format.fprintf fmt "%s" vl.vl_name
end

module Svl : Set.S with type elt = Vl.t = Set.Make(Vl)
module Mvl : Map.S with type key = Vl.t = Map.Make(Vl)


type level =
  | Secret
  | Poly of Svl.t (* The max of the polymorphic variables,
                     Remark that the set can contains Transient *)
  | Public of bool (* true means allowed to store msf variables *)

module Lvl : sig

  type t = level

  val poly1 : Vl.t -> level
  val transient : level
  val secret : level
  val public : level
  val msf : level

  val max : t -> t -> t

  val maxs : t list -> t

  val equal : t -> t -> bool

  val le : t -> t -> bool

  val pp : Format.formatter -> level -> unit

  val parse : ?dfl:level -> single:bool -> S.annotations -> level

  val is_public : level -> bool

  val fv : level -> Svl.t

end = struct

  type t = level

  let poly1 vl = Poly (Svl.singleton vl)

  let msf = Public true
  let public = Public false
  let secret = Secret
  let transient = poly1 Vl.transient

  let is_public = function
    | Public _ -> true
    | _ -> false

  let fv = function Poly s -> Svl.remove Vl.transient s | _ -> Svl.empty

  let max l1 l2 =
    match l1, l2 with
    | Secret, _ | _, Secret -> Secret
    | Public b1, Public b2 -> Public (b1 && b2)
    | Public _, l | l, Public _ -> l
    | Poly l1, Poly l2 -> Poly (Svl.union l1 l2)

  let maxs ls = List.fold_left max public ls

  let equal l1 l2 =
    match l1, l2 with
    | Public b1, Public b2 -> b1 = b2
    | Secret, Secret -> true
    | Poly l1, Poly l2 -> Svl.equal l1 l2
    | _, _ -> false

  (* WARNING
     [le l1 l2] = true ensures that for all substitution of the polymorphic variables
     the inequality will stay true.
     [le l1 l2] = false, say that we cannot ensure this property
   *)

  let le l1 l2 =
    match l1, l2 with
    | Public _, _ -> true
    | _, Secret -> true
    | Poly l1, Poly l2 -> Svl.subset l1 l2
    | _, _ -> false

  let pp fmt = function
    | Secret -> Format.fprintf fmt "#%s" ssecret
    | Poly s as lvl ->
      if equal lvl transient then Format.fprintf fmt "#%s" stransient
      else
        let l = Svl.elements s in
        begin match l with
        | [vl] -> Format.fprintf fmt "#%s=%a" spoly Vl.pp vl
        | _ -> Format.fprintf fmt "#%s=(@[%a@])" spoly (pp_list ",@ " Vl.pp) l
        end
    | Public false -> Format.fprintf fmt "#%s" spublic
    | Public true -> Format.fprintf fmt "#%s" smsf

  let parse ?(dfl=secret) ~(single:bool) (annot: S.annotations) =
    let module A = Pt.Annot in
    let on_struct loc _nid (s:S.annotations) =
      List.iter A.none s;
      let s = List.fold_left (fun s (id, _) -> Svl.add (Vl.mk_poly (L.unloc id)) s) Svl.empty s in
      if single && Svl.cardinal s <> 1 then
        Pt.rs_tyerror ~loc
          (Pt.string_error "= ident or = { ident } is expected after “%s”" spoly);
      Poly s in
    let on_id _loc _nid id = poly1 (Vl.mk_poly id) in
    let error loc _nid =
      Pt.rs_tyerror ~loc
        (Pt.string_error "= ident or = { ident, ..., ident } is expected after “%s”" spoly) in
    let poly arg = A.on_attribute ~on_id ~on_struct error arg in
    let filters =
      [spublic, (fun a -> A.none a; public);
       ssecret, (fun a -> A.none a; secret);
       stransient, (fun a -> A.none a; transient);
       smsf, (fun a -> A.none a; msf);
       spoly  , poly] in
    let lvl = A.ensure_uniq filters annot in
    odfl dfl lvl

end

(* -----------------------------------------------------------*)

type ty_fun = {
    tyin : level list; (* Poly are ensured to be singleton *)
    tyout: level list;
  }

type 'info fenv = {
    env_ty       : ty_fun Hf.t;
    env_def      : 'info func list;
  }

(* -----------------------------------------------------------*)

module MSF : sig

  type t = Sv.t * expr option
  val toinit : t
  val exact  : Sv.t -> t
  val exact1 : var_i -> t
  val trans  : Sv.t -> expr -> t

  val le  : t -> t -> bool
  val max : t -> t -> t

  val enter_if : t -> expr -> t
  val update   : t -> var  -> t

  val pp : Format.formatter -> t -> unit

  end = struct

  type t = Sv.t * expr option

  let toinit = (Sv.empty, None)
  let exact xs = (xs, None)
  let trans xs e = (xs, Some e)

  let is_toinit (xs, _) = Sv.is_empty xs

  let le (xs1, oe1) (xs2, oe2 as msf2) =
    is_toinit msf2 ||
      match oe1, oe2 with
      | Some e1, Some e2 when Prog.expr_equal e1 e2 -> Sv.subset xs2 xs1
      | None, None -> Sv.subset xs2 xs1
      | _, _ -> false


  let max (xs1, oe1) (xs2, oe2) =
    match oe1, oe2 with
    | Some e1, Some e2 when Prog.expr_equal e1 e2 -> (Sv.inter xs1 xs2, oe1)
    | _, _ -> toinit

  let enter_if msf e =
    match msf  with
    | (_, Some _) -> toinit
    | (xs, None) -> (xs, Some e)

  let exact1 x = exact (Sv.singleton (L.unloc x))

  let update (xs, oe) x =
    match oe with
    | Some e when Sv.mem x (vars_e e) -> toinit
    | _ -> (Sv.remove x xs, oe)

  let pp fmt (xs, oe) =
    match oe with
    | Some e ->
        Format.fprintf fmt "Trans {%a} %a"
          (pp_list "@, " (Printer.pp_var ~debug:false)) (Sv.elements xs)
          (Printer.pp_expr ~debug:false) e
    | None ->
        Format.fprintf fmt "Exact {%a}"
          (pp_list "@, " (Printer.pp_var ~debug:false)) (Sv.elements xs)

end

let is_register x = x.v_kind = Reg Direct

let is_inline x = x.v_kind = Inline

module Env : sig

  type env
  val empty : env
  val add : env -> var -> level -> env
  val get : env -> var -> level
  val get_i : env -> var_i -> level
  val gget  : env -> int ggvar -> level

end = struct

  type env = Lvl.t Mv.t

  let empty = Mv.empty

  let add env x lvl =
    if Lvl.is_public lvl && not (is_register x || is_inline x) then
      Pt.rs_tyerror ~loc:x.v_dloc
        (Pt.string_error "only register or inline can be declared with type %a" Lvl.pp lvl);
    let lvl =
      if (is_register x || is_inline x) then lvl
      else Lvl.max lvl Lvl.transient in
    Mv.add x lvl env

  let get env x =
    try Mv.find x env with Not_found -> assert false

  let get_i env (x:var_i) = get env (L.unloc x)

  let gget env x =
    if is_gkvar x then get_i env x.gv
    else Lvl.transient

end

(* -----------------------------------------------------------*)

module UE = struct

  type unienv = (Vl.t, level) Hashtbl.t

  let create n = Hashtbl.create n

  let get (ue:unienv) vl =
    try Hashtbl.find ue vl with Not_found -> Lvl.public

  let set (ue:unienv) s lvl =
    assert (Svl.cardinal s = 1);
    let vl = Svl.choose s in
    Hashtbl.add ue vl (Lvl.max (get ue vl) lvl)

end (* UE *)

let instanciate ue ty =
  match ty with
  | Secret | Public _ -> ty
  | Poly s -> Svl.fold (fun vl lvl -> Lvl.max (UE.get ue vl) lvl) s Lvl.public

let instanciates ue tys =
  List.map (instanciate ue) tys

(* -----------------------------------------------------------*)

(* [ty_expr ~lvl env e] return [lvl'] such that [env |- e : lvl'] and [lvl' <= lvl]
   Remark lvl is assumed to be >= Lvl.public
 *)

let check_var x lvl lvl' =
  if not (Lvl.le lvl' lvl) then
    Pt.rs_tyerror ~loc:(L.loc x)
      (Pt.string_error
         "The variable %a has type %a it should be a most %a"
         (Printer.pp_var ~debug:false) (L.unloc x)
           Lvl.pp lvl' Lvl.pp lvl)

let ty_get_gvar ~(lvl:level) env x =
  let lvl' = Env.gget env x in
  check_var x.gv lvl lvl';
  lvl'

let ty_get_var ~(lvl:level) env x =
  let lvl' = Env.get_i env x in
  check_var x lvl lvl';
  lvl'

let rec ty_expr ~(lvl:level) env (e:expr) =
  match e with
  | Pconst _ | Pbool _ | Parr_init _ -> Lvl.public

  | Pvar x -> ty_get_gvar ~lvl env x

  | Pget (_, _, x, i) | Psub (_, _, _, x, i) ->
    let ty = ty_get_gvar ~lvl env x in
    let _  = ty_expr ~lvl:Lvl.public env i in
    ty

  | Pload (_, x, i) ->
    let _ = ty_get_var ~lvl:Lvl.public env x in
    let _ = ty_expr ~lvl:Lvl.public env i in
    if not (Lvl.le Lvl.secret lvl) then
      Pt.rs_tyerror ~loc:(L.loc x) (Pt.string_error "loads are secret, %a data required here" Lvl.pp lvl);
    Lvl.secret

  | Papp1(_, e)        -> ty_expr ~lvl env e
  | Papp2(_, e1, e2)   -> ty_exprs_max ~lvl env [e1; e2]
  | PappN(_, es)       -> ty_exprs_max ~lvl env es
  | Pif(_, e1, e2, e3) -> ty_exprs_max ~lvl env [e1; e2; e3]

and ty_exprs ~lvl env es =
  List.map (ty_expr ~lvl env) es

and ty_exprs_max ~lvl env es =
  let lvls = ty_exprs ~lvl env es in
  Lvl.maxs lvls

(* -----------------------------------------------------------*)
let ty_lval env msf x lvl =
  let check x lvl xlvl =
    if not (Lvl.le lvl xlvl) then
      Pt.rs_tyerror ~loc:(L.loc x) (Pt.string_error "cannot assign a value of type %a into a variable of type %a"
                                      Lvl.pp lvl Lvl.pp xlvl);
  MSF.update msf (L.unloc x)
  in
  match x with
  | Lnone _ -> msf
  | Lvar x -> check x lvl (Env.get_i env x)
  | Lmem(_, x, i) ->
    let _ = ty_get_var ~lvl:Lvl.public env x in
    let _ = ty_expr ~lvl:Lvl.public env i in
    msf
  | Laset(_, _, x, i) | Lasub(_, _, _, x, i) ->
    (* x[i] = e is x = x[i <- e] *)
    let _  = ty_expr ~lvl:Lvl.public env i in
    check x lvl (Env.get_i env x)

let ty_lvals env msf xs lvls =
  List.fold_left2 (ty_lval env) msf xs lvls

let ty_lvals1 env msf xs lvl =
  List.fold_left (fun msf x -> ty_lval env msf x lvl) msf xs

(* -----------------------------------------------------------*)

let get_annot f =
  let mk_dfl x = if is_inline x then Lvl.public else Lvl.secret in
  let ain  = List.map (fun x -> Lvl.parse ~dfl:(mk_dfl x) ~single:true x.v_annot) f.f_args in
  (* Compute the set of polymorphic variables allowed in declarations *)
  let vpoly = List.fold_left (fun vp l -> Svl.union (Lvl.fv l) vp) Svl.empty ain in

  let do_annot ?dfl loc ty =
    let lvl = Lvl.parse ?dfl ~single:false ty in
    let fv = Lvl.fv lvl in
    if not (Svl.subset fv vpoly) then
      Pt.rs_tyerror ~loc
        (Pt.string_error "%a levels need to be declared in paramater annotations"
           (pp_list ",@ " Vl.pp) (Svl.elements (Svl.diff fv vpoly)));
    lvl in

  let aout = List.map (do_annot f.f_loc) f.f_outannot in

  (* Compute the local variables info *)
  let do_local x = x, do_annot ~dfl:(mk_dfl x) x.v_dloc x.v_annot in
  let ldecls = List.map do_local (Sv.elements (Prog.locals f)) in

  ain, aout, ldecls

(* -----------------------------------------------------------*)

type special_op =
  | Init_msf
  | Set_msf
  | Protect
  | Other

let is_special o =
  match o with
  | Sopn.Oasm (Arch_extra.ExtOp (X86_extra.Oprotect _)) -> Protect
  | Oasm (ExtOp Oset_msf) -> Set_msf
  | Oasm (ExtOp Oinit_msf) -> Init_msf
  | _ -> Other

(* -----------------------------------------------------------*)

let ensure_msf env x =
  let lvl = Env.get_i env x in
  if not (lvl = Lvl.msf) then
    Pt.rs_tyerror ~loc:(L.loc x)
      (Pt.string_error "the variable %a needs to be declared with type %a"
         (Printer.pp_var ~debug:false) (L.unloc x) Lvl.pp Lvl.msf)


let ensure_exact_x env msf x =
  match msf with
  | (xS, Some e) ->
    Pt.rs_tyerror ~loc:(L.loc x) (Pt.string_error "Current state is Trans ({%a}, %a), use #set_msf before"
                          (pp_list ",@ " (Printer.pp_var ~debug:false)) (Sv.elements xS)
                          (Printer.pp_expr ~debug:false) e)
  | (xS, None) ->
      if not (Sv.mem (L.unloc x) xS) then
        Pt.rs_tyerror ~loc:(L.loc x)
          (Pt.string_error "the variable %a is not a msf only {@[%a@]} are"
             (Printer.pp_var ~debug:false) (L.unloc x)
             (pp_list ",@ " (Printer.pp_var ~debug:false)) (Sv.elements xS));
      ensure_msf env x

let ensure_exact ~loc env msf xe =
  match xe with
  | Pvar x -> ensure_exact_x env msf x.gv
  | _ ->
      Pt.rs_tyerror ~loc  (Pt.string_error "the expression %a need to be a variable"
                               (Printer.pp_expr ~debug:false) xe)




(* [ty_instr env msf i] return msf' such that env, msf |- i : msf' *)

let rec ty_instr fenv env msf i =
  let msf1 =
  match i.i_desc with
  | Cassgn(x, _, _, e) ->
    let lvl = ty_expr ~lvl:Lvl.secret env e in
    ty_lval env msf x lvl

  | Copn(xs, _, o, es) ->
    let loc = i.i_loc.base_loc in
    begin match is_special o with
    | Init_msf ->
      begin match xs with
      | [Lvar x] ->
        ensure_msf env x;
        MSF.exact1 x

      | _ -> Pt.rs_tyerror ~loc (Pt.string_error "the result of #init_msf needs to be assigned in a register")
      end

    | Set_msf ->
      begin match msf with
      | (_, None) -> Pt.rs_tyerror ~loc (Pt.string_error "MSF is not Trans")
      | (xS, Some b') ->
        match es with
        | [b; Pvar ms] ->

          if not (Sv.mem (L.unloc ms.gv) xS) then
            Pt.rs_tyerror ~loc:(L.loc ms.gv)
              (Pt.string_error "the variable %a is not a msf only {@[%a@]} are"
                  (Printer.pp_var ~debug:false) (L.unloc ms.gv)
                  (pp_list ",@ " (Printer.pp_var ~debug:false)) (Sv.elements xS));
          if not (expr_equal b b') then
            Pt.rs_tyerror ~loc (Pt.string_error "the expression %a should be %a"
                                (Printer.pp_expr ~debug:false) b
                                (Printer.pp_expr ~debug:false) b');
          begin match xs with
          | [_; Lvar ms'] ->
            ensure_msf env ms';
            MSF.exact1 ms'
          | [_; e] ->
             Pt.rs_tyerror ~loc  (Pt.string_error "the expression %a need to be a variable"
                                  (Printer.pp_lval ~debug:false) e)
          | _ -> assert false
          end
      | [_; e] ->
          Pt.rs_tyerror ~loc  (Pt.string_error "the expression %a need to be a variable"
                                  (Printer.pp_expr ~debug:false) e)

      | _ -> assert false
      end

    | Protect ->
      let loc = i.i_loc.base_loc in
      begin match es with
      | [e1; ms] ->
        ensure_exact ~loc env msf ms;
        let _ = ty_expr ~lvl:Lvl.transient env e1 in
        ty_lvals1 env msf xs Lvl.public
      | _ -> assert false
      end

    | Other  ->
        let lvl = ty_exprs_max ~lvl:Lvl.secret env es in
        ty_lvals1 env msf xs lvl
    end

  | Cif(e, c1, c2) ->
    let _ = ty_expr ~lvl:Lvl.public env e in
    let msf1 = ty_cmd fenv env (MSF.enter_if msf e) c1 in
    let msf2 = ty_cmd fenv env (MSF.enter_if msf (Papp1(Onot, e))) c2 in
    MSF.max msf1 msf2

  | Cfor(x, (_, e1, e2), c) ->
    let _ = ty_exprs ~lvl:Lvl.public env [e1; e2] in
    let rec loop msf =
      let msf1 = ty_lval env msf (Lvar x) Lvl.public in
      let msf2 = ty_cmd fenv env msf1 c in (*  env, msf |- x = p; c : msf2 *)
      if MSF.le msf2 msf then msf
      else loop (MSF.max msf2 msf) in
    loop msf

  | Cwhile(_, c1, e, c2) ->
    (* c1; while e do c2; c1 *)
    (* env, msf |- c1 : msf1   env, msf1 |- e : public   env, enter_if e msf1 |- c2 : msf
       --------------------------------------------------------------------------------
       env, msf |- while c1 e c2 : enter_if e msf1
     *)

    let rec loop msf =
      let msf1 = ty_cmd fenv env msf c1 in   (* msf |- c1 : msf1 *)
      let _ = ty_expr ~lvl:Lvl.public env e in
      let msf2 = ty_cmd fenv env (MSF.enter_if msf1 e) c2 in  (* env, msf1 |- c2 : msf2 *)
      if MSF.le msf2 msf then msf1
      else loop (MSF.max msf2 msf) in
    let msf = loop msf in
    MSF.enter_if msf (Papp1(Onot, e))

  | Ccall (_, xs, f, es) ->
    let loc = i.i_loc.base_loc in
    let fty = get_fun fenv f in
    (* Check the arguments *)
    let ue = UE.create 31 in
    let do_e e lvl =
      match lvl with
      | Public b ->
        if b (* lvl = Lvl.msf *) then
          ensure_exact ~loc env msf e
        else ignore (ty_expr ~lvl env e)
      | Secret -> ignore (ty_expr ~lvl env e)
      | Poly l -> (* ensured to be a single element*)
        let l' = Svl.choose l in
        if l' = Vl.transient then ignore (ty_expr ~lvl env e)
        else
          let elvl = ty_expr ~lvl:Lvl.secret env e in
          UE.set ue l elvl in
   List.iter2 do_e es fty.tyin;
   let tout = instanciates ue fty.tyout in
   ignore (ty_lvals env msf xs tout);
   let do_out xs x lvl =
     if Lvl.equal lvl Lvl.msf then
       let x = match x with Lvar x -> L.unloc x
               | _ -> Pt.rs_tyerror ~loc  (Pt.string_error "the left value %a need to be a variable"
                                  (Printer.pp_lval ~debug:false) x) in
       Sv.add x xs
     else xs in
   MSF.exact (List.fold_left2 do_out Sv.empty xs tout)

  in
  if !Glob_options.debug then
    Format.eprintf "%a: @[<v>before %a@ after %a@]@." L.pp_loc (i.i_loc.base_loc) MSF.pp msf MSF.pp msf1;
  msf1

and ty_cmd fenv env msf c =
  List.fold_left (ty_instr fenv env) msf c

and get_fun fenv f =
  try Hf.find fenv.env_ty f
  with Not_found ->
    let fty = ty_fun fenv f in
    Hf.add fenv.env_ty f fty;
    fty

and ty_fun fenv fn =
  (* TODO: we should have this defined *)
  let f = List.find (fun f -> F.equal f.f_name fn) fenv.env_def in
  let tyin, tyout, ldecls = get_annot f in
  let env = List.fold_left2 Env.add Env.empty f.f_args tyin in
  let env = List.fold_left (fun env (x,lvl) -> Env.add env x lvl) env ldecls in
  let do_x xs x lvl =
    if Lvl.equal lvl Lvl.msf then Sv.add x xs
    else xs in
  let msf = MSF.exact (List.fold_left2 do_x Sv.empty f.f_args tyin) in
  let msf = ty_cmd fenv env msf f.f_body in
  (* Check the return *)
  let check_ret x lvl =
    if Lvl.equal lvl Lvl.msf then ensure_exact_x env msf x
    else ignore (ty_expr lvl env (Pvar (gkvar x))) in
  List.iter2 check_ret f.f_ret tyout;
  Format.eprintf "SCT type checking of %s done@." f.f_name.fn_name;
  {tyin; tyout}

let ty_prog (prog:'info prog) fl =
  let prog = snd prog in
  let fenv = { env_ty       = Hf.create 101 ; env_def      = prog } in
  let fl =
    if fl = [] then
      List.rev_map (fun f -> f.f_name) prog
    else
      let get fn =
        try (List.find (fun f -> f.f_name.fn_name = fn) prog).f_name
        with Not_found -> hierror ~loc:Lnone ~kind:"constant type checker" "unknown function %s" fn in
      List.map get fl in
  List.iter (fun fn -> ignore (get_fun fenv fn)) fl
