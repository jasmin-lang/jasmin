open Jasmin.Syscall_t
open Jasmin.Utils
open Jasmin.Prog
open Annotation

type dependencies = Sv.t Mv.t
(** Maps each variable to the set of variables it depends on. *)

type writeset = { get_writeset : Sv.t } [@@unboxed]
(** The set of variables that are written by a statement. *)

type signatures = (var list * var list) Mf.t
(** Maps each function name to its signature (parameters and returned
    variables). *)

let empty_writeset = { get_writeset = Sv.empty }

let merge_writesets w1 w2 =
  { get_writeset = Sv.union w1.get_writeset w2.get_writeset }

let get_dependencies (deps : dependencies) (x : var) : Sv.t =
  Mv.find_default Sv.empty x deps

let kill_dependencies (deps : dependencies) (x : var) : dependencies =
  Mv.remove x deps

let set_dependencies (deps : dependencies) (x : var) (d : Sv.t) : dependencies =
  if Sv.is_empty d then kill_dependencies deps x else Mv.add x d deps

let join_dependencies (deps : dependencies) (x : var) (d : Sv.t) : dependencies
    =
  Mv.modify_def Sv.empty x (Sv.union d) deps

let merge_dependencies d d' : dependencies =
  Mv.merge
    (fun _x o1 o2 ->
      match (o1, o2) with
      | Some s1, Some s2 -> Some (Sv.union s1 s2)
      | None, o | o, _ -> o)
    d d'

let is_included d d' : bool =
  Mv.for_all (fun x s -> Sv.subset s (get_dependencies d' x)) d

let write_dependencies (d : Sv.t) deps (x : lval) : dependencies =
  match x with
  | Lnone _ | Lmem _ -> deps
  | Lvar x -> set_dependencies deps (L.unloc x) d
  | Laset (_, _, _, x, e) | Lasub (_, _, _, x, e) ->
      let d' = vars_e e in
      join_dependencies deps (L.unloc x) (Sv.union d d')

let written_lvs w xs =
  { get_writeset = List.fold_left written_lv w.get_writeset xs }

let after_join deps d w : dependencies =
  Sv.fold (fun x deps -> join_dependencies deps x d) w.get_writeset deps

let analyse_call_args deps args es =
  List.fold_left2 (fun d x e -> set_dependencies d x (vars_e e)) deps args es

let analyse_stmt (context : signatures) dom stmt =
  let rec analyse_stmt dom stmt = List.fold_left_map analyse_instr dom stmt
  and analyse_instr ((_w, deps) as dom) instr =
    let dom, i_desc = analyse_instr_r dom instr.i_desc in
    (dom, { instr with i_desc; i_info = Annotation deps })
  and analyse_instr_r (w, deps) ir =
    match ir with
    | Cassgn (x, tg, ty, e) ->
        let d = vars_e e in
        ( ( { get_writeset = written_lv w.get_writeset x },
            write_dependencies d deps x ),
          Cassgn (x, tg, ty, e) )
    | Copn (xs, tg, op, es) ->
        let d = vars_es es in
        ( (written_lvs w xs, List.fold_left (write_dependencies d) deps xs),
          Copn (xs, tg, op, es) )
    | Ccall (xs, fn, es) ->
        let args, rets = Mf.find fn context in
        let w =
          {
            get_writeset =
              (let w =
                 List.fold_left (fun s x -> Sv.add x s) w.get_writeset args
               in
               List.fold_left (fun s x -> Sv.add x s) w rets);
          }
        in
        let deps = analyse_call_args deps args es in
        let deps =
          List.fold_left2
            (fun d lv x -> write_dependencies (Sv.singleton x) d lv)
            deps xs rets
        in
        ((written_lvs w xs, deps), Ccall (xs, fn, es))
    | Csyscall ([ x ], RandomBytes len, es) ->
        (* The result of #randombytes does not depend on its argument. *)
        ( ( { get_writeset = written_lv w.get_writeset x },
            write_dependencies Sv.empty deps x ),
          Csyscall ([ x ], RandomBytes len, es) )
    | Csyscall _ -> assert false
    | Cassert (msg, e) -> ((w, deps), Cassert (msg, e))
    | Cif (e, th, el) ->
        let (wth, dth), th = analyse_stmt (empty_writeset, deps) th in
        let (wel, del), el = analyse_stmt (empty_writeset, deps) el in
        let w' = merge_writesets wth wel in
        let d' = merge_dependencies dth del in
        ((merge_writesets w w', after_join d' (vars_e e) w'), Cif (e, th, el))
    | Cfor (i, (d, lo, hi), c) ->
        let range_vars = vars_es [ lo; hi ] in
        let reset_i deps = set_dependencies deps (L.unloc i) range_vars in
        let rec loop d =
          let d' = reset_i d in
          let (w', d'), c = analyse_stmt (empty_writeset, d') c in
          if is_included d' d then ((w', d), c)
          else loop (merge_dependencies d d')
        in
        let (w', deps'), c = loop deps in
        ( (merge_writesets w w', after_join deps' (Sv.singleton (L.unloc i)) w'),
          Cfor (i, (d, lo, hi), c) )
    | Cwhile (aa, c1, e, (ei, _), c2) ->
        let (w, deps), _ = analyse_stmt (w, deps) c1 in
        let rec loop d =
          let wd, c2 = analyse_stmt (empty_writeset, d) c2 in
          let (w', d'), c1 = analyse_stmt wd c1 in
          let d' = after_join d' (vars_e e) w' in
          if is_included d' d then (w', d, c1, c2)
          else loop (merge_dependencies d d')
        in
        let w', deps', c1, c2 = loop deps in
        ( (merge_writesets w w', deps'),
          Cwhile (aa, c1, e, (ei, Annotation deps'), c2) )
  in
  analyse_stmt dom stmt

let argument_dependencies args =
  List.fold_left (fun deps x -> Mv.add x (Sv.singleton x) deps) Mv.empty args

let analyse_function (context : signatures) (f : ('info, 'asm) func) :
    (dependencies annotation, 'asm) func =
  let deps = argument_dependencies f.f_args in
  let (_w, deps), f_body =
    analyse_stmt context (empty_writeset, deps) f.f_body
  in
  { f with f_body; f_info = Annotation deps }

(* ----------------------------------------------------------- *)

(** Adds to a set of variables the variables that are read when writing an
    L-value *)
let uses_lv s = function
  | Lnone _ | Lvar _ -> s
  | Lmem (_, _, _, e) -> rvars_e Sv.add s e
  | Laset (_, _, _, x, e) | Lasub (_, _, _, x, e) ->
      rvars_e Sv.add (Sv.add (L.unloc x) s) e

let uses (i : ('info, 'asm) instr_r) : Sv.t =
  match i with
  | Cassgn (x, _, _, e) -> uses_lv (vars_e e) x
  | Copn (xs, _, _, es) | Csyscall (xs, _, es) ->
      List.fold_left uses_lv (vars_es es) xs
  | Cassert (_, a) -> vars_a a
  | Cif (e, _, _) | Cwhile (_, _, e, _, _) -> vars_e e
  | Cfor _ | Ccall _ -> assert false

let error ~kind x y loc =
  let pp_var = Jasmin.Printer.pp_var ~debug:false in
  let pp_vars fmt = Format.fprintf fmt "{ %a }" (pp_list "; " pp_var) in
  let pp_varset fmt y =
    match Sv.elements y with
    | [ y ] ->
        Format.fprintf fmt " “%a (declared at %a)”" pp_var y L.pp_loc y.v_dloc
    | [] -> assert false
    | ys -> Format.fprintf fmt "s %a" pp_vars ys
  in
  let open CompileError in
  {
    location = loc;
    level = 1;
    code = "IR-E001";
    to_text =
      (fun fmt ->
        Format.fprintf fmt "%s “%a” depends on (non-inline) variable%a" kind
          pp_var x pp_varset y);
  }

let check_func (context : signatures) fd : CompileError.t list =
  let errors = ref [] in
  let check_set ~kind ~loc x d =
    let ys =
      Sv.filter
        (fun y ->
          match y.v_kind with
          | Stack _ | Reg _ -> true
          | Const | Inline | Global -> false)
        d
    in
    if not (Sv.is_empty ys) then errors := error ~kind x ys loc :: !errors
  in

  let check ?(kind = "Inline variable") ~loc a s =
    let a = Annotation.unwrap a in
    Sv.iter
      (fun x ->
        if x.v_kind = Inline then
          match Mv.find x a with
          | exception Not_found -> ()
          | d -> check_set ~kind ~loc x d)
      s
  in
  let check_instr i =
    match i.i_desc with
    | Ccall (xs, fn, es) ->
        check ~loc:i.i_loc.base_loc i.i_info
          (List.fold_left uses_lv (vars_es es) xs);
        let args, _rets = Mf.find fn context in
        let deps = Annotation.unwrap i.i_info in
        let deps = analyse_call_args deps args es in
        check ~kind:"Inline parameter" ~loc:i.i_loc.base_loc (Annotation deps)
          (Sv.of_list args)
    | Cfor (x, (_, lo, hi), _) ->
        let loc = i.i_loc.base_loc in
        let deps = vars_es [ lo; hi ] in
        check_set ~kind:"For loop counter" ~loc (L.unloc x) deps;
        check ~loc i.i_info deps
    | ir -> check ~loc:i.i_loc.base_loc i.i_info (uses ir)
  in

  iter_instr check_instr fd.f_body;
  check ~loc:fd.f_loc fd.f_info (Sv.of_list @@ List.map L.unloc fd.f_ret);
  !errors

let check_prog (_gds, fds) : CompileError.t list =
  (* Collect function signatures *)
  let context =
    List.fold_left
      (fun a fd -> Mf.add fd.f_name (fd.f_args, List.map L.unloc fd.f_ret) a)
      Mf.empty fds
  in
  fds
  |> List.map (analyse_function context)
  |> List.fold_left
       (fun acc fd -> List.rev_append (check_func context fd) acc)
       []
