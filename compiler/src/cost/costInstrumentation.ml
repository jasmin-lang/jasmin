open Utils
open Prog

(* ---------------------------------------------------------------- *)
(* Path in structured programs *)
(* FIXME: Is this the same datatype as in cost.v ? *)
type path_element = Scope | Branch of bool
type path = (path_element * int) list * int

let empty_path : path = [], 0
let next (p, n) = (p, n + 1)
let down (p, n) = (Scope, n) :: p, 0
let branch b (p, n) = (Branch b, n) :: p, 0
let branch_left p = branch true p
let branch_right p = branch false p

let string_of_indexed_path_element (pe, n) =
  Format.sprintf "%s.%d"
    (match pe with
     | Scope -> "s"
     | Branch true -> "t"
     | Branch false -> "e"
     ) n

let string_of_path fn (p, n) =
  String.concat ":" [
      "cost";
      fn;
      List.rev_map string_of_indexed_path_element p |> String.concat "_";
      string_of_int n;
    ]

let fresh_var_from_path fn p =
  V.mk (string_of_path fn p) Inline (Bty Int) L._dummy

(* ---------------------------------------------------------------- *)
(* Instruction generation *)
let inloc x = L.(mk_loc _dummy) x
let instr i_desc = { i_desc ; i_loc = L._dummy, [] ; i_info = () }

let assign x e =
  instr (Cassgn (Lvar (inloc x), AT_keep, Bty Int, e))

let add_reset_instruction x s : unit stmt =
  assign x (Pconst Z.zero) :: s

let add_count_instruction fn p f s =
  let x = fresh_var_from_path fn p in
  Sv.add x f,
  assign x (Papp2 (E.Oadd E.Op_int, Pvar (inloc x), Pconst Z.one)) :: s

(* ---------------------------------------------------------------- *)
(* Adds increment instructions in (nearly) each basic block
  Also returns the set of fresh variables introduced.
Maintains the current path
*)
let instrument_stmt context fn p f s =

let rec instrument_stmt p f s =
  let _p, f, acc = List.fold_left instrument_instr (p, f, []) s in
  f, List.rev acc
and instrument_instr (p, f, acc) i =
  let f, i_desc = instrument_instr_r p f i.i_desc in
  next p, f, { i with i_desc } :: acc
and instrument_instr_r p f i =
  match i with
  | (Cassgn _ | Copn _) -> f, i
  | Ccall (ii, xs, fn, es) ->
     let xs, es, f =
       List.fold_right (fun x (xs, es, f) ->
           let x = V.clone x in
           let xi = inloc x in
           Lvar xi :: xs,
           Pvar xi :: es,
           Sv.add x f
         )
         (Mf.find fn context)
         (xs, es, f)
     in f, Ccall (ii, xs, fn, es)
  | Cif (c, th, el) ->
     let f, th = instrument_stmt (branch_left p) f th in
     let f, th = add_count_instruction fn p f th in
     let f, el = instrument_stmt (branch_right p) f el in
     f, Cif (c, th, el)
  | Cfor (x, r, s) ->
     let f, s = instrument_stmt (down p) f s in
     let f, s = add_count_instruction fn p f s in
     f, Cfor (x, r, s)
  | Cwhile (a, s1, c, s2) ->
     let f, s1 = instrument_stmt (branch_right p) f s1 in
     let f, s2 = instrument_stmt (branch_left p) f s2 in
     let f, s2 = add_count_instruction fn p f s2 in
     f, Cwhile (a, s1, c, s2)

in instrument_stmt p f s

let instrument_body context fn s =
  instrument_stmt context fn empty_path Sv.empty s

let instrument_fd context fd =
  let f, f_body = instrument_body context fd.f_name.fn_name fd.f_body in
  match fd.f_cc with
  | Export ->
     let f_body = Sv.fold add_reset_instruction f f_body in
     f |> Sv.elements |> List.rev_map (fun x -> fd.f_name.fn_name, x),
     context,
     { fd with f_body }
  | Internal ->
     let f_tyin, f_args, f_tyout, f_ret, extra =
       Sv.fold (fun x (tyin, args, tyout, ret, extra) ->
           tint :: tyin,
           x :: args,
           tint :: tyout,
           inloc x :: ret,
           x :: extra
         ) f (fd.f_tyin, fd.f_args, fd.f_tyout, fd.f_ret, [])
     in
     [],
     Mf.add fd.f_name extra context,
     { fd with f_tyin; f_args; f_tyout; f_ret; f_body }

let instrument (gd, fds) =
  let fs, fds, _context =
    List.fold_right (fun fd (fs, fds, context) ->
        let f, context, fd = instrument_fd context fd in
        List.rev_append f fs,
        fd :: fds,
        context)
      fds
      ([], [], Mf.empty)
  in
  fs,
  (gd, fds)
