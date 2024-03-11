open Utils
open Prog

type keep = { vars : Sv.t; funs : Sf.t }

let with_var k x = { k with vars = Sv.add x k.vars }
let with_fun k f = { k with funs = Sf.add f k.funs }

let inspect_gvar k { gs; gv } =
  match gs with Slocal -> k | Sglob -> with_var k (L.unloc gv)

let rec inspect_e k = function
  | Pconst _ | Pbool _ | Parr_init _ -> k
  | Pvar x -> inspect_gvar k x
  | Pget (_, _, _, x, e) | Psub (_, _, _, x, e) -> inspect_gvar (inspect_e k e) x
  | Pload (_, _, _, e) | Papp1 (_, e) -> inspect_e k e
  | Papp2 (_, e1, e2) -> inspect_e (inspect_e k e1) e2
  | PappN (_, es) -> inspect_es k es
  | Pif (_, e1, e2, e3) -> inspect_e (inspect_e (inspect_e k e1) e2) e3

and inspect_es k es = List.fold_left inspect_e k es

let inspect_lv k = function
  | Lnone _ | Lvar _ -> k
  | Lmem (_, _, _, e) | Laset (_, _, _, _, e) | Lasub (_, _, _, _, e) -> inspect_e k e

let inspect_lvs k xs = List.fold_left inspect_lv k xs

let rec inspect_stmt k stmt = List.fold_left inspect_instr k stmt
and inspect_instr k i = inspect_instr_r k i.i_desc

and inspect_instr_r k = function
  | Cassgn (x, _, _, e) -> inspect_lv (inspect_e k e) x
  | Copn (xs, _, _, es) | Csyscall (xs, _, es) ->
      inspect_lvs (inspect_es k es) xs
  | Cif (g, a, b) | Cwhile (_, a, g, b) ->
      inspect_stmt (inspect_stmt (inspect_e k g) a) b
  | Cfor (_, (_, e1, e2), s) -> inspect_stmt (inspect_es k [ e1; e2 ]) s
  | Ccall (xs, fn, es) -> with_fun (inspect_lvs (inspect_es k es) xs) fn

let slice fs (gd, fds) =
  let funs =
    List.fold_left
      (fun s n ->
        match List.find (fun fd -> String.equal n fd.f_name.fn_name) fds with
        | exception Not_found ->
            warning Always L.i_dummy "slicing: function “%s” not found" n;
            s
        | fd -> Sf.add fd.f_name s)
      Sf.empty fs
  in
  let k =
    List.fold_left
      (fun k fd ->
        if Sf.mem fd.f_name k.funs then inspect_stmt k fd.f_body else k)
      { vars = Sv.empty; funs } fds
  in
  (* Keep only global variables that are referenced *)
  let gd = List.filter (fun (x, _) -> Sv.mem x k.vars) gd in
  (* Keep only functions that are referenced *)
  let fds = List.filter (fun fd -> Sf.mem fd.f_name k.funs) fds in
  (* Turn export functions that are not in the fs list into inline functions *)
  let fds =
    List.map
      (fun fd ->
        if List.mem fd.f_name.fn_name fs || not (FInfo.is_export fd.f_cc) then
          fd
        else { fd with f_cc = Internal })
      fds
  in
  (gd, fds)
