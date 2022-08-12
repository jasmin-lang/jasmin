(* This step has two purposes: 
   1/ Fix the size information (n) in Ocopy(ws, n). 
      For the moment pretyping add a dummy value for n, it is fixed here.
   2/ Replace x = y with #copy, when x and y are arrays and at least one of them
      is a reg array. This #copy will be transformed into a loop later.
      This is optional: !Glob_options.introduce_array_copy 
*)

open Utils
open Prog
module L = Location

let is_lv_array_copy =
  function
  | Lvar x ->
	let x = L.unloc x in
    begin match x.v_ty with
    | Arr (ws, n) -> Some (x, ws, n)
    | _ -> None
    end
  | Lasub (_, ws, n, x, _) -> Some (L.unloc x, ws, n)
  | _ -> None

let is_e_array_copy =
  function
  | Pvar x ->
	let x = L.unloc x.gv in
    begin match x.v_ty with
    | Arr (ws, n) -> Some (x, ws, n)
    | _ -> None
    end
  | Psub (_, ws, n, x, _) -> Some (L.unloc x.gv, ws, n)
  | _ -> None

let is_array_copy (x:lval) (e:expr) =
  match is_lv_array_copy x with
  | Some (x, xws, xn) ->
    begin match is_e_array_copy e with
    | Some (y, yws, yn) ->
      assert (arr_size xws xn = arr_size yws yn);
      if x.v_kind = Reg (Normal, Direct) then Some (xws, xn)
      else if y.v_kind = Reg (Normal, Direct) then Some (yws, arr_size xws xn / size_of_ws yws)
	  else None
    | None -> None
    end
  | None -> None

let rec iac_stmt pd is = List.map (iac_instr pd) is
and iac_instr pd i = { i with i_desc = iac_instr_r pd i.i_loc i.i_desc }
and iac_instr_r pd loc ir =
  match ir with
  | Cassgn (x, t, _, e) ->
    if !Glob_options.introduce_array_copy then 
      match is_array_copy x e with
      | None -> ir
      | Some (ws, n) -> 
          warning IntroduceArrayCopy 
            loc "an array copy is introduced";
          Copn([x], t, Sopn.Ocopy(ws, Conv.pos_of_int n), [e])
    else ir
  | Cif (b, th, el) -> Cif (b, iac_stmt pd th, iac_stmt pd el)
  | Cfor (i, r, s) -> Cfor (i, r, iac_stmt pd s)
  | Cwhile (a, c1, t, c2) -> Cwhile (a, iac_stmt pd c1, t, iac_stmt pd c2)
  | Copn (xs,t,o,es) ->
    begin match o, xs with
    | Sopn.Ocopy (ws, _), [Lvar x] ->
      (* Fix the size it is dummy for the moment *)
      let xn = size_of (L.unloc x).v_ty in
      let wsn = size_of_ws ws in
      if xn mod wsn <> 0 then
        Typing.error loc
          "the variable %a has type %a, its size (%i) should be a multiple of %i"
          (Printer.pp_var ~debug:false) (L.unloc x)
          Printer.pp_ty (L.unloc x).v_ty
          xn wsn
      else Copn(xs,t,Sopn.Ocopy(ws, Conv.pos_of_int (xn / wsn)), es)
    | Sopn.Ocopy (ws, _), [Lasub (_, xws, xn, x, _)] ->
      (* Fix the size it is dummy for the moment *)
      let xlen = arr_size xws xn in
      let wsn = size_of_ws ws in
      if xlen mod wsn <> 0 then
        Typing.error loc
          "the subarray of %a has type %a, its size (%i) should be a multiple of %i"
          (Printer.pp_var ~debug:false) (L.unloc x)
          Printer.pp_ty (Arr (xws, xn))
          xlen wsn
      else Copn(xs,t,Sopn.Ocopy(ws, Conv.pos_of_int (xn / wsn)), es)
    | Sopn.Ocopy _, _ -> assert false
    | _ -> ir
    end

  | Csyscall(xs, o, es) ->
    begin match o with
    | Syscall_t.RandomBytes _ ->
      (* Fix the size it is dummy for the moment *)
      let ty =
        match xs with
        | [x] -> Typing.ty_lval pd loc x
        | _ -> assert false in
      let p = Conv.pos_of_int (Prog.size_of ty) in
      Csyscall(xs, Syscall_t.RandomBytes p, es)
    end

  | Ccall _ -> ir

let iac_func pd f =
  { f with f_body = iac_stmt pd f.f_body }

let doit pd (p:(unit, 'asm) Prog.prog) = (fst p, List.map (iac_func pd) (snd p))

