(* This step has two purposes: 
   1/ Fix the size information (n) in Ocopy(ws, n). 
      For the moment pretyping add a dummy value for n, it is fixed here.
   2/ Replace x = y when x and y are arrays and at least one of then 
      is a reg array with #copy, that will be transformed with loop.
      This is optional: !Glob_options.introduce_array_copy 
*)
        
open Utils
open Prog
module L = Location

let is_array_copy (x:lval) (e:expr) =
  match x with
  | Lvar x ->
    let x = L.unloc x in
    begin match x.v_ty with
    | Arr (xws, xn) ->
      begin match e with
      | Pvar y ->
        let y = L.unloc y.gv in
        begin match y.v_ty with
        | Arr(yws, yn) ->
           assert (arr_size xws xn <= arr_size yws yn);
           if x.v_kind = Reg Direct then Some (xws, xn)
           else if y.v_kind = Reg Direct then Some (yws, arr_size xws xn / size_of_ws yws)
           else None
        | _ -> None
        end
      | _ -> None
      end
    | _ -> None
    end
  | _ -> None

let rec iac_stmt is = List.map iac_instr is
and iac_instr i = { i with i_desc = iac_instr_r i.i_loc i.i_desc }
and iac_instr_r loc ir =
  match ir with
  | Cassgn (x, t, _, e) ->
    if !Glob_options.introduce_array_copy then 
      match is_array_copy x e with
      | None -> ir
      | Some (ws, n) -> 
          warning IntroduceArrayCopy 
            loc "an array copy is introduced";
          Copn([x], t, E.Ocopy(ws, Conv.pos_of_int n), [e])
    else ir
  | Cif (b, th, el) -> Cif (b, iac_stmt th, iac_stmt el)
  | Cfor (i, r, s) -> Cfor (i, r, iac_stmt s)
  | Cwhile (a, c1, t, c2) -> Cwhile (a, iac_stmt c1, t, iac_stmt c2)
  | Copn (xs,t,o,es) ->
    begin match o, xs with
    | E.Ocopy(ws, _), [Lvar x] ->
      (* Fix the size it is dummy for the moment *)
      let xn = size_of (L.unloc x).v_ty in
      let wsn = size_of_ws ws in
      if xn mod wsn <> 0 then 
        Typing.error loc 
          "the variable %a has type %a, its size (%i) should be a multiple of %i"
          (Printer.pp_var ~debug:false) (L.unloc x)
          Printer.pp_ty (L.unloc x).v_ty 
          xn wsn
      else Copn(xs,t,E.Ocopy(ws, Conv.pos_of_int (xn / wsn)), es)
    | E.Ocopy _, _ -> assert false
    | _ -> ir
    end
  | Ccall _ -> ir

let iac_func f =
  { f with f_body = iac_stmt f.f_body }

let doit (p:unit Prog.prog) = (fst p, List.map iac_func (snd p))

