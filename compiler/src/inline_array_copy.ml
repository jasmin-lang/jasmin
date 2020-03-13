open Utils
open Prog

module L = Location

let is_array_copy (x:lval) kind e =
  if kind = AT_address then None
  else
    match x with
    | Lvar z ->
      begin match (L.unloc z).v_ty with
      | Arr (ws, n) ->
        begin match e with
        | Pvar y -> 
          assert (is_gkvar y);
          Some (z, ws, n, y)
        | _ -> None
        end
      | _ -> None
      end
    | _ -> None

let array_copy z ws n y =
  let i = gkvar (L.mk_loc (L.loc z) (V.mk "i" Inline (Bty Int) (L.loc z))) in
  Cfor(i.gv, (UpTo, Pconst B.zero, Pconst (B.of_int n)), [
      let i_desc =
        Cassgn (Laset (ws, z, Pvar i), AT_none, Bty (U ws), 
                 Pget (ws, y, Pvar i)) in
      { i_desc ; i_loc = L.loc z, [] ; i_info = () }
    ])

let rec iac_stmt is = List.map iac_instr is
and iac_instr i = { i with i_desc = iac_instr_r i.i_desc }
and iac_instr_r ir =
  match ir with
  | Cassgn (x, k, _, e) ->
    begin match is_array_copy x k e with
    | None -> ir
    | Some (z, ws, n, y) -> array_copy z ws n y
    end
  | Cif (b, th, el) -> Cif (b, iac_stmt th, iac_stmt el)
  | Cfor (i, r, s) -> Cfor (i, r, iac_stmt s)
  | Cwhile (a, c1, t, c2) -> Cwhile (a, iac_stmt c1, t, iac_stmt c2)
  | (Copn _ | Ccall _) -> ir

let iac_func f =
  { f with f_body = iac_stmt f.f_body }

let doit (p:unit Prog.prog) = (fst p, List.map iac_func (snd p))
