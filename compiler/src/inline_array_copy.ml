open Utils
open Prog

module L = Location

let is_array_copy x e =
  match x with
  | Lvar z ->
    begin match (L.unloc z).v_ty with
    | Arr (ws, n) ->
      begin match e with
      | Pvar y -> Some (z, ws, n, y)
      | _ -> None
      end
    | _ -> None
    end
  | _ -> None

let array_copy z ws n y =
  let i = L.mk_loc (L.loc z) (PV.mk "i" Inline (Bty Int) (L.loc z)) in
  Cfor(i, (UpTo, Pconst B.zero, n), [
      let i_desc = Cassgn (Laset (z, Pvar i), AT_none, Bty (U ws), Pget (y, Pvar i)) in
      { i_desc ; i_loc = L.loc z, [] ; i_info = () }
    ])

let rec iac_pstmt is = List.map iac_pinstr is
and iac_pinstr i = { i with i_desc = iac_pinstr_r i.i_desc }
and iac_pinstr_r ir =
  match ir with
  | Cassgn (x, _, _, e) ->
    begin match is_array_copy x e with
    | None -> ir
    | Some (z, ws, n, y) -> array_copy z ws n y
    end
  | Cif (b, th, el) -> Cif (b, iac_pstmt th, iac_pstmt el)
  | Cfor (i, r, s) -> Cfor (i, r, iac_pstmt s)
  | Cwhile (a, b, c) -> Cwhile (iac_pstmt a, b, iac_pstmt c)
  | (Copn _ | Ccall _) -> ir

let iac_pfunc pf =
  { pf with f_body = iac_pstmt pf.f_body }

let iac_pmod_item =
  function
  | MIfun pf -> MIfun (iac_pfunc pf)
  | pmi -> pmi

let doit p = List.map iac_pmod_item p
