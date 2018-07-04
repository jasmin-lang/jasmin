module L = Location
module E = Expr
module P = Prog

let is_array_copy x e =
  match x with
  | P.Lvar z ->
    begin match (L.unloc z).v_ty with
    | P.Arr (ws, n) ->
      begin match e with
      | P.Pvar y -> Some (z, ws, n, y)
      | _ -> None
      end
    | _ -> None
    end
  | _ -> None

let array_copy z ws n y =
  let i = L.mk_loc (L.loc z) (P.PV.mk "i" P.Inline (Bty Int) (L.loc z)) in
  P.Cfor(i, (UpTo, Pconst P.B.zero, n), [
      let i_desc = P.Cassgn (Laset (z, Pvar i), AT_none, P.Bty (P.U ws), Pget (y, Pvar i)) in
      { i_desc ; i_loc = L.loc z, [] ; i_info = () }
    ])

let rec iac_pstmt is = List.map iac_pinstr is
and iac_pinstr i = { i with P.i_desc = iac_pinstr_r i.P.i_desc }
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
  { pf with P.f_body = iac_pstmt pf.P.f_body }

let iac_pmod_item =
  function
  | P.MIfun pf -> P.MIfun (iac_pfunc pf)
  | pmi -> pmi

let doit p = List.map iac_pmod_item p
