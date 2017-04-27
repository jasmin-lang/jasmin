open List0
open Expr
open Sem
open Seq

(** val unroll_cmd : (instr -> instr list) -> instr list -> instr list **)

let unroll_cmd unroll_i0 c =
  fold_right (fun i c' -> cat (unroll_i0 i) c') [] c

(** val assgn : instr_info -> var_i -> pexpr -> instr **)

let assgn ii x e =
  MkI (ii, (Cassgn ((Lvar x), AT_inline, e)))

(** val unroll_i : instr -> instr list **)

let rec unroll_i i = match i with
| MkI (ii, ir) ->
  (match ir with
   | Cif (b, c1, c2) ->
     (MkI (ii, (Cif (b, (unroll_cmd unroll_i c1),
       (unroll_cmd unroll_i c2))))) :: []
   | Cfor (i0, r, c) ->
     let (p, hi) = r in
     let (dir, low) = p in
     let c' = unroll_cmd unroll_i c in
     (match is_const low with
      | Some vlo ->
        (match is_const hi with
         | Some vhi ->
           let l = wrange dir vlo vhi in
           let cs = map (fun n -> (assgn ii i0 (Pconst n)) :: c') l in
           flatten cs
         | None -> (MkI (ii, (Cfor (i0, ((dir, low), hi), c')))) :: [])
      | None -> (MkI (ii, (Cfor (i0, ((dir, low), hi), c')))) :: [])
   | Cwhile (e, c) -> (MkI (ii, (Cwhile (e, (unroll_cmd unroll_i c))))) :: []
   | _ -> i :: [])

(** val unroll_fun : fundef -> fundef **)

let unroll_fun f =
  let { f_iinfo = ii; f_params = p; f_body = c; f_res = r } = f in
  { f_iinfo = ii; f_params = p; f_body = (unroll_cmd unroll_i c); f_res = r }

(** val unroll_prog : prog -> (funname * fundef) list **)

let unroll_prog p =
  map_prog unroll_fun p
