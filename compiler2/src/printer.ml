open Prog

module F = Format
module B = Bigint

let pp_btype fmt = function
  | Bool -> F.fprintf fmt "bool"
  | U i  -> F.fprintf fmt "U%i" (int_of_ws i)
  | Int  -> F.fprintf fmt "int"

let pp_gtype pp_size fmt = function
  | Bty ty -> pp_btype fmt ty
  | Arr(ws,e) -> F.fprintf fmt "%a[%a]" pp_btype (U ws) pp_size e

let pp_var_i pp_var fmt v = pp_var fmt v.L.pl_desc 

let string_of_op2 = function
  | Oand  -> "&&"  
  | Oor   -> "||"      
  | Oadd  -> "+"    
  | Omul  -> "*"    
  | Osub  -> "-"    
  | Oeq   -> "=="    
  | Oneq  -> "!="
  | Olt   -> "<"
  | Ole   -> "<="
  | Ogt   -> ">"
  | Oge   -> ">="

let pp_expr pp_var = 
  let pp_var_i = pp_var_i pp_var in
  let rec pp_expr fmt = function
  | Pconst i    -> B.pp_print fmt i
  | Pbool  b    -> F.fprintf fmt "%b" b
  | Pcast(ws,e) -> F.fprintf fmt "(%a)%a" pp_btype (U ws) pp_expr e
  | Pvar v      -> pp_var_i fmt v
  | Pget(x,e)   -> F.fprintf fmt "%a[%a]" pp_var_i x pp_expr e
  | Pload(ws,x,e) -> 
      F.fprintf fmt "@[(load %a@ %a@ %a)@]" 
                pp_btype (U ws) pp_var_i x pp_expr e
  | Pnot e        -> 
      F.fprintf fmt "(~ %a)" pp_expr e
  | Papp2(op,e1,e2) -> 
      F.fprintf fmt "@[(%a %s@ %a)@]" 
                pp_expr e1 (string_of_op2 op) pp_expr e2 in
  pp_expr   



