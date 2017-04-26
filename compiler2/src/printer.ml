(* -------------------------------------------------------------------- *)
open Prog

module F = Format
module B = Bigint

(* -------------------------------------------------------------------- *)
let rec pp_list sep pp fmt xs =
  let pp_list = pp_list sep pp in
    match xs with
    | []      -> ()
    | [x]     -> Format.fprintf fmt "%a" pp x
    | x :: xs -> Format.fprintf fmt "%a%(%)%a" pp x sep pp_list xs

(* -------------------------------------------------------------------- *)
let pp_btype fmt = function
  | Bool -> F.fprintf fmt "bool"
  | U i  -> F.fprintf fmt "U%i" (int_of_ws i)
  | Int  -> F.fprintf fmt "int"

(* -------------------------------------------------------------------- *)
let pp_gtype (pp_size:F.formatter -> 'size -> unit) fmt = function
  | Bty ty -> pp_btype fmt ty
  | Arr(ws,e) -> F.fprintf fmt "%a[%a]" pp_btype (U ws) pp_size e

(* -------------------------------------------------------------------- *)
let pp_gvar_i pp_var fmt v = pp_var fmt (L.unloc v)

(* -------------------------------------------------------------------- *)
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

(* -------------------------------------------------------------------- *)
let pp_ge pp_var =
  let pp_var_i = pp_gvar_i pp_var in
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

(* -------------------------------------------------------------------- *)
let pp_glv pp_var fmt = function
  | Lnone _ -> F.fprintf fmt "_"
  | Lvar x  -> pp_gvar_i pp_var fmt x
  | Lmem (ws, x, e) ->
    F.fprintf fmt "@[store %a@ %a@ %a@]"
     pp_btype (U ws) (pp_gvar_i pp_var) x (pp_ge pp_var) e
  | Laset(x,e) ->
    F.fprintf fmt "%a[%a]" (pp_gvar_i pp_var) x (pp_ge pp_var) e

(* -------------------------------------------------------------------- *)
let pp_ges pp_var fmt es =
  Format.fprintf fmt "@[%a@]" (pp_list ",@ " (pp_ge pp_var)) es

(* -------------------------------------------------------------------- *)
let pp_glvs pp_var fmt lvs =
  match lvs with
  | [] -> assert false
  | [x] -> pp_glv pp_var fmt x
  | _   -> F.fprintf fmt "(@[%a@])" (pp_list ",@ " (pp_glv pp_var)) lvs

(* -------------------------------------------------------------------- *)
let pp_opn = function
  | Olnot     -> "#lnot"   
  | Oxor      -> "#xor"
  | Oland     -> "#land"
  | Olor      -> "#lor"
  | Olsr      -> "#lsr"
  | Olsl      -> "#lsl"
  | Oif       -> "#if"
  | Omulu     -> "#mulu"
  | Omuli     -> "#muli"
  | Oaddcarry -> "#addcarry"
  | Osubcarry -> "#subcarry"
  | Oleu      -> "#leu"
  | Oltu      -> "#ltu"
  | Ogeu      -> "#geu"
  | Ogtu      -> "#gtu"
  | Oles      -> "#les"
  | Olts      -> "#lts"
  | Oges      -> "#ges"
  | Ogts      -> "#gts"
  | Oeqw      -> "#eqw"     

(* -------------------------------------------------------------------- *)
let rec pp_gi pp_var fmt i =
  match i.i_desc with
  | Cblock c ->
    F.fprintf fmt "@[<v>%a@]" (pp_cblock pp_var) c

  | Cassgn(x , _, e) ->
    F.fprintf fmt "@[<hov 2>%a =@ %a;@]" (pp_glv pp_var) x (pp_ge pp_var) e

  | Copn(x, o, e) -> (* FIXME *)
    F.fprintf fmt "@[<hov 2>%a =@ %s(%a);@]"
       (pp_glvs pp_var) x (pp_opn o)
       (pp_ges pp_var) e

  | Cif(e, c, []) ->
    F.fprintf fmt "@[<v>if %a %a@]"
      (pp_ge pp_var) e (pp_cblock pp_var) c

  | Cif(e, c1, c2) ->
    F.fprintf fmt "@[<v>if %a %a else %a@]"
      (pp_ge pp_var) e (pp_cblock pp_var) c1 (pp_cblock pp_var) c2

  | Cfor(i, (dir, lo, hi), c) ->
    let dir, e1, e2 =
      if dir = UpTo then "to", lo, hi else "downto", hi, lo in
    F.fprintf fmt "@[<v>for %a = @[%a %s@ %a] %a@]"
      (pp_gvar_i pp_var) i (pp_ge pp_var) e1 dir (pp_ge pp_var) e2
      (pp_gc pp_var) c

  | Cwhile(e, c) ->
    F.fprintf fmt "@[<v>while (%a) {@   %a@ }@]"
      (pp_ge pp_var) e (pp_gc pp_var) c

  | Ccall(_ii, x, f, e) -> (* FIXME ii *)
    F.fprintf fmt "@[<hov 2> %a =@ %s(%a);@]"
      (pp_glvs pp_var) x f.fn_name (pp_ges pp_var) e

(* -------------------------------------------------------------------- *)
and pp_gc pp_var fmt c =
  F.fprintf fmt "@[<v>%a@]" (pp_list "@ " (pp_gi pp_var)) c

(* -------------------------------------------------------------------- *)
and pp_cblock pp_var fmt c =
  F.fprintf fmt "{@   %a@ }" (pp_gc pp_var) c

(* -------------------------------------------------------------------- *)

let pp_kind = function
  | Const  -> "Const"
  | Stack  -> "Stack"
  | Reg    -> "Reg"
  | Inline -> "Inline"

let pp_ty_decl (pp_size:F.formatter -> 'size -> unit) fmt v =
  F.fprintf fmt "%s %a" (pp_kind v.v_kind) (pp_gtype pp_size) v.v_ty
  
let pp_var_decl pp_var pp_size fmt v = 
  F.fprintf fmt "%a %a" (pp_ty_decl pp_size) v pp_var v

let pp_gfun (pp_size:F.formatter -> 'size -> unit) pp_var fmt fd =  
  let pp_vd =  pp_var_decl pp_var pp_size in
(*  let locals = locals fd in *)
  let ret = List.map L.unloc fd.f_ret in
  let pp_ret fmt () =
    F.fprintf fmt "return @[(%a)@];"
      (pp_list ",@ " pp_var) ret in

  F.fprintf fmt "@[<v>fn %s @[(%a)@] -> @[(%a)@] {@   @[<v>%a@ %a@]@ }@]" 
   fd.f_name.fn_name
   (pp_list ",@ " pp_vd) fd.f_args
   (pp_list ",@ " (pp_ty_decl pp_size)) ret 
(*   (pp_list ";@ " pp_vd) (Sv.elements locals) *)
   (pp_gc pp_var) fd.f_body
   pp_ret ()


let pp_pitem pp_var = 
  let pp_size = pp_ge pp_var in
  let aux fmt = function
    | MIfun fd -> pp_gfun pp_size pp_var fmt fd
    | MIparam (x,e) ->
      F.fprintf fmt "%a = %a" 
        (pp_var_decl pp_var pp_size) x
        (pp_ge pp_var) e in
  aux

let pp_pprog fmt p = 
  let pp_var fmt x = F.fprintf fmt "%s" x.v_name in
  Format.fprintf fmt "@[<v>%a@]"
    (pp_list "@ @ " (pp_pitem pp_var)) (List.rev p)


let pp_fun pp_var fmt fd =  
  let pp_size fmt i = F.fprintf fmt "%i" i in
  let pp_vd =  pp_var_decl pp_var pp_size in
  let locals = locals fd in 
  let ret = List.map L.unloc fd.f_ret in
  let pp_ret fmt () =
    F.fprintf fmt "return @[(%a)@];"
      (pp_list ",@ " pp_var) ret in

  F.fprintf fmt "@[<v>fn %s @[(%a)@] -> @[(%a)@] {@   @[<v>%a@ %a@ %a@]@ }@]" 
   fd.f_name.fn_name
   (pp_list ",@ " pp_vd) fd.f_args
   (pp_list ",@ " (pp_ty_decl pp_size)) ret 
   (pp_list ";@ " pp_vd) (Sv.elements locals) 
   (pp_gc pp_var) fd.f_body
   pp_ret ()

let pp_prog ~debug fmt p = 
  let pp_var = 
    if debug then 
      fun fmt x -> F.fprintf fmt "%s.%i" x.v_name (int_of_uid x.v_id) 
    else
      fun fmt x -> F.fprintf fmt "%s" x.v_name 
  in
  Format.fprintf fmt "@[<v>%a@]"
     (pp_list "@ @ " (pp_fun pp_var)) (List.rev p)
  


    
                
