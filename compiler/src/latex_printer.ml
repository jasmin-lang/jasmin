(* * License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* * Pretty-print Jasmin program (concrete syntax) as LATEX fragments *)

open Syntax
open Printer

module F = Format

type ('a, 'b, 'c, 'd) str = ('a, 'b, 'c, 'd, 'd, 'a) CamlinternalFormatBasics.format6

let eol : _ str = "\\\\\n"

let latex cmd fmt arg =
  F.fprintf fmt "\\jasmin%s{%s}" cmd arg

let symbol s fmt () = latex s fmt ""

let kw = latex "kw"
let ptype = latex "type"
let dname = latex "dname"
let arrow = symbol "arrow"
let sharp fmt () = F.fprintf fmt "\\#"
let openbrace fmt () = F.fprintf fmt "\\{"
let closebrace fmt () = F.fprintf fmt "\\}"

let indent fmt d = if d > 0 then latex "indent" fmt (string_of_int d)

let pp_opt p fmt =
  function
  | None -> ()
  | Some x -> p fmt x

let pp_paren p fmt =
  F.fprintf fmt "(%a)" p

let pp_cc =
    pp_opt (fun fmt x -> F.fprintf fmt "%a " kw (match x with `Inline -> "inline" | `Export -> "export"))

let pp_var fmt x =
  F.fprintf fmt "%s" (L.unloc x)

let pp_op2 fmt =
  let f s p = F.fprintf fmt "%s%a" p ptype (string_of_castop s) in
  let ret s = F.fprintf fmt "%s" s in
  function
  | `Add s -> f s "+"
  | `Sub s -> f s "-"
  | `Mul s -> f s "*"
  | `Div s -> f s "/"
  | `Mod s -> f s "\\%"
  | `And -> ret "&&"
  | `Or -> ret "||"
  | `BAnd s -> f s "&"
  | `BOr s -> f s "|"
  | `BXOr s -> f s "\\textasciicircum{}"
  | `ShR s -> f s ">{}>"
  | `ShL s -> f s "<{}<"
  | `Eq s -> f s "=="
  | `Neq s -> f s "!="
  | `Lt s -> f s "<"
  | `Le s -> f s "<="
  | `Gt s -> f s ">"
  | `Ge s -> f s ">="
  | `Raw -> ret ""

type prio =
  | Pmin
  | Pternary
  | Por
  | Pand
  | Pbwor
  | Pbwxor
  | Pbwand
  | Pcmpeq
  | Pcmp
  | Pshift
  | Padd
  | Pmul
  | Punary
  | Pbang
  | Pmax

let prio_of_op1 =
  function
  | `Cast _
  | `Not _ -> Pbang
  | `Neg _ -> Punary

let prio_of_op2 =
  function
  | `Add _ | `Sub _ -> Padd
  | `Mul _ | `Div _ | `Mod _ -> Pmul
  | `And -> Pand
  | `Or -> Por
  | `BAnd _ -> Pbwand
  | `BOr _ -> Pbwor
  | `BXOr _ -> Pbwxor
  | `ShR _ | `ShL _ -> Pshift
  | `Eq _ | `Neq _ -> Pcmpeq
  | `Lt _ | `Le _ | `Gt _ | `Ge _
    -> Pcmp

let optparent fmt ctxt prio p =
  if prio < ctxt then F.fprintf fmt "%s" p

let string_of_wsize w = Format.sprintf "u%d" (bits_of_wsize w)

let pp_svsize fmt (vs,s,ve) = 
  Format.fprintf fmt "%d%s%d"
    (int_of_vsize vs) (suffix_of_sign s) (bits_of_vesize ve)

let pp_space fmt _ =
  F.fprintf fmt " "

let rec pp_expr_rec prio fmt pe =
  match L.unloc pe with
  | PEParens e -> pp_expr_rec prio fmt e
  | PEVar x -> pp_var fmt x
  | PEGet (aa, ws, x, e, len) -> 
    pp_arr_access fmt aa ws x e len
  | PEFetch me -> pp_mem_access fmt me 
  | PEpack (vs,es) ->
    F.fprintf fmt "(%a)[@[%a@]]" pp_svsize vs (pp_list ",@ " pp_expr) es
  | PEBool b -> F.fprintf fmt "%s" (if b then "true" else "false")
  | PEInt i -> F.fprintf fmt "%a" Bigint.pp_print i
  | PECall (f, args) -> F.fprintf fmt "%a(%a)" pp_var f (pp_list ", " pp_expr) args
  | PEPrim (f, args) -> F.fprintf fmt "%a%a(%a)" sharp () pp_var f (pp_list ", " pp_expr) args
  | PEOp1 (op, e) ->
    let p = prio_of_op1 op in
    optparent fmt prio p "(";
    F.fprintf fmt "%s %a" (string_of_peop1 op) (pp_expr_rec p) e;
    optparent fmt prio p ")"
  | PEOp2 (op, (e, r)) ->
    let p = prio_of_op2 op in
    optparent fmt prio p "(";
    F.fprintf fmt "%a %a %a" (pp_expr_rec p) e pp_op2 op (pp_expr_rec p) r;
    optparent fmt prio p ")"
  | PEIf (e1, e2, e3) ->
    let p = Pternary in
    optparent fmt prio p "(";
    F.fprintf fmt "%a ? %a : %a" (pp_expr_rec p) e1 (pp_expr_rec p) e2 (pp_expr_rec p) e3;
    optparent fmt prio p ")"

and pp_mem_access fmt (ty,x,e) = 
  let pp_e fmt e = 
    match e with
    | None -> ()
    | Some (`Add, e) -> Format.fprintf fmt " + %a" pp_expr e 
    | Some (`Sub, e) -> Format.fprintf fmt " - %a" pp_expr e in
  F.fprintf fmt "%a[%a%a]" (pp_opt (pp_paren pp_ws)) ty pp_var x pp_e e
  
and pp_type fmt ty =
  match L.unloc ty with
  | TBool -> F.fprintf fmt "%a" ptype "bool"
  | TInt -> F.fprintf fmt "%a" ptype "int"
  | TWord w -> pp_ws fmt w
  | TArray (w, e) -> F.fprintf fmt "%a[%a]" ptype (string_of_wsize w) pp_expr e

and pp_ws fmt w = F.fprintf fmt "%a" ptype (string_of_wsize w)
and pp_expr fmt e = pp_expr_rec Pmin fmt e

and pp_arr_access fmt aa ws x e len= 
 let pp_olen fmt len = 
   match len with
   | None -> ()
   | Some len -> Format.fprintf fmt " : %a" pp_expr len in
 F.fprintf fmt "%a%s[%a%a%a%a]" 
    pp_var x 
    (if aa = Warray_.AAdirect then "." else "")
    (pp_opt pp_ws) ws (pp_opt pp_space) ws pp_expr e pp_olen len

let pp_writable = function
  | Some `Constant -> " const"
  | Some `Writable -> " mut"
  | None  -> ""

let pp_pointer = function
  | `Pointer w-> pp_writable w ^ " ptr"
  | `Direct  -> ""
  
  
let pp_storage fmt s =
  latex "storageclass" fmt
    (match s with
     | `Reg ptr -> "reg" ^ (pp_pointer ptr)
     | `Stack ptr -> "stack" ^ (pp_pointer ptr)
     | `Inline -> "inline"
     | `Global -> "global")

let pp_sto_ty fmt (sto, ty) =
  F.fprintf fmt "%a %a" pp_storage sto pp_type ty

let pp_arg fmt (sty, x) =
  F.fprintf
    fmt
    "%a %a"
    pp_sto_ty sty
    pp_var x

let pp_aarg fmt (_a,(sty, x)) =
  F.fprintf
    fmt
    "%a %a"
    pp_sto_ty sty
    pp_var x


let pp_args fmt (sty, xs) =
  F.fprintf
    fmt
    "%a %a"
    pp_sto_ty sty
    (pp_list ", " pp_var) xs

let pp_rty =
  pp_opt
    (fun fmt tys ->
       F.fprintf fmt " %a %a"
         arrow ()
         (pp_list ", " pp_sto_ty) tys)

let pp_inbraces depth p fmt x =
  openbrace fmt ();
  F.fprintf fmt eol;
  p fmt x;
  F.fprintf fmt eol;
  indent fmt depth;
  closebrace fmt ()

let pp_lv fmt x =
  match L.unloc x with
  | PLIgnore -> F.fprintf fmt "_"
  | PLVar x -> pp_var fmt x
  | PLArray (aa, ws, x, e, len) -> pp_arr_access fmt aa ws x e len
  | PLMem me -> pp_mem_access fmt me 

let pp_eqop fmt op =
  F.fprintf fmt "%a=" pp_op2 op

let pp_sidecond fmt =
  F.fprintf fmt " %a %a" kw "if" pp_expr

let rec pp_instr depth fmt p =
  indent fmt depth;
  match L.unloc p with
  | PIArrayInit x -> F.fprintf fmt "%a (%a);" kw "arrayinit" pp_var x
  | PIAssign (lvs, op, e, cnd) ->
    begin match lvs with
    | [] -> ()
    | _ -> F.fprintf fmt "%a %a " (pp_list ", " pp_lv) lvs pp_eqop op end;
    F.fprintf fmt "%a%a;"
      pp_expr e
      (pp_opt pp_sidecond) cnd
  | PIIf (b, th, el) ->
    begin
    F.fprintf fmt "%a %a %a"
      kw "if"
      pp_expr b
      (pp_block depth) th;
    match el with
    | Some el -> F.fprintf fmt " %a %a" kw "else" (pp_block depth) el
    | None -> () end
  | PIFor (i, (d, lo, hi), body) ->
    F.fprintf fmt "%a %a = %a %a %a %a"
      kw "for"
      pp_var i
      pp_expr lo
      kw (match d with `Down -> "downto" | `Up -> "to")
      pp_expr hi
      (pp_inbraces depth (pp_list eol (pp_instr (depth + 1)))) (L.unloc body)
  | PIWhile (_, pre, b, body) ->
    F.fprintf fmt "%a %a (%a) %a"
      kw "while"
      (pp_opt (pp_block depth)) pre
      pp_expr b
      (pp_opt (pp_block depth)) body

and pp_block depth fmt blk =
  pp_inbraces depth (pp_list eol (pp_instr (depth + 1))) fmt (L.unloc blk)

let pp_funbody fmt { pdb_vars ; pdb_instr ; pdb_ret } =
  List.iter (fun d -> F.fprintf fmt "%a%a;" indent 1 pp_args d; F.fprintf fmt eol) pdb_vars;
  pp_list eol (pp_instr 1) fmt pdb_instr;
  pp_opt (
    fun fmt ret ->
      F.fprintf fmt eol;
      F.fprintf fmt "%a%a %a;"
        indent 1
        kw "return"
        (pp_list ", " pp_var) ret;
  ) fmt pdb_ret

let pp_fundef fmt {pdf_cc ; pdf_name ; pdf_args ; pdf_rty ; pdf_body } =
  F.fprintf
    fmt
    "%a%a %a(%a)%a %a"
    pp_cc pdf_cc
    kw "fn"
    dname (L.unloc pdf_name)
    (pp_list ", " pp_aarg) pdf_args
    pp_rty pdf_rty
    (pp_inbraces 0 pp_funbody) pdf_body;
  F.fprintf fmt eol

let pp_param fmt { ppa_ty ; ppa_name ; ppa_init } =
  F.fprintf fmt "%a %a %a = %a;"
    kw "param"
    pp_type ppa_ty
    dname (L.unloc ppa_name)
    pp_expr ppa_init;
  F.fprintf fmt eol

let pp_pgexpr fmt = function
  | GEword e -> pp_expr fmt e 
  | GEarray es -> 
    Format.fprintf fmt "{@[%a@]}" (pp_list ",@ " pp_expr) es

let pp_global fmt { pgd_type ; pgd_name ; pgd_val } =
  F.fprintf fmt "%a %a = %a;"
    pp_type pgd_type
    dname (L.unloc pgd_name)
    pp_pgexpr pgd_val;
  F.fprintf fmt eol

let pp_pitem fmt pi =
  match L.unloc pi with
  | PFundef f -> pp_fundef fmt f
  | PParam p  -> pp_param fmt p
  | PGlobal g -> pp_global fmt g
  | Pexec _   -> ()
  | Prequire s -> 
    Format.fprintf fmt "require @[<hov>%a@]"
      (pp_list "@ " (fun fmt s -> Format.fprintf fmt "\"%s\"" (L.unloc s)))
      s

let pp_prog fmt prog =
  F.fprintf fmt "%a" (pp_list "\n" pp_pitem) prog
