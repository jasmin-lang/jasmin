(* * Pretty-print Jasmin program (concrete syntax) as LATEX fragments *)

open Utils
open Annotations
open Syntax

module F = Format
module L = Location

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
  | `ROR s -> f s ">{}>r"
  | `ROL s -> f s "<{}<r"
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
  | `ShR _  | `ShL _ | `ROR _ | `ROL _ -> Pshift
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

let pp_attribute_key fmt s =
  if String.for_all (function 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false) s
  then F.fprintf fmt "%s" s
  else F.fprintf fmt "%S" s

let pp_aligned fmt = function
  | None -> ()
  | Some `Aligned -> F.fprintf fmt "%aaligned " sharp ()
  | Some `Unaligned -> F.fprintf fmt "%aunaligned " sharp ()

let rec pp_simple_attribute fmt a = 
  match L.unloc a with 
  | Aint i -> Z.pp_print fmt i
  | Aid s | Astring s -> Format.fprintf fmt "%s" s
  | Aws ws -> Format.fprintf fmt "%a" ptype (string_of_wsize ws)
  | Astruct struct_ -> Format.fprintf fmt "(%a)" pp_struct_attribute struct_

and pp_struct_attribute fmt struct_ =
  Format.fprintf fmt "@[<hov 2>%a@]" (pp_list ",@ " pp_annotation) struct_

and pp_attribute fmt = function
  | Some a -> Format.fprintf fmt "@ =@ %a" pp_simple_attribute a
  | None -> ()

and pp_annotation fmt (id, atr) =
  Format.fprintf fmt "@[%a%a@]" pp_attribute_key (L.unloc id) pp_attribute atr

let pp_top_annotations fmt annot =
  match annot with
  | []  -> ()
  | [a] -> Format.fprintf fmt "@[%a%a\\\\@]\n" sharp () pp_annotation a
  | _   -> Format.fprintf fmt "#[%a]" pp_struct_attribute annot

let rec pp_expr_rec prio fmt pe =
  match L.unloc pe with
  | PEParens e -> pp_expr_rec prio fmt e
  | PEVar x -> pp_var fmt x
  | PEGet (al, aa, ws, x, e, len) ->
    pp_arr_access fmt al aa ws x e len
  | PEFetch me -> pp_mem_access fmt me
  | PEpack (vs,es) ->
    F.fprintf fmt "(%a)[@[%a@]]" pp_svsize vs (pp_list ",@ " pp_expr) es
  | PEBool b -> F.fprintf fmt "%s" (if b then "true" else "false")
  | PEInt i -> F.fprintf fmt "%a" Z.pp_print i
  | PECall (f, args) -> F.fprintf fmt "%a(%a)" pp_var f (pp_list ", " pp_expr) args
  | PECombF (f, args) -> 
    F.fprintf fmt "%a(%a)" pp_var f (pp_list ", " pp_expr) args
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

and pp_mem_access fmt (al, ty,x,e) =
  let pp_e fmt e = 
    match e with
    | None -> ()
    | Some (`Add, e) -> Format.fprintf fmt " + %a" pp_expr e 
    | Some (`Sub, e) -> Format.fprintf fmt " - %a" pp_expr e in
  F.fprintf fmt "%a[%a%a%a]" (pp_opt (pp_paren pp_ws)) ty pp_aligned al pp_var x pp_e e
  
and pp_type fmt ty =
  match L.unloc ty with
  | TBool -> F.fprintf fmt "%a" ptype "bool"
  | TInt -> F.fprintf fmt "%a" ptype "int"
  | TWord w -> pp_ws fmt w
  | TArray (w, e) -> F.fprintf fmt "%a[%a]" ptype (string_of_wsize w) pp_expr e

and pp_ws fmt w = F.fprintf fmt "%a" ptype (string_of_wsize w)
and pp_expr fmt e = pp_expr_rec Pmin fmt e

and pp_arr_access fmt al aa ws x e len=
 let pp_olen fmt len = 
   match len with
   | None -> ()
   | Some len -> Format.fprintf fmt " : %a" pp_expr len in
 F.fprintf fmt "%a%s[%a%a%a%a%a]"
    pp_var x
    (if aa = Warray_.AAdirect then "." else "")
    pp_aligned (Option.bind len (fun _ -> al))
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
     | `Reg(ptr) -> "reg" ^ (pp_pointer ptr)
     | `Stack ptr -> "stack" ^ (pp_pointer ptr)
     | `Inline -> "inline"
     | `Global -> "global")

let pp_sto_ty fmt (sto, ty) =
  F.fprintf fmt "%a %a" pp_storage sto pp_type ty

let pp_args fmt (sty, xs) =
  F.fprintf
    fmt
    "%a %a"
    pp_sto_ty sty
    (pp_list " " pp_var) xs

let pp_rty =
  pp_opt
    (fun fmt tys ->
       F.fprintf fmt " %a %a"
         arrow ()
         (pp_list ", " (fun fmt (_annot, ty) -> pp_sto_ty fmt ty)) tys)

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
  | PLArray (al, aa, ws, x, e, len) -> pp_arr_access fmt al aa ws x e len
  | PLMem me -> pp_mem_access fmt me 

let pp_eqop fmt op =
  F.fprintf fmt "%a=" pp_op2 op

let pp_sidecond fmt =
  F.fprintf fmt " %a %a" kw "if" pp_expr

let pp_vardecls fmt d =
  F.fprintf fmt "%a;" pp_args d

let rec pp_instr depth fmt (annot, p) =
  if annot <> [] then F.fprintf fmt "%a%a" indent depth pp_top_annotations annot;
  indent fmt depth;
  match L.unloc p with
  | PIdecl d -> pp_vardecls fmt d 
  | PIArrayInit x -> F.fprintf fmt "%a (%a);" kw "arrayinit" pp_var x
  | PIAssign ((pimp,lvs), op, e, cnd) ->
    begin match pimp, lvs with
    | None, [] ->
       (* Special case for Primitive calls without return value *)
       begin
         assert (op = `Raw);
         match L.unloc e with
         | PEPrim _ -> F.fprintf fmt "() %a" pp_eqop op
         | _ -> ()
       end
    | None, _ -> F.fprintf fmt "%a %a " (pp_list ", " pp_lv) lvs pp_eqop op 
    | Some pimp, _ ->
      F.fprintf fmt "?%a%a%a, %a %a "
        openbrace ()
        pp_struct_attribute (L.unloc pimp)
        closebrace ()
        (pp_list ", " pp_lv) lvs 
        pp_eqop op
      
    end;
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
     let from, direction, limit =
       match d with
       | `Down -> hi, "downto", lo
       | `Up -> lo, "to", hi
     in
    F.fprintf fmt "%a %a = %a %a %a %a"
      kw "for"
      pp_var i
      pp_expr from
      kw direction
      pp_expr limit
      (pp_inbraces depth (pp_list eol (pp_instr (depth + 1)))) (L.unloc body)

  | PIWhile (pre, b, body) ->
    F.fprintf fmt "%a %a (%a) %a"
      kw "while"
      (pp_opt (pp_block depth)) pre
      pp_expr b
      (pp_opt (pp_block depth)) body

and pp_block depth fmt blk =
  pp_inbraces depth (pp_list eol (pp_instr (depth + 1))) fmt (L.unloc blk)

let pp_funbody fmt { pdb_instr ; pdb_ret } =
  pp_list eol (pp_instr 1) fmt pdb_instr;
  pp_opt (
    fun fmt ret ->
      F.fprintf fmt eol;
      F.fprintf fmt "%a%a %a;"
        indent 1
        kw "return"
        (pp_list ", " pp_var) ret;
  ) fmt pdb_ret

let pp_fundef fmt { pdf_cc ; pdf_name ; pdf_args ; pdf_rty ; pdf_body ; pdf_annot } =
  F.fprintf
    fmt
    "%a%a%a %a(%a)%a %a"
    pp_top_annotations pdf_annot
    pp_cc pdf_cc
    kw "fn"
    dname (L.unloc pdf_name)
    (pp_list ", " (fun fmt (_annot, d) -> pp_args fmt d)) pdf_args
    pp_rty pdf_rty
    (pp_inbraces 0 pp_funbody) pdf_body;
  F.fprintf fmt eol

let pp_string fmt s =
  s |> L.unloc |> F.asprintf "%S" |> String.iter @@ function
  | '\\' -> F.fprintf fmt "\\textbackslash{}"
  | '\'' -> F.fprintf fmt "\\textquotesingle{}"
  | '"' -> F.fprintf fmt "\\textquotedbl{}"
  | c -> F.fprintf fmt "%c" c

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
    F.fprintf fmt "%a @[%a@] %a"
      openbrace ()
      (pp_list ",@ " pp_expr) es
      closebrace ()
  | GEstring e -> pp_string fmt e

let pp_global fmt { pgd_type ; pgd_name ; pgd_val } =
  F.fprintf fmt "%a %a = %a;"
    pp_type pgd_type
    dname (L.unloc pgd_name)
    pp_pgexpr pgd_val;
  F.fprintf fmt eol

let pp_path fmt s =
  F.fprintf fmt "%S " (L.unloc s)

let rec pp_pitem fmt pi =
  match L.unloc pi with
  | PFundef f -> pp_fundef fmt f
  | PParam p  -> pp_param fmt p
  | PGlobal g -> pp_global fmt g
  | Pexec _   -> ()
  | Prequire (from, s) ->
    let pp_from fmt =
      Option.may (fun name ->
          F.fprintf fmt "%a %s " kw "from" (L.unloc name)) in
      F.fprintf fmt "%a%a " pp_from from kw "require";
      List.iter (pp_path fmt) s;
      F.fprintf fmt eol
  | PNamespace (ns, pis) ->
     (* TODO: ident within namespaces? *)
     F.fprintf fmt "%a %s " kw "namespace" (L.unloc ns);
     openbrace fmt ();
     F.fprintf fmt eol;
     List.iter (pp_pitem fmt) pis;
     F.fprintf fmt eol;
     closebrace fmt ();
     F.fprintf fmt eol

let pp_prog fmt =
  List.iter (F.fprintf fmt "%a" pp_pitem)
