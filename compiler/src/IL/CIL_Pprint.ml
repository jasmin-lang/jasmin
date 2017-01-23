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

(* * Pretty-print Coq language *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open CIL_Utils
open Compiler_util
open Util
open Dmasm_expr
open Dmasm_type
open Dmasm_var

module F   = Format
module Lex = ParserUtil.Lexing
module HT  = Hashtbl

let show_vinfo = ref true

(* ** Pretty printing for basic types
 * ------------------------------------------------------------------------ *)

let pp_clist sep pp_elem fmt clist =
  pp_list sep pp_elem fmt (list_of_clist clist)

let pp_pos fmt pos =
  F.fprintf fmt "%i" (int_of_pos pos)

let pp_var_name fmt vname =
  pp_string fmt (string_of_string0 (Obj.magic vname))
    
let pp_coqZ fmt cz =
  pp_string fmt (Big_int.string_of_big_int (bi_of_coqZ cz))

let pp_cbool fmt cb =
  pp_bool fmt (bool_of_cbool cb)

let pp_minfo pp1 fmt () =
  if !show_vinfo then pp1 fmt else pp_string fmt ""

(* ** Pretty printing
 * ------------------------------------------------------------------------ *)

let pp_ty fmt t =
  match t with
  | Coq_sbool     -> pp_string fmt "bool"
  | Coq_sint      -> pp_string fmt "int"
  | Coq_sarr(pos) -> F.fprintf fmt "u64[%i]" (int_of_pos pos)
  | Coq_sword     -> pp_string fmt "u64"

let pp_inline fmt inl =
  pp_string fmt 
    (match inl with
    | InlineFun   -> "inline"
    | DoNotInline -> "noinline")

let pp_atag fmt inl =
  pp_string fmt 
    (match inl with
    | AT_keep   -> "keep"
    | AT_inline -> "inline"
    | AT_rename -> "rename")

let pp_sop2 fmt sop2 =
  pp_string fmt
    (match sop2 with
    | Oand -> "/\\"
    | Oor  -> "\\/"
    | Oadd -> "+"
    | Omul -> "*"
    | Osub -> "-"
    | Oeq  -> "="
    | Oneq -> "!="
    | Olt  -> "<"
    | Ole  -> "<="
    | Ogt  -> ">"
    | Oge  -> ">=")

let pp_sopn fmt sopn =
  pp_string fmt
    (match sopn with
    | Olnot     -> "lnot"
    | Oxor      -> "xor"
    | Oland     -> "land"
    | Olor      -> "lor"
    | Olsr      -> "lsr"
    | Olsl      -> "lsf"
    | Oif       -> "if"
    | Omulu     -> "mulu"
    | Omuli     -> "muli"
    | Oaddcarry -> "adc"
    | Osubcarry -> "subc")

let pp_var_info fmt vi =
  F.fprintf fmt "v%a%a:%a"
    pp_var_name vi.v_var.Var.vname
    (pp_minfo (fun fmt -> F.fprintf fmt ".%a" pp_pos vi.v_info)) ()
    pp_ty (vi.v_var.Var.vtype)

let rec pp_pexpr fmt pe =
  match pe with
  | Pconst(cz)          -> pp_coqZ fmt cz
  | Pbool(b)            -> pp_cbool fmt b
  | Pcast(pe)           -> F.fprintf fmt "(%a as u64)" pp_pexpr pe
  | Pvar(vi)            -> pp_var_info fmt vi
  | Pget(vi,pe)         -> F.fprintf fmt "%a[%a]" pp_var_info vi pp_pexpr pe
  | Pload(vi,pe)        -> F.fprintf fmt "MEM[%a + %a]" pp_var_info vi pp_pexpr pe
  | Pnot(pe)            -> F.fprintf fmt "!(%a)" pp_pexpr pe
  | Papp2(sop2,pe1,pe2) -> F.fprintf fmt "(%a %a %a)" pp_pexpr pe1 pp_sop2 sop2 pp_pexpr pe2

let pp_rval fmt rv =
  match rv with
  | Rnone(i)     -> F.fprintf fmt "_#%a" pp_pos i
  | Rvar(vi)     -> pp_var_info fmt vi
  | Rmem(vi,pe)  -> F.fprintf fmt "MEM[%a + %a]" pp_var_info vi pp_pexpr pe
  | Raset(vi,pe) -> F.fprintf fmt "%a[%a]" pp_var_info vi pp_pexpr pe

let pp_ret_type fmt res =
  let rtypes = List.map ~f:(fun vi -> vi.v_var.Var.vtype) @@ list_of_clist res in
  if rtypes=[] then (
    pp_string fmt ""
  ) else (
    F.fprintf fmt "-> %a " (pp_list " * " pp_ty) rtypes
  )

let pp_range fmt rng =
  let (dlb,ub) = pair_of_cpair rng in
  let (dir,lb) = pair_of_cpair dlb in
  F.fprintf fmt "%a .. %a%s"
    pp_pexpr lb
    pp_pexpr ub
    (if dir=DownTo then "[rev]" else "")

let rec pp_instr_r fmt instr =
  match instr with
  | Cassgn(rv,atag,pe) ->
    F.fprintf fmt "%a =[%a] %a" pp_rval rv pp_atag atag pp_pexpr pe
  | Copn(rvs,sopn,pes) ->
    F.fprintf fmt "%a = %a(%a)" (pp_clist "," pp_rval) rvs pp_sopn sopn (pp_clist ", " pp_pexpr) pes
  | Cif(pe,instrs_if,instrs_else) ->
    F.fprintf fmt "if %a {@\n  @[<v 0>%a@]@\n} else {@\n  @[<v 0>%a@]@\n}"
      pp_pexpr pe pp_instrs instrs_if pp_instrs instrs_else
  | Cfor(vi,rng,instrs)           ->
    F.fprintf fmt "for %a in %a {@\n  @[<v 0>%a@]@\n}"
      pp_var_info vi pp_range rng pp_instrs instrs
  | Cwhile(pe,instrs)             ->
    F.fprintf fmt "while %a {@\n  @[<v 0>%a@]@\n}" pp_pexpr pe pp_instrs instrs
  | Ccall(inl,rvs,fname,pes)      ->
    F.fprintf fmt "%a = %a[%a](%a)"
      (pp_clist "," pp_rval) rvs
      pp_pos fname
      pp_inline inl
      (pp_clist "," pp_pexpr) pes


and pp_instr fmt instr =
  let MkI(iinfo,instr) = instr in
  F.fprintf fmt "%a;%a"
    pp_instr_r instr
    (pp_minfo (fun fmt -> F.fprintf fmt "// %a" pp_pos iinfo)) ()

and pp_instrs fmt instrs =
  pp_clist "@\n" pp_instr fmt instrs

let pp_fundef fmt fd =
  F.fprintf fmt "(%a) %a{@\n  @[<v 0>%a@\nreturn %a;@]@\n}"
    (pp_clist ", " pp_var_info) fd.f_params
    pp_ret_type fd.f_res
    (pp_clist "@\n" pp_instr) fd.f_body
    (pp_clist ", " pp_var_info) fd.f_params

let pp_named_fun fmt nf =
  let (fn,fd) = pair_of_cpair nf in
  F.fprintf fmt "fn %a %a" pp_pos fn pp_fundef fd

let pp_prog fmt prog =
  pp_clist "@\n@\n" pp_named_fun fmt prog

(* ** Pretty printing errors
 * ------------------------------------------------------------------------ *)

let rec pp_error fmt e =
  match e with
  | Cerr_arr_exp_v(rv1,rv2) ->
    F.fprintf fmt "arr_exp_v: rval1=%a, rval2=%a" pp_rval rv1 pp_rval rv2
  | Cerr_stk_alloc(s) ->
    F.fprintf fmt "stk_alloc: %s" (string_of_string0 s)
  | Cerr_varalloc(vi1,vi2,s) ->
    F.fprintf fmt "varalloc: vi1=%a, vi2=%a, msg=%s"
      pp_var_info vi1 pp_var_info vi2 (string_of_string0 s)
  | Cerr_inline(_v1,_v2) ->
    F.fprintf fmt "inline: v1=?, v2=?" (* how to print Sv.t *)
  | Cerr_Loop(s) ->
    F.fprintf fmt "loop: %s" (string_of_string0 s)
  | Cerr_fold2(s) ->
    F.fprintf fmt "loop: %s" (string_of_string0 s)
  | Cerr_neqdir(s) ->
    F.fprintf fmt "neqdir: %s" (string_of_string0 s)
  | Cerr_in_fun(fe) ->
    F.fprintf fmt "in_fun: %a" pp_fun_error fe
  | Cerr_arr_exp(pe1,pe2) ->
    F.fprintf fmt "arr_exp: pexpr1=%a, pexpr2=%a" pp_pexpr pe1 pp_pexpr pe2
  | Cerr_neqop2(so1,so2,s) ->
    F.fprintf fmt "neqop2: sop2_1=%a, sop2_2=%a, msg=%s"
      pp_sop2 so1 pp_sop2 so2 (string_of_string0 s)  
  | Cerr_neqop(so1,so2,s) ->
    F.fprintf fmt "neqop: sop2_1=%a, sop2_2=%a, msg=%s"
      pp_sopn so1 pp_sopn so2 (string_of_string0 s)
  | Cerr_unknown_fun(fn,s) ->
    F.fprintf fmt "unknown_fun: funname=%a, msg=%s"
      pp_pos fn (string_of_string0 s)
  | Cerr_neqexpr(pe1,pe2,s) ->
    F.fprintf fmt "neqexpr: pexpr1=%a, pexpr2=%a, msg=%s"
      pp_pexpr pe1 pp_pexpr pe2 (string_of_string0 s)    
  | Cerr_neqrval(rv1,rv2,s) ->
    F.fprintf fmt "neqrval: rval1=%a, rval2=%a, msg=%s"
      pp_rval rv1 pp_rval rv2 (string_of_string0 s)
  | Cerr_neqfun(fn1,fn2,s) ->
    F.fprintf fmt "neqfun: fn1=%a, fn2=%a, msg=%s"
      pp_pos fn1 pp_pos fn2 (string_of_string0 s)    
  | Cerr_neqinstr(i1,i2,s) ->
    F.fprintf fmt "neqinstr: instr1=%a, instr2=%a, msg=%s"
      pp_instr_r i1 pp_instr_r i2 (string_of_string0 s)    

and pp_fun_error fmt fe =
  match fe with
  | Ferr_in_body(fn1,fn2,Datatypes.Coq_pair(i_info (*:instr_info*),e_msg (*:error_msg*))) ->
    F.fprintf fmt "fun_error.in_body: funname1=%a, funname2=%a, instr_info=%a, error_msg=%a"
      pp_pos fn1 pp_pos fn2 pp_pos i_info pp_error e_msg
  | Ferr_neqfun(fn1,fn2) ->
    F.fprintf fmt "fun_error.neqfun: funname1=%a, funname2=%a" pp_pos fn1 pp_pos fn2
  | Ferr_neqprog ->
    F.fprintf fmt "fun_error.neqprog"
  | Ferr_loop ->
    F.fprintf fmt "fun_error.loop"
