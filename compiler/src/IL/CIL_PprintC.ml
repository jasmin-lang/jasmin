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

(* * Pretty-print Coq language in concrete syntax *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open CIL_Utils
open Compiler_util
open Util
open Dmasm_expr
open Dmasm_type
open Dmasm_var

module F   = Format

(* ** Pretty printing for basic types
 * ------------------------------------------------------------------------ *)

let pp_clist sep pp_elem fmt clist =
  pp_list sep pp_elem fmt (list_of_clist clist)

let pp_pos fmt pos =
  F.fprintf fmt "%i" (int_of_pos pos)

let pp_var_name fmt vname =
  F.fprintf fmt "%S" (string_of_string0 (Obj.magic vname))

let pp_coqZ fmt cz =
  pp_string fmt (Big_int.string_of_big_int (bi_of_coqZ cz))

let pp_cbool fmt cb =
  pp_bool fmt (bool_of_cbool cb)

let pp_minfo pp1 fmt () =
  if true then pp1 fmt else pp_string fmt ""

(* ** Pretty printing
 * ------------------------------------------------------------------------ *)

let pp_ty fmt t =
  match t with
  | Coq_sbool     -> pp_string fmt "sbool"
  | Coq_sint      -> pp_string fmt "sint"
  | Coq_sarr(pos) -> F.fprintf fmt "sarr %i" (int_of_pos pos)
  | Coq_sword     -> pp_string fmt "sword"

let pp_inline fmt inl =
  pp_string fmt
    (match inl with
    | InlineFun   -> "InlineFun"
    | DoNotInline -> "DoNotInline")

let pp_atag fmt inl =
  pp_string fmt
    (match inl with
    | AT_keep   -> "AT_keep"
    | AT_inline -> "AT_inline"
    | AT_rename -> "AT_rename")

let pp_sop2 fmt sop2 =
  pp_string fmt
    (match sop2 with
    | Oand -> "Oand"
    | Oor  -> "Oor"
    | Oadd -> "Oadd"
    | Omul -> "Omul"
    | Osub -> "Osub"
    | Oeq  -> "Oeq"
    | Oneq -> "Oneq"
    | Olt  -> "Olt"
    | Ole  -> "Ole"
    | Ogt  -> "Ogt"
    | Oge  -> "Oge")

let pp_sopn fmt sopn =
  pp_string fmt
    (match sopn with
    | Olnot     -> "Olnot"
    | Oxor      -> "Oxor"
    | Oland     -> "Oland"
    | Olor      -> "Olor"
    | Olsr      -> "Olsr"
    | Olsl      -> "Olsl"
    | Oif       -> "Oif"
    | Omulu     -> "Omulu"
    | Omuli     -> "Omuli"
    | Oaddcarry -> "Oaddcarry"
    | Osubcarry -> "Osubcarry")

let pp_var_info fmt vi =
  let open Var in
  let { v_var ; v_info } = vi in
  F.fprintf fmt "(VarI (Var %a %a) %a)"
    pp_ty v_var.vtype
    pp_var_name v_var.vname
    (pp_minfo (fun fmt -> pp_pos fmt v_info)) ()

let rec pp_pexpr fmt pe =
  match pe with
  | Pconst(cz)          -> F.fprintf fmt "(Pconst %a)" pp_coqZ cz
  | Pbool(b)            -> F.fprintf fmt "(Pbool %a)" pp_cbool b
  | Pcast(pe)           -> F.fprintf fmt "(Pcast %a)" pp_pexpr pe
  | Pvar(vi)            -> F.fprintf fmt "(Pvar %a)" pp_var_info vi
  | Pget(vi,pe)         -> F.fprintf fmt "(Pget %a %a)" pp_var_info vi pp_pexpr pe
  | Pload(vi,pe)        -> F.fprintf fmt "(Pload %a %a)" pp_var_info vi pp_pexpr pe
  | Pnot(pe)            -> F.fprintf fmt "(Pnot %a)" pp_pexpr pe
  | Papp2(sop2,pe1,pe2) -> F.fprintf fmt "(Papp2 %a %a %a)" pp_sop2 sop2 pp_pexpr pe1 pp_pexpr pe2

let pp_rval fmt rv =
  match rv with
  | Rnone(i)     -> F.fprintf fmt "(Rnone %a)" pp_pos i
  | Rvar(vi)     -> F.fprintf fmt "(Rvar %a)" pp_var_info vi
  | Rmem(vi,pe)  -> F.fprintf fmt "(Rmem %a %a)" pp_var_info vi pp_pexpr pe
  | Raset(vi,pe) -> F.fprintf fmt "(Raset %a %a)" pp_var_info vi pp_pexpr pe

let pp_ret_type fmt res =
  F.fprintf fmt "[:: %a]" (pp_clist "; " pp_var_info) res

let pp_range fmt rng =
  let (dlb,ub) = pair_of_cpair rng in
  let (dir,lb) = pair_of_cpair dlb in
  F.fprintf fmt "(%s, %a, %a)"
    (match dir with UpTo -> "UpTo" | DownTo -> "DownTo")
    pp_pexpr lb
    pp_pexpr ub

let rec pp_instr_r fmt instr =
  match instr with
  | Cassgn(rv,atag,pe) ->
    F.fprintf fmt "Cassgn %a %a %a" pp_rval rv pp_atag atag pp_pexpr pe
  | Copn(rvs,sopn,pes) ->
    F.fprintf fmt "Copn [:: %a] %a [:: %a]" (pp_clist "; " pp_rval) rvs pp_sopn sopn (pp_clist "; " pp_pexpr) pes
  | Cif(pe,instrs_if,instrs_else) ->
    F.fprintf fmt "Cif %a[:: @[<v 0>%a@]@\n] [:: @[<v 0>%a@]]"
      pp_pexpr pe pp_instrs instrs_if pp_instrs instrs_else
  | Cfor(vi,rng,instrs) ->
    F.fprintf fmt "Cfor %a %a [:: @[<v 0>%a@]]"
      pp_var_info vi pp_range rng pp_instrs instrs
  | Cwhile(pe,instrs) ->
    F.fprintf fmt "Cwhile %a [:: @[<v 0>%a@]]" pp_pexpr pe pp_instrs instrs
  | Ccall(inl,rvs,fname,pes) ->
    F.fprintf fmt "Ccall %a [:: %a] %a [:: %a]"
      pp_inline inl
      (pp_clist "; " pp_rval) rvs
      pp_pos fname
      (pp_clist "; " pp_pexpr) pes


and pp_instr fmt instr =
  let MkI(iinfo,instr) = instr in
  F.fprintf fmt "MkI %a (%a)"
    (pp_minfo (fun fmt -> pp_pos fmt iinfo)) ()
    pp_instr_r instr

and pp_instrs fmt instrs =
  pp_clist ";@\n" pp_instr fmt instrs

let pp_fundef fmt fd =
  let { f_iinfo ; f_params ; f_body ; f_res } = fd in
  F.fprintf fmt "MkFun %a [:: %a] [::@[<v 0>%a@]@\n] %a"
    pp_pos f_iinfo
    (pp_clist "; " pp_var_info) f_params
    (pp_clist ";@\n" pp_instr) f_body
    pp_ret_type f_res

let pp_named_fun fmt nf =
  let (fn,fd) = pair_of_cpair nf in
  F.fprintf fmt "(%a, %a)" pp_pos fn pp_fundef fd

let prefix = "Require Import dmasm_sem.
Import dmasm_type.
Import dmasm_expr.
Import dmasm_var.
Import seq.

Open Scope string_scope.
Open Scope positive_scope.

Definition program := "

let pp_prog fmt prog =
  F.fprintf fmt "%s[::@\n%a@\n]." prefix (pp_clist ";@\n@\n" pp_named_fun) prog
