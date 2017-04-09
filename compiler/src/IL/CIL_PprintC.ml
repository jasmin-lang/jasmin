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
module H = Hashtbl
open Core_kernel.Std
open CIL_Utils
open Compiler_util
open Util
open Expr
open Type
open Var0
open BinNums
open IL_Iter
module F   = Format

(* ** Pretty printing for basic types
 * ------------------------------------------------------------------------ *)

let pp_clist sep pp_elem fmt clist =
  pp_list sep pp_elem fmt (list_of_clist clist)

let pp_pos fmt pos =
  F.fprintf fmt "%i%%positive" (int_of_pos pos)

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
  | Coq_sarr(pos) -> F.fprintf fmt "(sarr %i)" (int_of_pos pos)
  | Coq_sword     -> pp_string fmt "sword"

let string_of_ty t =
  match t with
  | Coq_sbool     -> "sbool"
  | Coq_sint      -> "sint"
  | Coq_sarr(pos) -> "sarr"^(string_of_int (int_of_pos pos))
  | Coq_sword     -> "sword"

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

let pp_ass_tag fmt = function
  | AT_keep   -> F.fprintf fmt "::="
  | AT_rename -> F.fprintf fmt ":r="
  | AT_inline -> F.fprintf fmt ":i="
   
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

let infix_sop2 = function
  | Oand -> "&&"
  | Oor  -> "||"
  | Oadd -> "+"
  | Omul -> "*"
  | Osub -> "-"
  | Oeq  -> "=="
  | Oneq -> "!="
  | Olt  -> "<"
  | Ole  -> "<="
  | Ogt  -> ">"
  | Oge  -> ">="

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


type withinfo = 
  | AllInfo
  | OnlyInstr
  | NoInfo


let vars_tbl = H.create 101 

let pp_var_info withinfo fmt vi =
  let open Var in
  let { v_var ; v_info } = vi in
  if withinfo = AllInfo then   
    F.fprintf fmt "(VarI (Var %a %a) %a)"
      pp_ty v_var.vtype
      pp_var_name v_var.vname
      (pp_minfo (fun fmt -> pp_pos fmt v_info)) ()
  else
    let x = 
      try H.find vars_tbl v_var with Not_found -> assert false 
    in
    F.fprintf fmt "%s" x
  
let pp_pexpr withinfo =
  let rec pp_pexpr fmt pe = 
    match pe with
    | Pconst(cz)          -> F.fprintf fmt "%a" pp_coqZ cz
    | Pbool(b)            -> F.fprintf fmt "%a" pp_cbool b
    | Pcast(pe)           -> F.fprintf fmt "(Pcast %a)" pp_pexpr pe
    | Pvar(vi)            -> F.fprintf fmt "%a" (pp_var_info withinfo) vi
    | Pget(vi,pe)         -> 
      F.fprintf fmt "%a.[%a]" (pp_var_info withinfo) vi pp_pexpr pe
    | Pload(vi,pe)        -> 
      F.fprintf fmt "@[<hov 2>(load@ %a@ %a)@]" 
        (pp_var_info withinfo) vi pp_pexpr pe
    | Pnot(pe)            -> F.fprintf fmt "~~ %a" pp_pexpr pe
    | Papp2(sop2,pe1,pe2) -> 
      Format.fprintf fmt "@[<hov 2>(%a %s@ %a)@]" 
        pp_pexpr pe1 (infix_sop2 sop2) pp_pexpr pe2
  in 
  pp_pexpr

let pp_rval withinfo fmt rv =
  match rv with
  | Lnone(i)     -> 
    let i = int_of_pos i in
    if i = 1 then Format.fprintf fmt "__"
    else Format.fprintf fmt "#_ %i" i 
  | Lvar(vi)     -> 
    pp_var_info withinfo fmt vi
  | Lmem(vi,pe)  -> 
    F.fprintf fmt "@[<hov 2>store %a@ %a@]" 
      (pp_var_info withinfo) vi (pp_pexpr withinfo) pe
  | Laset(vi,pe) -> 
    F.fprintf fmt "%a.[%a]" (pp_var_info withinfo) vi (pp_pexpr withinfo) pe

let pp_ret_type withinfo fmt res =
  F.fprintf fmt "[:: %a]" (pp_clist "; " (pp_var_info withinfo) ) res

let pp_range withinfo fmt rng =
  let (dlb,ub) = pair_of_cpair rng in
  let (dir,lb) = pair_of_cpair dlb in
  match dir with
  | UpTo -> 
    F.fprintf fmt "%a to %a" (pp_pexpr withinfo) lb (pp_pexpr withinfo) ub
  | DownTo ->
    F.fprintf fmt "%a downto %a" (pp_pexpr withinfo) ub (pp_pexpr withinfo) lb

let dotdot = function
  | [_] -> "::"
  | _ -> ""

  
let rec pp_instr_r withinfo fmt instr =
  let pp_rval = pp_rval withinfo in
  let pp_pexpr = pp_pexpr withinfo in
  let pp_instrs = pp_instrs withinfo in
  let pp_var_info = pp_var_info withinfo in
  match instr with
  | Cassgn(rv,atag,pe) ->
    F.fprintf fmt "@[%a %a@ %a@]"
      pp_rval rv pp_ass_tag atag pp_pexpr pe
  | Copn(rvs,sopn,pes) ->
    begin match sopn, rvs, pes with
    | Olnot, [x], [e] -> 
      F.fprintf fmt "@[ %a :=@ ! %a@]" pp_rval x pp_pexpr e
    | Oxor, [x], [e1; e2] ->
      F.fprintf fmt "@[ %a :=@ %a ^ %a @]" pp_rval x pp_pexpr e1 pp_pexpr e2
    | Oland, [x], [e1; e2] ->
      F.fprintf fmt "@[ %a :=@ %a & %a @]" pp_rval x pp_pexpr e1 pp_pexpr e2
    | Olor, [x], [e1; e2] ->
      F.fprintf fmt "@[ %a :=@ %a | %a @]" pp_rval x pp_pexpr e1 pp_pexpr e2
    | Olsl, [x], [e1; e2] ->
      F.fprintf fmt "@[ %a :=@ %a << %a @]" pp_rval x pp_pexpr e1 pp_pexpr e2
    | Olsr, [x], [e1; e2] ->
      F.fprintf fmt "@[ %a :=@ %a >> %a @]" pp_rval x pp_pexpr e1 pp_pexpr e2
    | Oif, [x], [e1; e2; e3] ->
      F.fprintf fmt "@[ %a :=@ %a ? %a : %a@]" 
        pp_rval x pp_pexpr e1 pp_pexpr e2 pp_pexpr e3 
    | Omuli, [x], [e1; e2] ->
      F.fprintf fmt "@[ %a :=@ %a * %a @]" pp_rval x pp_pexpr e1 pp_pexpr e2
    | Omulu, [x1; x2], [e1; e2] ->
      F.fprintf fmt "@[ [p %a, %a] :=@ %a * %a @]" 
        pp_rval x1 pp_rval x2 pp_pexpr e1 pp_pexpr e2
    | Oaddcarry, [x1; x2], [e1; e2; c] ->
      F.fprintf fmt "@[ [p %a, %a] :=@ ++(%a, %a, %a) @]" 
        pp_rval x1 pp_rval x2 pp_pexpr e1 pp_pexpr e2 pp_pexpr c
    | Osubcarry, [x1; x2], [e1; e2; c] ->
      F.fprintf fmt "@[ [p %a, %a] :=@ --(%a, %a, %a) @]" 
        pp_rval x1 pp_rval x2 pp_pexpr e1 pp_pexpr e2 pp_pexpr c
    | _, _, _ -> 
      F.fprintf fmt "@[Copn [:: %a]@ %a [:: %a]@]"
        (pp_clist ";@ " pp_rval) rvs 
        pp_sopn sopn
        (pp_clist ";@ " pp_pexpr) pes 
    end    
  | Cif(pe,instrs_if,instrs_else) ->
    begin match instrs_else with
    | [] ->
      F.fprintf fmt "@[<v>If %a then {%s@   @[<v>%a@]@ }@]"
        pp_pexpr pe (dotdot instrs_if) pp_instrs instrs_if 
    | _ ->
      F.fprintf fmt 
        "@[<v>If %a then {%s@   @[<v>%a@]@ } else {%s@   @[<v>%a@]@ }@]"
        pp_pexpr pe (dotdot instrs_if) pp_instrs instrs_if 
        (dotdot instrs_else) pp_instrs instrs_else
    end 
  | Cfor(vi,rng,instrs) ->
    F.fprintf fmt "@[<v>For %a from %a do {%s@   @[<v>%a@]@ }@]"
      pp_var_info vi (pp_range withinfo) rng (dotdot instrs) pp_instrs instrs
  | Cwhile(pe,instrs) ->
    F.fprintf fmt "@[<v>While %a do {%s@   @[<v>%a@]@ }@]"
      pp_pexpr pe (dotdot instrs) pp_instrs instrs
  | Ccall(inl,rvs,fname,pes) ->
    F.fprintf fmt "@[Ccall %a [:: %a] %a [:: %a]@]"
      pp_inline inl
      (pp_clist "; " pp_rval) rvs
      pp_var_name fname
      (pp_clist "; " pp_pexpr) pes


and pp_instr withinfo fmt instr =
  let MkI(iinfo,instr) = instr in
  if withinfo = NoInfo then pp_instr_r withinfo fmt instr
  else
    F.fprintf fmt "@[<hov 2>%a :@@@ %a@]"
      pp_pos iinfo (pp_instr_r withinfo) instr

and pp_instrs withinfo fmt instrs =
  pp_clist ";@ " (pp_instr withinfo) fmt instrs

let pp_fundef withinfo fmt fd =
  let { f_iinfo ; f_params ; f_body ; f_res } = fd in
  F.fprintf fmt "@[<v>MkFun %a @[[:: %a]@] {%s@   @[<v>%a@]@ }%%P@ %a@]"
    pp_pos f_iinfo
    (pp_clist ";@ " (pp_var_info withinfo)) f_params
    (dotdot f_body)
    (pp_instrs withinfo) f_body
    (pp_ret_type withinfo) f_res

let pp_named_fun withinfo fmt nf =
  let (fn,fd) = pair_of_cpair nf in
  F.fprintf fmt "@[<v>(%a,@ %a)@]" pp_var_name fn (pp_fundef withinfo) fd

let pp_prefix fmt () = 
  F.fprintf fmt "@[<v>From mathcomp Require Import all_ssreflect.@ ";
  F.fprintf fmt "Require Import prog_notation sem.@ ";
  F.fprintf fmt "Import ZArith type expr var seq.@ @ ";
  F.fprintf fmt "Open Scope string_scope.@ ";
  F.fprintf fmt "Open Scope Z_scope.@ @ @ @]"

let pp_prog withinfo vars fmt prog =
  let itbl = H.create 101 in
  if withinfo <> AllInfo then begin 
    H.clear vars_tbl;
    let mk_name s ty = 
      if H.mem itbl s then 
        s ^ string_of_ty ty 
      else s in
    let dov v = 
      let s = mk_name (string_of_string0 (Obj.magic v.Var.vname)) v.Var.vtype in
      H.add itbl s ();
      H.add vars_tbl v s in
     List.iter vars ~f:dov 
  end; 
  let pp_vars fmt () = 
    let dov v s = 
      F.fprintf fmt "Notation %s := (%a).@ " s
        (pp_var_info AllInfo) {v_var = v; v_info = Coq_xH} in
    H.iter dov vars_tbl in
  F.fprintf fmt "%a" pp_prefix ();
  F.fprintf fmt "@[<v>%a@ @ @]" pp_vars ();
  F.fprintf fmt "@[<v>Definition program := [::@   @[<v>%a@]]@]."
      (pp_clist ";@ @ " (pp_named_fun withinfo)) prog



