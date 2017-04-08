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
    | Pconst(cz)          -> F.fprintf fmt "(Pconst %a)" pp_coqZ cz
    | Pbool(b)            -> F.fprintf fmt "(Pbool %a)" pp_cbool b
    | Pcast(pe)           -> F.fprintf fmt "(Pcast %a)" pp_pexpr pe
    | Pvar(vi)            -> F.fprintf fmt "%a" (pp_var_info withinfo) vi
    | Pget(vi,pe)         -> 
      F.fprintf fmt "(Pget %a %a)" (pp_var_info withinfo) vi pp_pexpr pe
    | Pload(vi,pe)        -> 
      F.fprintf fmt "(Pload %a %a)" (pp_var_info withinfo) vi pp_pexpr pe
    | Pnot(pe)            -> F.fprintf fmt "(Pnot %a)" pp_pexpr pe
    | Papp2(sop2,pe1,pe2) -> 
      F.fprintf fmt "(Papp2 %a %a %a)" pp_sop2 sop2 pp_pexpr pe1 pp_pexpr pe2
  in pp_pexpr

let pp_rval withinfo fmt rv =
  match rv with
  | Lnone(i)     -> F.fprintf fmt "(Lnone %a)" pp_pos i
  | Lvar(vi)     -> 
    F.fprintf fmt "(Lvar %a)" (pp_var_info withinfo) vi
  | Lmem(vi,pe)  -> 
    F.fprintf fmt "(Lmem %a %a)" (pp_var_info withinfo) vi (pp_pexpr withinfo) pe
  | Laset(vi,pe) -> 
    F.fprintf fmt "(Laset %a %a)" (pp_var_info withinfo) vi (pp_pexpr withinfo) pe

let pp_ret_type withinfo fmt res =
  F.fprintf fmt "[:: %a]" (pp_clist "; " (pp_var_info withinfo) ) res

let pp_range withinfo fmt rng =
  let (dlb,ub) = pair_of_cpair rng in
  let (dir,lb) = pair_of_cpair dlb in
  F.fprintf fmt "(%s, %a, %a)"
    (match dir with UpTo -> "UpTo" | DownTo -> "DownTo")
    (pp_pexpr withinfo) lb
    (pp_pexpr withinfo) ub

let rec pp_instr_r withinfo fmt instr =
  let pp_rval = pp_rval withinfo in
  let pp_pexpr = pp_pexpr withinfo in
  let pp_instrs = pp_instrs withinfo in
  let pp_var_info = pp_var_info withinfo in
  match instr with
  | Cassgn(rv,atag,pe) ->
    F.fprintf fmt "@[Cassgn@ %a@ %a@ %a@]" pp_rval rv pp_atag atag pp_pexpr pe
  | Copn(rvs,sopn,pes) ->
    F.fprintf fmt "@[Copn [:: %a]@ %a@ [:: %a]@]" 
      (pp_clist "; " pp_rval) rvs pp_sopn sopn (pp_clist "; " pp_pexpr) pes
  | Cif(pe,instrs_if,instrs_else) ->
    F.fprintf fmt "@[<hov 2>Cif %a[::@ @[<v 0>%a@]@ ] [::@ @[<v 0>%a@]]@]"
      pp_pexpr pe pp_instrs instrs_if pp_instrs instrs_else
  | Cfor(vi,rng,instrs) ->
    F.fprintf fmt "@[<hov 2>Cfor %a %a [::@ @[<v 0>%a@]@ ]@]"
      pp_var_info vi (pp_range withinfo) rng pp_instrs instrs
  | Cwhile(pe,instrs) ->
    F.fprintf fmt "@[<hov 2>Cwhile %a [::@ @[<v 0>%a@]@ ]@]" pp_pexpr pe pp_instrs instrs
  | Ccall(inl,rvs,fname,pes) ->
    F.fprintf fmt "@[Ccall %a [:: %a] %a [:: %a]@]"
      pp_inline inl
      (pp_clist "; " pp_rval) rvs
      pp_var_name fname
      (pp_clist "; " pp_pexpr) pes


and pp_instr withinfo fmt instr =
  let MkI(iinfo,instr) = instr in
  F.fprintf fmt "MkI %a (%a)"
    (pp_minfo (fun fmt -> pp_pos fmt (if withinfo <> NoInfo then iinfo else Coq_xH))) ()
    (pp_instr_r withinfo) instr

and pp_instrs withinfo fmt instrs =
  pp_clist ";@\n" (pp_instr withinfo) fmt instrs

let pp_fundef withinfo fmt fd =
  let { f_iinfo ; f_params ; f_body ; f_res } = fd in
  F.fprintf fmt "@[<v>MkFun %a @[[:: %a]@] [::@ @[<v>%a@]]@ %a@]"
    pp_pos f_iinfo
    (pp_clist ";@ " (pp_var_info withinfo)) f_params
    (pp_clist ";@ " (pp_instr withinfo)) f_body
    (pp_ret_type withinfo) f_res

let pp_named_fun withinfo fmt nf =
  let (fn,fd) = pair_of_cpair nf in
  F.fprintf fmt "@[<v>(%a,@ %a)@]" pp_var_name fn (pp_fundef withinfo) fd

let pp_prefix fmt () = 
  F.fprintf fmt "@[<v>Require Import sem.@ ";
  F.fprintf fmt "Import ZArith type expr var seq.@ @ ";
  F.fprintf fmt "Open Scope string_scope.@ ";
  F.fprintf fmt "Open Scope Z_scope.@ @ @]"



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


(*
Delimit Scope prog_scope with P.
Notation "x ':==' e" := 
  (MkI 1%positive (Cassgn x AT_keep e)) (at level 42) : prog_scope.
Open Scope prog_scope.

Notation "x .[ n ]" := (Pget x n) : prog_scope.
Notation "vm .[ k  <- v ]" := (@Fv.set _ vm k v) : vmap_scope.
*)
