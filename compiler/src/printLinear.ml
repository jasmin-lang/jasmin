open Utils
open Label
open Linear
open PrintCommon
open PrintFexpr

module W = Wsize
module T = Type
module E = Expr

module P = Prog

module F = Format

(* ---------------------------------------------------------------- *)
let pp_stype fmt =
  function
  | T.Coq_sbool  -> F.fprintf fmt "bool"
  | T.Coq_sint   -> F.fprintf fmt "int"
  | T.Coq_sarr n -> F.fprintf fmt "u%a[%a]" pp_wsize U8 Z.pp_print (Conv.z_of_pos n)
  | T.Coq_sword sz -> F.fprintf fmt "u%a" pp_wsize sz

(* ---------------------------------------------------------------- *)
let pp_label fmt lbl =
  F.fprintf fmt "%a" Z.pp_print (Conv.z_of_pos lbl)

let pp_remote_label tbl fmt (fn, lbl) =
  F.fprintf fmt "%s.%a" (Conv.string_of_funname tbl fn) pp_label lbl

let pp_label_kind fmt = function
  | InternalLabel -> ()
  | ExternalLabel -> F.fprintf fmt "#returnaddress "

let pp_instr asmOp tbl fmt i =
  match i.li_i with
  | Lopn (lvs, op, es) ->
    let pp_cast fmt = function
      | Sopn.Oasm (Arch_extra.BaseOp(Some ws, _)) -> Format.fprintf fmt "(%du)" (P.int_of_ws ws)
      | _ -> () in

    F.fprintf fmt "@[%a@] = %a%a@[(%a)@]"
      (pp_list ",@ " (pp_lexpr tbl)) lvs
      pp_cast op
      (pp_opn asmOp) op
      (pp_list ",@ " (pp_rexpr tbl)) es
  | Lsyscall o -> F.fprintf fmt "SysCall %s" (pp_syscall o)
  | Lcall(lr, lbl) -> 
      let pp_o fmt o = match o with None -> () | Some v -> Format.fprintf fmt "%a " (pp_var_i tbl) v in
      F.fprintf fmt "Call %a%a" pp_o lr (pp_remote_label tbl) lbl
  | Lret       -> F.fprintf fmt "Return"
  | Lalign     -> F.fprintf fmt "Align"
  | Llabel (k, lbl) -> F.fprintf fmt "Label %a%a" pp_label_kind k pp_label lbl
  | Lgoto lbl -> F.fprintf fmt "Goto %a" (pp_remote_label tbl) lbl
  | Ligoto e -> F.fprintf fmt "IGoto %a" (pp_rexpr tbl) e
  | LstoreLabel (x, lbl) -> F.fprintf fmt "%a = Label %a" (pp_var tbl) x pp_label lbl
  | Lcond (e, lbl) -> F.fprintf fmt "If %a goto %a" (pp_fexpr tbl) e pp_label lbl

let pp_param tbl fmt x =
  let y = Conv.var_of_cvar tbl x.E.v_var in
  F.fprintf fmt "%a %a %s" pp_ty y.P.v_ty pp_kind y.P.v_kind y.P.v_name

let pp_stackframe fmt (sz, ws) =
  F.fprintf fmt "maximal stack usage: %a, alignment = %s"
    Z.pp_print (Conv.z_of_cz sz) (P.string_of_ws ws)

let pp_meta fmt fd =
  F.fprintf fmt "(* %a *)"
    pp_stackframe (fd.lfd_total_stack, fd.lfd_align)

let pp_return tbl is_export fmt =
  function
  | [] -> if is_export then F.fprintf fmt "@ return"
  | res -> F.fprintf fmt "@ return %a" (pp_list ",@ " (pp_var_i tbl)) res

let pp_lfun asmOp tbl fmt (fn, fd) =
  let name = Conv.fun_of_cfun tbl fn in
  F.fprintf fmt "@[<v>%a@ fn %s @[(%a)@] -> @[(%a)@] {@   @[<v>%a%a@]@ }@]"
    pp_meta fd
    name.P.fn_name
    (pp_list ",@ " (pp_param tbl)) fd.lfd_arg
    (pp_list ",@ " pp_stype) fd.lfd_tyout
    (pp_list ";@ " (pp_instr asmOp tbl)) fd.lfd_body
    (pp_return tbl fd.lfd_export) fd.lfd_res

let pp_prog asmOp tbl fmt lp =
  F.fprintf fmt "@[<v>%a@ @ %a@]"
    pp_datas lp.lp_globs
    (pp_list "@ @ " (pp_lfun asmOp tbl)) (List.rev lp.lp_funcs)

