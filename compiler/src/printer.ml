(* -------------------------------------------------------------------- *)
open Utils
open Prog
open PrintCommon
module W = Wsize
module T = Type
module E = Expr
module F = Format

(* -------------------------------------------------------------------- *)
let pp_print_X fmt z =
  Format.fprintf fmt "%s" (Z.format "#X" z)

(* -------------------------------------------------------------------- *)
let pp_gvar_i pp_var fmt v = pp_var fmt (L.unloc v)

(* -------------------------------------------------------------------- *)

let string_of_combine_flags = function
  | E.CF_LT s -> Format.sprintf "_%sLT" (string_of_signess s)
  | E.CF_LE s -> Format.sprintf "_%sLE" (string_of_signess s)
  | E.CF_EQ   -> Format.sprintf "_EQ" 
  | E.CF_NEQ  -> Format.sprintf "_NEQ" 
  | E.CF_GE s -> Format.sprintf "_%sGE" (string_of_signess s)
  | E.CF_GT s -> Format.sprintf "_%sGT" (string_of_signess s)

(* -------------------------------------------------------------------- *)

let pp_ge pp_len pp_var =
  let pp_var_i = pp_gvar_i pp_var in
  let pp_gvar fmt x =
    let s = if is_gkvar x then "" else "/* global: */ " in
    Format.fprintf fmt "%s%a" s pp_var_i x.gv in

  let rec pp_expr fmt = function
  | Pconst i    -> Z.pp_print fmt i
  | Pbool  b    -> F.fprintf fmt "%b" b
  | Parr_init _ -> assert false (* This case is handled in pp_gi *)
  | Pvar v      -> pp_gvar fmt v
  | Pget(al,aa,ws,x,e) ->
    pp_arr_access pp_gvar pp_expr fmt al aa ws x e
  | Psub(aa,ws,len,x,e) ->
    pp_arr_slice pp_gvar pp_expr pp_len fmt aa ws x e len
  | Pload(al,ws,x,e) ->
    F.fprintf fmt "@[(%a)[%a%a@ +@ %a]@]"
      pp_btype (U ws)
      pp_aligned al
      pp_var_i x pp_expr e
  | Papp1(o, e) ->
    F.fprintf fmt "@[(%s@ %a)@]" (string_of_op1 o) pp_expr e
  | Papp2(op,e1,e2) ->
    F.fprintf fmt "@[(%a %s@ %a)@]"
      pp_expr e1 (string_of_op2 op) pp_expr e2
  | PappN (E.Opack(_sz, pe), es) ->
    F.fprintf fmt "@[(%du%n)[%a]@]" (List.length es) (int_of_pe pe) (pp_list ",@ " pp_expr) es
  | PappN (Ocombine_flags c, es) ->
    F.fprintf fmt "@[%s(%a)@]" (string_of_combine_flags c) (pp_list ",@ " pp_expr) es  
  | Pif(_, e,e1,e2) ->
    F.fprintf fmt "@[(%a ?@ %a :@ %a)@]"
      pp_expr e pp_expr e1  pp_expr e2
  in
  pp_expr

(* -------------------------------------------------------------------- *)
let pp_glv pp_len pp_var fmt = function
  | Lnone (_, ty) -> F.fprintf fmt "_ /* %a */" (pp_gtype (fun fmt _ -> F.fprintf fmt "?")) ty
  | Lvar x  -> pp_gvar_i pp_var fmt x
  | Lmem (al, ws, x, e) ->
    F.fprintf fmt "@[(%a)[%a%a@ +@ %a]@]"
     pp_btype (U ws)
     pp_aligned al
     (pp_gvar_i pp_var) x (pp_ge pp_len pp_var) e
  | Laset(al, aa, ws, x, e) ->
    pp_arr_access (pp_gvar_i pp_var) (pp_ge pp_len pp_var) fmt al aa ws x e
  | Lasub(aa, ws, len, x, e) ->
    pp_arr_slice (pp_gvar_i pp_var) (pp_ge pp_len pp_var) pp_len fmt aa ws x e len


(* -------------------------------------------------------------------- *)
let pp_ges pp_len pp_var fmt es =
  Format.fprintf fmt "@[%a@]" (pp_list ",@ " (pp_ge pp_len pp_var)) es

(* -------------------------------------------------------------------- *)
let pp_glvs pp_len pp_var fmt lvs =
  match lvs with
  | [] -> F.fprintf fmt "()"
  | [x] -> pp_glv pp_len pp_var fmt x
  | _   -> F.fprintf fmt "(@[%a@])" (pp_list ",@ " (pp_glv pp_len pp_var)) lvs

(* -------------------------------------------------------------------- *)
let rec pp_simple_attribute fmt =
  function
  | Annotations.Aint z -> Z.pp_print fmt z
  | Aid s | Astring s -> F.fprintf fmt "%S" s
  | Aws ws -> F.fprintf fmt "%s" (string_of_ws ws)
  | Astruct a -> F.fprintf fmt "(%a)" pp_annotations a

and pp_attribute fmt = function
  | None -> ()
  | Some a -> Format.fprintf fmt "=%a" pp_simple_attribute (L.unloc a)

and pp_annotation fmt (k, v) =
  F.fprintf fmt "%s%a" (L.unloc k) pp_attribute v

and pp_annotations fmt a =
  Format.fprintf fmt "%a" (pp_list ",@ " pp_annotation) a

let pp_annotations fmt a =
  if a != [] then F.fprintf fmt "#[@[<hov>%a@]]@ " pp_annotations a

(* -------------------------------------------------------------------- *)
let pp_tag = E.(function
  | AT_none    -> ""
  | AT_keep    -> ":k"
  | AT_rename  -> ":r"
  | AT_inline  -> ":i"
  | AT_phinode -> ":φ")

let pp_align fmt = function 
  | E.Align -> Format.fprintf fmt "#[align]@ "
  | E.NoAlign -> ()

let rec pp_gi pp_info pp_len pp_opn pp_var fmt i =
  F.fprintf fmt "%a" pp_info (i.i_loc, i.i_info);
  F.fprintf fmt "%a" pp_annotations i.i_annot;
  match i.i_desc with
  | Cassgn(x, tg, ty, Parr_init n) ->
    F.fprintf fmt "@[<hov 2>ArrayInit(%a); /* length=%a %a%s */@]"
      (pp_glv pp_len pp_var) x
      pp_len n
      (pp_gtype pp_len) ty
      (pp_tag tg)

  | Cassgn(x , tg, ty, e) ->
    F.fprintf fmt "@[<hov 2>%a =@ %a; /* %a%s */@]"
      (pp_glv pp_len pp_var) x
      (pp_ge pp_len pp_var) e
      (pp_gtype pp_len) ty
      (pp_tag tg)

  | Copn(x, t, o, e) ->
    let pp_cast fmt = function
      | Sopn.Oasm (Arch_extra.BaseOp(Some ws, _)) -> Format.fprintf fmt "(%du)" (int_of_ws ws)
      | _ -> () in

    F.fprintf fmt "@[<hov 2>%a =@ %a#%a(%a); /* %s */@]"
      (pp_glvs pp_len pp_var) x pp_cast o pp_opn o
      (pp_ges pp_len pp_var) e
      (pp_tag t)

  | Csyscall(x, o, e) ->
      F.fprintf fmt "@[<hov 2>%a =@ %s(%a);@]"
        (pp_glvs pp_len pp_var) x (pp_syscall o) (pp_ges pp_len pp_var) e

  | Cif(e, c, []) ->
    F.fprintf fmt "@[<v>if %a %a@]"
      (pp_ge pp_len pp_var) e (pp_cblock pp_info pp_len pp_opn pp_var) c

  | Cif(e, c1, c2) ->
    F.fprintf fmt "@[<v>if %a %a else %a@]"
      (pp_ge pp_len pp_var) e (pp_cblock pp_info pp_len pp_opn pp_var) c1
      (pp_cblock pp_info pp_len pp_opn pp_var) c2

  | Cfor(i, (dir, lo, hi), c) ->
    let dir, e1, e2 =
      if dir = UpTo then "to", lo, hi else "downto", hi, lo in
    F.fprintf fmt "@[<v>for %a = @[%a %s@ %a@] %a@]"
      (pp_gvar_i pp_var) i (pp_ge pp_len pp_var) e1 dir (pp_ge pp_len pp_var) e2
      (pp_cblock pp_info pp_len pp_opn pp_var) c

  | Cwhile(a, [], e, c) ->
    F.fprintf fmt "@[<v>%awhile (%a) %a@]"
      pp_align a
      (pp_ge pp_len pp_var) e (pp_cblock pp_info pp_len pp_opn pp_var) c

  | Cwhile(a, c, e, []) ->
    F.fprintf fmt "@[<v>%awhile %a (%a)@]"
      pp_align a
      (pp_cblock pp_info pp_len pp_opn pp_var) c (pp_ge pp_len pp_var) e

  | Cwhile(a, c, e, c') ->
    F.fprintf fmt "@[<v>%awhile %a (%a) %a@]"
      pp_align a
      (pp_cblock pp_info pp_len pp_opn pp_var) c (pp_ge pp_len pp_var) e
      (pp_cblock pp_info pp_len pp_opn pp_var) c'

  | Ccall(x, f, e) ->
    let pp_x fmt = function
      | [] -> ()
      | x -> F.fprintf fmt "%a =@ " (pp_glvs pp_len pp_var) x in
    F.fprintf fmt "@[<hov 2>%a%s(%a);@]"
      pp_x x f.fn_name (pp_ges pp_len pp_var) e

(* -------------------------------------------------------------------- *)
and pp_gc pp_info pp_len pp_opn pp_var fmt c =
  F.fprintf fmt "@[<v>%a@]" (pp_list "@ " (pp_gi pp_info pp_len pp_opn pp_var)) c

(* -------------------------------------------------------------------- *)
and pp_cblock pp_info pp_len pp_opn pp_var fmt c =
  F.fprintf fmt "{@   %a@ }"  (pp_gc pp_info pp_len pp_opn pp_var) c

(* -------------------------------------------------------------------- *)
let pp_ty_decl (pp_size:F.formatter -> 'size -> unit) fmt v =
  F.fprintf fmt "%a %a" pp_kind v.v_kind (pp_gtype pp_size) v.v_ty

let pp_var_decl pp_var pp_size fmt v =
  F.fprintf fmt "%a %a" (pp_ty_decl pp_size) v pp_var v

let pp_call_conv fmt =
  function
  | FInfo.Export _ -> Format.fprintf fmt "export@ "
  | FInfo.Internal -> Format.fprintf fmt "inline@ "
  | FInfo.Subroutine _ -> ()

let pp_gfun pp_info (pp_size:F.formatter -> 'size -> unit) pp_opn pp_var fmt fd =
  let pp_vd =  pp_var_decl pp_var pp_size in
  let pp_locals fmt fd =
    let seen = ref Spv.empty in
    let mark x = seen := Spv.add x !seen in
    let is_seen x = Spv.mem x !seen in
    List.iter mark fd.f_args;
    fold_vars_fc (fun x () ->
        if x.v_kind <> Const && not (is_seen x) then (
          mark x;
          F.fprintf fmt "%a;@ " pp_vd x)
    ) () fd
  in
  let ret = List.map L.unloc fd.f_ret in
  let pp_ret fmt () =
    F.fprintf fmt "return @[(%a)@];"
      (pp_list ",@ " pp_var) ret in

  F.fprintf fmt "@[<v>%afn %s @[(%a)@] -> @[(%a)@] {@   @[<v>%a@ %a@ %a@]@ }@]"
   pp_call_conv fd.f_cc
   fd.f_name.fn_name
   (pp_list ",@ " pp_vd) fd.f_args
   (pp_list ",@ " (pp_ty_decl pp_size)) ret
   pp_locals fd
   (pp_gc pp_info pp_size pp_opn pp_var) fd.f_body
   pp_ret ()

let pp_noinfo _ _ = ()

let pp_gexpr pp_len pp_var fmt = function
  | GEword e -> pp_ge pp_len pp_var fmt e
  | GEarray es -> Format.fprintf fmt "{@[%a@]}" (pp_ges pp_len pp_var) es

let pp_pitem pp_len pp_opn pp_var =
  let aux fmt = function
   | MIfun fd -> pp_gfun pp_noinfo pp_len pp_opn pp_var fmt fd
   | MIparam (x,e) ->
      F.fprintf fmt "%a = %a;"
        (pp_var_decl pp_var pp_len) x
        (pp_ge pp_len pp_var) e
    | MIglobal (x, e) ->
      F.fprintf fmt "%a %a = %a;"
        (pp_gtype pp_len) x.v_ty
        pp_var x
        (pp_gexpr pp_len pp_var) e
 in
  aux

let pp_pvar fmt x = F.fprintf fmt "%s" x.v_name 

let rec pp_pexpr e = pp_ge pp_pexpr pp_pvar e

let pp_ptype = pp_gtype pp_pexpr

let pp_plval = pp_glv pp_pexpr pp_pvar 

let pp_pprog pd asmOp fmt p =
  let pp_opn = pp_opn pd asmOp in
  Format.fprintf fmt "@[<v>%a@]"
    (pp_list "@ @ " (pp_pitem pp_pexpr pp_opn pp_pvar)) (List.rev p)

let pp_fun ?pp_locals ?(pp_info=pp_noinfo) pp_opn pp_var fmt fd =
  let pp_vd =  pp_var_decl pp_var pp_len in
  let pp_locals = Option.default (fun fmt -> Sv.iter (F.fprintf fmt "%a;@ " pp_vd)) pp_locals in
  let locals = locals fd in
  let ret = List.map L.unloc fd.f_ret in
  let pp_ret fmt () =
    F.fprintf fmt "return @[(%a)@];"
      (pp_list ",@ " pp_var) ret in

  F.fprintf fmt "@[<v>%afn %s @[(%a)@] -> @[(%a)@] {@   @[<v>%a@ %a@ %a@]@ }@]"
   pp_call_conv fd.f_cc
   fd.f_name.fn_name
   (pp_list ",@ " pp_vd) fd.f_args
   (pp_list ",@ " (pp_ty_decl pp_len)) ret
   pp_locals locals
   (pp_gc pp_info pp_len pp_opn pp_var) fd.f_body
   pp_ret ()

let pp_var ~debug =
    if debug then
      fun fmt x -> F.fprintf fmt "%s.%s" x.v_name (string_of_uid x.v_id)
    else
      fun fmt x -> F.fprintf fmt "%s" x.v_name

let pp_dvar ~debug fmt x =
  let pp_dloc fmt d =
    if not (L.isdummy d) then F.fprintf fmt " (defined at %a)" L.pp_loc d
  in
  F.fprintf fmt "%a%a" (pp_var ~debug) x pp_dloc x.v_dloc

let pp_expr ~debug fmt e =
  let pp_var = pp_var ~debug in
  pp_ge pp_len pp_var fmt e

let pp_lval ~debug fmt x = 
  pp_glv pp_len (pp_var ~debug) fmt x

let pp_instr ~debug pd asmOp fmt i =
  let pp_opn = pp_opn pd asmOp in
  let pp_var = pp_var ~debug in
  pp_gi pp_noinfo pp_len pp_opn pp_var fmt i

let pp_stmt ~debug pd asmOp fmt i =
  let pp_opn = pp_opn pd asmOp in
  let pp_var = pp_var ~debug in
  pp_gc pp_noinfo pp_len pp_opn pp_var fmt i

let pp_ifunc ~debug pp_info pd asmOp fmt fd =
  let pp_opn = pp_opn pd asmOp in
  let pp_var = pp_var ~debug in
  pp_fun ~pp_info pp_opn pp_var fmt fd

let pp_func ~debug pd asmOp fmt fd =
  let pp_opn = pp_opn pd asmOp in
  let pp_var = pp_var ~debug in
  pp_fun pp_opn pp_var fmt fd

let pp_glob pp_var fmt (x, gd) = 
  let pp_size fmt i = F.fprintf fmt "%i" i in
  let pp_vd =  pp_var_decl pp_var pp_size in
  let pp_gd fmt gd = 
    match gd with
    | Global.Gword(ws,w) -> 
      Format.fprintf fmt "%a" pp_print_X (Conv.z_of_word ws w) 
    | Global.Garr(p, t) ->
      let _, t = Conv.to_array x.v_ty p t in
      Format.fprintf fmt "@[{%a}@]"
        (pp_list ",@ " pp_print_X) 
        (Array.to_list t)  in
  Format.fprintf fmt "@[%a =@ %a;@]"
    pp_vd x pp_gd gd

let pp_globs pp_var fmt gds = 
  Format.fprintf fmt "@[<v>%a@]"
    (pp_list "@ @ " (pp_glob pp_var)) (List.rev gds)

let pp_iprog ~debug pp_info pd asmOp fmt (gd, funcs) =
  let pp_opn = pp_opn pd asmOp in
  let pp_var = pp_var ~debug in
  Format.fprintf fmt "@[<v>%a@ %a@]"
     (pp_globs pp_var) gd
     (pp_list "@ @ " (pp_fun ~pp_info pp_opn pp_var)) (List.rev funcs)

let pp_prog ~debug pd asmOp fmt ((gd, funcs):('info, 'asm) Prog.prog) =
  let pp_opn = pp_opn pd asmOp in
  let pp_var = pp_var ~debug in
  Format.fprintf fmt "@[<v>%a@ %a@]"
     (pp_globs pp_var) gd
     (pp_list "@ @ " (pp_fun pp_opn pp_var)) (List.rev funcs)

let pp_to_save ~debug fmt (x, ofs) =
  Format.fprintf fmt "%a/%a" (pp_var ~debug) (Conv.var_of_cvar x) Z.pp_print (Conv.z_of_cz ofs)

let pp_saved_stack ~debug fmt = function
  | Expr.SavedStackNone  -> Format.fprintf fmt "none"
  | Expr.SavedStackReg x -> Format.fprintf fmt "in reg %a" (pp_var ~debug) (Conv.var_of_cvar x)
  | Expr.SavedStackStk z -> Format.fprintf fmt "in stack %a" Z.pp_print (Conv.z_of_cz z)


let pp_tmp_option ~debug =
   Format.pp_print_option (fun fmt x -> Format.fprintf fmt " [tmp = %a]" (pp_var ~debug) (Conv.var_of_cvar x))

let pp_return_address ~debug fmt = function
  | Expr.RAreg (x, o) ->
    Format.fprintf fmt "%a%a" (pp_var ~debug) (Conv.var_of_cvar x) (pp_tmp_option ~debug) o

  | Expr.RAstack(Some x, z, o) ->
    Format.fprintf fmt "%a, RSP + %a%a" (pp_var ~debug) (Conv.var_of_cvar x) Z.pp_print (Conv.z_of_cz z) (pp_tmp_option ~debug) o
  | Expr.RAstack(None, z, o) ->
    Format.fprintf fmt "RSP + %a%a" Z.pp_print (Conv.z_of_cz z) (pp_tmp_option ~debug) o
  | Expr.RAnone   -> Format.fprintf fmt "_"

let pp_sprog ~debug pd asmOp fmt ((funcs, p_extra):('info, 'asm) Prog.sprog) =
  let pp_opn = pp_opn pd asmOp in
  let pp_var = pp_var ~debug in
  let pp_f_extra fmt f_extra = 
    Format.fprintf fmt "(* @[<v>alignment = %s; stack size = %a + %a; max stack size = %a;@ max call depth = %a;@ saved register = @[%a@];@ saved stack = %a;@ return_addr = %a@] *)"
      (string_of_ws f_extra.Expr.sf_align)
      Z.pp_print (Conv.z_of_cz f_extra.Expr.sf_stk_sz)
      Z.pp_print (Conv.z_of_cz f_extra.Expr.sf_stk_extra_sz)
      Z.pp_print (Conv.z_of_cz f_extra.Expr.sf_stk_max)
      Z.pp_print (Conv.z_of_cz f_extra.Expr.sf_max_call_depth)
      (pp_list ",@ " (pp_to_save ~debug)) (f_extra.Expr.sf_to_save)
      (pp_saved_stack ~debug) (f_extra.Expr.sf_save_stack)
      (pp_return_address ~debug)  (f_extra.Expr.sf_return_address)
  in
  let pp_fun fmt (f_extra,f) =
    Format.fprintf fmt "@[<v>%a@ %a@]" pp_f_extra f_extra (pp_fun pp_opn pp_var) f in
  let pp_p_extra fmt p_extra = 
    Format.fprintf fmt "global data:@    %a" pp_datas p_extra.Expr.sp_globs in
  Format.fprintf fmt "@[<v>%a@ %a@]"
     pp_p_extra p_extra
     (pp_list "@ @ " pp_fun) (List.rev funcs)

(* ----------------------------------------------------------------------- *)

let pp_warning_msg fmt = function
  | Compiler_util.Use_lea -> Format.fprintf fmt "LEA instruction is used"

let pp_err ~debug fmt (pp_e : Compiler_util.pp_error) =
  let pp_var fmt v =
    let v = Conv.var_of_cvar v in
    Format.fprintf fmt "%a" (pp_dvar ~debug) v
  in
  let rec pp_err fmt pp_e =
    match pp_e with
    | Compiler_util.PPEstring s -> Format.fprintf fmt "%s" s
    | Compiler_util.PPEz z -> Format.fprintf fmt "%a" Z.pp_print (Conv.z_of_cz z)
    | Compiler_util.PPEvar v -> Format.fprintf fmt "%a" pp_var v
    | Compiler_util.PPEvarinfo loc ->
      Format.fprintf fmt "%a" L.pp_loc loc
    | Compiler_util.PPElval x ->
       x |> Conv.lval_of_clval |>
       pp_glv pp_len (pp_dvar ~debug) fmt
    | Compiler_util.PPEfunname fn -> Format.fprintf fmt "%s" fn.fn_name
    | Compiler_util.PPEiinfo ii ->
      let i_loc, _ = ii in
      Format.fprintf fmt "%a" L.pp_iloc i_loc
    | Compiler_util.PPEfuninfo fi ->
      let (f_loc, _, _, _) = fi in
      Format.fprintf fmt "%a" L.pp_sloc f_loc
    | Compiler_util.PPEexpr e ->
      let e = Conv.expr_of_cexpr e in
      pp_expr ~debug fmt e
    | Compiler_util.PPErexpr e ->
       PrintFexpr.pp_rexpr fmt e
    | Compiler_util.PPEfexpr e ->
       PrintFexpr.pp_fexpr fmt e
    | Compiler_util.PPEbox (box, pp_e) ->
      begin match box with
      | Compiler_util.Hbox -> Format.fprintf fmt "@[<h>%a@]" (pp_list "@ " pp_err) pp_e
      | Compiler_util.Vbox -> Format.fprintf fmt "@[<v>%a@]" (pp_list "@ " pp_err) pp_e
      | Compiler_util.HoVbox -> Format.fprintf fmt "@[<hov>%a@]" (pp_list "@ " pp_err) pp_e
      | Compiler_util.Nobox -> Format.fprintf fmt "%a" (pp_list "" pp_err) pp_e
      end
    | Compiler_util.PPEbreak -> Format.fprintf fmt "@ "
  in
  pp_err fmt pp_e
