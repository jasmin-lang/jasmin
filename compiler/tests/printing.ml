(** Printing tests.

    This checks the result of the printing of Jasmin programs (after
    pre-typing). Given a source file, it is parsed, printed, and the result of
    printing is parsed again. Then the two results of parsing are compared. The
    comparison uses a dedicated “equality” relation that ignores locations and
    internal identifiers.

    This test is applied to every `.jazz` file in the `success/` directory. The
    target architectures to use are guessed from the path.

    This test is run when executing `dune runtest`. *)

open Jasmin
open Utils
open Common
open Prog

(** Specific configuration for some example programs. This in particular
    disables warnings that are expected. *)
let config path =
  let default () =
    Glob_options.stack_zero_strategy := None;
    set_all_warnings ()
  in
  try
    List.assoc path
      [
        ( "success/arm-m4/rand.jazz",
          fun () -> Glob_options.stack_zero_strategy := Some SZSloop );
        ("success/common/bug_729.jazz", disable_warnings [ InlinedCallToExport ]);
        ("success/x86-64/bug_895.jazz", disable_warnings [ UnusedVar ]);
        ( "success/common/test_warn_var.jazz",
          disable_warnings [ UnusedVar; DuplicateVar ] );
        ("success/x86-64/vpblendvb.jazz", disable_warnings [ Deprecated ]);
        ("success/x86-64/vpmovmskb.jazz", disable_warnings [ Deprecated ]);
      ]
      ()
  with Not_found -> default ()

(* ---------------------------------------------------------------- *)
(* Compare programs for equality, ignoring locations and internal identifiers *)
let rec eq_annotations x y = List.for_all2 eq_annotation x y

and eq_annotation (a, b) (c, d) =
  String.equal (L.unloc a) (L.unloc c) && Option.eq ~eq:eq_attribute b d

and eq_attribute x y = eq_simple_attribute (L.unloc x) (L.unloc y)

and eq_simple_attribute x y =
  let open Annotations in
  match (x, y) with
  | Aint a, Aint b -> Z.equal a b
  | Aid a, Aid b | Astring a, Astring b -> String.equal a b
  | Aws a, Aws b -> Wsize.wsize_eqb a b
  | Astruct a, Astruct b -> eq_annotations a b
  | (Aint _ | Aid _ | Astring _ | Aws _ | Astruct _), _ -> false

let rec eq_pty x y =
  match (x, y) with
  | Bty a, Bty b -> a = b
  | Arr (a, n), Arr (b, m) -> Wsize.wsize_eqb a b && eq_pexpr_ n m
  | (Bty _ | Arr _), _ -> false

and eq_pvar x y =
  x.v_name = y.v_name && x.v_kind = y.v_kind && eq_pty x.v_ty y.v_ty
  && eq_annotations x.v_annot y.v_annot

and eq_pvar_i x y = eq_pvar (L.unloc x) (L.unloc y)
and eq_pgvar x y = eq_pvar_i x.gv y.gv && x.gs = y.gs

and eq_plval x y =
  match (x, y) with
  | Lnone (_, a), Lnone (_, b) -> eq_pty a b
  | Lvar a, Lvar b -> eq_pvar_i a b
  | Lmem (a, b, _, d), Lmem (e, f, _, h) ->
      a = e && Wsize.wsize_eqb b f && eq_pexpr d h
  | Laset (a, b, c, d, e), Laset (f, g, h, i, j) ->
      a = f && b = g && Wsize.wsize_eqb c h && eq_pvar_i d i && eq_pexpr e j
  | Lasub (a, b, c, d, e), Lasub (f, g, h, i, j) ->
      a = f && Wsize.wsize_eqb b g && eq_pexpr_ c h && eq_pvar_i d i
      && eq_pexpr e j
  | (Lnone _ | Lvar _ | Lmem _ | Laset _ | Lasub _), _ -> false

and eq_plvals x y = List.for_all2 eq_plval x y

and eq_pexpr x y =
  match (x, y) with
  | Pconst a, Pconst b -> Z.equal a b
  | Pbool a, Pbool b -> Stdlib.Bool.equal a b
  | Parr_init a, Parr_init b -> eq_pexpr_ a b
  | Pvar a, Pvar b -> eq_pgvar a b
  | Pget (a, b, c, d, e), Pget (f, g, h, i, j) ->
      a = f && b = g && Wsize.wsize_eqb c h && eq_pgvar d i && eq_pexpr e j
  | Psub (a, b, c, d, e), Psub (f, g, h, i, j) ->
      a = f && Wsize.wsize_eqb b g && eq_pexpr_ c h && eq_pgvar d i
      && eq_pexpr e j
  | Pload (a, b, d), Pload (e, f, h) ->
      a = e && Wsize.wsize_eqb b f && eq_pexpr d h
  | Papp1 (a, b), Papp1 (c, d) -> a = c && eq_pexpr b d
  | Papp2 (a, b, c), Papp2 (d, e, f) -> a = d && eq_pexpr b e && eq_pexpr c f
  | PappN (a, b), PappN (c, d) -> a = c && eq_pexprs b d
  | Pif (a, b, c, d), Pif (e, f, g, h) ->
      eq_pty a e && eq_pexpr b f && eq_pexpr c g && eq_pexpr d h
  | ( ( Pconst _ | Pbool _ | Parr_init _ | Pvar _ | Pget _ | Psub _ | Pload _
      | Papp1 _ | Papp2 _ | PappN _ | Pif _ ),
      _ ) ->
      false

and eq_pexprs x y = List.for_all2 eq_pexpr x y
and eq_pexpr_ (PE x) (PE y) = eq_pexpr x y

let eq_pgexpr x y =
  match (x, y) with
  | GEword a, GEword b -> eq_pexpr a b
  | GEarray a, GEarray b -> eq_pexprs a b
  | (GEword _ | GEarray _), _ -> false

let eq_prange (x : pexpr_ grange) (y : pexpr_ grange) =
  let a, b, c = x and d, e, f = y in
  a = d && eq_pexpr b e && eq_pexpr c f

let rec eq_pstmt x y = List.for_all2 eq_pinstr x y

and eq_pinstr x y =
  eq_annotations x.i_annot y.i_annot && eq_pinstr_r x.i_desc y.i_desc

and eq_pinstr_r (x : _ pinstr_r) y =
  match (x, y) with
  | Cassgn (a, b, c, d), Cassgn (e, f, g, h) ->
      eq_plval a e && b = f && eq_pty c g && eq_pexpr d h
  | Copn (a, b, c, d), Copn (e, f, g, h) ->
      eq_plvals a e && b = f && c = g && eq_pexprs d h
  | Csyscall (a, b, c), Csyscall (d, e, f) ->
      eq_plvals a d && b = e && eq_pexprs c f
  | Cif (a, b, c), Cif (d, e, f) -> eq_pexpr a d && eq_pstmt b e && eq_pstmt c f
  | Cfor (a, b, c), Cfor (d, e, f) ->
      eq_pvar_i a d && eq_prange b e && eq_pstmt c f
  | Cwhile (a, b, c, _d, e), Cwhile (f, g, h, _i, j) ->
      a = f && eq_pstmt b g && eq_pexpr c h && eq_pstmt e j
  | Ccall (a, b, c), Ccall (d, e, f) ->
      eq_plvals a d && b.fn_name = e.fn_name && eq_pexprs c f
  | (Cassgn _ | Copn _ | Csyscall _ | Cif _ | Cfor _ | Cwhile _ | Ccall _), _ ->
      false

let eq_f_annot x y =
  let open FInfo in
  x.retaddr_kind = y.retaddr_kind
  && Option.eq ~eq:Z.equal x.stack_allocation_size y.stack_allocation_size
  && Option.eq ~eq:Z.equal x.stack_size y.stack_size
  && Option.eq ~eq:Wsize.wsize_eqb x.stack_align y.stack_align
  && Option.eq ~eq:Z.equal x.max_call_depth y.max_call_depth
  && x.stack_zero_strategy = y.stack_zero_strategy
  && eq_annotations x.f_user_annot y.f_user_annot

let eq_pfunc x y =
  eq_f_annot x.f_annot y.f_annot
  && x.f_cc = y.f_cc
  && String.equal x.f_name.fn_name y.f_name.fn_name
  && List.for_all2 eq_pty x.f_tyin y.f_tyin
  && List.for_all2 eq_pvar x.f_args y.f_args
  && List.for_all2 eq_pty x.f_tyout y.f_tyout
  && List.for_all2 eq_annotations x.f_ret_info.ret_annot y.f_ret_info.ret_annot
  && List.for_all2 eq_pvar_i x.f_ret y.f_ret
  && eq_pstmt x.f_body y.f_body

let eq_pmod_item x y =
  match (x, y) with
  | MIfun f, MIfun g -> eq_pfunc f g
  | MIparam (x, i), MIparam (y, j) -> eq_pvar x y && eq_pexpr i j
  | MIglobal (x, i), MIglobal (y, j) -> eq_pvar x y && eq_pgexpr i j
  | (MIfun _ | MIparam _ | MIglobal _), _ -> false

let eq_pmod_items x y = List.for_all2 eq_pmod_item x y

(* ---------------------------------------------------------------- *)
let parse arch_info fname =
  try
    try
      let _env, pprog, _ast = Compile.parse_file arch_info fname in
      pprog
    with Pretyping.TyError (loc, msg) ->
      hierror ~loc:(Lone loc) ~kind:"typing error" "%a" Pretyping.pp_tyerror msg
  with HiError err ->
    Format.eprintf "%a@." pp_hierror err;
    exit 1

let print (type reg) (type regx) (type xreg) (type rflag) (type cond)
    (type asm_op) (type extra_op)
    (module Arch : Arch_full.Arch
      with type reg = reg
       and type regx = regx
       and type xreg = xreg
       and type rflag = rflag
       and type cond = cond
       and type asm_op = asm_op
       and type extra_op = extra_op) fmt pprog =
  Printer.pp_pprog ~debug:true Arch.reg_size Arch.asmOp fmt pprog

(* Increments its [errors] argument in case of failure. *)
let parse_and_print fname errors arch =
  let module Arch = (val CoreArchFactory.get_arch_module arch Linux) in
  let pprog = parse Arch.arch_info fname in
  let printed =
    BatFile.with_temporary_out ~prefix:"test" ~suffix:".jazz" (fun oc fname ->
        let fmt = BatFormat.formatter_of_out_channel oc in
        print (module Arch) fmt pprog;
        fname)
  in
  let reparsed = parse Arch.arch_info printed in
  if eq_pmod_items reparsed pprog then errors
  else (
    Format.eprintf "Failure: %s@." fname;
    1 + errors)

(* ---------------------------------------------------------------- *)
let check_file archs path errors =
  config path;
  List.fold_left (parse_and_print path) errors archs

(* ---------------------------------------------------------------- *)
let () = check_dir check_file [] "success" 0 |> exit
