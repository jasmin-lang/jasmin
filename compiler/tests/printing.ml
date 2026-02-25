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
        ("success/common/bug_1145.jazz", disable_warnings [ DuplicateVar ]);
        ("success/x86-64/bug_895.jazz", disable_warnings [ UnusedVar ]);
        ( "success/common/test_warn_var.jazz",
          disable_warnings [ UnusedVar; DuplicateVar ] );
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

  (* FIXME: we need to compare length to compare types, but to compare lengths,
     we need to be able to compare vars that contain types...
     We break the cycle by defining a dedicated check for length vars,
     and check that types are equal to int.
  *)
  let eq_length_var x y =
  x.v_name = y.v_name && x.v_kind = y.v_kind && x.v_ty = Bty Int && y.v_ty = Bty Int
  && eq_annotations x.v_annot y.v_annot

let rec eq_al x y =
  match x, y with
  | Const n1, Const n2 -> n1 = n2
  | Var x1, Var x2 -> eq_length_var x1 x2
  | Neg al1, Neg al2 -> eq_al al1 al2
  | Add (al11, al12), Add (al21, al22) -> eq_al al11 al21 && eq_al al12 al22
  | Sub (al11, al12), Sub (al21, al22) -> eq_al al11 al21 && eq_al al12 al22
  | Mul (al11, al12), Mul (al21, al22) -> eq_al al11 al21 && eq_al al12 al22
  | Div (sg1, al11, al12), Div (sg2, al21, al22) -> sg1 = sg2 && eq_al al11 al21 && eq_al al12 al22
  | Mod (sg1, al11, al12), Mod (sg2, al21, al22) -> sg1 = sg2 && eq_al al11 al21 && eq_al al12 al22
  | Shl (al11, al12), Shl (al21, al22) -> eq_al al11 al21 && eq_al al12 al22
  | Shr (al11, al12), Shr (al21, al22) -> eq_al al11 al21 && eq_al al12 al22
  | _, _ -> false

let eq_ty x y =
  match (x, y) with
  | Bty a, Bty b -> a = b
  | Arr (a, n), Arr (b, m) -> Wsize.wsize_eqb a b && eq_al n m
  | (Bty _ | Arr _), _ -> false

  let eq_pvar x y =
  x.v_name = y.v_name && x.v_kind = y.v_kind && eq_ty x.v_ty y.v_ty
  && eq_annotations x.v_annot y.v_annot

  let eq_pvar_i x y = eq_pvar (L.unloc x) (L.unloc y)
  let eq_pgvar x y = eq_pvar_i x.gv y.gv && x.gs = y.gs

  let rec eq_pexpr x y =
  match (x, y) with
  | Pconst a, Pconst b -> Z.equal a b
  | Pbool a, Pbool b -> Stdlib.Bool.equal a b
  | Parr_init (a, b), Parr_init (c, d) -> Wsize.wsize_eqb a c && eq_al b d
  | Pvar a, Pvar b -> eq_pgvar a b
  | Pget (a, b, c, d, e), Pget (f, g, h, i, j) ->
      a = f && b = g && Wsize.wsize_eqb c h && eq_pgvar d i && eq_pexpr e j
  | Psub (a, b, c, d, e), Psub (f, g, h, i, j) ->
      a = f && Wsize.wsize_eqb b g && eq_al c h && eq_pgvar d i
      && eq_pexpr e j
  | Pload (a, b, d), Pload (e, f, h) ->
      a = e && Wsize.wsize_eqb b f && eq_pexpr d h
  | Papp1 (a, b), Papp1 (c, d) -> a = c && eq_pexpr b d
  | Papp2 (a, b, c), Papp2 (d, e, f) -> a = d && eq_pexpr b e && eq_pexpr c f
  | PappN (a, b), PappN (c, d) -> a = c && eq_pexprs b d
  | Pif (a, b, c, d), Pif (e, f, g, h) ->
      eq_ty a e && eq_pexpr b f && eq_pexpr c g && eq_pexpr d h
  | ( ( Pconst _ | Pbool _ | Parr_init _ | Pvar _ | Pget _ | Psub _ | Pload _
      | Papp1 _ | Papp2 _ | PappN _ | Pif _ ),
      _ ) ->
      false

and eq_pexprs x y = List.for_all2 eq_pexpr x y

let eq_plval x y =
  match (x, y) with
  | Lnone (_, a), Lnone (_, b) -> eq_ty a b
  | Lvar a, Lvar b -> eq_pvar_i a b
  | Lmem (a, b, _, d), Lmem (e, f, _, h) ->
      a = e && Wsize.wsize_eqb b f && eq_pexpr d h
  | Laset (a, b, c, d, e), Laset (f, g, h, i, j) ->
      a = f && b = g && Wsize.wsize_eqb c h && eq_pvar_i d i && eq_pexpr e j
  | Lasub (a, b, c, d, e), Lasub (f, g, h, i, j) ->
      a = f && Wsize.wsize_eqb b g && eq_al c h && eq_pvar_i d i
      && eq_pexpr e j
  | (Lnone _ | Lvar _ | Lmem _ | Laset _ | Lasub _), _ -> false

  let eq_plvals x y = List.for_all2 eq_plval x y


let eq_pgexpr x y =
  match (x, y) with
  | GEword a, GEword b -> eq_pexpr a b
  | GEarray a, GEarray b -> eq_pexprs a b
  | (GEword _ | GEarray _), _ -> false

let eq_prange (x : length grange) (y : length grange) =
  let a, b, c = x and d, e, f = y in
  a = d && eq_pexpr b e && eq_pexpr c f

let rec eq_pstmt x y = List.for_all2 eq_pinstr x y

and eq_pinstr x y =
  eq_annotations x.i_annot y.i_annot && eq_pinstr_r x.i_desc y.i_desc

and eq_pinstr_r (x : _ instr_r) y =
  match (x, y) with
  | Cassgn (a, b, c, d), Cassgn (e, f, g, h) ->
      eq_plval a e && b = f && eq_ty c g && eq_pexpr d h
  | Copn (a, b, c, d), Copn (e, f, g, h) ->
      eq_plvals a e && b = f && c = g && eq_pexprs d h
  | Cassert (a, b), Cassert (c, d) -> a = c && eq_pexpr b d
  | Csyscall (a, b, c, d), Csyscall (e, f, g, h) ->
      eq_plvals a e && b = f && List.for_all2 eq_al c g && eq_pexprs d h
  | Cif (a, b, c), Cif (d, e, f) -> eq_pexpr a d && eq_pstmt b e && eq_pstmt c f
  | Cfor (a, b, c), Cfor (d, e, f) ->
      eq_pvar_i a d && eq_prange b e && eq_pstmt c f
  | Cwhile (a, b, c, _d, e), Cwhile (f, g, h, _i, j) ->
      a = f && eq_pstmt b g && eq_pexpr c h && eq_pstmt e j
  | Ccall (a, b, c, d), Ccall (e, f, g, h) ->
      eq_plvals a e && b.fn_name = f.fn_name && List.for_all2 eq_al c g && eq_pexprs d h
  | ( ( Cassgn _ | Copn _ | Csyscall _ | Cassert _ | Cif _ | Cfor _ | Cwhile _
      | Ccall _ ),
      _ ) ->
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
  && List.for_all2 eq_ty x.f_tyin y.f_tyin
  && List.for_all2 eq_pvar x.f_args y.f_args
  && List.for_all2 eq_ty x.f_tyout y.f_tyout
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
let parse arch_info ctxt fname =
  try
    try
      let _env, pprog, _ast = Compile.parse_file arch_info fname in
      pprog
    with
    | Pretyping.TyError (loc, msg) ->
        hierror ~loc:(Lone loc) ~kind:"typing error" "%a" Pretyping.pp_tyerror
          msg
    | Syntax.ParseError (loc, msg) ->
        hierror ~loc:(Lone loc) ~kind:"parsing" "%s: %s" ctxt
          (Option.default "parse error" msg)
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
  Printer.pp_pprog ~debug:true Arch.reg_size Arch.msf_size Arch.asmOp fmt pprog

(* Increments its [errors] argument in case of failure. *)
let parse_and_print fname errors arch =
  let module Arch = (val CoreArchFactory.get_arch_module arch Linux) in
  let pprog = parse Arch.arch_info fname fname in
  let printed =
    BatFile.with_temporary_out ~prefix:"test" ~suffix:".jazz" (fun oc fname ->
        let fmt = BatFormat.formatter_of_out_channel oc in
        print (module Arch) fmt pprog;
        fname)
  in
  let reparsed = parse Arch.arch_info fname printed in
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
