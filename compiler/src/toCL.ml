open Allocation
open Arch_extra
open Arch_params
open Array_copy
open Array_expansion
open Array_init
open Compiler_util
open Dead_calls
open Dead_code
open Eqtype
open Expr
open Inline
open Lowering
open MakeReferenceArguments
open Propagate_inline
open Remove_globals
open Utils0
open Compiler
open Utils
open Prog
open Glob_options
open Utils
(*
module CL = struct

type ty = Uint of int | Sint of int (* Should be bigger than 1 *)

type const = Z.t

type var = Prog.var

type tyvar = var * ty option

type atom =
  | Aconst of const * ty
  | Avar of var

type lval = tyvar

type arg =
  | Atom of atom
  | Lval of lval

type args = arg list

type instr =
  { iname : string;
    iargs : args; }

let mov (d : lval) (s : atom) =
  { iname = "mov"; iargs = [Lval d; Atom s] }

let op2 iname (d : lval) (s1 : atom) (s2 : atom) =
  { iname; iargs = [Lval d; Atom s1; Atom s2] }

let op2c iname (d : lval) (s1 : atom) (s2 : atom) (c : var) =
  { iname; iargs = [Lval d; Atom s1; Atom s2; Atom (Avar c)] }

let op2_2 iname (d1 : lval) (d2: lval) (s1 : atom) (s2 : atom) =
  { iname; iargs = [Lval d1; Lvar d2 Atom s1; Atom s2] }

let add  = op2   "add"
let adc  = op2_c "adc"
let sub  = op2   "sub"
let subc = op2_2 "subc"
let sbc  = op2_c "sbc"

let pp_arg fmt
let pp_instr fmt (i : instr) =
  Format.fprintf "%s %a;"
    i.iname (pp_list "@ " pp_arg) i.iargs






let adc (d : lval) (s1 : atom) (s2 : atom) (c : var) =
  { iname = "adc"; iargs = [Lval d; Atom s1; Atom s2; Atom (Avar c)] }

let adc (d : lval) (s1 : atom) (s2 : atom) (c : var) =
  { iname = "adc"; iargs = [Lval d; Atom s1; Atom s2; Atom (Avar c)] }


end CL

*)


(*
   TODO:
    - Define a small ast for cryptoline
    - Then do the printing in two steps:
      - Generate the ast
      - Print it

*)


let unsharp = String.map (fun c -> if c = '#' then '_' else c)

let fresh_name name = String.concat "_" [ name; string_of_int (Uniq.gen ())]

let pp_var fmt x =
  Format.fprintf fmt "%s_%s" (unsharp x.v_name) (string_of_uid x.v_id)

let pp_gvar_i fmt x =
  pp_var fmt (L.unloc x)

let pp_print_i fmt z =
  if Z.leq Z.zero z then Z.pp_print fmt z
  else Format.fprintf fmt "(%a)" Z.pp_print z

let pp_uint fmt ws =
  Format.fprintf fmt "uint%i" ws

(* let pp_sint fmt ws = *)
(*   Format.fprintf fmt "@@sint%i" (int_of_ws ws) *)

(* let pp_bw fmt t = *)
(*   Format.fprintf fmt "@@%i" (int_of_ws t) *)

(* let pp_sign t = *)
(*   match t with *)
(*   | Wsize.Signed -> "s" *)
(*   | Unsigned -> "u" *)


let rec pp_rexp fmt e =
  match e with
  | Pconst z ->
    Format.fprintf fmt "%a" pp_print_i z
  | Pvar x ->
    (* let ws = ws_of_ty (L.unloc x.gv).v_ty in
       Format.fprintf fmt "limbs %i [%a]" (int_of_ws ws) pp_gvar_i x.gv *)
    Format.fprintf fmt "%a" pp_gvar_i x.gv
  | Papp1 (Oword_of_int ws, x) ->
    (* Format.fprintf fmt "limbs %i [%a@%i]" (int_of_ws ws) pp_rexp x (int_of_ws ws) *)
    Format.fprintf fmt "%a@%i" pp_rexp x (int_of_ws ws)
  | Papp1(Oneg _, e) ->
    Format.fprintf fmt "(-1) * (%a)" pp_rexp e
  | Papp1(Olnot _, e) ->
    Format.fprintf fmt "not (%a)" pp_rexp e
  | Papp2(Oadd _, e1, e2) ->
    Format.fprintf fmt "(%a) + (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Osub _, e1, e2) ->
    Format.fprintf fmt "(%a) - (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Omul _, e1, e2) ->
    Format.fprintf fmt "(%a) * (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Odiv (Cmp_w (Unsigned,_)), e1, e2) ->
    Format.fprintf fmt "udiv (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Odiv (Cmp_w (Signed,_)), e1, e2) ->
    Format.fprintf fmt "sdiv (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Olxor _, e1, e2) ->
    Format.fprintf fmt "xor (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Oland _, e1, e2) ->
    Format.fprintf fmt "and (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Olor _, e1, e2) ->
    Format.fprintf fmt "or (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Omod (Cmp_w (Unsigned,_)), e1, e2) ->
    Format.fprintf fmt "umod (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Omod (Cmp_w (Signed,_)), e1, e2) ->
    Format.fprintf fmt "smod (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Olsl _, e1, e2) ->
    Format.fprintf fmt "shl (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Olsr _, e1, e2) ->
    Format.fprintf fmt "shr (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp1(Ozeroext (osz,isz), e1) ->
    Format.fprintf fmt "(uext %a %i)"
      pp_rexp e1
      (int_of_ws osz- int_of_ws isz)
  | Pabstract ({name="se_16_64"}, [v]) ->
    Format.fprintf fmt "sext %a 48"
      pp_rexp v
  | Pabstract ({name="se_32_64"}, [v]) ->
    Format.fprintf fmt "sext %a 32"
      pp_rexp v
  (* FIXME why this is needed *)
  | Pabstract ({name="ze_16_64"}, [v]) ->
    Format.fprintf fmt "uext %a 48"
      pp_rexp v
(*
| Pabstract ({name="smod64"}, [v1;v2]) ->
    Format.fprintf fmt "smod (%a) (%a)"
      pp_rexp v1
      pp_rexp v2
*)
  | Presult x ->
    Format.fprintf fmt "%a" pp_gvar_i x.gv
  | _ -> assert false

let pp_rexp_par fmt es = Format.fprintf fmt "(%a)" pp_rexp es

let rec pp_rpred fmt e =
  match e with
  | Pbool (true) -> Format.fprintf fmt "true"
  | Pbool (false) -> Format.fprintf fmt "false"
  | Papp1(Onot, e) ->
    Format.fprintf fmt "~(%a)" pp_rpred e
  | Papp2(Oeq _, e1, e2)  ->
    Format.fprintf fmt "(%a) = (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Obeq, e1, e2)  ->
    Format.fprintf fmt "eq (%a) (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Oand, e1, e2)  ->
    Format.fprintf fmt "(%a) /\\ (%a)"
      pp_rpred e1
      pp_rpred e2
  | Papp2(Oor, e1, e2)  ->
    Format.fprintf fmt "(%a) \\/ (%a)"
      pp_rpred e1
      pp_rpred e2
  | Papp2(Ole (Cmp_w (Signed,_)), e1, e2)  ->
    Format.fprintf fmt "(%a) <=s (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Ole (Cmp_w (Unsigned,_)), e1, e2)  ->
    Format.fprintf fmt "(%a) <= (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Olt (Cmp_w (Signed,_)), e1, e2)  ->
    Format.fprintf fmt "(%a) <s (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Olt (Cmp_w (Unsigned,_)), e1, e2)  ->
    Format.fprintf fmt "(%a) < (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Oge (Cmp_w (Signed,_)), e1, e2)  ->
    Format.fprintf fmt "(%a) >=s (%a)"
      pp_rexp e1
      pp_rpred e2
  | Papp2(Oge (Cmp_w (Unsigned,_)), e1, e2)  ->
    Format.fprintf fmt "(%a) >= (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Ogt (Cmp_w (Signed,_)), e1, e2)  ->
    Format.fprintf fmt "(%a) >s (%a)"
      pp_rexp e1
      pp_rexp e2
  | Papp2(Ogt (Cmp_w (Unsigned,_)), e1, e2)  ->
    Format.fprintf fmt "(%a) > (%a)"
      pp_rexp e1
      pp_rexp e2
  | Pif(_, e1, e2, e3)  ->
    Format.fprintf fmt "((~(%a))\\/ (%a)) /\\ ((%a) \\/ (%a))"
      pp_rpred e1
      pp_rpred e2
      pp_rpred e1
      pp_rpred e3
  | Pabstract ({name="eqsmod64"}, es) ->
    Format.fprintf fmt "eqsmod %a"
      (pp_list " " pp_rexp_par) es
  | _ ->  assert false

let rec extract_list e aux =
  match e with
  | Pabstract ({name="word_nil"}, []) -> List.rev aux
  | Pabstract ({name="word_cons"}, [h;q]) -> extract_list q (h :: aux)
  | _ -> assert false


let rec pp_eexp_par fmt es = Format.fprintf fmt "(%a)" pp_eexp es
and pp_eexp fmt e =
  match e with
  | Pconst z ->
    Format.fprintf fmt "%a" pp_print_i z
  | Pvar x ->
    Format.fprintf fmt "%a" pp_gvar_i x.gv
  | Papp1 (Oword_of_int _ws, x) ->
    Format.fprintf fmt "%a" pp_eexp x
  | Papp1 (Oint_of_word _ws, x) ->
    Format.fprintf fmt "%a" pp_eexp x
  | Papp1(Oneg _, e) ->
    Format.fprintf fmt "(-1)*(%a)" pp_eexp e
  | Papp2(Oadd _, e1, e2) ->
    Format.fprintf fmt "(%a) + (%a)"
      pp_eexp e1
      pp_eexp e2
  | Papp2(Osub _, e1, e2) ->
    Format.fprintf fmt "(%a) - (%a)"
      pp_eexp e1
      pp_eexp e2
  | Papp2(Omul _, e1, e2) ->
    Format.fprintf fmt "(%a) * (%a)"
      pp_eexp e1
      pp_eexp e2
  (*  | Papp2(Odiv _, e1, e2) ->
      Format.fprintf fmt "(%a) / (%a)"
        pp_eexp e1
        pp_eexp e2     *)
  | Pabstract ({name="limbs"}, [h;q]) ->
    Format.fprintf fmt "(limbs %a [%a])"
      pp_eexp h
      (pp_list ", "  pp_eexp_par) (extract_list q [])
  | Pabstract ({name="indetX"}, _) ->
    Format.fprintf fmt "X"
  | Pabstract ({name="pow"}, [b;e]) ->
    Format.fprintf fmt "(%a**%a)"
      pp_eexp b
      pp_eexp e
  | Pabstract ({name="couple"}, [h;q]) ->
    Format.fprintf fmt "[%a,%a]"
      pp_eexp h
      pp_eexp q
  | Presult x ->
    Format.fprintf fmt "%a" pp_gvar_i x.gv
  | _ -> assert false


let rec  pp_epred fmt e =
  match e with
  | Pbool (true) -> Format.fprintf fmt "true"
  | Papp2(Oeq _, e1, e2)  ->
    Format.fprintf fmt "eq (%a) (%a)"
      pp_eexp e1
      pp_eexp e2
  | Papp2(Oand, e1, e2)  ->
    Format.fprintf fmt "and (%a) (%a)"
      pp_epred e1
      pp_epred e2
  | Pabstract ({name="eqmod"} as opa, [h1;h2;h3]) ->
    Format.fprintf fmt "%s %a %a"
      opa.name
      (pp_list " " pp_eexp_par) [h1;h2]
      pp_eexp h3
  | Pabstract ({name="eqmodpol"}, es) ->
    Format.fprintf fmt "eqmod %a %a [%a,%a]"
      pp_eexp_par (List.nth es 1)
      pp_eexp_par (List.nth es 2)
      pp_eexp_par (List.nth es 3)
      pp_eexp_par (List.nth es 4)
  (*x = if b then e1 else e2 --> b*e1 + (1-b)e2*)
  | _ -> assert false

let pp_lval fmt (x,ws) =
  match x with
  | Lvar x -> Format.fprintf fmt "%a@@%a" pp_gvar_i x pp_uint ws
  (* Manuel: Never reached for assignments. *)
  | Lnone _  -> Format.fprintf fmt "NONE____"
  | Lmem _ | Laset _ | Lasub _ -> assert false

(* Manuel: We translate some atomic expressions based on a size
   which is not theirs. See consts and word_of_ints below.
   Does this make sense everywhere? *)
let rec pp_atome fmt (x,ws) =
  match x with
  | Pconst z ->
    Format.fprintf fmt "%a@@%a" pp_print_i z pp_uint ws
  | Pvar x ->
    let ws_x = ws_of_ty (L.unloc x.gv).v_ty in
    Format.fprintf fmt "%a@@%a" pp_gvar_i x.gv pp_uint (int_of_ws ws_x)
  | Papp1 (Oword_of_int _ws, x) ->
    Format.fprintf fmt "%a" pp_atome (x, ws)
  | _ -> assert false

type trans =
  | Smt
  | Cas

let rec power acc n = match n with | 0 -> acc | n -> power (acc * 2) (n - 1)

let pp_mov fmt ws xs es =
  match (List.nth es 0) with
  | Pvar x ->
    let ws_x = ws_of_ty (L.unloc x.gv).v_ty in
    if ws_x != ws
    then
      Format.fprintf fmt "cast %a %a"
        pp_lval (List.nth xs 0, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws_x)
    else
      Format.fprintf fmt "mov %a %a"
        pp_lval (List.nth xs 0, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)
  | Pconst _ ->
      Format.fprintf fmt "mov %a %a"
        pp_lval (List.nth xs 0, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)
  | Papp1 (Oword_of_int ws, Pconst x) ->
      Format.fprintf fmt "mov %a %a@uint%i"
        pp_lval (List.nth xs 0, int_of_ws ws)
        pp_print_i x
        (int_of_ws ws)
  | _ -> assert false

 let rec pp_cast fmt (x,ws) =
    match x with
    | Pconst z -> x
    | Pvar va ->
      let ws_x = ws_of_ty (L.unloc va.gv).v_ty in
      if ws = ws_x then x
      else
        let v = va.gv in
        let k = va.gs in
        let v_ = v.L.pl_desc in
        let v1 = V.mk "TMP" v_.v_kind (CoreIdent.tu ws) v_.v_dloc v_.v_annot in
        let pp fmt = pp_mov fmt ws [(Lvar (L.mk_loc v.pl_loc v1))] [x]
        in
        Format.fprintf fmt "%t;@ " pp;
        let v  = { v with L.pl_desc = v1 } in
        (* FIXME : I think we should not view it as a global is x is global *)
        let v0 = { gv = v; gs = k } in
        Pvar v0
    | Papp1 (Oword_of_int _ws, x) ->
      pp_cast fmt (x, ws)
    | _ -> assert false

module type BaseOp = sig
  type op
  type extra_op

  val pp_baseop :
    Stdlib__Format.formatter ->
    trans ->
    int Jasmin__Prog.glval list ->
    op -> int Jasmin__Prog.gexpr list -> unit
end

module I = struct
  let pp_var fmt (x,ws) =
      match x with
      | Pvar x ->
        Format.fprintf fmt "%a@@%a" pp_gvar_i x.gv pp_uint ws
      | _ -> assert false (* Manuel: What is this case? *)

  let rec pp_const fmt x =
      match x with
      | Pconst z ->
        Format.fprintf fmt "%a" pp_print_i z
      | Papp1 (Oword_of_int _ws, x) ->
        Format.fprintf fmt "%a" pp_const x
      | _ -> assert false

  let rec get_const x =
      match x with
      | Pconst z -> Z.to_int z
      | Papp1 (Oword_of_int _ws, x) -> get_const x
      | _ -> assert false


  let pp_op2_1 op fmt ws d v1 v2 =
    Format.fprintf fmt "%s %a %a %a"
      op
      pp_lval (d, int_of_ws ws)
      pp_atome (v1, int_of_ws ws)
      pp_atome (v2, int_of_ws ws)

  let pp_add = pp_op2_1 "add"

end

module X86BaseOp : BaseOp
  with type op = X86_instr_decl.x86_op
  with type extra_op = X86_extra.x86_extra_op
= struct

  type op = X86_instr_decl.x86_op
  type extra_op = X86_extra.x86_extra_op

  (* For x86 *)

  let pp_baseop fmt trans xs o es =

    match o with
    (* Manuel: Special case not handled in assignments? *)
    | X86_instr_decl.MOV ws -> pp_mov fmt ws xs es

    | ADD ws ->
      let v1 = pp_cast fmt (List.nth es 0, ws) in
      let v2 = pp_cast fmt (List.nth es 1, ws) in
      I.pp_add fmt ws (List.nth xs 5) v1 v2

    | SUB ws ->
      begin
        let v1 = pp_cast fmt (List.nth es 0, ws) in
        let v2 = pp_cast fmt (List.nth es 1, ws) in

        match trans with
        | Smt ->
            Format.fprintf fmt "sub %a %a %a"
            pp_lval (List.nth xs 5, int_of_ws ws)
            pp_atome (v1, int_of_ws ws)
            pp_atome (v2, int_of_ws ws)
        | Cas ->
          Format.fprintf fmt "subs TMP__ %a %a %a"
            pp_lval (List.nth xs 5, int_of_ws ws)
            pp_atome (v1, int_of_ws ws)
            pp_atome (v2, int_of_ws ws)
      end

    | IMULr ws ->
      Format.fprintf fmt "mull TMP__ %a %a %a"
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)
        pp_atome (List.nth es 1, int_of_ws ws)

    | IMULri ws ->
      Format.fprintf fmt "mull TMP__ %a %a %a"
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)
        pp_atome (List.nth es 1, int_of_ws ws)

    | ADC ws ->
      Format.fprintf fmt "adcs %a %a %a %a %a"
        pp_lval (List.nth xs 1, 1)
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)
        pp_atome (List.nth es 1, int_of_ws ws)
        I.pp_var (List.nth es 2, 1)

    | SBB ws ->
      Format.fprintf fmt "sbbs %a %a %a %a %a"
        pp_lval (List.nth xs 1, 1)
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)
        pp_atome (List.nth es 1, int_of_ws ws)
        I.pp_var (List.nth es 2, 1)

    | NEG ws ->
      Format.fprintf fmt "sub %a %a %a"
        pp_lval (List.nth xs 4, int_of_ws ws)
        pp_print_i (Z.of_int 0)
        pp_atome (List.nth es 0, int_of_ws ws)

    | INC ws ->
      Format.fprintf fmt "add %a %a %a"
        pp_lval (List.nth xs 4, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)
        pp_atome (Pconst (Z.of_int 1), int_of_ws ws)

    | DEC ws ->
      Format.fprintf fmt "sub %a %a %a"
        pp_lval (List.nth xs 4, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)
        pp_atome (Pconst (Z.of_int 1), int_of_ws ws)

    | AND ws ->
      Format.fprintf fmt "and %a %a %a"
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)
        pp_atome (List.nth es 1, int_of_ws ws)

    | ANDN ws ->
      Format.fprintf fmt "not %a %a;\nand %a %a %a"
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (List.nth es 1, int_of_ws ws)

    | OR ws ->
      Format.fprintf fmt "or %a %a %a"
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)
        pp_atome (List.nth es 1, int_of_ws ws)

    | XOR ws ->
      Format.fprintf fmt "xor %a %a %a"
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)
        pp_atome (List.nth es 1, int_of_ws ws)

    | NOT ws ->
      Format.fprintf fmt "not %a %a"
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)

    | SHL ws ->
      begin
        match trans with
        | Smt ->
          Format.fprintf fmt "shl %a %a %a"
            pp_lval (List.nth xs 5, int_of_ws ws)
            pp_atome (List.nth es 0, int_of_ws ws)
            I.pp_const (List.nth es 1)
        | Cas ->
          Format.fprintf fmt "shls TMP__ %a %a %a"
            pp_lval (List.nth xs 5, int_of_ws ws)
            pp_atome (List.nth es 0, int_of_ws ws)
            I.pp_const (List.nth es 1)
      end
    | SHR ws ->
      Format.fprintf fmt "shr %a %a %a"
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)
        I.pp_const (List.nth es 1)

    | SAL ws ->
      (* FIXME the type of second argument is wrong *)
      Format.fprintf fmt "shl %a %a %a"
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (List.nth es 0, int_of_ws ws)
        I.pp_const (List.nth es 1)

    | SAR ws ->
      begin
        match trans with
        | Smt ->
          let v1 = fresh_name "TMP" in
          let v2 = fresh_name "TMP" in
          Format.fprintf fmt "cast %s@@sint%d %a;@ "
            v1
            (int_of_ws ws)
            pp_atome (List.nth es 0, int_of_ws ws);
          Format.fprintf fmt "ssplit %s@@sint%d dontcare %s@@sint%d %a;@ "
            v2
            (int_of_ws ws)
            v1
            (int_of_ws ws)
            I.pp_const (List.nth es 1);
          Format.fprintf fmt "cast %a %s@@sint%d"
            pp_lval (List.nth xs 5, int_of_ws ws)
            v2
            (int_of_ws ws)
        | Cas ->
          let v1 = fresh_name "TMP" in
          let v2 = fresh_name "TMP" in
          let v3 = fresh_name "TMP" in
          let v4 = fresh_name "TMP" in
          let v5 = fresh_name "TMP" in
          let v6 = fresh_name "TMP" in
          let c = I.get_const (List.nth es 1) in
          Format.fprintf fmt "spl %s@@uint1 %s@@uint%d %a %d;@ "
            v1
            v2
            (int_of_ws ws - 1)
            pp_atome (List.nth es 0, int_of_ws ws)
            (int_of_ws ws - 1);
          Format.fprintf fmt "join %s@@uint%d 0@@uint%d %s@@uint1;@ "
            v3
            c
            (c-1)
            v1;
          Format.fprintf fmt "mul %s@@uint%d %s@@uint%d %d@@uint%d;@ "
            v4
            c
            v3
            c
            (power 1 c - 1)
            c;
          Format.fprintf fmt "join %s@@uint%d %s@@uint%d %a;@ "
            v5
            (c + (int_of_ws ws))
            v4
            c
            pp_atome (List.nth es 0, int_of_ws ws);
          Format.fprintf fmt "spl %a %s@@uint%d %s@@uint%d %d"
            pp_lval (List.nth xs 5, int_of_ws ws)
            v6
            c
            v5
            (c + (int_of_ws ws))
            c
      end

    | MOVSX (ws1, ws2) ->
      begin
        match trans with
        | Smt ->
          let v1 = fresh_name "TMP" in
          let v2 = fresh_name "TMP" in
          Format.fprintf fmt "cast %s@@sint%d %a;@ "
            v1
            (int_of_ws ws2)
            pp_atome (List.nth es 0, int_of_ws ws2);
          Format.fprintf fmt "cast %s@@sint%d %s@@sint%d;@ "
            v2
            (int_of_ws ws1)
            v1
            (int_of_ws ws2);
          Format.fprintf fmt "cast %a %s@@sint%d"
            pp_lval (List.nth xs 0, int_of_ws ws1)
            v2
            (int_of_ws ws1)
        | Cas ->
          let v1 = fresh_name "TMP" in
          let v2 = fresh_name "TMP" in
          let v3 = fresh_name "TMP" in
          let v4 = fresh_name "TMP" in
          Format.fprintf fmt "spl %s@@uint1 %s@@uint%d %a %d;@ "
            v1
            v2
            (int_of_ws ws2 -1)
            pp_atome (List.nth es 0, int_of_ws ws2)
            (int_of_ws ws2 -1);
          Format.fprintf fmt "join %s@@uint%d 0@@uint%d %s@@uint1;@ "
            v3
            (int_of_ws ws2)
            (int_of_ws ws2 -1)
            v1;
          Format.fprintf fmt "mul %s@@uint%d %s@@uint%d %d@uint%d;@ "
            v4
            (int_of_ws ws2)
            v3
            (int_of_ws ws2)
            (power 1 (int_of_ws ws1 - (int_of_ws ws2)) - 1)
            (int_of_ws ws2);
          Format.fprintf fmt "join %a %s@@uint%d %a"
            pp_lval (List.nth xs 0, int_of_ws ws1)
            v4
            (int_of_ws ws2)
            pp_atome (List.nth es 0, int_of_ws ws2)
      end
    | MOVZX (ws1, ws2) ->
      Format.fprintf fmt "cast %a %a"
        pp_lval (List.nth xs 0, int_of_ws ws1)
        pp_atome (List.nth es 0, int_of_ws ws2)
    | _ -> assert false

end

module ARMBaseOp : BaseOp
  with type op = Arm_instr_decl.arm_op
   and  type extra_op = Arm_extra.__
= struct

  open Arm_instr_decl

  type op = Arm_instr_decl.arm_op
  type extra_op = Arm_extra.__

  let ws = Wsize.U32

  let pp_baseop fmt trans xs o es =
    let mn, opt = match o with Arm_instr_decl.ARM_op (mn, opt) -> mn, opt in
    match mn with
    | ADD -> assert false
(*
      let v1 = pp_cast fmt (List.nth es 0, ws) in
      let v2 = pp_cast fmt (List.nth es 1, ws) in
      let v2' = pp_shifted fmt opt v2 es in
      Format.fprintf fmt "add %a %a %a"
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (v1, int_of_ws ws)
        pp_atome (v2', int_of_ws ws)
*)

| ADC
| MUL
| MLA
| MLS
| SDIV
| SUB
| RSB
| UDIV
| UMULL
| UMAAL
| UMLAL
| SMULL
| SMLAL
| SMMUL
| SMMULR
| SMUL_hw _
| SMLA_hw _
| SMULW_hw _
| AND
| BFC
| BFI
| BIC
| EOR
| MVN
| ORR
| ASR
| LSL
| LSR
| ROR
| REV
| REV16
| REVSH
| ADR
| MOV
| MOVT
| UBFX
| UXTB
| UXTH
| SBFX
| CLZ
| CMP
| TST
| CMN
| LDR
| LDRB
| LDRH
| LDRSB
| LDRSH
| STR
| STRB
| STRH -> assert false

end

module Mk(O:BaseOp) = struct

  let pp_extop fmt xs o es tcas = assert false

  let pp_ext_op fmt xs o es trans =
    match o with
    | Arch_extra.BaseOp (_, o) -> O.pp_baseop fmt trans xs o es
    | Arch_extra.ExtOp o -> pp_extop fmt xs o es trans

  let pp_sopn fmt xs o es tcas =
    match o with
    | Sopn.Opseudo_op _ -> assert false
    | Sopn.Oslh _ -> assert false
    | Sopn.Oasm o -> pp_ext_op fmt xs o es tcas

  let rec filter_clause cs (cas,smt) =
    match cs with
    | [] -> cas,smt
    | (Expr.Cas,c)::q -> filter_clause q (c::cas,smt)
    | (Expr.Smt,c)::q -> filter_clause q (cas,c::smt)

  let pp_clause fmt f_pre =
    let cas,smt = filter_clause f_pre ([],[]) in
    match cas,smt with
    | [],[] ->
      Format.fprintf fmt "true@ &&@ true"
    | [],smt ->
      Format.fprintf fmt "true@ &&@ and [@[<v>%a@]]"
        (pp_list ",@ " pp_rpred) smt
    | cas,[] ->
      Format.fprintf fmt "and [@[<v>%a@]] @ &&@ true"
        (pp_list ",@ " pp_epred) cas
    | _,_ ->
      Format.fprintf fmt "and [@[<v>%a@]] @ &&@ and [@[<v>%a@]]"
        (pp_list ",@ " pp_epred) cas
        (pp_list ",@ " pp_rpred) smt

  let pp_i pd asmOp fds fmt i =
    let mk_trans = Annot.filter_string_list None ["smt", Smt ; "cas", Cas ] in
    let atran annot =
      match Annot.ensure_uniq1 "tran" mk_trans annot with
      | None -> Smt
      | Some aty -> aty
    in
    let trans = atran i.i_annot in
    match i.i_desc with
    | Cassert (t, p, e) ->
      let efmt, pp_pred  =
        match p with
        | Expr.Cas -> format_of_string "@[<v>%s %a && true@]",pp_epred
        | Expr.Smt -> format_of_string "@[<v>%s true && %a@]",pp_rpred
      in
      begin
        match t with
        | Expr.Assert -> Format.fprintf fmt efmt "assert" pp_pred e
        | Expr.Assume -> Format.fprintf fmt efmt "assume" pp_pred e
        | Expr.Cut -> assert false
      end
    | Csyscall _ | Cif _ | Cfor _ | Cwhile _ -> assert false
    | Ccall (r,f,params) ->
      let fd = List.find (fun fd -> fd.f_name.fn_id = f.fn_id) fds in
      let aux f =
        List.map (fun (prover,clause) -> prover, f clause)
      in
      let check v vi=
        (L.unloc v.gv).v_name = vi.v_name && (L.unloc v.gv).v_id = vi.v_id
      in
      let aux1 v =
        match List.findi (fun _ vi -> check v vi) fd.f_args with
        | i,_ ->  let _,e = List.findi (fun ii _ -> ii = i) params in
          e
        | exception _ ->
          begin
            match List.findi (fun _ vi -> check v (L.unloc vi)) fd.f_ret with
            | i,_ ->  let _,e = List.findi (fun ii _ -> ii = i) r in
              begin
                match e with
                | Lvar v ->  Pvar({gv = v; gs = Expr.Slocal})
                | _ ->  Pvar v
              end
            | exception _ ->  Pvar v
          end
      in
      let aux2 = Subst.gsubst_e (fun x -> x) aux1 in
      let pre = aux aux2 fd.f_contra.f_pre in
      let post = aux aux2  fd.f_contra.f_post in
      Format.fprintf fmt "assert @[<v>%a@]; @ assume @[<v>%a@]"
        pp_clause pre
        pp_clause post

    | Cassgn (a, _, _, e) ->
      begin
        match a with
        | Lvar x ->
          (* Manuel: we keep word sizes in assignments. *)
          let ws_x = ws_of_ty (L.unloc x).v_ty in
          Format.fprintf fmt "@[<h>mov %a %a@]"
            pp_lval (a, int_of_ws ws_x)
            pp_atome (e, int_of_ws ws_x)
        (* No memory array or subarray assignments *)
        | Lnone _ | Lmem _ | Laset _ |Lasub _ -> assert false
      end
    (* Manuel: we are sending MOVs here *)
    | Copn(xs, _, o, es) -> pp_sopn fmt xs o es trans

  let pp_c pd asmOp fds fmt c =
    Format.fprintf fmt "@[<v>%a;@]"
      (pp_list ";@ " (pp_i pd asmOp fds)) c

  let pp_ty fmt ty =
    match ty with
    | Bty Bool -> Format.fprintf fmt "uint1"
    (* Manuel: We should have a way to set default width for smt words.
       For example, why are we mapping int to uint64? *)
    | Bty Int -> Format.fprintf fmt "uint64"
    | Bty (U ws) -> Format.fprintf fmt "uint%i" (int_of_ws ws)
    | Bty (Abstract _) -> assert false
    | Arr _ -> assert false

  let pp_args fmt xs =
    (pp_list ",@ "
       (fun fmt x -> Format.fprintf fmt "%a %a"
           pp_ty x.v_ty pp_var x)) fmt xs

  let pp_fun pd asmOp fds fmt fd =
    let ret = List.map L.unloc fd.f_ret in
    let args = List.fold_left (
        fun l a ->
          if List.exists (fun x -> (x.v_name = a.v_name) && (x.v_id = a.v_id)) l
          then l else a :: l
      ) fd.f_args ret in
    Format.fprintf fmt
      "@[<v>proc main(@[<hov>%a@]) = @ {@[<v>@ %a@]@ }@ %a@ ghost X@@bit : true && true;@ {@[<v>@ %a@] @ }@ @]"
      pp_args args
      pp_clause fd.f_contra.f_pre
      (pp_c pd asmOp fds) fd.f_body
      pp_clause fd.f_contra.f_post

end
