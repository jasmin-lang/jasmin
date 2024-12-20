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

let unsharp = String.map (fun c -> if c = '#' then '_' else c)

module CL = struct

  type const = Z.t

  let pp_const fmt c = Format.fprintf fmt "(%s)" (Z.to_string c)

  let pp_lconst fmt cl = Format.fprintf fmt "[%a]" (pp_list ", " pp_const) cl

  type var = Prog.var

  let pp_var fmt x =
    Format.fprintf fmt "%s_%s" (unsharp x.v_name) (string_of_uid x.v_id)

  type ty =
    | Uint of int
    | Sint of int (* Should be bigger than 1 *)
    | Bit
    | Vector of int * ty

  let rec pp_ty fmt ty =
    match ty with
    | Uint i -> Format.fprintf fmt "uint%i" i
    | Sint i -> Format.fprintf fmt "sint%i" i
    | Bit -> Format.fprintf fmt "bit"
    | Vector (i,t) -> Format.fprintf fmt "%a[%i]" pp_ty t i

  let pp_cast fmt ty = Format.fprintf fmt "%@%a" pp_ty ty

  type tyvar = var * ty

  let pp_vector fmt typ =
    match typ with
    | Vector _ -> Format.fprintf fmt "%%"
    | _ -> ()

  let pp_vvar fmt (x, ty) =
      Format.fprintf fmt "%a%a" pp_vector ty pp_var x

  let pp_tyvar fmt ((x, ty) as v) =
      Format.fprintf fmt "%a%a" pp_vvar v pp_cast ty

  let pp_tyvars fmt xs =
    Format.fprintf fmt "%a" (pp_list ",@ " pp_tyvar) xs

  let pp_tyvar2 fmt (x, ty) =
    Format.fprintf fmt "%a%a" pp_vector ty pp_var x

  let pp_tyvars2 fmt xs =
    Format.fprintf fmt "%a" (pp_list ",@ " pp_tyvar2) xs

  (* Expression over z *)

  module I = struct

    type eexp =
      | Iconst of const
      | Ivar   of tyvar
      | Iunop  of string * eexp
      | Ibinop of eexp * string * eexp
      | Ilimbs of const * eexp list
      | IUnPack of tyvar * int * int * bool

    let (!-) e1 = Iunop ("-", e1)
    let (-) e1 e2 = Ibinop (e1, "-", e2)
    let (+) e1 e2 = Ibinop (e1, "+", e2)
    let mull e1 e2 = Ibinop (e1, "*", e2)
    let power e1 e2 = Ibinop (e1, "**", e2)

    let rec pp_eexp fmt e =
      match e with
      | Iconst c    -> pp_const fmt c
      | Ivar   x    -> pp_tyvar2 fmt x
      | Iunop(s, e) -> Format.fprintf fmt "(%s %a)" s pp_eexp e
      | Ibinop (e1, s, e2) -> Format.fprintf fmt "(%a %s %a)" pp_eexp e1 s pp_eexp e2
      | Ilimbs (c, es) ->
        Format.fprintf fmt  "(limbs %a [%a])"
          pp_const c
          (pp_list ",@ " pp_eexp) es
      | IUnPack _ -> assert false

    type epred =
      | Eeq of eexp * eexp
      | Eeqmod of eexp * eexp * eexp list

    let pp_epred fmt ep =
      match ep with
      | Eeq(e1, e2) -> Format.fprintf fmt "(%a = %a)" pp_eexp e1 pp_eexp e2
      | Eeqmod(e1,e2, es) ->
        Format.fprintf fmt "(%a = %a (mod [%a]))"
          pp_eexp e1
          pp_eexp e2
          (pp_list ",@ " pp_eexp) es

    let pp_epreds fmt eps =
      if eps = [] then Format.fprintf fmt "true"
      else Format.fprintf fmt "/\\[@[%a@]]" (pp_list ",@ " pp_epred) eps

  end

  (* Range expression *)
  module R = struct

    type rexp =
      | Rvar   of tyvar
      | Rconst of int * const
      | Ruext of rexp * int
      | Rsext of rexp * int
      | Runop  of string * rexp
      | Rbinop of rexp * string * rexp
      | RVget  of tyvar * const
      | UnPack of  tyvar * int * int * bool
      | Rlimbs of const * rexp list

    let const (i1,z1) = Rconst (i1,z1)
    let (!-) e1 = Runop ("-", e1)
    let minu e1 e2 = Rbinop (e1, "-", e2)
    let add e1 e2 = Rbinop (e1, "+", e2)
    let mull e1 e2 = Rbinop (e1, "*", e2)
    let neg e1 = Runop ("neg", e1)
    let not e1 = Runop ("not", e1)

    let rec pp_rexp fmt r =
      match r with
      | Rvar x -> pp_tyvar fmt x
      | Rconst (c1,c2) -> Format.fprintf fmt "(const %i %a)" c1 pp_const c2
      | Ruext (e, c) -> Format.fprintf fmt "(uext %a %i)" pp_rexp e c
      | Rsext (e, c) -> Format.fprintf fmt "(sext %a %i)" pp_rexp e c
      | Runop(s, e) -> Format.fprintf fmt "(%s %a)" s pp_rexp e
      | Rbinop(e1, s, e2) ->  Format.fprintf fmt "(%a %s %a)" pp_rexp e1 s pp_rexp e2
      | RVget(e,c) ->
        Format.fprintf fmt  "(%a[%a])"
          pp_tyvar e
          pp_const c
      | Rlimbs (c, es) ->
        Format.fprintf fmt  "(limbs %a [%a])"
          pp_const c
          (pp_list ",@ " pp_rexp) es
      | UnPack _ -> assert false

    type rpred =
      | RPcmp   of rexp * string * rexp
      | RPnot   of rpred
      | RPand   of rpred list
      | RPor    of rpred list
      | RPeqsmod of rexp * rexp * rexp

    let eq e1 e2 = RPcmp (e1, "=", e2)
    let ult e1 e2 = RPcmp (e1, "<", e2)
    let ule e1 e2 = RPcmp (e1, "<=", e2)
    let ugt e1 e2 = RPcmp (e1, ">", e2)
    let uge e1 e2 = RPcmp (e1, ">=", e2)

    let rec pp_rpred fmt rp =
      match rp with
      | RPcmp(e1, s, e2) -> Format.fprintf fmt "(%a %s %a)" pp_rexp e1 s pp_rexp e2
      | RPnot e -> Format.fprintf fmt "(~ %a)" pp_rpred e
      | RPand rps ->
        begin
          match rps with
          | [] -> Format.fprintf fmt "true"
          | [h] -> pp_rpred fmt h
          | h :: q -> Format.fprintf fmt "/\\[%a]" (pp_list ",@ " pp_rpred) rps
        end
      | RPor  rps -> Format.fprintf fmt "\\/[%a]" (pp_list ",@ " pp_rpred) rps
      | RPeqsmod (e1,e2,e3) -> Format.fprintf fmt "(eqsmod %a %a %a)" pp_rexp e1 pp_rexp e2 pp_rexp e3

    let pp_rpreds fmt rps = pp_rpred fmt (RPand rps)

  end

  type clause = I.epred list * R.rpred list

  let pp_clause fmt (ep,rp) =
    Format.fprintf fmt "@[<hov 2>@[%a@] &&@ @[%a@]@]"
      I.pp_epreds ep
      R.pp_rpreds rp

  type gvar = var

  let pp_gvar fmt x =
    Format.fprintf fmt "%a@@bit :" pp_var x

  let pp_gvars fmt xs =
    Format.fprintf fmt "%a" (pp_list ",@ " pp_gvar) xs

  module Instr = struct

    type atom =
      | Aconst of const * ty
      | Avar of tyvar
      | Avecta of tyvar * int
      | Avatome of atom list

    let rec pp_atom fmt a =
      match a with
      | Aconst (c, ty) -> Format.fprintf fmt "%a%a" pp_const c pp_cast ty
      | Avar tv -> pp_tyvar fmt tv
      | Avecta (v, i) -> Format.fprintf fmt "%a[%i]" pp_vvar v i
      | Avatome al -> Format.fprintf fmt "[%a]" (pp_list ", " pp_atom) al

    type lval =
      | Llvar of tyvar
      | Lvatome of lval list

    let rec pp_lval fmt l =
      match l with
      | Llvar tv -> pp_tyvar fmt tv
      | Lvatome ll -> Format.fprintf fmt "[%a]" (pp_list ", " pp_lval) ll

    type arg =
      | Atom of atom
      | Lval of lval
      | Const of const
      | Lconst of const list
      | Ty    of ty
      | Pred of clause
      | Gval of gvar

    type args = arg list

    let pp_arg fmt a =
      match a with
      | Atom a  -> pp_atom fmt a
      | Lval lv -> pp_lval fmt lv
      | Const c -> pp_const fmt c
      | Lconst cl -> pp_lconst fmt cl
      | Ty ty   -> pp_ty fmt ty
      | Pred cl -> pp_clause fmt cl
      | Gval x  -> pp_gvar fmt x

    type instr =
      { iname : string;
        iargs : args; }

    let pp_instr fmt (i : instr) =
      Format.fprintf fmt "%s %a;"
        i.iname (pp_list " " pp_arg) i.iargs

    let pp_instrs fmt (is : instr list) =
      Format.fprintf fmt "%a" (pp_list "@ " pp_instr) is

    module Op1 = struct

      let op1 iname (d : lval) (s : atom) =
        { iname; iargs = [Lval d; Atom s] }

      let mov  = op1 "mov"
      let not  = op1 "not"

    end

    module Op2 = struct

      let op2 iname (d : lval) (s1 : atom) (s2 : atom) =
        { iname; iargs = [Lval d; Atom s1; Atom s2] }

      let add  = op2  "add"
      let sub  = op2  "sub"
      let mul  = op2  "mul"
      let smul = op2 "smul"
      let seteq = op2 "seteq"
      let and_  = op2 "and"
      let xor  = op2  "xor"
      let mulj = op2  "mulj"
      let setne = op2 "setne"
      let or_   = op2 "or"
      let join = op2 "join"

    end

    module Op2c = struct

      let op2c iname (d : lval) (s1 : atom) (s2 : atom) (c : tyvar) =
        { iname; iargs = [Lval d; Atom s1; Atom s2; Atom (Avar c)] }

      let adc  = op2c  "adc"
      let sbc  = op2c  "sbc"
      let sbb  = op2c  "sbb"

    end

    module Op2_2 = struct

      let op2_2 iname (d1 : lval) (d2: lval) (s1 : atom) (s2 : atom) =
        { iname; iargs = [Lval d1; Lval d2; Atom s1; Atom s2] }

      let subc = op2_2 "subc"
      let mull = op2_2 "mull"
      let cmov = op2_2  "cmov"
      let adds = op2_2  "adds"
      let subb = op2_2  "subb"
      let muls = op2_2  "muls"

    end

    module Op2_2c = struct

      let op2_2c iname (d1 : lval) (d2: lval) (s1 : atom) (s2 : atom) (c : tyvar) =
        { iname; iargs = [Lval d1; Lval d2; Atom s1; Atom s2; Atom (Avar c)] }

      let adcs = op2_2c "adcs"
      let sbcs = op2_2c "sbcs"
      let sbbs = op2_2c "sbbs"

    end

    module Shift = struct

      let shift iname (d : lval) (s : atom) (c : const) =
        { iname; iargs = [Lval d; Atom s; Const c] }

      let shl  = shift "shl"
      let shr  = shift "shr"
      let sar  = shift "sar"

      let vsar (d : lval) (s : atom) (c : const list) =
        { iname = "sar"; iargs = [Lval d; Atom s; Lconst c]}

    end

    module Cshift = struct

      let cshift iname (d1 : lval) (d2 : lval) (s1 : atom) (s2 : atom) (c : const) =
        { iname; iargs = [Lval d1; Lval d2; Atom s1; Atom s2; Const c] }

      let cshl = cshift "cshl"
      let cshr = cshift "cshr"

    end

    module Shifts =  struct

      let shifts iname (d1 : lval) (d2 : lval) (s : atom) (c : const) =
        { iname; iargs = [Lval d1; Lval d2; Atom s; Const c] }

      let shls = shifts "shls"
      let shrs = shifts "shrs"
      let sars = shifts "sars"
      let spl = shifts "spl"
      let split = shifts "split"
      let ssplit = shifts "ssplit"

      let vsars (d1 : lval) (d2 : lval) (s : atom) (c : const list) =
        { iname = "sars"; iargs = [Lval d1; Lval d2; Atom s; Lconst c]}

    end

    module Shift2s = struct

      let shift2s iname (d1 : lval) (d2 : lval) (d3 : lval) (s1 : atom) (s2 : atom) (c : const) =
        { iname; iargs = [Lval d1; Lval d2; Lval d3; Atom s1; Atom s2; Const c] }

      let cshls = shift2s "cshls"
      let cshrs = shift2s "cshrs"

    end

    let cast _ty (d : lval) (s : atom) =
      { iname = "cast"; iargs = [Lval d; Atom s] }

    let assert_ cl =
      { iname = "assert"; iargs = [Pred cl] }

    let cut ep rp =
      { iname = "cut"; iargs = [Pred(ep, rp)] }

    let vpc _ty (d : lval) (s : atom) =
      { iname = "vpc"; iargs = [Lval d; Atom s] }

    let assume cl =
      { iname = "assume"; iargs  = [Pred cl] }

    let ghost (v: gvar) cl =
      { iname = "ghost";  iargs = [Gval v; Pred cl] }

    let clear (v: lval) =
      { iname = "clear";  iargs = [Lval v] }

    (* nondet set rcut ecut *)

  end

  module Proc = struct

    type proc =
      { id : string;
        formals : tyvar list;
        pre : clause;
        prog : Instr.instr list;
        post : clause;
        ret_vars: tyvar list;
      }

    let pp_proc fmt (proc : proc) =
      Format.fprintf fmt
        "@[<v>proc %s(@[<hov>%a@]) =@ {@[<v>@ %a@]@ }@ %a@ {@[<v>@ %a@]@ }@ @] "
        proc.id
        pp_tyvars proc.formals
        pp_clause proc.pre
        Instr.pp_instrs proc.prog
        pp_clause proc.post
  end
end

module type I = sig

  val power: Z.t -> Z.t -> Z.t
  val int_of_typ : 'a Prog.gty -> int option
  val to_var :
    ?sign:bool -> 'a Prog.ggvar -> 'a Prog.gvar * CL.ty
  val gexp_to_rexp : ?sign:bool -> int Prog.gexpr -> CL.R.rexp
  val gexp_to_rpred : ?sign:bool -> int Prog.gexpr -> CL.R.rpred
  val extract_list :
    'a Prog.gexpr ->
    'a Prog.gexpr list -> 'a Prog.gexpr list
  val get_const : 'a Prog.gexpr -> int
  val var_to_tyvar :
    ?sign:bool -> ?vector:int * int -> int Prog.gvar -> CL.tyvar
  val get_lval:
      CL.Instr.lval ->
      CL.tyvar
  val mk_tmp_lval :
    ?name:Jasmin__CoreIdent.Name.t ->
    ?l:Prog.L.t ->
    ?kind:Wsize.v_kind ->
    ?sign:bool ->
    ?vector:int * int -> int Jasmin__CoreIdent.gty -> CL.Instr.lval
  val wsize_of_int:
    int -> Wsize.wsize
  val mk_spe_tmp_lval :
    ?name:Jasmin__CoreIdent.Name.t ->
    ?l:Prog.L.t ->
    ?kind:Wsize.v_kind -> ?sign:bool -> int -> CL.Instr.lval
  val gexp_to_eexp :
    (int, CL.Instr.lval) Utils.Hash.t ->
    ?sign:bool -> int Prog.gexpr -> CL.I.eexp
  val gexp_to_epred :
    (int, CL.Instr.lval) Utils.Hash.t ->
    ?sign:bool -> int Prog.gexpr -> CL.I.epred list
  val glval_to_lval : ?sign:bool -> int Prog.glval -> CL.Instr.lval
  val gexp_to_var : ?sign:bool -> int Prog.gexpr -> CL.tyvar
  val gexp_to_const : ?sign:bool -> 'a Prog.gexpr -> CL.const * CL.ty
  val mk_const : int -> CL.const
  val mk_const_atome : int -> ?sign:bool -> CL.const -> CL.Instr.atom
  val gexp_to_atome : ?sign:bool -> int Prog.gexpr -> CL.Instr.atom
  val mk_lval_atome : CL.Instr.lval -> CL.Instr.atom
end

module type S = sig
  val s : bool
  val error : string
end

module I (S:S): I = struct

  let int_of_typ = function
    | Bty (U ws) -> Some (int_of_ws ws)
    | Bty (Bool) -> Some 1
    | Bty (Abstract s) ->
      begin
        match String.to_list s with
        | '/'::'*':: q -> Some (String.to_int (String.of_list q))
        | _ -> assert false
      end
    | Bty (Int)  -> None
    | _ -> assert false

  let to_var ?(sign=S.s) x =
    let var = L.unloc x.gv in
    if sign then var, CL.Sint (Option.get (int_of_typ var.v_ty))
    else var, CL.Uint (Option.get (int_of_typ var.v_ty))

  let error e =
    let msg =
      Format.asprintf "Unsupport expression in %s translation" S.error
    in
    hierror ~loc:Lnone ~kind:msg  "@[%a@]" (Printer.pp_expr ~debug:true) e

  let rec power (acc: Z.t) (n: Z.t) =
    match n with
    | n when n = Z.zero -> acc
    | n when Z.(n < Z.zero) -> assert false
    | n -> power Z.(acc * (Z.of_int 2)) Z.(n - Z.one)

  (* Fixme: what happens if value is out of bounds *)
  let w2i ?(sign=S.s) c ws =
    assert ((Z.of_int 0) <= c);
    if sign then
      let c =
        if Z.(c >= power Z.one Z.((z_of_ws ws) - one)) then
          Z.(c - (power Z.one (z_of_ws ws))) else c
      in
      c
    else c

  (* let w2i ?(sign=S.s) ws z = *)
  (*   assert ((Z.of_int 0) <= c); *)
  (*   let zi = Z.rem z (Z.pow (Z.of_int 2) ws) in *)
  (*   if sign *)
  (*   then if zi < (Z.pow (Z.of_int 2) (ws-1)) *)
  (*     then zi *)
  (*     else (Z.sub zi (Z.pow (Z.of_int 2) ws)) *)
  (*   else zi *)


  let rec extract_list e aux =
      match e with
      | PappN (Oabstract {pa_name="single"}, [h]) -> [h]
      | PappN (Oabstract {pa_name="pair"}, [h1;h2]) -> [h1;h2]
      | PappN (Oabstract {pa_name="triple"}, [h1;h2;h3]) -> [h1;h2;h3]
      | PappN (Oabstract {pa_name="quad"}, [h1;h2;h3;h4]) -> [h1;h2;h3;h4]
      | PappN (Oabstract {pa_name="word_nil"}, []) -> List.rev aux
      | PappN (Oabstract {pa_name="word_cons"}, [h;q]) -> extract_list q (h :: aux)
      | _ -> assert false

  let rec gexp_to_rexp ?(sign=S.s) e : CL.R.rexp =
    let open CL.R in
    let (!>) e = gexp_to_rexp ~sign e in
    match e with
    | Papp1 (Oword_of_int ws, Pconst z) -> Rconst(int_of_ws ws, w2i ~sign z ws)
    | Papp1 (Oword_of_int ws, Pvar x) -> Rvar (L.unloc x.gv, Uint (int_of_ws ws))
    | Pvar x -> Rvar (to_var ~sign x)
    | Papp1(Oneg _, e) -> neg !> e
    | Papp1(Olnot _, e) -> not !> e
    | Papp2(Oadd _, e1, e2) -> add !> e1 !> e2
    | Papp2(Osub _, e1, e2) -> minu !> e1 !> e2
    | Papp2(Omul _, e1, e2) -> mull !> e1 !> e2
    | PappN(Oabstract {pa_name="se_16_64"}, [v]) -> Rsext (!> v, 48)
    | PappN(Oabstract {pa_name="se_32_64"}, [v]) -> Rsext (!> v, 32)
    | PappN(Oabstract {pa_name="ze_16_64"}, [v]) -> Ruext (!> v, 48)
    | PappN(Oabstract {pa_name="ze_16_32"}, [v]) -> Ruext (!> v, 16)
    | PappN(Oabstract {pa_name="limbs_4u64"}, [q]) -> Rlimbs ((Z.of_int 64), (List.map (!>) (extract_list q [])))
    | PappN(Oabstract {pa_name="u256_as_16u16"}, [Pvar x ; Pconst z]) ->
      UnPack (to_var ~sign x, 16, Z.to_int z, false)
    | PappN(Oabstract {pa_name="u256_as_16u16"}, [Presult (_, x) ; Pconst z]) ->
      UnPack (to_var ~sign x, 16, Z.to_int z, true)
    | _ -> error e

  let rec gexp_to_rpred ?(sign=S.s) e : CL.R.rpred =
    let open CL.R in
    let (!>) e = gexp_to_rexp ~sign e in
    let (!>>) e = gexp_to_rpred ~sign e in
    match e with
    | Pvar { gv = { pl_desc = { v_ty=Bty Bool }}} -> eq !> e (Rconst(1, Z.of_int 1))
    | Pbool (true) -> RPand []
    | Papp1(Onot, e) -> RPnot (!>> e)
    | Papp2(Oand, e1, e2)  -> RPand [!>> e1; !>> e2]
    | Papp2(Oor, e1, e2)  -> RPor [!>> e1; !>> e2]
    | Papp2(Ole int, e1, e2)  -> ule !> e1 !> e2
    | Papp2(Oge int, e1, e2)  -> uge !> e1 !> e2
    | Papp2(Obeq, e1, e2)
    | Papp2(Oeq _, e1, e2) -> eq !> e1 !> e2
    | Papp2(Olt int, e1, e2)  -> ult !> e1 !> e2
    | Papp2(Ogt int, e1, e2)  -> ugt !> e1 !> e2
    | Pif(_, e1, e2, e3) -> RPand [RPor [RPnot !>> e1; !>> e2];RPor[ !>> e1; !>> e3]]
    | Pabstract ({name="eq"}, [e1;e2]) -> eq !> e1 !> e2
    | Pabstract ({name="eqsmod"} as _opa, [e1;e2;e3]) -> RPeqsmod (!> e1, !> e2, !> e3)
    | _ -> error e

  let rec get_const x =
    match x with
    | Pconst z -> assert ((Z.of_int 0) <= z);Z.to_int z
    | Papp1 (Oword_of_int _ws, x) -> get_const x
    | _ -> assert false

  let var_to_tyvar ?(sign=S.s) ?vector v : CL.tyvar =
    match vector with
    | None ->
      begin
        match int_of_typ v.v_ty with
        | None -> v, CL.Bit
        | Some w ->
          if sign then v, CL.Sint w
          else v, CL.Uint w
      end
    | Some (n,w) ->
      begin
        match int_of_typ v.v_ty with
        | None -> assert false
        | Some w' ->
          assert (n * w = w');
          v, CL.Vector (n, if sign then CL.Sint w else CL.Uint w)
      end

  
  let get_lval (l: CL.Instr.lval)  =
    match l with
      | Llvar x -> x
      | _ -> assert false

  let mk_tmp_lval ?(name = "TMP____") ?(l = L._dummy)
      ?(kind = (Wsize.Stack Direct)) ?(sign=S.s)
      ?vector ty : CL.Instr.lval =
    let v = CoreIdent.GV.mk name kind ty l [] in
    let tv = var_to_tyvar ~sign ?vector v in
    Llvar tv

  let wsize_of_int = function
    | 8   -> Wsize.U8
    | 16  -> Wsize.U16
    | 32  -> Wsize.U32
    | 64  -> Wsize.U64
    | 128 -> Wsize.U128
    | 256 -> Wsize.U256
    | _ -> assert false

  let mk_spe_tmp_lval ?(name = "TMP____") ?(l = L._dummy)
      ?(kind = (Wsize.Stack Direct)) ?(sign=S.s)
      size =
    let size = String.to_list (String.of_int size) in
    let s = String.of_list ('/'::'*':: size) in
    mk_tmp_lval ~name ~l ~kind ~sign (Bty(Abstract s))

  let rec gexp_to_eexp env ?(sign=S.s) e : CL.I.eexp =
    let open CL.I in
    let (!>) e = gexp_to_eexp env ~sign e in
    match e with
    | Pconst z -> Iconst z
    | Pvar x -> Ivar (to_var ~sign x)
    | Papp1 (Oword_of_int ws, Pconst z) -> Iconst (w2i ~sign z ws)
    | Papp1 (Oint_of_word _ws, x) -> assert false
    | Papp1(Oneg _, e) -> !- !> e
    | Papp2(Oadd _, e1, e2) -> !> e1 + !> e2
    | Papp2(Osub _, e1, e2) -> !> e1 - !> e2
    | Papp2(Omul _, e1, e2) -> mull !> e1 !> e2
    | PappN (Oabstract {pa_name="limbs"}, [h;q]) ->
      begin
        match !> h with
        | Iconst c -> Ilimbs (c, (List.map (!>) (extract_list q [])))
        | _ -> assert false
      end
   | PappN (Oabstract {pa_name="u16i"}, [v]) ->
       begin
         match v with
       (* why do we have more cases?  | Pvar _ -> !> v *)
         | Papp1 (Oword_of_int _ws, Pconst z) ->  !>
              (Pconst (w2i ~sign z U16))
         | _ -> !> v
       end
    | PappN (Oabstract {pa_name="pow"}, [b;e]) -> power !> b !> e
    | PappN (Oabstract {pa_name="u32i"}, [v]) -> 
      begin 
        match v with 
      (* why do we have more cases?  | Pvar _ -> !> v *) 
        | Papp1 (Oword_of_int _ws, Pconst z) ->  !> 
             (Pconst (w2i ~sign z U32)) 
        | _ -> !> v 
      end
    | PappN (Oabstract {pa_name="u64i"}, [v]) ->
       begin
         match v with
         | Papp1 (Oword_of_int _ws, Pconst z) ->  !>
              (Pconst (w2i ~sign z U64))
        | _ -> !> v
      end
    | PappN (Oabstract {pa_name="b2i"}, [v]) -> !> v
    | PappN (Oabstract {pa_name="mon"}, [c;a;b]) ->
      let c = get_const c in
      let v =
        match Hash.find env c with
        | exception Not_found ->
          let name = "X" ^ "_" ^ string_of_int c in
          let x =
            mk_tmp_lval ~name (Bty Int)
          in
          Hash.add env c x;
          (get_lval x)
        | x -> (get_lval x)
      in
      mull !> b (power (Ivar v) !> a)
    | PappN (Oabstract {pa_name="mon0"}, [b]) ->
      !> b
    | PappN (Oabstract {name="u256_as_16u16"}, [Pvar x; Pconst z]) ->
      IUnPack (to_var ~sign x, 16, Z.to_int z, false)
    | Pabstract ({name="u256_as_16u16"}, [Presult (_, x) ; Pconst z]) ->
        IUnPack (to_var ~sign x, 16, Z.to_int z, true)
    | Presult (_,x) -> Ivar (to_var ~sign x)
    | _ -> error e

  let rec gexp_to_epred env ?(sign=S.s) e :CL.I.epred list =
    let open CL.I in
    let (!>) e = gexp_to_eexp env ~sign e in
    let (!>>) e = gexp_to_epred env ~sign e in
    match e with
    | Papp2(Oeq _, e1, e2)  -> [Eeq (!> e1, !> e2)]
    | Papp2(Oand, e1, e2)  -> !>> e1 @ !>> e2
    | PappN (Oabstract {pa_name="eqmod"} as _opa, [h1;h2;h3]) ->
      [Eeqmod (!> h1, !> h2, List.map (!>) (extract_list h3 []))]
    | PappN (Oabstract {pa_name="eqmod_int"} as _opa, [h1;h2;h3]) ->
      [Eeqmod (!> h1, !> h2, [!> h3])]
    | _ -> error e

  let glval_to_lval ?(sign=S.s) x : CL.Instr.lval =
    match x with
    | Lvar v -> Llvar (var_to_tyvar ~sign (L.unloc v))
    | Lnone (l,ty)  ->
      let name = "NONE____" in
      mk_tmp_lval ~sign ~name ~l ty
    | Lmem _ | Laset _ | Lasub _ -> assert false

  let gexp_to_var ?(sign=S.s) x : CL.tyvar =
    match x with
    | Pvar x -> var_to_tyvar ~sign (L.unloc x.gv)
    | _ -> assert false

  let mk_const_atome ws ?(sign=S.s) c =
    if sign then CL.Instr.Aconst (c, CL.Sint ws)
    else
      begin
        assert ((Z.of_int 0) <= c);
        CL.Instr.Aconst (c, CL.Uint ws)
      end

  let gexp_to_const ?(sign=S.s) x : CL.const * CL.ty =
    match x with
    | Papp1 (Oword_of_int ws, Pconst c) ->
      let c = w2i ~sign c ws in
      if sign then c, CL.Sint (int_of_ws ws)
      else c, CL.Uint (int_of_ws ws)
    | _ -> assert false

  let mk_const c : CL.const = Z.of_int c

  let gexp_to_atome ?(sign=S.s) x : CL.Instr.atom =
    match x with
    | Pvar _ -> Avar (gexp_to_var ~sign x)
    | Papp1 (Oword_of_int _, Pconst _) ->
      let c,ty = gexp_to_const x in
      Aconst (c,ty)
    | _ -> assert false

  let rec mk_lval_atome (lval: CL.Instr.lval) =
    match lval with
    | Llvar tv -> CL.Instr.Avar tv
    | Lvatome l -> Avatome (List.map mk_lval_atome l)
end

module type BaseOp = sig
  type op
  type extra_op

  module I: I

  val op_to_instr :
    Annotations.annotations ->
    Location.t ->
    int Prog.glval list ->
    op -> int Prog.gexpr list -> CL.Instr.instr list

  val extra_op_to_instr :
    Annotations.annotations ->
    Location.t ->
    int Prog.glval list ->
    extra_op -> int Prog.gexpr list -> CL.Instr.instr list

  val assgn_to_instr :
    Annotations.annotations ->
    int Prog.glval -> int Prog.gexpr -> CL.Instr.instr list

end

type trans = [ `Default]

let trans annot l =
  let v =
      match Annotations.get "tran" annot with
      | Some (Some {pl_desc=(Annotations.Aid an);pl_loc=loc}) ->
        let _,a =
          try List.find (fun (x,_) -> String.equal x an) l with
          | _ ->
            hierror ~loc:(Lone loc) ~kind:"Translation option"
              "Translation \"%s\" not found among valid translations: [%s]@." an
                (List.reduce (fun a b -> a ^ "; " ^ b) (List.map fst l))

        in
        Some a
      | Some (Some {pl_desc=an;pl_loc=loc}) ->
        hierror ~loc:(Lone loc) ~kind:"Translation option"  "Unsupported attribute@."

      | _ -> None
  in

  match v with
  | None -> `Default
  | Some aty -> aty


module X86BaseOpU : BaseOp
  with type op = X86_instr_decl.x86_op
  with type extra_op = X86_extra.x86_extra_op
= struct

  type op = X86_instr_decl.x86_op
  type extra_op = X86_extra.x86_extra_op

  module S = struct
    let s = false
    let error = "unsigned x86"
  end

  module I = I (S)

  let cast_atome ws x =
    match x with
    | Pvar va ->
      let ws_x = ws_of_ty (L.unloc va.gv).v_ty in
      if ws = ws_x then I.gexp_to_atome x,[]
      else
        let e = I.gexp_to_atome x in
        let v = L.unloc va.gv in
        let kind = v.v_kind in
        let lx = I.mk_tmp_lval ~kind (CoreIdent.tu ws) in
        let (_,ty) as x = I.get_lval lx in
        CL.Instr.Avar x, [CL.Instr.cast ty lx e]
    | Papp1 (Oword_of_int ws_x, Pconst z) ->
      if ws = ws_x then I.gexp_to_atome x,[]
      else
        let e = I.gexp_to_atome x in
        let lx = I.mk_tmp_lval (CoreIdent.tu ws) in
        let (_,ty) as x = I.get_lval lx in
        CL.Instr.Avar x, [CL.Instr.cast ty lx e]
    | _ -> assert false

  let (!) e = I.mk_lval_atome e

  let cast_vector_atome ws v x =
    let a,i = cast_atome ws x in
    let a1 = CL.Instr.Avatome [a] in
    let v = int_of_velem v in
    let s = int_of_ws ws in
    let l_tmp = I.mk_tmp_lval ~vector:(1,s) (CoreIdent.tu ws) in
    let l_tmp2 = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
    let l_tmp2v = I.get_lval l_tmp2 in
    let ty = CL.(Vector (v, Uint (s/v))) in
    CL.Instr.Avar l_tmp2v,
    i @ [CL.Instr.Op1.mov l_tmp a1;
         CL.Instr.cast ty l_tmp2 !l_tmp;
        ]

  let cast_atome_vector ws v x l =
    let s = int_of_ws ws in
    let l_tmp = I.mk_tmp_lval ~vector:(1,s) (CoreIdent.tu ws) in
    let l_tmpv = I.get_lval l_tmp in
    let ty = CL.(Vector (v, Uint s)) in
    let a = CL.Instr.Avecta (l_tmpv, 0) in
    [CL.Instr.cast ty l_tmp x;
     CL.Instr.Op1.mov l a
    ]

  let assgn_to_instr _annot x e =
    let a = I.gexp_to_atome e in
    let l = I.glval_to_lval x in
    [CL.Instr.Op1.mov l a]

  let op_to_instr annot loc xs o es =
    match o with
    | X86_instr_decl.MOV ws ->
      let a,i = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 0) in
      i @ [CL.Instr.Op1.mov l a]

    | CMOVcc ws -> (* warning, does not work with ! cf *)
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let a3, i3 = cast_atome ws (List.nth es 2) in
      let x1 = I.glval_to_lval (List.nth xs 0) in
      begin match (List.nth es 0) with
      | Pvar _ as cc->
        let cc = I.gexp_to_var cc in
        i2 @ [CL.Instr.Op2_2.cmov x1 cc a2 a3]
      | Papp1(Onot, (Pvar _ as cc)) ->
        let cc = I.gexp_to_var cc in
        i2 @ [CL.Instr.Op2_2.cmov x1 cc a3 a2]
      | _ -> assert false
      end

    | ADD ws ->
      begin
        let l = ["smt", `Smt ; "default", `Default] in
        let trans = trans annot l in
        let a1,i1 = cast_atome ws (List.nth es 0) in
        let a2,i2 = cast_atome ws (List.nth es 1) in
        let l = I.glval_to_lval (List.nth xs 5) in
        match trans with
        | `Smt ->
          i1 @ i2 @ [CL.Instr.Op2.add l a1 a2]
        | `Default ->
          let lc = I.glval_to_lval (List.nth xs 1) in
          i1 @ i2 @ [CL.Instr.Op2_2.adds lc l a1 a2]
      end

    | SUB ws ->
      begin
        let l = ["smt", `Smt ; "default", `Default] in
        let trans = trans annot l in
        let a1, i1 = cast_atome ws (List.nth es 0) in
        let a2, i2 = cast_atome ws (List.nth es 1) in
        let l = I.glval_to_lval (List.nth xs 5) in
        match trans with
        | `Smt ->
          i1 @ i2 @ [CL.Instr.Op2.sub l a1 a2]
        | `Default ->
          let lb = I.glval_to_lval (List.nth xs 1) in
          i1 @ i2 @ [CL.Instr.Op2_2.subb lb l a1 a2]
      end

    | IMULr ws
    | IMULri ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l1 = I.glval_to_lval (List.nth xs 5) in
      let l = I.mk_spe_tmp_lval 64 in
      i1 @ i2 @ [CL.Instr.Op2_2.mull l l1 a1 a2;
               CL.Instr.assert_ ([], [RPcmp(Rvar l, "=", (Rconst(64, Z.of_int 0)))]);
               CL.Instr.assume ([Eeq(Ivar l, Iconst Z.zero)] ,[]);
       ]

    | MUL ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l1 = I.glval_to_lval (List.nth xs 5) in
      let l2 = I.glval_to_lval (List.nth xs 6) in
      i1 @ i2 @ [CL.Instr.Op2_2.mull l1 l2 a1 a2;]
(* (\*  *)
(*     | IMULri ws -> *)
(*       let a1, i1 = cast_atome ws (List.nth es 0) in *)
(*       let a2, i2 = cast_atome ws (List.nth es 1) in *)
(*       let l = I.glval_to_lval (List.nth xs 5) in *)
(*       let l_tmp = I.mk_tmp_lval(CoreIdent.tu ws) in *)
(*       i1 @ i2 @ [CL.Instr.Op2_2.mull l_tmp l a1 a2] *\) *)

    | ADC ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l1 = I.glval_to_lval (List.nth xs 1) in
      let l2 = I.glval_to_lval (List.nth xs 5) in
      let v = I.gexp_to_var (List.nth es 2) in
      i1 @ i2 @ [CL.Instr.Op2_2c.adcs l1 l2 a1 a2 v]

    | SBB ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l1 = I.glval_to_lval (List.nth xs 1) in
      let l2 = I.glval_to_lval (List.nth xs 5) in
      let v = I.gexp_to_var (List.nth es 2) in
      i1 @ i2 @ [CL.Instr.Op2_2c.sbbs l1 l2 a1 a2 v]

    | NEG ws ->
      let a = I.mk_const_atome ~sign:true (int_of_ws ws) Z.zero in
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let l_tmp1 = I.mk_tmp_lval ~sign:true (CoreIdent.tu ws) in
      let ty1 = CL.Sint (int_of_ws ws) in
      let l_tmp2 = I.mk_tmp_lval ~sign:true (CoreIdent.tu ws) in
      let ty2 = CL.Sint (int_of_ws ws) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ [CL.Instr.cast ty1 l_tmp1 a1;
            CL.Instr.Op2.sub l_tmp2 a !l_tmp1;
            CL.Instr.cast ty2 l !l_tmp2
           ]

    | INC ws ->
      let a1 = I.mk_const_atome (int_of_ws ws) Z.one in
      let a2,i2 = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 4) in
      let l_tmp = I.mk_spe_tmp_lval 1 in
      i2 @ [CL.Instr.Op2_2.adds l_tmp l a1 a2] (* should we account for overflow in increment? *)

    | DEC ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2 = I.mk_const_atome (int_of_ws ws) Z.one in
      let l = I.glval_to_lval (List.nth xs 4) in
      let l_tmp = I.mk_spe_tmp_lval 1 in
      i1 @ [CL.Instr.Op2_2.subb l_tmp l a1 a2] (* should we account for underflow in decrement? *)

    | AND ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ i2 @ [CL.Instr.Op2.and_ l a1 a2]

    | ANDN ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l_tmp = I.mk_tmp_lval (CoreIdent.tu ws) in
      let at = I.mk_lval_atome l_tmp in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ i2 @ [CL.Instr.Op1.not l_tmp a1; CL.Instr.Op2.and_ l a2 at]

    | OR ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ i2 @ [CL.Instr.Op2.or_ l a1 a2]

    | XOR ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ i2 @ [CL.Instr.Op2.xor l a1 a2]

    | NOT ws ->
      let a,i = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 0) in
      i @ [CL.Instr.Op1.not l a]

    | SHL ws ->
      begin
        let l = ["smt", `Smt ; "default", `Default] in
        let trans = trans annot l in
        match trans with
        | `Smt ->
          let a, i = cast_atome ws (List.nth es 0) in
          let (c,_) = I.gexp_to_const(List.nth es 1) in
          let l = I.glval_to_lval (List.nth xs 5) in
          i @ [CL.Instr.Shift.shl l a c]
        | `Default ->
          let a, i = cast_atome ws (List.nth es 0) in
          let (c,_) = I.gexp_to_const (List.nth es 1) in
          let l = I.glval_to_lval (List.nth xs 5) in
          let l_tmp = I.mk_spe_tmp_lval (Z.to_int c) in
          i @ [CL.Instr.Shifts.shls l_tmp l a c]
      end

    | SHR ws ->
      begin
        let l = ["smt", `Smt ; "default", `Default] in
        let trans = trans annot l in
        match trans with
        | `Smt ->
          let a, i = cast_atome ws (List.nth es 0) in
          let (c,_) = I.gexp_to_const(List.nth es 1) in
          let l = I.glval_to_lval (List.nth xs 5) in
          i @ [CL.Instr.Shift.shr l a c]
        | `Default ->
          let a, i = cast_atome ws (List.nth es 0) in
          let (c,_) = I.gexp_to_const (List.nth es 1) in
          let l = I.glval_to_lval (List.nth xs 5) in
          let l_tmp = I.mk_spe_tmp_lval (Z.to_int c) in
          i @ [CL.Instr.Shifts.shrs l l_tmp a c]
      end

    | SAR ws ->
      begin
        let l =
          ["smt", `Smt ; "smt2", `Smt2 ; "default", `Default; "cas_two", `Cas2; "cas_three", `Cas3]
        in
        let trans = trans annot l in
        match trans with
        | `Smt ->
          let a,i = cast_atome ws (List.nth es 0) in
          let l_tmp1 = I.mk_tmp_lval ~sign:true (CoreIdent.tu ws) in
          let ty1 = CL.Sint (int_of_ws ws) in
          let (c,_) = I.gexp_to_const(List.nth es 1) in
          let l_tmp2 = I.mk_tmp_lval ~sign:true (CoreIdent.tu ws) in
          let l_tmp3 = I.mk_tmp_lval (CoreIdent.tu ws) in
          let ty2 = CL.Uint (int_of_ws ws) in
          let l = I.glval_to_lval (List.nth xs 5) in
          i @ [CL.Instr.cast ty1 l_tmp1 a;
               CL.Instr.Shifts.ssplit l_tmp2 l_tmp3 !l_tmp1 c;
               CL.Instr.cast ty2 l !l_tmp2]
        | `Smt2 ->
          let a, i = cast_atome ws (List.nth es 0) in
          let (c,_) = I.gexp_to_const (List.nth es 1) in
          let l = I.glval_to_lval (List.nth xs 5) in
          let l_tmp = I.mk_spe_tmp_lval (Z.to_int c) in
          i @ [CL.Instr.Shifts.sars l l_tmp a c]
        | `Default ->
          let a1,i1 = cast_atome ws (List.nth es 0) in
          let c1 = I.mk_const (int_of_ws ws - 1) in
          let l_tmp1 = I.mk_spe_tmp_lval 1 in
          let l_tmp2 = I.mk_spe_tmp_lval (int_of_ws ws - 1) in
          let c = I.get_const (List.nth es 1) in
          let a2 = I.mk_const_atome c Z.zero in
          let l_tmp3 = I.mk_spe_tmp_lval (c + 1) in
          let a3 = I.mk_const_atome (c + 1) Z.(I.power Z.one (Z.of_int (c) + Z.one) - Z.one) in
          let l_tmp4 = I.mk_spe_tmp_lval (c + 1) in
          let l_tmp5 = I.mk_spe_tmp_lval (c + int_of_ws ws) in
          let c2 = Z.of_int c in
          let l_tmp6 = I.mk_spe_tmp_lval c in
          let l = I.glval_to_lval (List.nth xs 5) in
          i1 @ [CL.Instr.Shifts.spl l_tmp1 l_tmp2 a1 c1;
                CL.Instr.Op2.join l_tmp3 a2 !l_tmp1;
                CL.Instr.Op2.mul l_tmp4 !l_tmp3 a3;
                CL.Instr.Op2.join l_tmp5 !l_tmp4 !l_tmp2;
                CL.Instr.Shifts.spl l l_tmp6 !l_tmp5 c2
               ]
        | `Cas2 ->
          let a1,i1 = cast_atome ws (List.nth es 0) in
          let c1 = I.mk_const (int_of_ws ws - 1) in
          let l_tmp1 = I.mk_spe_tmp_lval 1 in
          let l_tmp2 = I.mk_spe_tmp_lval (int_of_ws ws - 1) in
          let c = I.get_const (List.nth es 1) in
          let a2 = I.mk_const_atome (c -1) Z.zero in
          let l_tmp3 = I.mk_spe_tmp_lval c in
          let a3 = I.mk_const_atome c (I.power Z.one Z.((of_int c) - one)) in
          let l_tmp4 = I.mk_spe_tmp_lval c in
          let l_tmp5 = I.mk_spe_tmp_lval c in
          let c2 = Z.of_int c in
          let l_tmp6 = I.mk_spe_tmp_lval (int_of_ws ws - c) in
          let l = I.glval_to_lval (List.nth xs 5) in
          i1 @ [CL.Instr.Shifts.spl l_tmp1 l_tmp2 a1 c1;
                CL.Instr.Op2.join l_tmp3 a2 !l_tmp1;
                CL.Instr.Op2.mul l_tmp4 !l_tmp3 a3;
                CL.Instr.Shifts.spl l_tmp6 l_tmp5 a1 c2;
                CL.Instr.Op2.join l !l_tmp4 !l_tmp6;
               ]
        | `Cas3 ->
          let a1,i1 = cast_atome ws (List.nth es 0) in
          let c1 = I.mk_const (int_of_ws ws - 1) in
          let l_tmp = I.mk_spe_tmp_lval (int_of_ws ws) in
          let l_tmpv = I.get_lval l_tmp in
          let l_tmp1 = I.mk_spe_tmp_lval 1 in
          let l_tmp2 = I.mk_spe_tmp_lval (int_of_ws ws - 1) in
          let c = I.get_const (List.nth es 1) in
          let a2 = I.mk_const_atome (c -1) Z.zero in
          let l_tmp3 = I.mk_spe_tmp_lval c in
          let a3 = I.mk_const_atome c (I.power Z.one Z.((of_int c) - one)) in
          let l_tmp4 = I.mk_spe_tmp_lval c in
          let l_tmp5 = I.mk_spe_tmp_lval c in
          let l_tmp5v = I.get_lval l_tmp5 in
          let c2 = Z.of_int c in
          let c3 = (I.power Z.one Z.(of_int c)) in
          let l_tmp6 = I.mk_spe_tmp_lval (int_of_ws ws - c) in
          let l = I.glval_to_lval (List.nth xs 5) in
          i1 @ [CL.Instr.Op1.mov l_tmp a1;
                CL.Instr.assert_ ([Eeqmod(Ivar l_tmpv, Iconst Z.zero,[Iconst c3])] ,[]);
                CL.Instr.Shifts.spl l_tmp1 l_tmp2 a1 c1;
                CL.Instr.Op2.join l_tmp3 a2 !l_tmp1;
                CL.Instr.Op2.mul l_tmp4 !l_tmp3 a3;
                CL.Instr.Shifts.spl l_tmp6 l_tmp5 a1 c2;
                CL.Instr.assume ([Eeq(Ivar l_tmp5v, Iconst Z.zero)] ,[]);
                CL.Instr.Op2.join l !l_tmp4 !l_tmp6;
               ]
      end

    | MOVSX (ws1, ws2) ->
      begin
        let l = ["smt", `Smt ; "default", `Default] in
        let trans = trans annot l in
        match trans with
        | `Smt ->
          let a,i = cast_atome ws2 (List.nth es 0) in
          let sign = true in
          let l_tmp1 = I.mk_tmp_lval ~sign (CoreIdent.tu ws2) in
          let ty1 = CL.Sint (int_of_ws ws2) in
          let l_tmp2 = I.mk_tmp_lval ~sign (CoreIdent.tu ws1) in
          let ty2 = CL.Sint (int_of_ws ws1) in
          let l = I.glval_to_lval (List.nth xs 0) in
          let ty3 = CL.Uint (int_of_ws ws1) in
          i @ [CL.Instr.cast ty1 l_tmp1 a;
               CL.Instr.cast ty2 l_tmp2 !l_tmp1;
               CL.Instr.cast ty3 l !l_tmp2]
        | `Default ->
          let a,i = cast_atome ws2 (List.nth es 0) in
          let c = Z.of_int (int_of_ws ws2 - 1) in
          let l_tmp1 = I.mk_spe_tmp_lval 1 in
          let l_tmp2 = I.mk_spe_tmp_lval (int_of_ws ws2 - 1) in
          let diff = int_of_ws ws1 - (int_of_ws ws2) in
          let a2 = I.mk_const_atome (diff - 1) Z.zero in
          let l_tmp3 = I.mk_spe_tmp_lval diff in
          let a3 =
            I.mk_const_atome diff (Z.(I.power Z.one (Z.of_int diff) - one))
          in
          let l_tmp4 = I.mk_spe_tmp_lval diff in
          let l = I.glval_to_lval (List.nth xs 0) in
          i @ [CL.Instr.Shifts.spl l_tmp1 l_tmp2 a c;
               CL.Instr.Op2.join l_tmp3 a2 !l_tmp1;
               CL.Instr.Op2.mul l_tmp4 !l_tmp3 a3;
               CL.Instr.Op2.join l !l_tmp4 a;
              ]
      end

    | MOVZX (ws1, ws2) ->
      let a,i = cast_atome ws2 (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 0) in
      let ty = CL.Uint (int_of_ws ws1) in
      i @ [CL.Instr.cast ty l a]

    | ADCX ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l1 = I.glval_to_lval (List.nth xs 0) in
      let l2 = I.glval_to_lval (List.nth xs 1) in
      let v = I.gexp_to_var (List.nth es 2) in
      i1 @ i2 @ [CL.Instr.Op2_2c.adcs l1 l2 a2 a1 v]


    | ADOX ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l1 = I.glval_to_lval (List.nth xs 0) in
      let l2 = I.glval_to_lval (List.nth xs 1) in
      let v = I.gexp_to_var (List.nth es 2) in
      i1 @ i2 @ [CL.Instr.Op2_2c.adcs l1 l2 a2 a1 v]


    | VPADD (ve,ws) ->
      begin
      let l = ["smt", `Smt ; "default", `Default] in
      let trans = trans annot l in
      let a1,i1 = cast_vector_atome ws ve (List.nth es 0) in
      let a2,i2 = cast_vector_atome ws ve (List.nth es 1) in
      let v = int_of_velem ve in
      let s = int_of_ws ws in
      let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
      let l = I.glval_to_lval (List.nth xs 0) in
      let i3 = cast_atome_vector ws v !l_tmp l in
      match trans with
        | `Smt ->
          i1 @ i2 @ [CL.Instr.Op2.add l_tmp a1 a2] @ i3
        | `Default ->
          let l_tmp1 = I.mk_tmp_lval ~vector:(v,1) (CoreIdent.tu (I.wsize_of_int v)) in
          i1 @ i2 @ [CL.Instr.Op2_2.adds l_tmp1 l_tmp a1 a2] @ i3 (* TODO: add assertions for carry bit *)
    end

    | VMOVDQU ws ->
      let a,i = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 0) in
      i @ [CL.Instr.Op1.mov l a]

    | VPAND ws ->
      let a1,i1 = cast_vector_atome ws VE16 (List.nth es 0) in
      let a2,i2 = cast_vector_atome ws VE16 (List.nth es 1) in
      let s = int_of_ws ws in
      let v = s / 16 in
      let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
      let l = I.glval_to_lval (List.nth xs 0) in
      let i3 = cast_atome_vector ws v !l_tmp l in
          i1 @ i2 @ [CL.Instr.Op2.and_ l_tmp a1 a2] @ i3

    | VPSUB (ve,ws) ->
      begin
      let l = ["smt", `Smt ; "default", `Default] in
      let trans = trans annot l in
      let a1,i1 = cast_vector_atome ws ve (List.nth es 0) in
      let a2,i2 = cast_vector_atome ws ve (List.nth es 1) in
      let v = int_of_velem ve in
      let s = int_of_ws ws in
      let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
      let l = I.glval_to_lval (List.nth xs 0) in
      let i3 = cast_atome_vector ws v !l_tmp l in
      match trans with
        | `Smt ->
          i1 @ i2 @ [CL.Instr.Op2.sub l_tmp a1 a2] @ i3
        | `Default ->
          let l_tmp1 = I.mk_tmp_lval ~vector:(v,1) (CoreIdent.tu (I.wsize_of_int v)) in
          i1 @ i2 @ [CL.Instr.Op2_2.subb l_tmp1 l_tmp a1 a2] @ i3
      end

    | VPMULL (v,ws) ->
        let a1,i1 = cast_vector_atome ws v (List.nth es 0) in
        let a2,i2 = cast_vector_atome ws v (List.nth es 1) in
        let v = int_of_velem v in
        let s = int_of_ws ws in
        let l0_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
        let l1_tmp = I.mk_tmp_lval ~sign:true ~vector:(v,s/v) (CoreIdent.tu ws) in
        let (_, l1_ty) = I.get_lval l1_tmp in
        let l = I.glval_to_lval (List.nth xs 0) in
        let i3 = cast_atome_vector ws v !l1_tmp l in
        i1 @ i2 @ 
        [
          CL.Instr.Op2.smul l0_tmp a1 a2;
          CL.Instr.cast l1_ty l1_tmp !l0_tmp;
        ] @ i3

    | VPMULH ws ->
        let a1,i1 = cast_vector_atome ws VE16 (List.nth es 0) in
        let a2,i2 = cast_vector_atome ws VE16 (List.nth es 1) in
        let s = int_of_ws ws in
        let v = s / 16 in
        let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
        let l = I.glval_to_lval (List.nth xs 0) in
        let i3 = cast_atome_vector ws v !l_tmp l in
        let l_tmp1 = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
        i1 @ i2 @ [CL.Instr.Op2_2.mull l_tmp l_tmp1 a1 a2] @ i3

    | VPSRA (ve, ws) ->
      begin
        let l = ["smt", `Smt ; "default", `Default] in
        let trans = trans annot l in
        let a1,i1 = cast_vector_atome ws ve (List.nth es 0) in
        let (c, _) = I.gexp_to_const(List.nth es 1) in
        let v = int_of_velem ve in
        let s = int_of_ws ws in
        match trans with
        | `Default ->
            let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
            let l = I.glval_to_lval (List.nth xs 0) in
            let i3 = cast_atome_vector ws v !l_tmp l in
            let l_tmp1 = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
            i1 @ [CL.Instr.Shifts.split l_tmp l_tmp1 a1 c] @ i3
        | `Smt ->
          let l1_tmp = I.mk_tmp_lval ~sign:true ~vector:(v,s/v) (CoreIdent.tu ws) in
          let (_, l1_ty) = I.get_lval l1_tmp in
          let l2_tmp = I.mk_tmp_lval ~sign:true ~vector:(v,s/v) (CoreIdent.tu ws) in
          let (_, l2_ty) = I.get_lval l2_tmp in
          let l3_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
          let l4_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
          let l = I.glval_to_lval (List.nth xs 0) in
          let i2 = cast_atome_vector ws v !l4_tmp l in
          i1 @ [CL.Instr.cast l1_ty l1_tmp a1;
                CL.Instr.Shifts.split l2_tmp l3_tmp !l1_tmp c;
                CL.Instr.cast l2_ty l4_tmp !l2_tmp] @ i2
      end

    | VPBROADCAST (ve, ws) ->
      begin
        let a1,i1 = cast_vector_atome ws ve (List.nth es 0) in
        let v = int_of_velem ve in
        let s = int_of_ws ws in
        let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
        let l = I.glval_to_lval (List.nth xs 0) in
        let i2 = cast_atome_vector ws v !l_tmp l in
        i1 @ [CL.Instr.Op1.mov l_tmp a1] @ i2
      end

    | _ ->
      let x86_id = X86_instr_decl.x86_instr_desc Build_Tabstract o in
      let name = (x86_id.id_pp_asm []).pp_aop_name in
      let msg =
        Format.asprintf "Unsupport operator in %s translation" S.error
      in
      hierror ~loc:(Lone loc) ~kind:msg  "%s" name

  let extra_op_to_instr annot loc xs (o:extra_op) es =
    match o with
    | Ox86MULX  ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l1 = I.glval_to_lval (List.nth xs 0) in
      let l2 = I.glval_to_lval (List.nth xs 1) in
      i1 @ i2 @ [CL.Instr.Op2_2.mull l1 l2 a1 a2;]
    | Oset0 ws ->
      let a = I.mk_const_atome ~sign:false (int_of_ws ws) Z.zero in
      let l1 = I.glval_to_lval (List.nth xs 0) in
      let l2 = I.glval_to_lval (List.nth xs 1) in
      let l3 = I.glval_to_lval (List.nth xs 2) in
      let l4 = I.glval_to_lval (List.nth xs 3) in
      let l5 = I.glval_to_lval (List.nth xs 4) in
      let l6 = I.glval_to_lval (List.nth xs 5) in
      [CL.Instr.clear l1; CL.Instr.clear l2; CL.Instr.clear l3; CL.Instr.clear l4; CL.Instr.clear l5; CL.Instr.Op1.mov l6 a;]
    | _ ->
      let x86_id = X86_extra.get_instr_desc Build_Tabstract X86_arch_full.X86_core.atoI o in
      let name = x86_id.str () in
      let msg =
        Format.asprintf "Unsupport extra operator in %s translation" S.error
      in
      hierror ~loc:(Lone loc) ~kind:msg  "%s" name

end

module X86BaseOpS : BaseOp
  with type op = X86_instr_decl.x86_op
  with type extra_op = X86_extra.x86_extra_op
= struct

  type op = X86_instr_decl.x86_op
  type extra_op = X86_extra.x86_extra_op


  module S = struct
    let s = true
    let error = "signed x86"
  end

  module I = I (S)

  let cast_atome ws x =
    match x with
    | Pvar va ->
      let ws_x = ws_of_ty (L.unloc va.gv).v_ty in
      if ws = ws_x then I.gexp_to_atome  x,[]
      else
        let e = I.gexp_to_atome x in
        let v = L.unloc va.gv in
        let kind = v.v_kind in
        let lx = I.mk_tmp_lval ~kind (CoreIdent.tu ws) in
        let (_,ty) as x = I.get_lval lx in
        CL.Instr.Avar x, [CL.Instr.cast ty lx e]
    | Papp1 (Oword_of_int ws_x, Pconst z) ->
      if ws = ws_x then I.gexp_to_atome  x,[]
      else
        let e = I.gexp_to_atome x in
        let lx = I.mk_tmp_lval  (CoreIdent.tu ws) in
        let (_,ty) as x = I.get_lval lx in
        CL.Instr.Avar x, [CL.Instr.cast ty lx e]
    | _ -> assert false

  let (!) e = I.mk_lval_atome e

  let cast_vector_atome ws v x =
    let a,i = cast_atome ws x in
    let a1 = CL.Instr.Avatome [a] in
    let v = int_of_velem v in
    let s = int_of_ws ws in
    let l_tmp = I.mk_tmp_lval ~vector:(1,s) (CoreIdent.tu ws) in
    let l_tmp2 = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
    let l_tmp2v = I.get_lval l_tmp2 in
    let ty = CL.(Vector (v, Sint (s/v))) in
    CL.Instr.Avar l_tmp2v,
    i @ [CL.Instr.Op1.mov l_tmp a1;
          CL.Instr.cast ty l_tmp2 !l_tmp;
        ]

  let cast_atome_vector ws v x l =
    let s = int_of_ws ws in
    let l_tmp = I.mk_tmp_lval ~vector:(1,s) (CoreIdent.tu ws) in
    let l_tmpv = I.get_lval l_tmp in
    let ty = CL.(Vector (v, Sint s)) in
    let a = CL.Instr.Avecta (l_tmpv, 0) in
    [CL.Instr.cast ty l_tmp x;
      CL.Instr.Op1.mov l a
    ]

  let vpc_atome ws x =
    match x with
    | Pvar va ->
      let ws_x = ws_of_ty (L.unloc va.gv).v_ty in
      if ws = ws_x then I.gexp_to_atome  x,[]
      else
        let e = I.gexp_to_atome x in
        let v = L.unloc va.gv in
        let kind = v.v_kind in
        let lx = I.mk_tmp_lval ~kind (CoreIdent.tu ws) in
        let (_,ty) as x = I.get_lval lx in
        CL.Instr.Avar x, [CL.Instr.vpc ty lx e]
    | Papp1 (Oword_of_int ws_x, Pconst z) ->
      if ws = ws_x then I.gexp_to_atome  x,[]
      else
        let e = I.gexp_to_atome x in
        let lx = I.mk_tmp_lval  (CoreIdent.tu ws) in
        let (_,ty) as x = I.get_lval lx in
        CL.Instr.Avar x, [CL.Instr.vpc ty lx e]
    | _ -> assert false

  let (!) e = I.mk_lval_atome e

  let assgn_to_instr _annot x e =
    let a = I.gexp_to_atome  e in
    let l = I.glval_to_lval  x in
    [CL.Instr.Op1.mov l a]

  let op_to_instr annot loc xs o es =
    match o with
    | X86_instr_decl.MOV ws ->
      begin
        let l = ["smt", `Smt ; "default", `Default] in
        let trans = trans annot l in
        match trans with
      | `Smt -> let a, i = vpc_atome ws (List.nth es 0) in
        let l = I.glval_to_lval (List.nth xs 0) in
        i @ [CL.Instr.Op1.mov l a]
      | `Default ->
        let a,i = cast_atome ws (List.nth es 0) in
        let l = I.glval_to_lval  (List.nth xs 0) in
        i @ [CL.Instr.Op1.mov l a]
      end
    | ADD ws ->
      begin
      let l = ["smt", `Smt ; "default", `Default] in
      let trans = trans annot l in
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
        match trans with
        | `Smt ->
          i1 @ i2 @ [CL.Instr.Op2.add l a1 a2]
        | `Default ->
          let l_tmp = I.mk_spe_tmp_lval ~sign:false 1 in
          i1 @ i2 @ [CL.Instr.Op2_2.adds l_tmp l a1 a2]
      end

    | SUB ws ->
      begin
        let l = ["smt", `Smt ; "default", `Default] in
        let trans = trans annot l in
        let a1, i1 = cast_atome ws (List.nth es 0) in
        let a2, i2 = cast_atome ws (List.nth es 1) in
        let l = I.glval_to_lval (List.nth xs 5) in
        match trans with
        | `Smt ->
          i1 @ i2 @ [CL.Instr.Op2.sub l a1 a2]
        | `Default ->
          let l_tmp = I.mk_spe_tmp_lval  ~sign:false 1 in
          i1 @ i2 @ [CL.Instr.Op2_2.subb l_tmp l a1 a2]
      end

    | IMULr ws
    | IMULri ws ->
      let l = ["smt", `Smt; "default", `Default] in
      let trans = trans annot l in
      begin match trans with
      | `Default ->
        let a1, i1 = cast_atome ws (List.nth es 0) in
        let a2, i2 = cast_atome ws (List.nth es 1) in
        let l = I.glval_to_lval (List.nth xs 5) in
        let l_tmp = I.mk_tmp_lval (CoreIdent.tu ws) in
        let l_tmp1 = I.mk_tmp_lval ~sign:false (CoreIdent.tu ws) in
        let ty = CL.Sint (int_of_ws ws) in
        i1 @ i2 @ [CL.Instr.Op2_2.mull l_tmp l_tmp1 a1 a2;
                   CL.Instr.cast ty l !l_tmp1]

      | `Smt ->
        let a1, i1 = cast_atome ws (List.nth es 0) in
        let a2, i2 = cast_atome ws (List.nth es 1) in
        let l = I.glval_to_lval (List.nth xs 5) in
        i1 @ i2 @ [CL.Instr.Op2.mul l a1 a2]
      end

    | NEG ws ->
      let a = I.mk_const_atome (int_of_ws ws) Z.zero in
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ [CL.Instr.Op2.sub l a a1]

    | INC ws ->
      let a1 = I.mk_const_atome (int_of_ws ws)   Z.one in
      let a2,i2 = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 4) in
      let l_tmp = I.mk_spe_tmp_lval ~sign:false 1 in
      i2 @ [CL.Instr.Op2_2.adds l_tmp l a1 a2]

    | DEC ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2 = I.mk_const_atome (int_of_ws ws)   Z.one in
      let l = I.glval_to_lval (List.nth xs 4) in
      let l_tmp = I.mk_spe_tmp_lval ~sign:false 1 in
      i1 @ [CL.Instr.Op2_2.subb l_tmp l a1 a2]

    | SHL ws ->
      begin
        let l = ["smt", `Smt ; "default", `Default] in
        let trans = trans annot l in
        match trans with
        | `Smt ->
          let a, i = cast_atome ws (List.nth es 0) in
          let (c,_) = I.gexp_to_const  (List.nth es 1) in
          let l = I.glval_to_lval  (List.nth xs 5) in
          i @ [CL.Instr.Shift.shl l a c]
        | `Default ->
          let a, i = cast_atome ws (List.nth es 0) in
          let (c,_) = I.gexp_to_const (List.nth es 1) in
          let l = I.glval_to_lval (List.nth xs 5) in
          let l_tmp = I.mk_spe_tmp_lval  (Z.to_int c) in
          i @ [CL.Instr.Shifts.shls l_tmp l a c]
        (* maybe do a multiplication *)
      end

    | SAR ws ->
      begin
        let l = ["default", `Default; "force_low_zero", `ForceLowZero] in
        let trans = trans annot l in
        match trans with
        | `Default->
          let a1,i1 = cast_atome ws (List.nth es 0) in
          let c = I.get_const (List.nth es 1) in
          (* let l_tmp = I.mk_spe_tmp_lval (int_of_ws ws) in *)
          let l_tmp = I.mk_spe_tmp_lval ~sign:false c in
          let l = I.glval_to_lval (List.nth xs 5) in
          let c = Z.of_int c in
          i1 @ [CL.Instr.Shifts.sars l l_tmp a1 c]
        | `ForceLowZero ->
          let a1,i1 = cast_atome ws (List.nth es 0) in
          let c = I.get_const (List.nth es 1) |> Z.of_int in
          let l = I.glval_to_lval (List.nth xs 5) in
          i1 @ [CL.Instr.Shift.sar l a1 c]
      end

    | MOVSX (ws1, ws2) ->
      begin
        let l = ["smt", `Smt1; "smt_two", `Smt2 ; "default", `Default] in
        let trans = trans annot l in

        match trans with
        | `Smt1 ->
          let a,i = cast_atome ws2 (List.nth es 0) in
          let sign = true in
          let l_tmp1 = I.mk_tmp_lval ~sign (CoreIdent.tu ws2) in
          let ty1 = CL.Sint (int_of_ws ws2) in
          let l_tmp2 = I.mk_tmp_lval ~sign (CoreIdent.tu ws1) in
          let ty2 = CL.Sint (int_of_ws ws1) in
          let l = I.glval_to_lval (List.nth xs 0) in
          let ty3 = CL.Uint (int_of_ws ws1) in
          i @ [CL.Instr.cast ty1 l_tmp1 a;
               CL.Instr.cast ty2 l_tmp2 !l_tmp1;
               CL.Instr.cast ty3 l !l_tmp2]
        | `Smt2 ->
          let a, i = vpc_atome ws2 (List.nth es 0) in
          let l = I.glval_to_lval (List.nth xs 0) in
          i @ [CL.Instr.vpc (CL.Sint (int_of_ws ws1)) l a]

        | `Default ->
          let a,i = cast_atome ws2 (List.nth es 0) in
          let l = I.glval_to_lval (List.nth xs 0) in
          i @ [CL.Instr.cast (CL.Sint (int_of_ws ws1)) l a]
      end

    | VPSUB (ve,ws) ->
      begin
        let l = ["smt", `Smt ; "default", `Default] in
        let trans = trans annot l in
        let a1,i1 = cast_vector_atome ws ve (List.nth es 0) in
        let a2,i2 = cast_vector_atome ws ve (List.nth es 1) in
        let v = int_of_velem ve in
        let s = int_of_ws ws in
        let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
        let l = I.glval_to_lval (List.nth xs 0) in
        let i3 = cast_atome_vector ws v !l_tmp l in
        match trans with
          | `Smt ->
            i1 @ i2 @ [CL.Instr.Op2.sub l_tmp a1 a2] @ i3
          | `Default ->
            let l_tmp1 = I.mk_tmp_lval ~vector:(v,1) (CoreIdent.tu (I.wsize_of_int v)) in
            i1 @ i2 @ [CL.Instr.Op2_2.subb l_tmp1 l_tmp a1 a2] @ i3
      end

    | VPMULL (v,ws) ->
      let a1,i1 = cast_vector_atome ws v (List.nth es 0) in
      let a2,i2 = cast_vector_atome ws v (List.nth es 1) in
      let v = int_of_velem v in
      let s = int_of_ws ws in
      let l0_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
      let l1_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
      let (_, l1_ty) = I.get_lval l1_tmp in
      let l = I.glval_to_lval (List.nth xs 0) in
      let i3 = cast_atome_vector ws v !l1_tmp l in
      i1 @ i2 @ [
        CL.Instr.Op2.smul l0_tmp a1 a2;
        CL.Instr.cast l1_ty l1_tmp !l0_tmp;
      ] @ i3

    | VPMULH ws ->
      let a1,i1 = cast_vector_atome ws VE16 (List.nth es 0) in
      let a2,i2 = cast_vector_atome ws VE16 (List.nth es 1) in
      let s = int_of_ws ws in
      let v = s / 16 in
      let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
      let l_tmp1 = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
      let l = I.glval_to_lval (List.nth xs 0) in
      let i3 = cast_atome_vector ws v !l_tmp l in
      i1 @ i2 @ [CL.Instr.Op2_2.mull l_tmp l_tmp1 a1 a2] @ i3

    | VPSRA (ve, ws) ->
      begin
        let l = ["smt", `Smt ; "default", `Default] in
        let trans = trans annot l in
        let a1,i1 = cast_vector_atome ws ve (List.nth es 0) in
        let rec repeat acc n x =
          if n == 0 then acc else repeat (x :: acc) (n - 1) x in
        let (c, _) = I.gexp_to_const(List.nth es 1) in
        let ac = repeat [] 16 c in
        let v = int_of_velem ve in
        let s = int_of_ws ws in
        let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
        let l = I.glval_to_lval (List.nth xs 0) in
        let i2 = cast_atome_vector ws v !l_tmp l in
        match trans with
        | `Default ->
            let l_tmp1 = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
            i1 @ [CL.Instr.Shifts.vsars l_tmp l_tmp1 a1 ac] @ i2
        | `Smt ->
          i1 @ [CL.Instr.Shift.vsar l_tmp a1 ac] @ i2
      end

    | _ ->
      let x86_id = X86_instr_decl.x86_instr_desc Build_Tabstract o in
      let name = (x86_id.id_pp_asm []).pp_aop_name in
      let msg =
        Format.asprintf "@[Unsupport operator in %s translation]@ " S.error;
      in
      hierror ~loc:(Lone loc) ~kind: msg "%s" name

  let extra_op_to_instr annot loc xs (o:extra_op) es =
    match o with
    | _ ->
      let x86_id = X86_extra.get_instr_desc Build_Tabstract X86_arch_full.X86_core.atoI o in
      let name = x86_id.str () in
      let msg =
        Format.asprintf "Unsupport extra operator in %s translation" S.error
      in
      hierror ~loc:(Lone loc) ~kind:msg  "%s" name

end

let x86BaseOpsign s :
  (module BaseOp  with type op = X86_instr_decl.x86_op
                   and type extra_op = X86_extra.x86_extra_op
  )
  =
  if s then (module X86BaseOpS)
  else (module X86BaseOpU)

module ARMBaseOp : BaseOp
  with type op = Arm_instr_decl.arm_op
   and  type extra_op = Arm_extra.arm_extra_op
= struct

  open Arm_instr_decl

  type op = Arm_instr_decl.arm_op
  type extra_op = Arm_extra.arm_extra_op

  module S = struct
    let s = false
    let error = "Unsiged ARM"
  end

  module I = I (S)

  let ws = Wsize.U32

  let assgn_to_instr trans x e = assert false

  let op_to_instr trans loc xs o es =
    let mn, opt = match o with Arm_instr_decl.ARM_op (mn, opt) -> mn, opt in
    match mn with
    | _ ->
      let arm_id = Arm_instr_decl.arm_instr_desc Build_Tabstract o in
      let name = (arm_id.id_pp_asm []).pp_aop_name in
      let msg =
        Format.asprintf "@[Unsupport operator in %s translation]@ " S.error
      in
      hierror ~loc:(Lone loc) ~kind:msg "%s" name

  let extra_op_to_instr annot loc xs (o:extra_op) es =
    match o with
    | _ ->
      let x86_id = Arm_extra.get_instr_desc Build_Tabstract o in
      let name = x86_id.str () in
      let msg =
        Format.asprintf "Unsupport extra operator in %s translation" S.error
      in
      hierror ~loc:(Lone loc) ~kind:msg  "%s" name

end

let sub_fun_params params args =
  let assoc = List.combine params args in
  let subst_v v =
    try snd (List.find (fun (vi, _) -> (L.unloc v.gv).v_id = (L.unloc vi).v_id) assoc)
    with Not_found -> Pvar v in
  let subst = Subst.gsubst_e (fun ?loc:_ x -> x) subst_v in
  List.map (fun (prover,clause) -> prover, subst clause)

let sub_fun_returns res lval =
  let to_expr lv =
    match lv with
    | Lvar v -> Pvar {gv = v; gs = Expr.Slocal}
    | _ -> assert false in
  sub_fun_params res (List.map to_expr lval)

let armeBaseOpsign _s :
  (module BaseOp  with type op = Arm_instr_decl.arm_op
                   and type extra_op = Arm_extra.arm_extra_op
  )
  =
  (module ARMBaseOp)


module Mk(O:BaseOp) = struct


  let pp_ext_op loc xs o es trans =
    match o with
    | Arch_extra.BaseOp (_, o) -> O.op_to_instr trans loc xs o es
    | Arch_extra.ExtOp o -> O.extra_op_to_instr trans loc xs o es

  let pp_sopn loc xs o es tcas =
    match o with
    | Sopn.Opseudo_op _ -> assert false
    | Sopn.Oslh _ -> assert false
    | Sopn.Oasm o -> pp_ext_op loc xs o es tcas

  let rec filter_clause cs (cas,smt) =
    match cs with
    | [] -> cas,smt
    | (Expr.Cas,c)::q -> filter_clause q (c::cas,smt)
    | (Expr.Smt,c)::q -> filter_clause q (cas,c::smt)

  let to_smt smt =
    List.fold_left (fun acc a -> O.I.gexp_to_rpred a ::  acc) [] smt

  let to_cas env cas =
    List.fold_left (fun acc a -> O.I.gexp_to_epred env a  @ acc) [] cas

  let to_clause env clause : CL.clause =
    let cas,smt = filter_clause clause ([],[]) in
    let smt = to_smt smt in
    let cas = to_cas env cas in
    (cas,smt)

  let pp_i env fds i =
    let trans = i.i_annot in
    match i.i_desc with
    | Cassert (t, p, e) ->
      let cl = to_clause env [(p,e)] in
      begin
        match t with
        | Expr.Assert -> [], [CL.Instr.assert_ cl]
        | Expr.Assume -> [], [CL.Instr.assume cl]
        | Expr.Cut -> assert false
      end
    | Csyscall _ | Cif _ | Cfor _ | Cwhile _ -> assert false
    | Ccall (r,f,params) ->
      let fd = List.find (fun fd -> fd.f_name.fn_id = f.fn_id) fds in
      let pre_cl, post_cl =
        match fd.f_contra with
        | None -> [], []
        | Some ci ->
            let pre = sub_fun_params ci.f_iparams params ci.f_pre in
            let pre_cl = to_clause env pre in
            let post = sub_fun_params ci.f_iparams params ci.f_post in
            let post = sub_fun_returns ci.f_ires r post in
            let post_cl = to_clause env post in
            [CL.Instr.assert_ pre_cl], [CL.Instr.assume post_cl]
        in
      (* FIXME: How are we sure that the variables in r are fresh ? *)
      r , pre_cl @ post_cl

    | Cassgn (a, _, _, e) ->
      begin
        match a with
        | Lvar x -> [], O.assgn_to_instr trans a e
        | Lnone _ | Lmem _ | Laset _ |Lasub _ -> assert false
      end
    | Copn(xs, _, o, es) -> [], pp_sopn i.i_loc.base_loc xs o es trans

  let pp_c env fds c =
    (* FIXME: this is really a bad complexity *)
    List.fold_left (fun (acc1,acc2) a ->
        let l1,l2 = pp_i env fds a in
        acc1 @ l1, acc2 @ l2
      ) ([],[]) c

  let filter_add cond l1 l2 =
    (* FIXME : use a set it will be more efficiant *)
    List.fold_left (
        fun l a ->
          if List.exists (cond a) l
          then l else a :: l
      ) l1 l2

  let fun_to_proc fds fd =
    let env = Hash.create 10 in
    let ret = List.map L.unloc fd.f_ret in
    let ret_vars = List.map O.I.var_to_tyvar ret in (* OUTPUT vars as formals *)
    let cond a x = (x.v_name = a.v_name) && (x.v_id = a.v_id) in
    let args = filter_add cond fd.f_args ret in
    let formals = List.map O.I.var_to_tyvar args in
    let pre, post =
      match fd.f_contra with
      | None -> ([],[]), ([],[])
      | Some ci ->
        let params = List.map (fun x -> Pvar (Prog.gkvar (L.mk_loc x.v_dloc x))) fd.f_args in
        let pre = sub_fun_params ci.f_iparams params ci.f_pre in
        let pre = to_clause env pre in
        let post = sub_fun_params ci.f_iparams params ci.f_post in
        let r = List.map (fun x -> Lvar x) fd.f_ret in
        let post = sub_fun_returns ci.f_ires r post in
        let post = to_clause env post in
        pre, post in
    let lval,prog = pp_c env fds fd.f_body in
    let formals_lval = List.map (fun x -> O.I.get_lval (O.I.glval_to_lval x)) lval in
    let cond (a,_) (x,_) = (x.v_name = a.v_name) && (x.v_id = a.v_id) in
    let formals = filter_add cond formals formals_lval in
    let ghost = ref [] in
    Hash.iter (fun _ x -> ghost := (O.I.get_lval x) :: ! ghost) env;
    let formals = filter_add cond formals !ghost in

    CL.Proc.{id = fd.f_name.fn_name;
             formals;
             pre;
             prog;
             post;
             ret_vars}

end
